;;; beluga-mode.el --- Major mode for Beluga source code  -*- coding: utf-8 -*-

;; Copyright (C) 2009, 2010  Stefan Monnier

;; Author: Stefan Monnier <monnier@iro.umontreal.ca>
;; Keywords: 

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; BUGS

;; - Indentation thinks "." can only be the termination marker of
;;   an LF declaration.  This can mess things up badly.
;; - Indentation after curried terms like "fn x => fn y =>" is twice that
;;   after "fn x y =>".

;;; Code:

(eval-when-compile (require 'cl))

(defgroup beluga-mode ()
  "Editing support for the Beluga language."
  :group 'languages)

(defvar beluga-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\C-c\C-c" 'compile)
    map))

(defvar beluga-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?% "< 14" st)
    (modify-syntax-entry ?\{ "(}2 b" st)
    (modify-syntax-entry ?\} "){3 b" st)
    (modify-syntax-entry ?\n ">" st)
    ;; For application of dependent arguments "exp A < ctx . term >", we'd want
    ;; <..> to match, but that breaks ->, <-, and other things.
    ;; (modify-syntax-entry ?< "(>" st)
    ;; (modify-syntax-entry ?> ")<" st)
    (modify-syntax-entry ?#  "'" st)
    (modify-syntax-entry ?< "." st)
    (modify-syntax-entry ?> "." st)
    (modify-syntax-entry ?- "." st)
    (modify-syntax-entry ?= "." st)
    st))

(defcustom beluga-font-lock-symbols t
  "Display \\ and -> and such using symbols in fonts.
This may sound like a neat trick, but be extra careful: it changes the
alignment and can thus lead to nasty surprises w.r.t layout.
If t, try to use whichever font is available.  Otherwise you can
set it to a particular font of your preference among `japanese-jisx0208'
and `unicode'."
  :type '(choice (const nil)
	         (const t)
	         (const unicode)
	         (const japanese-jisx0208)))

(defconst beluga-font-lock-symbols-alist
  ;; Not sure about fn → λ, since we could also have \ → λ.
  (append
   ;; The symbols can come from a JIS0208 font.
   (and (fboundp 'make-char) (fboundp 'charsetp) (charsetp 'japanese-jisx0208)
	(memq beluga-font-lock-symbols '(t japanese-jisx0208))
	(list (cons "not" (make-char 'japanese-jisx0208 34 76))
	      ;; (cons "fn" (make-char 'japanese-jisx0208 38 75))
	      ;;(cons "\" (make-char 'japanese-jisx0208 38 75))
              (cons "Sigma" (make-char 'japanese-jisx0208 38 50))
	      (cons "FN" (make-char 'japanese-jisx0208 38 43))
	      (cons "->" (make-char 'japanese-jisx0208 34 42))
	      (cons "<-" (make-char 'japanese-jisx0208 34 43))
	      (cons "=>" (make-char 'japanese-jisx0208 34 77))
	      ;; (cons ".." (make-char 'japanese-jisx0208 33 68)) ; "..."
	      ;; (cons ".." (make-char 'japanese-jisx0208 33 69)) ; Why bother?
              ;; (cons "forall" (make-char 'japanese-jisx0208 34 79))
              ))
   ;; Or a unicode font.
   (and (fboundp 'decode-char)
	(memq beluga-font-lock-symbols '(t unicode))
	'(;;("not"   . ?¬)
          ;; ("fn"    . ?λ)
          ("FN"    . ?Λ)
          ("Sigma" . ?Σ)
          ("->"    . ?→)
          ("<-"    . ?←)
          ("=>"    . ?⇒)
          ;; ("::"    . ?∷)
          (".." . ?…) ; Actually "..."
          ;;(".."    . ?‥)
          ;; ("forall" . ?∀)
          )))
  "Alist mapping Beluga symbols to chars.
Each element has the form (STRING . CHAR) or (STRING CHAR PREDICATE).
STRING is the Beluga symbol.
CHAR is the character with which to represent this symbol.
PREDICATE if present is a function of one argument (the start position
of the symbol) which should return non-nil if this mapping should be disabled
at that position.")

(defun beluga-font-lock-compose-symbol (alist)
  "Compose a sequence of ascii chars into a symbol.
Regexp match data 0 points to the chars."
  ;; Check that the chars should really be composed into a symbol.
  (let* ((start (match-beginning 0))
         (end (match-end 0))
	 (syntaxes (cond
                    ((eq (char-syntax (char-after start)) ?w) '(?w))
                    ;; Special case for the . used for qualified names.
                    ((and (eq (char-after start) ?\.) (= end (1+ start)))
                     '(?_ ?\\ ?w))
                    (t '(?_ ?\\))))
         sym-data)
    (if (or (memq (char-syntax (or (char-before start) ?\ )) syntaxes)
	    (memq (char-syntax (or (char-after end) ?\ )) syntaxes)
	    (memq (get-text-property start 'face)
		  '(font-lock-doc-face font-lock-string-face
		    font-lock-comment-face))
            (and (consp (setq sym-data (cdr (assoc (match-string 0) alist))))
                 (let ((pred (cadr sym-data)))
                   (setq sym-data (car sym-data))
                   (funcall pred start))))
	;; No composition for you.  Let's actually remove any composition
	;; we may have added earlier and which is now incorrect.
	(remove-text-properties start end '(composition))
      ;; That's a symbol alright, so add the composition.
      (compose-region start end sym-data)))
  ;; Return nil because we're not adding any face property.
  nil)

(defun beluga-font-lock-symbols-keywords ()
  (when (fboundp 'compose-region)
    (let ((alist nil))
      (dolist (x beluga-font-lock-symbols-alist)
	(when (and (if (fboundp 'char-displayable-p)
		       (char-displayable-p (if (consp (cdr x)) (cadr x) (cdr x)))
		     t)
		   (not (assoc (car x) alist)))	;Not yet in alist.
	  (push x alist)))
      (when alist
	`((,(regexp-opt (mapcar 'car alist) t)
	   (0 (beluga-font-lock-compose-symbol ',alist)
              ;; In Emacs-21, if the `override' field is nil, the face
              ;; expressions is only evaluated if the text has currently
              ;; no face.  So force evaluation by using `keep'.
              keep)))))))

(defvar beluga-syntax-id-re "[[:alpha:]_][[:alnum:]_']*")
(defvar beluga-syntax-fundec-re "^[ \t]*\\(rec\\|and\\)\\>")

(defvar beluga-font-lock-keywords
  `(,(concat (regexp-opt
              '("FN" "and" "block" "case" "fn" "else" "if" "in" "let" "mlam"
                "impossible" "of" "rec" "schema" "some" "then" "type" "ttrue"
                "ffalse" "%name" "%not") 'words)
             "\\|\\\\")
    (,(concat "^\\(" beluga-syntax-id-re
              "\\)[ \t\n]*:\\([^.]*\\<type\\>[ \t\n]*.\\)?")
     ;; This is a regexp that can span multiple lines, so it may not
     ;; always highlight properly.  `font-lock-multiline' tries to help.
     (0 (if (match-end 2) '(face nil font-lock-multiline t)))
     (1 (if (match-end 2)
            font-lock-type-face font-lock-variable-name-face)))
    (,(concat "^schema[ \t\n]+\\(" beluga-syntax-id-re "\\)")
     (1 font-lock-type-face))
    (,(concat beluga-syntax-fundec-re "[ \t\n]+\\(" beluga-syntax-id-re "\\)")
     (2 font-lock-function-name-face))
    ,@(beluga-font-lock-symbols-keywords)))

(defvar beluga-imenu-generic-expression
  `(("Schemas"
     ,(concat "^[ \t]*schema[ \t\n]+\\(" beluga-syntax-id-re "\\)") 1)
    ("Constructors"
     ,(concat "^\\(" beluga-syntax-id-re "\\)[ \t\n]*:") 1)
    ("Type Constructors"
     ,(concat "^\\(" beluga-syntax-id-re "\\)[ \t\n]*:[^.]*\\<type\\>[ \t\n]*.") 1)
    ("Functions"
     ,(concat beluga-syntax-fundec-re "[ \t\n]+\\(" beluga-syntax-id-re "\\)") 1)))

(define-obsolete-variable-alias 'beluga-interpreter-path
  ;; A "path" is a list of file names, as in $PATH, $MANPATH.
  'beluga-interpreter-name "Sep-2010")
(defcustom beluga-interpreter-name "beluga"
  "Name of the interpreter executable."
  :type 'string)

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.bel\\'" . beluga-mode))
(add-to-list 'auto-mode-alist '("\\.sbel\\'" . beluga-mode))

;;;###autoload
(define-derived-mode beluga-mode nil "Beluga"
  "Major mode to edit Beluga source code."
  (set (make-local-variable 'imenu-generic-expression)
       beluga-imenu-generic-expression)
  (set (make-local-variable 'outline-regexp) beluga-syntax-fundec-re)
  (set (make-local-variable 'require-final-newline) t)
  (when buffer-file-name
    (set (make-local-variable 'compile-command)
         ;; Quite dubious, but it's the intention that counts.
         (concat beluga-interpreter-name
                 " " (shell-quote-argument buffer-file-name))))
  (set (make-local-variable 'comment-start) "% ")
  (set (make-local-variable 'comment-start-skip) "%[%{]*[ \t]*")
  (set (make-local-variable 'comment-end-skip) "[ \t]*\\(?:\n\\|}%\\)")
  (comment-normalize-vars)
  (set (make-local-variable 'electric-indent-chars)
       (append '(?|) (if (boundp 'electric-indent-chars)
                         electric-indent-chars
                       '(?\n))))
  ;; SMIE setup.
  (set (make-local-variable 'parse-sexp-ignore-comments) t)
  (smie-setup beluga-smie-grammar #'beluga-smie-rules
              :forward-token #'beluga-smie-forward-token
              :backward-token #'beluga-smie-backward-token)
  ;; (set (make-local-variable 'belugasmie-closer-alist)
  ;;      '(("<" . ">"))) ;; (t . ".")
  
  (set (make-local-variable 'font-lock-defaults)
       '(beluga-font-lock-keywords nil nil () nil
         (font-lock-syntactic-keywords . nil))))

;;; Emacs-22 compatibility.

(eval-when-compile
  (unless (fboundp 'with-demoted-errors)
    (defmacro with-demoted-errors (&rest body)
      "Run BODY and demote any errors to simple messages."
      (declare (debug t) (indent 0))
      (let ((err (make-symbol "err")))
        `(condition-case ,err
             (progn ,@body)
           (error (message "Error: %s" ,err) nil))))))

(unless (fboundp 'string-prefix-p)
  (defun string-prefix-p (str1 str2 &optional ignore-case)
    "Return non-nil if STR1 is a prefix of STR2.
If IGNORE-CASE is non-nil, the comparison is done without paying attention
to case differences."
    (eq t (compare-strings str1 nil nil
                           str2 0 (length str1) ignore-case))))
  

;;; Beluga indentation and navigation via SMIE

(defcustom beluga-indent-basic nil
  "Basic amount of indentation."
  :type 'integer)

(defconst beluga-smie-punct-re
  (regexp-opt '("->" "<-" "=>" "\\" "." "<" ">" "," ";" "..")))

(defun beluga-smie-forward-token ()
  (forward-comment (point-max))
  (if (looking-at "\\.[ \t]*\\(?:$\\|[0-9]\\(\\)\\)")
      ;; Either an LF-terminating dot, or a projection-dot.
      (progn (forward-char 1) (if (match-end 1) ".n" ";."))
    (buffer-substring-no-properties
     (point)
     (progn (cond
             ((looking-at beluga-smie-punct-re) (goto-char (match-end 0)))
             ((not (zerop (skip-syntax-forward "w_'"))))
             ;; In case of non-ASCII punctuation.
             ((not (zerop (skip-syntax-forward ".")))))
            (point)))))

(defun beluga-smie-backward-token ()
  (forward-comment (- (point-max)))
  (if (and (eq ?\. (char-before))
           (looking-at "[ \t]*\\(?:$\\|[0-9]\\(\\)\\)")
           (not (looking-back "\\.\\." (- (point) 2))))
      ;; Either an LF-terminating dot, or a projection-dot.
      (progn (forward-char -1) (if (match-end 1) ".n" ";."))
    (buffer-substring-no-properties
     (point)
     (progn (cond
             ((looking-back beluga-smie-punct-re (- (point) 2) 'greedy)
              (goto-char (match-beginning 0)))
             ((not (zerop (skip-syntax-backward "w_'"))))
             ;; In case of non-ASCII punctuation.
             ((not (zerop (skip-syntax-backward ".")))))
            (point)))))

(defconst beluga-smie-grammar
  ;; The "." used for terminating LF declarations is syntactically completely
  ;; different from the "." used in the binding forms.  Conflating the two
  ;; leads here to a lot of precedence conflicts, so we try and guess the two
  ;; based on a heuristic in the tokenizing code.
  (smie-prec2->grammar
   (smie-merge-prec2s
    (smie-bnf->prec2
     ;; FIXME: without this dummy, "=>" is marked as "open paren" because it
     ;; can only bind to `atom' on the left.
     '((atom ("--dummy--"))
       (def (exp "=" exp) (atom ":" exp))
       (decl (atom ":" type)
             ("schema" sdef)
             ("let" def)
             (recs))
       (simpletype (simpletype "->" simpletype)
                   (simpletype "<-" simpletype))
       (recs ("rec" def) (recs "and" recs))
       (decls (decl) (decls ";" decls) (decls ";." decls))
       ;; FIXME: only allow simple types here, otherwise we get nasty
       ;; precedence conflicts between "." and ",".  In practice, this seems to
       ;; be sufficient.
       (sdecl (atom ":" type))
       (sdecls (sdecl) (sdecls "," sdecls))
       (dotted-type (sdecls "." type))
       (type (simpletype)
             ("\\" atom "." type)       ;dotted-type
             ("block" sdecls "." type)  ;dotted-type
             ;; ("{" blabla "}" type)  ; FIXME!
             ;; FIXME: the projection via "." creates precedence conflicts.
             ;; (type "." atom)
             )
       (sdef (atom "=" schema))
       (schema (type)
               ;; Not sure if it's correct, and create precedence conflicts.
               ;; ("some" sdecls "block" sdecls "." schema)
               )
       (exp ("if" exp "then" exp "else" exp)
            (type)
            ("let" def "in" exp)
            ("fn" atom "=>" exp)
            ("FN" atom "=>" exp)
            ("mlam" atom "=>" exp)
            ("<" dotted-type ">")
            ("case" exp "of" cases))
       
       (exps (exps ";" exps) (exp))
       ;; Separate cases/branch so that "|" is recognized as associative.
       (cases (branch) (cases "|" cases))
       (branch (atom "=>" exp)))
     '((assoc ";" ";."))
     '((assoc "->" "<-"))
     '((assoc ","))
     '((assoc "and"))
     '((nonassoc "of") (assoc "|")) ; Trailing | ambiguity.
     ;; '((nonassoc "\\") (nonassoc ".")) ; Trailing . ambiguity.
     ;; '((nonassoc "block") (nonassoc ".")) ; Trailing . ambiguity.
     )

    ;; The above BNF grammar should cover this already, so this ends up only
    ;; useful to check that the BNF entails the expected precedences.
    (smie-precs->prec2
     '((assoc ";")
       (assoc ",")
       (left ":")
       (assoc "<-" "->")
       (nonassoc " -dummy- "))) ;Bogus anchor at the end.
     )))

(defun beluga-smie-rules (kind token)
  (case kind
    (:elem (if (eq token 'basic) beluga-indent-basic))
    (:list-intro (member token '("fn" "FN" "mlam")))
    (:before
     (cond
      ((equal token "|") 0) ;; (smie-rule-separator kind)
      ((member token '("case" "fn" "mlam"))
       (if (smie-rule-prev-p "=>") (smie-rule-parent)))))
    (:after
     (cond
      ((equal token "of") 2)
      ;; FIXME: we'd like some way to specify the indentation after =>
      ;; depending on whether it is a "=>" that goes with an "fn" or
      ;; with a "|".
      ((equal token "=>") 0)
      ;; Not sure what rule we want here.
      ;; ((equal token "=") (smie-rule-parent 2))
      ((equal token "in") (if (smie-rule-hanging-p) 0))
      ((equal token ":") (or beluga-indent-basic smie-indent-basic))))))

;; (defcustom beluga-indent-args beluga-indent-basic
;;   "Amount of indentation of args below their function."
;;   :type 'integer)

(provide 'beluga-mode)
;;; beluga-mode.el ends here
