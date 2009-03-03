;;; beluga-mode.el --- Major mode for Beluga source code  -*- coding: utf-8 -*-

;; Copyright (C) 2009  Stefan Monnier

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

;; 

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
    (modify-syntax-entry ?% "<" st)
    (modify-syntax-entry ?\n ">" st)
    (modify-syntax-entry ?#  "'" st)
    st))

(defcustom beluga-font-lock-symbols t
  "Display \\ and -> and such using symbols in fonts.
This may sound like a neat trick, but be extra careful: it changes the
alignment and can thus lead to nasty surprises w.r.t layout.
If t, try to use whichever font is available.  Otherwise you can
set it to a particular font of your preference among `japanese-jisx0208'
and `unicode'."
  :group 'beluga
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
	      (cons "fn" (make-char 'japanese-jisx0208 38 75))
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
	'(("not"   . ?¬)
          ("fn"    . ?λ)
          ("FN"    . ?Λ)
          ("Sigma" . ?Σ)
          ("->"    . ?→)
          ("<-"    . ?←)
          ("=>"    . ?⇒)
          ("::"    . ?∷)
          ;; (".." . ?…) ; Actually "..."
          (".."    . ?‥)
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
(defvar beluga-syntax-fundec-re "^[ \t]*rec\\>")

(defvar beluga-font-lock-keywords
  `(,(concat (regexp-opt '("FN" "fn" "case" "of" "rec" "schema" "in" "Sigma"
                           "block" "let" "some" "type") 'words)
             "\\|\\\\")
    (,(concat "^\\(" beluga-syntax-id-re "\\)[ \t\n]*:\\([^.]*\\<type\\>[ \t\n]*.\\)?")
     ;; This is a regexp that can span multiple lines, so it may not
     ;; always highlight properly.  `font-lock-multiline' tries to help.
     (0 (if (match-end 2) '(face nil font-lock-multiline t)))
     (1 (if (match-end 2)
            font-lock-type-face font-lock-variable-name-face)))
    (,(concat beluga-syntax-fundec-re "[ \t\n]+\\(" beluga-syntax-id-re "\\)")
     (1 font-lock-function-name-face))
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


;;;###autoload
(add-to-list 'auto-mode-alist '("\\.bel\\'" . beluga-mode))

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
         (concat "interpreter " (shell-quote-argument buffer-file-name))))
  (set (make-local-variable 'comment-start) "% ")
  (comment-normalize-vars)
  (set (make-local-variable 'indent-line-function) 'beluga-indent-line)
  (set (make-local-variable 'font-lock-defaults)
       '(beluga-font-lock-keywords nil nil () nil
         (font-lock-syntactic-keywords . nil))))

;;; Indentation

(defconst beluga-op-levels
  '(("of"      99  90  "case")
    ("let"    nil  80)                  ;..=..in..
    ("rec"    nil  80)                  ;..=..
    ;; How to represent the nestability of if..then..else?
    ("if"      nil 80)
    ("then"    75  75)
    ("else"    75  76)
    ("|"       80  80)
    ("in"      98  75  "let")           ;let..=..in
    ;; Adding "let" breaks indentation because beluga-indent-rules applies
    ;; to pairs where the first isn't mentioned here.
    ("="       80  80)
    ("fn"     nil  75)
    ("FN"     nil  75)
    ("=>"      70  70  "fn" "FN")
    ;; ("forall" nil  75)
    ;; ("end"      t nil  "case")
    (","       60  60)
    (":"       70  50)
    ("->"      40  40)
    ("<-"      40  40)
    (";"      150 150)
    ("."      200 200))
  "List of token info.
Each element is of the form (TOKEN LEFT-LEVEL RIGHT-LEVEL &rest STOPS).")

(defconst beluga-funlike-ops '("fn" "FN")
  "Keywords that take a variable number of arguments.
Those arguments will be aligned as if the keyword was a function.")

(defcustom beluga-indent-basic 4
  "Basic amount of indentation.")

(defcustom beluga-indent-args beluga-indent-basic
  "Amount of indentation of args below their function."
  :type 'integer)

(defconst beluga-indent-rules
  '((("if" . "then") . 0)
    ("of" 2)
    ("in" nil 0)
    ("=" 0)
    ("=>")
    ((t . "|") . -2)
    ("let") ("if"))
  "Rules of the following form.
\((TOK1 . TOK2) . OFFSET)	how to indent TOK2 w.r.t TOK1.
\(TOK OFFSET)			how to indent right after TOK.
\(TOK)				OFFSET defaults to `beluga-indent-basic'.")

(defun beluga-backward-token ()
  (buffer-substring (point)
                    (progn (if (zerop (skip-syntax-backward "."))
                               (skip-syntax-backward "w_'"))
                           (point))))

(defun beluga-forward-token ()
  (buffer-substring (point)
                    (progn (if (zerop (skip-syntax-forward "."))
                               (skip-syntax-forward "w_'"))
                           (point))))

(defun beluga-backward-sexp (&optional level stops)
  "Skip over one sexp.
Don't skip over an operator with right-level higher then LEVEL.
LEVEL can be:
  nil, meaning it's not decided yet.
  t, meaning we're inside parentheses and should only
     consider other parenthesized elements.
  a number.
Possible return values:
  (stop POS TOKEN): we skipped over TOKEN which is in STOPS.
  (LEFT-LEVEL POS TOKEN): we couldn't skip TOKEN because its right-level
    is higher than LEVEL.  LEFT-LEVEL is the left-level of TOKEN,
    POS is its start position in the buffer.
  (t POS): we bumped into an open paren or the beginning of buffer.
  (nil POS TOKEN): we skipped over a paren-like pair.
  nil: we skipped over an identifier, matched parentheses, ..."
  (if (bobp) (list t (point))
    (let* ((pos (point))
           (token (progn (forward-comment (- (point-max)))
                         (beluga-backward-token)))
           (tokinfo (cdr (assoc token beluga-op-levels))))

      ;; Closing a paren-like thingy.
      (if (member token stops)
          
          (list 'stop nil token)

        (if tokinfo
            (cond
             ;; Bumping into a paren-like thingy.
             ((or (eq (cadr tokinfo) t)
                  ;; For a token that's "nil N", we shouldn't bump into
                  ;; it if level > N because we may have skipped the
                  ;; corresponding non-paren closer.
                  (and (null level) (null (car tokinfo))))
              (prog1 (list t (point)) (goto-char pos)))
             ;; Bumping into an operator of higher right-level.
             ((and (numberp level) (numberp (cadr tokinfo))
                   (<= level (cadr tokinfo)))
              ;; If left-level is nil, then it's kind of like an open-paren,
              ;; so return t to indicate we bumped into an open-paren.
              (prog1 (list (or (car tokinfo) t) (point) token)
                (goto-char pos)))
             ;; Skipping an operator of lower left-level.
             ((and level (if (eq level t)
                             (not (eq (car tokinfo) t))
                           (or (null (car tokinfo))
                               (and (numberp (car tokinfo))
                                    (< (car tokinfo) level)))))
              nil)
             (t
              (let (res)
                (while (not
                        (car (setq res
                                   (beluga-backward-sexp
                                    (car tokinfo)
                                    ;; We append, so as to be more permissive
                                    ;; w.r.t mismatched parenthesized elements.
                                    (append stops (cddr tokinfo)))))))
                (case (car res)
                  ((t) res)
                  (stop (cons nil (cdr res)))
                  (t (if (or (not (numberp level))
                             (and (numberp (car res)) (< level (car res))))
                         res))))))
          (if (equal token "")
              (condition-case err
                  (progn (goto-char pos) (backward-sexp 1) nil)
                (scan-error (list t (caddr err))))
            nil))))))

(defun beluga-find-opener (re &optional level)
  (unless level (setq level 100))
  (while (progn
           (beluga-backward-sexp level)
           (not (looking-at re))))
  t)

(defun beluga-indent-hanging-p ()
  ;; A Hanging keyword is one that's at the end of a line except it's not at
  ;; the beginning of a line.
  (and (save-excursion (beluga-forward-token)
                       (skip-chars-forward " \t") (eolp))
       (save-excursion (skip-chars-backward " \t") (not (bolp)))))

(defun beluga-indent-virtual ()
  (if (beluga-indent-hanging-p)
      (beluga-indent-calculate 'virtual)
    (current-column)))

(defun beluga-bolp ()
  (save-excursion (skip-chars-backward " \t") (bolp)))

(defun beluga-indent-calculate (&optional virtual)
  (or
   ;; Trust pre-existing indentation on other lines.
   (and virtual (beluga-bolp)
        (current-column))
   ;; Align close paren with opening paren.
   (save-excursion
     ;; (forward-comment (point-max))
     (when (looking-at "\\s)")
       (while (not (zerop (skip-syntax-forward ")")))
         (skip-chars-forward " \t"))
       (condition-case nil
           (progn
             (backward-sexp 1)
             (beluga-indent-virtual))
         (scan-error nil))))
   ;; Align `of' with the corresponding `match'.
   (save-excursion
     (let* ((pos (point))
            (token (beluga-forward-token))
            (tokinfo (cdr (assoc token beluga-op-levels))))
       (when (car tokinfo)
         (let ((res (beluga-backward-sexp)) tmp)
           ;; If we didn't move at all, that means we didn't really skip
           ;; what we wanted.
           (when (< (point) pos)
             (cond
              ((eq (car res) (car tokinfo))
               ;; We bumped into a same-level operator. align with it.
               (goto-char (cadr res))
               ;; Don't use beluga-indent-virtual here, because we want to
               ;; jump back over a sequence of same-level ops such as
               ;;    a -> b -> c
               ;;    -> d
               ;; So as to align with the earliest appropriate place.
               (beluga-indent-calculate 'virtual))
              (t
               (+ (if (null (setq tmp (assoc (cons (caddr res) token)
                                             beluga-indent-rules)))
                      (or (cdr (assoc (cons t token) beluga-indent-rules)) 0)
                    (goto-char (cadr res))
                    (cdr tmp))
                  (beluga-indent-virtual)))))))))
   ;; Indentation of a comment.
   (and (looking-at comment-start-skip)
        (save-excursion
          (forward-comment (point-max))
          (skip-chars-forward " \t\r\n")
          (beluga-indent-calculate nil)))
   ;; Indentation inside a comment.
   (and (looking-at "\\*") (nth 4 (syntax-ppss))
        (let ((ppss (syntax-ppss)))
          (save-excursion
            (forward-line -1)
            (if (<= (point) (nth 8 ppss))
                (progn (goto-char (1+ (nth 8 ppss))) (current-column))
              (skip-chars-forward " \t")
              (if (looking-at "\\*")
                  (current-column))))))
   ;; Indentation right after a special keyword.
   (save-excursion
     (let* ((tok (progn (forward-comment (- (point-max)))
                        (beluga-backward-token)))
            (tokinfo (assoc tok beluga-indent-rules))
            (toklevel (assoc tok beluga-op-levels)))
       (when (or tokinfo (and toklevel (null (cadr toklevel))))
         (if (beluga-indent-hanging-p)
             (+ (beluga-indent-calculate 'virtual)
                (or (caddr tokinfo) (cadr tokinfo) beluga-indent-basic))
           (+ (current-column)
              (or (cadr tokinfo) beluga-indent-basic))))))
   ;; Main loop.
   (save-excursion
     (let ((positions nil)
           (begline nil)
           arg)
       (while (and (null (car (beluga-backward-sexp 0)))
                   (push (point) positions)
                   (not (setq begline (beluga-bolp)))))
       (save-excursion
         (setq arg (or (null (car (beluga-backward-sexp 0)))
                       (member (progn (forward-comment (- (point-max)))
                                      (beluga-backward-token)) beluga-funlike-ops))))
       (cond
        ((and arg positions)
         (goto-char (car positions))
         (current-column))
        ((and (null begline) (cdr positions))
         ;; We skipped some args plus the function and bumped into something.
         ;; Align with the first arg.
         (goto-char (cadr positions))
         (current-column))
        ((and (null begline) positions)
         ;; We're the first arg.
         ;; FIXME: it might not be a funcall, in which case we might be the
         ;; second element.
         (goto-char (car positions))
         (+ beluga-indent-args (beluga-indent-calculate 'virtual)))
        ((and (null arg) (null positions))
         ;; We're the function itself.  Not sure what to do here yet.
         (if virtual (current-column)
           (save-excursion
             (let* ((pos (point))
                    (tok (progn (forward-comment (- (point-max)))
                                (beluga-backward-token)))
                    (tokinfo (cdr (assoc tok beluga-op-levels))))
               (cond
                ((numberp (car tokinfo))
                 ;; We're right after an infix token.  Let's skip over the
                 ;; lefthand side.
                 (goto-char pos)
                 (let (res)
                   (while (progn (setq res (beluga-backward-sexp))
                                 (and (not (beluga-bolp))
                                      (equal (car res) (car tokinfo)))))
                   ;; We should be right after a token of equal or
                   ;; higher precedence.
                   (cond
                    ((and (consp res) (memq (car res) '(t nil)))
                     ;; The token of higher-precedence is like an open-paren.
                     ;; Sample case for t: foo { bar, \n[TAB] baz }.
                     ;; Sample case for nil: match ... with \n[TAB] | toto ...
                     ;; (goto-char (cadr res))
                     (beluga-indent-virtual))
                    ((and (consp res) (>= (car res) (car tokinfo)))
                     ;; We stopped at a token of equal or higher precedence
                     ;; because we found a place with which to align.
                     (current-column))
                    )))
                ;; For other cases.... hmm... we'll see when we get there.
                )))))
        ((null positions)
         (beluga-backward-token)
         (+ beluga-indent-args (beluga-indent-calculate 'virtual)))
        ((car (beluga-backward-sexp 0))
         ;; No arg stands on its own line, but the function does:
         (if (cdr positions)
             (progn
               (goto-char (cadr positions))
               (current-column))
           (goto-char (car positions))
           (+ (current-column) beluga-indent-args)))
        (t
         ;; We've skipped to a previous arg on its own line: align.
         (goto-char (car positions))
         (current-column)))))
   ;; Other main loop.
   ;; (save-excursion
   ;;   (and (null (car (beluga-backward-sexp)))
   ;;        (current-column)))
   ;; ;; Old code.
   ;; (beluga-indent-offset)
   ))

(defun beluga-indent-line ()
  "Indent current line of Beluga code."
  (interactive)
  (let* ((savep (point))
	 (indent (condition-case nil
		     (save-excursion
		       (forward-line 0)
		       (skip-chars-forward " \t")
		       (if (>= (point) savep) (setq savep nil))
		       (max (beluga-indent-calculate) 0))
		   (error 0))))
    (if savep
	(save-excursion (indent-line-to indent))
      (indent-line-to indent))))


(provide 'beluga-mode)
;;; beluga-mode.el ends here
