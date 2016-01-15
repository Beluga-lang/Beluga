;;; beluga-mode.el --- Major mode for Beluga source code  -*- coding: utf-8; lexical-binding:t -*-

;; Copyright (C) 2009, 2010, 2012, 2013, 2014  Free Software Foundation, Inc.

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
(require 'smie nil t)                   ;Use smie when available.

(provide 'beluga-unicode-input-method)
(require 'quail)

(quail-define-package
 "beluga-unicode" ;; name
 "UTF-8" ;; language
 "\\" ;; title
 t ;; guidance
 "Beluga unicode input method: actually replaces keyword strings with a single unicode character instead of merely representing the keywords in unicode using Font Lock mode."
  nil nil nil nil nil nil nil nil nil nil t)


(quail-define-rules
 ;; Greek letters
 ("\\alpha " ["α"])
 ("\\Alpha " ["Α"])
 ("\\beta " ["β"])
 ("\\Beta " ["Β"])
 ("\\gamma " ["γ"])
 ("\\Gamma " ["Γ"])
 ("\\delta " ["δ"])
 ("\\Delta " ["Δ"])
 ("\\epsilon " ["ε"])
 ("\\Epsilon " ["Ε"])
 ("\\zeta " ["ζ"])
 ("\\Zeta " ["Ζ"])
 ("\\eta " ["η"])
 ("\\Eta " ["Η"])
 ("\\theta " ["θ"])
 ("\\Theta " ["Θ"])
 ("\\iota " ["ι"])
 ("\\Iota " ["Ι"])
 ("\\kappa " ["κ"])
 ("\\Kappa " ["Κ"])
 ("\\lambda " ["λ"])
 ("\\Lambda " ["Λ"])
 ("\\lamda " ["λ"])
 ("\\Lamda " ["Λ"])
 ("\\mu " ["μ"])
 ("\\Mu " ["Μ"])
 ("\\nu " ["ν"])
 ("\\Nu " ["Ν"])
 ("\\xi " ["ξ"])
 ("\\Xi " ["Ξ"])
 ("\\omicron " ["ο"])
 ("\\Omicron " ["Ο"])
 ("\\pi " ["π"])
 ("\\Pi " ["Π"])
 ("\\rho " ["ρ"])
 ("\\Rho " ["Ρ"])
 ("\\sigma " ["σ"])
 ("\\Sigma " ["Σ"])
 ("\\tau " ["τ"])
 ("\\Tau " ["Τ"])
 ("\\upsilon " ["υ"])
 ("\\Upsilon " ["Υ"])
 ("\\phi " ["φ"])
 ("\\Phi " ["Φ"])
 ("\\chi " ["χ"])
 ("\\Chi " ["Χ"])
 ("\\psi " ["ψ"])
 ("\\Psi " ["Ψ"])
 ("\\omega " ["ω"])
 ("\\Omega " ["Ω"])


 ;; Arrows
 ("->" ["→"])
 ("<-" ["←"])
 ("=>" ["⇒"])

 ;;LF
 ("|-" ["⊢"])
 ("not" ["¬"])
 ("::" ["∷"])
 (".." ["…"])
 ("FN" ["Λ"])
)

(defgroup beluga-mode ()
  "Editing support for the Beluga language."
  :group 'languages)

(defvar beluga-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\C-c\C-c" 'compile)
    (define-key map "\C-c\C-l" 'beluga-highlight-holes)
    (define-key map "\C-c\C-x" 'beli-cmd)
    (define-key map "\C-c\C-t" 'beli--type)
    (define-key map "\C-c\C-s" 'beluga-split-hole)
    (define-key map "\C-c\C-i" 'beluga-intro-hole)
    (define-key map "\C-c\C-j" 'hole-jump)
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
    (modify-syntax-entry ?| "." st)
    (modify-syntax-entry ?= "." st)
    (modify-syntax-entry ?\' "_" st)
    st))

(defcustom beluga-font-lock-symbols
  (not (fboundp 'prettify-symbols-mode))
  "Display |- and -> and such using symbols in fonts.
This may sound like a neat trick, but be extra careful: it changes the
alignment and can thus lead to nasty surprises w.r.t layout."
  :type 'boolean)
(when (fboundp 'prettify-symbols-mode)
  (make-obsolete-variable 'beluga-font-lock-symbols
                          'prettify-symbols-mode "Emacs-24.4"))

(defconst beluga-font-lock-symbols-alist
  ;; Not sure about fn → λ, since we could also have \ → λ.
  '(("not"   . ?¬)
    ;; ("fn"    . ?λ)
    ("FN"    . ?Λ)
    ("|-"    . ?⊢)
    ("psi"   . ?ψ)
    ("phi"   . ?φ)
    ("gamma" . ?γ)
    ("sigma" . ?σ)
    ("#S"    . ?σ)
    ("#S[^]" . ?σ)
    ("#R"    . ?ρ)
    ("#R[^]" . ?ρ)
    ("omega" . ?ω)
    ("Sigma" . ?Σ)
    ("->"    . ?→)
    ("<-"    . ?←)
    ("=>"    . ?⇒)
    ;; ("::"    . ?∷)
    (".." . ?…) ; Actually "..."
    ;;(".."    . ?‥)
    ;; ("forall" . ?∀)
    )
  "Alist mapping Beluga symbols to chars.
Each element has the form (STRING . CHAR) or (STRING CHAR PREDICATE).
STRING is the Beluga symbol.
CHAR is the character with which to represent this symbol.
PREDICATE if present is a function of one argument (the start position
of the symbol) which should return non-nil if this mapping should be disabled
at that position.")

(defun proc-live (process)
  "Returns non-nil if PROCESS is alive.
    A process is considered alive if its status is `run', `open',
    `listen', `connect' or `stop'."
  (memq (process-status process)
        '(run open listen connect stop)))

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
  (when (and (fboundp 'compose-region) beluga-font-lock-symbols)
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
  `(,(concat "\\_<"
             (regexp-opt
              '("FN" "and" "block" "case" "inductive" "LF" "coinductive" "stratified" "else" "ffalse" "fn" "if"
                "in" "impossible" "let" "mlam" "of" "rec" "schema" "some"
                "then" "type" "ctype" "ttrue" "%name" "%not" "module" "struct" "end"
                "%coverage" "%nostrengthen" "%infix" "%prefix" "%assoc"
                 "%open"  "%abbrev" "#stratified" "#positive" "total"))
             "\\_>\\|\\\\")
    (,(concat "^\\(" beluga-syntax-id-re
              "\\)[ \t\n]*:\\([^.]*\\_<type\\_>[ \t\n]*.\\)?")
     ;; This is a regexp that can span multiple lines, so it may not
     ;; always highlight properly.  `font-lock-multiline' tries to help.
     (0 (if (match-end 2) '(face nil font-lock-multiline t)))
     (1 (if (match-end 2)
            font-lock-type-face font-lock-variable-name-face)))
    (,(concat "^\\(?:schema\\|inductive\\|coinductive\\|LF\\|stratified\\)[ \t\n]+\\("
              beluga-syntax-id-re "\\)")
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
     ,(concat "^\\(?:inductive[ \t]+\\(" beluga-syntax-id-re
              "\\)\\|\\(?1:" beluga-syntax-id-re
              "\\)[ \t\n]*:[^.]*\\<type\\>[ \t\n]*.\\)") 1)
    ("Functions"
     ,(concat beluga-syntax-fundec-re "[ \t\n]+\\(" beluga-syntax-id-re "\\)") 1)))

(define-obsolete-variable-alias 'beluga-interpreter-path
  ;; A "path" is a list of file names, as in $PATH, $MANPATH.
  'beluga-interpreter-name "Sep-2010")
(defcustom beluga-interpreter-name "beluga"
  "Name of the interpreter executable."
  :type 'string)

;;---------------------------- Interactive mode ----------------------------;;

(defvar beluga--proc ()
  "Contain the process running beli.")
(make-variable-buffer-local 'beluga--proc)

(defun beluga--proc ()
(unless (proc-live beluga--proc) (beluga--start))
;;  (beluga--start)
  beluga--proc)

;; (defun beluga-buffer ()
;;   (process-buffer (beluga--proc)))

(defun beluga--start ()
  "Start an inferior beli process with the -emacs option.
The process is put into a buffer called \"*beli*\".
If a previous beli process already exists, kill it first."
  (beluga--stop)
  (setq beluga--proc
        (get-buffer-process
         (make-comint "beluga"
		      beluga-interpreter-name
                      nil "-I" "-emacs" ))))

(defun beluga--stop ()
  "Stop the beli process."
  (when (processp 'beluga--proc)
    (kill-process 'beluga--proc)))

(defun beluga--wait (proc)
  (assert (eq (current-buffer) (process-buffer proc)))
  (while (and (progn
                (goto-char comint-last-input-end)
                (not (re-search-forward ".*;" nil t)))
              (accept-process-output proc 0.4))))

(defun chomp (str)
  "Chomp leading and tailing whitespace from STR."
  (replace-regexp-in-string (rx (or (: bos (* (any " \t\n")))
                                    (: (* (any " \t\n")) eos)))
                            ""
                            str))
(defun trim (str)
  (let ((str2 (chomp str)))
    (substring str2 0 (1- (length str2)))))

(defun beluga--send (cmd)
  "Send commands to beli."
  ; (interactive)
  (let ((proc (beluga--proc)))
    (with-current-buffer (process-buffer proc)
      (beluga--wait proc)
      ;; We could also just use `process-send-string', but then we wouldn't
      ;; have the input text in the buffer to separate the various prompts.
      (goto-char (point-max))
      (insert (concat "%:" cmd))
      (comint-send-input))))

(defun beluga--receive ()
  "Reads the last output of beli."
  (let ((proc (beluga--proc)))
    (with-current-buffer (process-buffer proc)
      (beluga--wait proc)
      (trim (buffer-substring-no-properties comint-last-input-end (point-max))))))

(defun beluga--rpc (cmd)
  (beluga--send cmd)
  (beluga--receive))

(defvar btypes-buf-name "*beluga-types*"
  "Name of buffer for displaying Beluga types")
(defvar btypes-ovl (make-overlay 1 1))
(make-face 'btypes-face)
(set-face-doc-string 'btypes-face
                     "face for hilighting expressions and types")
(if (not (face-differs-from-default-p 'btypes-face))
    (set-face-background 'btypes-face "#88FF44"))
(overlay-put btypes-ovl 'face 'btypes-face)

(defun beli--type ()
  "Get the type at the current cursor position (if it exists)"
  (interactive)
  (let ((target-buf (current-buffer))
	(line (count-lines 1 (point)))
	(col (current-column)))
    (setq btypes-buffer (get-buffer-create btypes-buf-name))
    (let* ((typeinfo (beluga--rpc (format "get-type %d %d" line col)))
	    (pos (read (beluga--rpc (format "loc-type %d %d" line col))))
	    )
	 (cond
	  ((null typeinfo)
	   (delete-overlay btypes-ovl)
	   (message "No type information found for current point."))
	  (t
	   (let ((start (beluga--pos (nth 1 pos) (nth 2 pos) (nth 3 pos)))
		 (end (beluga--pos (nth 4 pos) (nth 5 pos) (nth 6 pos))))
	     (move-overlay btypes-ovl start end target-buf)
	     (with-current-buffer btypes-buffer
	       (erase-buffer)
	       (insert typeinfo)
	       (message (format "type: %s" typeinfo))))))))
  (unwind-protect
      (sit-for 60)
      (delete-overlay btypes-ovl)
    )
)

(defun beli ()
  "Start beli mode"
  (interactive)
  (beluga--start))

(defun beli-cmd (cmd)
  "Run a command in beli"
  (interactive "MCommand: ")
  (message "%s" (beluga--rpc cmd)))

(defun maybe-save ()
  (if (buffer-modified-p)
    (if (y-or-n-p "Save current file?")
      (save-buffer)
      ())))

(defun beluga-load ()
  "Loads the current file in beli."
  (interactive)
  (beluga--start)
  (maybe-save)
  (let ((file-name
	 (expand-file-name (read-file-name "Load file:" buffer-file-name))))
    (message "%s" (beluga--rpc (concat "load " file-name)))))

(defvar beluga--holes-overlays ()
  "Will contain the list of hole overlays so that they can be resetted.")
(make-variable-buffer-local 'beluga--holes-overlays)

(defun beluga-sorted-holes ()
  (defun hole-comp (a b)
     (let* ((s1 (overlay-start a))
            (s2 (overlay-start b)))
       (< s1 s2)))
  (sort beluga--holes-overlays `hole-comp))



(defface beluga-holes
  '((t :background "cyan")) ;; :foreground "white"
  "Face used to highlight holes in Beluga mode.")

(defun beluga--pos (line bol offset)
  ;; According to http://caml.inria.fr/mantis/view.php?id=5159,
  ;; `line' can refer to line numbers in various source files,
  ;; whereas `bol' and `offset' refer to "character" (byte?) positions within
  ;; the actual parsed stream.
  ;; So if there might be #line directives, we need to do:
   (save-excursion
     (goto-char (point-min))
     (forward-line (1- line)) ;Lines count from 1 :-(
     (+ (point) (- offset bol))))
  ;; But as long as we know there's no #line directive, we can ignore all that
  ;; and use the more efficient code below.  When #line directives can appear,
  ;; we will need to make further changes anyway, such as passing the file-name
  ;; to select the appropriate buffer.
  ; (+ (point-min) offset))

(defun beluga--create-overlay (pos)
  "Create an overlay at the position described by POS (a Loc.to_tuple)."
  (let* (;; (file-name (nth 0 pos))
         (start-line (nth 1 pos))
         (start-bol (nth 2 pos))
         (start-off (nth 3 pos))
         (stop-line (nth 4 pos))
         (stop-bol (nth 5 pos))
         (stop-off (nth 6 pos))
         (ol
          (make-overlay (beluga--pos start-line start-bol start-off)
                        (beluga--pos stop-line  stop-bol  stop-off))))
    (overlay-put ol 'face 'beluga-holes)
    ol))

(defun beluga-highlight-holes ()
  "Create overlays for each of the holes and color them."
  (interactive)
  (beluga-load)
  (beluga-erase-holes)
  (let ((numholes (string-to-number (beluga--rpc "numholes"))))
    (dotimes (i numholes)
      (let* ((pos (read (beluga--rpc (format "lochole %d" i))))
             (ol (beluga--create-overlay pos))
             (info (beluga--rpc (format "printhole %d" i))))
        (overlay-put ol 'help-echo info)
        (push ol beluga--holes-overlays)
        )))
  (let ((numholes (string-to-number (beluga--rpc "numlfholes"))))
    (dotimes (i numholes)
      (let* ((pos (read (beluga--rpc (format "lochole-lf %d" i))))
             (ol (beluga--create-overlay pos))
             (info (beluga--rpc (format "printhole-lf %d" i))))
        (overlay-put ol 'help-echo info)
        (push ol beluga--holes-overlays)
        ))))

(defun beluga-split-hole (hole var)
  "Split on a hole"
  (interactive "nHole to split at: \nsVariable to split on: ")
  (let ((resp (beluga--rpc (format "split %d %s" hole var))))
    (if (string= "-" (substring resp 0 1))
      (message "%s" resp)
      (let* ((ovr (nth hole (beluga-sorted-holes)))
             (start (overlay-start ovr))
             (end (overlay-end ovr)))
        (delete-overlay ovr)
        (delete-region start end)
        (goto-char start)
        (insert (format "(%s)" resp))
        (save-buffer)
        (beluga-load)
        (beluga-highlight-holes)))))

(defun beluga-intro-hole (hole)
  "Introduce variables into a hole"
  (interactive "nHole to introduce variables into: ")
  (let ((resp (beluga--rpc (format "intro %d" hole))))
    (if (string= "-" (substring resp 0 1))
      (message "%s" resp)
      (let* ((ovr (nth hole (beluga-sorted-holes)))
             (start (overlay-start ovr))
             (end (overlay-end ovr)))
        (delete-overlay ovr)
        (delete-region start end)
        (goto-char start)
        (insert resp)
        (save-buffer)
        (beluga-load)
        (beluga-highlight-holes)))))

(defun hole-jump (hole)
  (interactive "nHole to jump to: ")
  (let* ((ovr (nth hole (beluga-sorted-holes)))
             (start (overlay-start ovr)))
    (goto-char start)))

(defun beluga-erase-holes ()
  (interactive)
  (mapc #'delete-overlay beluga--holes-overlays)
  (setq beluga--holes-overlays nil))


;;---------------------------- Loading of the mode ----------------------------;;

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.s?bel\\'" . beluga-mode))

(unless (fboundp 'prog-mode)
  (defalias 'prog-mode #'fundamental-mode))

;;;###autoload
(define-derived-mode beluga-mode prog-mode "Beluga"
  "Major mode to edit Beluga source code."
  (set (make-local-variable 'imenu-generic-expression)
       beluga-imenu-generic-expression)
  (set (make-local-variable 'outline-regexp)
       (concat beluga-syntax-fundec-re "\\|^(inductive|coinductive|LF|stratified)\\_>"))
  (set (make-local-variable 'require-final-newline) t)
  (when buffer-file-name
    (set (make-local-variable 'compile-command)
         ;; Quite dubious, but it's the intention that counts.
         (concat beluga-interpreter-name
                 " "
                 (shell-quote-argument buffer-file-name))))
  (set (make-local-variable 'comment-start) "% ")
  (set (make-local-variable 'comment-start-skip) "%[%{]*[ \t]*")
  (set (make-local-variable 'comment-end-skip) "[ \t]*\\(?:\n\\|}%\\)")
  (comment-normalize-vars)
  (set (make-local-variable 'electric-indent-chars)
       (append '(?|) (if (boundp 'electric-indent-chars)
                         electric-indent-chars
                       '(?\n))))
  ;;QUAIL
  ; (add-hook 'beluga-mode-hook
    ; (lambda () (set-input-method "beluga-unicode")))

  ;;Turn off hilighting
;;(setq input-method-highlight-flag nil)

  ;; SMIE setup.
  (set (make-local-variable 'parse-sexp-ignore-comments) t)
  (if (fboundp 'smie-setup)
      ;; `beluga-smie-grammar' is defined further, because it needs to be
      ;; defined after the `belugasmie-' stuff, which I'd rather not move
      ;; up here.
      (smie-setup (with-no-warnings beluga-smie-grammar)
                  #'beluga-smie-indent-rules
                  :forward-token #'beluga-smie-forward-token
                  :backward-token #'beluga-smie-backward-token)
    (with-no-warnings
      (belugasmie-setup beluga-smie-grammar beluga-smie-indent-rules)
      (set (make-local-variable 'belugasmie-indent-basic) beluga-indent-basic)
      (set (make-local-variable 'forward-sexp-function)
           #'belugasmie-forward-sexp-command)
      (set (make-local-variable 'belugasmie-forward-token-function)
           #'beluga-smie-forward-token)
      (set (make-local-variable 'belugasmie-backward-token-function)
           #'beluga-smie-backward-token)
      (set (make-local-variable 'belugasmie-closer-alist)
           '(("<" . ">"))) ;; (t . ".")
      ;; Only needed for interactive calls to blink-matching-open.
      (set (make-local-variable 'blink-matching-check-function)
           #'belugasmie-blink-matching-check)
      (add-hook 'post-self-insert-hook
                #'belugasmie-blink-matching-open 'append 'local)
      (set (make-local-variable 'belugasmie-blink-matching-triggers) '(?>))))

  (set (make-local-variable 'prettify-symbols-alist)
       beluga-font-lock-symbols-alist)
  (set (make-local-variable 'font-lock-defaults)
       '(beluga-font-lock-keywords nil nil () nil
         (font-lock-syntactic-keywords . nil))))

;;---------------------------- SMIE ----------------------------;;
;;; Our own copy of (a version of) SMIE.

(defun belugasmie-set-prec2tab (table x y val &optional override)
  (assert (and x y))
  (let* ((key (cons x y))
         (old (gethash key table)))
    (if (and old (not (eq old val)))
        (if (and override (gethash key override))
            ;; FIXME: The override is meant to resolve ambiguities,
            ;; but it also hides real conflicts.  It would be great to
            ;; be able to distinguish the two cases so that overrides
            ;; don't hide real conflicts.
            (puthash key (gethash key override) table)
          (display-warning 'smie (format "Conflict: %s %s/%s %s" x old val y)))
      (puthash key val table))))

(defun belugasmie-precs->prec2 (precs)
  "Compute a 2D precedence table from a list of precedences.
PRECS should be a list, sorted by precedence (e.g. \"+\" will
come before \"*\"), of elements of the form \(left OP ...)
or (right OP ...) or (nonassoc OP ...) or (assoc OP ...).  All operators in
one of those elements share the same precedence level and associativity."
  (let ((prec2-table (make-hash-table :test 'equal)))
    (dolist (prec precs)
      (dolist (op (cdr prec))
        (let ((selfrule (cdr (assq (car prec)
                                   '((left . >) (right . <) (assoc . =))))))
          (when selfrule
            (dolist (other-op (cdr prec))
              (belugasmie-set-prec2tab prec2-table op other-op selfrule))))
        (let ((op1 '<) (op2 '>))
          (dolist (other-prec precs)
            (if (eq prec other-prec)
                (setq op1 '> op2 '<)
              (dolist (other-op (cdr other-prec))
                (belugasmie-set-prec2tab prec2-table op other-op op2)
                (belugasmie-set-prec2tab prec2-table other-op op op1)))))))
    prec2-table))

(defun belugasmie-merge-prec2s (&rest tables)
  (if (null (cdr tables))
      (car tables)
    (let ((prec2 (make-hash-table :test 'equal)))
      (dolist (table tables)
        (maphash (lambda (k v)
                   (belugasmie-set-prec2tab prec2 (car k) (cdr k) v))
                 table))
      prec2)))

(defun belugasmie-bnf->prec2 (bnf &rest precs)
  (let ((nts (mapcar 'car bnf))         ;Non-terminals
        (first-ops-table ())
        (last-ops-table ())
        (first-nts-table ())
        (last-nts-table ())
        (prec2 (make-hash-table :test 'equal))
        (override (apply 'belugasmie-merge-prec2s
                         (mapcar 'belugasmie-precs->prec2 precs)))
        again)
    (dolist (rules bnf)
      (let ((nt (car rules))
            (last-ops ())
            (first-ops ())
            (last-nts ())
            (first-nts ()))
        (dolist (rhs (cdr rules))
          (unless (consp rhs)
            (signal 'wrong-type-argument `(consp ,rhs)))
          (if (not (member (car rhs) nts))
              (pushnew (car rhs) first-ops)
            (pushnew (car rhs) first-nts)
            (when (consp (cdr rhs))
              ;; If the first is not an OP we add the second (which
              ;; should be an OP if BNF is an "operator grammar").
              ;; Strictly speaking, this should only be done if the
              ;; first is a non-terminal which can expand to a phrase
              ;; without any OP in it, but checking doesn't seem worth
              ;; the trouble, and it lets the writer of the BNF
              ;; be a bit more sloppy by skipping uninteresting base
              ;; cases which are terminals but not OPs.
              (assert (not (member (cadr rhs) nts)))
              (pushnew (cadr rhs) first-ops)))
          (let ((shr (reverse rhs)))
            (if (not (member (car shr) nts))
                (pushnew (car shr) last-ops)
              (pushnew (car shr) last-nts)
              (when (consp (cdr shr))
                (assert (not (member (cadr shr) nts)))
                (pushnew (cadr shr) last-ops)))))
        (push (cons nt first-ops) first-ops-table)
        (push (cons nt last-ops) last-ops-table)
        (push (cons nt first-nts) first-nts-table)
        (push (cons nt last-nts) last-nts-table)))
    ;; Compute all first-ops by propagating the initial ones we have
    ;; now, according to first-nts.
    (setq again t)
    (while (prog1 again (setq again nil))
      (dolist (first-nts first-nts-table)
        (let* ((nt (pop first-nts))
               (first-ops (assoc nt first-ops-table)))
          (dolist (first-nt first-nts)
            (dolist (op (cdr (assoc first-nt first-ops-table)))
              (unless (member op first-ops)
                (setq again t)
                (push op (cdr first-ops))))))))
    ;; Same thing for last-ops.
    (setq again t)
    (while (prog1 again (setq again nil))
      (dolist (last-nts last-nts-table)
        (let* ((nt (pop last-nts))
               (last-ops (assoc nt last-ops-table)))
          (dolist (last-nt last-nts)
            (dolist (op (cdr (assoc last-nt last-ops-table)))
              (unless (member op last-ops)
                (setq again t)
                (push op (cdr last-ops))))))))
    ;; Now generate the 2D precedence table.
    (dolist (rules bnf)
      (dolist (rhs (cdr rules))
        (while (cdr rhs)
          (cond
           ((member (car rhs) nts)
            (dolist (last (cdr (assoc (car rhs) last-ops-table)))
              (belugasmie-set-prec2tab prec2 last (cadr rhs) '> override)))
           ((member (cadr rhs) nts)
            (dolist (first (cdr (assoc (cadr rhs) first-ops-table)))
              (belugasmie-set-prec2tab prec2 (car rhs) first '< override))
            (if (and (cddr rhs) (not (member (car (cddr rhs)) nts)))
                (belugasmie-set-prec2tab prec2 (car rhs) (car (cddr rhs))
                                   '= override)))
           (t (belugasmie-set-prec2tab prec2 (car rhs) (cadr rhs) '= override)))
          (setq rhs (cdr rhs)))))
    prec2))

;; (defun belugasmie-prec2-closer-alist (prec2 include-inners)
;;   "Build a closer-alist from a PREC2 table.
;; The return value is in the same form as `belugasmie-closer-alist'.
;; INCLUDE-INNERS if non-nil means that inner keywords will be included
;; in the table, e.g. the table will include things like (\"if\" . \"else\")."
;;   (let* ((non-openers '())
;;          (non-closers '())
;;          ;; For each keyword, this gives the matching openers, if any.
;;          (openers (make-hash-table :test 'equal))
;;          (closers '())
;;          (done nil))
;;     ;; First, find the non-openers and non-closers.
;;     (maphash (lambda (k v)
;;                (unless (or (eq v '<) (member (cdr k) non-openers))
;;                  (push (cdr k) non-openers))
;;                (unless (or (eq v '>) (member (car k) non-closers))
;;                  (push (car k) non-closers)))
;;              prec2)
;;     ;; Then find the openers and closers.
;;     (maphash (lambda (k _)
;;                (unless (member (car k) non-openers)
;;                  (puthash (car k) (list (car k)) openers))
;;                (unless (or (member (cdr k) non-closers)
;;                            (member (cdr k) closers))
;;                  (push (cdr k) closers)))
;;              prec2)
;;     ;; Then collect the matching elements.
;;     (while (not done)
;;       (setq done t)
;;       (maphash (lambda (k v)
;;                  (when (eq v '=)
;;                    (let ((aopeners (gethash (car k) openers))
;;                          (dopeners (gethash (cdr k) openers))
;;                          (new nil))
;;                      (dolist (o aopeners)
;;                        (unless (member o dopeners)
;;                          (setq new t)
;;                          (push o dopeners)))
;;                      (when new
;;                        (setq done nil)
;;                        (puthash (cdr k) dopeners openers)))))
;;                prec2))
;;     ;; Finally, dump the resulting table.
;;     (let ((alist '()))
;;       (maphash (lambda (k v)
;;                  (when (or include-inners (member k closers))
;;                    (dolist (opener v)
;;                      (unless (equal opener k)
;;                        (push (cons opener k) alist)))))
;;                openers)
;;       alist)))

(defun belugasmie-bnf-closer-alist (bnf &optional no-inners)
  ;; We can also build this closer-alist table from a prec2 table,
  ;; but it takes more work, and the order is unpredictable, which
  ;; is a problem for belugasmie-close-block.
  ;; More convenient would be to build it from a levels table since we
  ;; always have this table (contrary to the BNF), but it has all the
  ;; disadvantages of the prec2 case plus the disadvantage that the levels
  ;; table has lost some info which would result in extra invalid pairs.
  "Build a closer-alist from a BNF table.
The return value is in the same form as `belugasmie-closer-alist'.
NO-INNERS if non-nil means that inner keywords will be excluded
from the table, e.g. the table will not include things like (\"if\" . \"else\")."
  (let ((nts (mapcar #'car bnf))        ;non terminals.
        (alist '()))
    (dolist (nt bnf)
      (dolist (rhs (cdr nt))
        (unless (or (< (length rhs) 2) (member (car rhs) nts))
          (if no-inners
              (let ((last (car (last rhs))))
                (unless (member last nts)
                  (pushnew (cons (car rhs) last) alist :test #'equal)))
            ;; Reverse so that the "real" closer gets there first,
            ;; which is important for belugasmie-close-block.
            (dolist (term (reverse (cdr rhs)))
              (unless (member term nts)
                (pushnew (cons (car rhs) term) alist :test #'equal)))))))
    (nreverse alist)))


(defun belugasmie-debug--prec2-cycle (csts)
  "Return a cycle in CSTS, assuming there's one.
CSTS is a list of pairs representing arcs in a graph."
  ;; A PATH is of the form (START . REST) where REST is a reverse
  ;; list of nodes through which the path goes.
  (let ((paths (mapcar (lambda (pair) (list (car pair) (cdr pair))) csts))
        (cycle nil))
    (while (null cycle)
      (dolist (path (prog1 paths (setq paths nil)))
        (dolist (cst csts)
          (when (eq (car cst) (nth 1 path))
            (if (eq (cdr cst) (car path))
                (setq cycle path)
              (push (cons (car path) (cons (cdr cst) (cdr path)))
                    paths))))))
    (cons (car cycle) (nreverse (cdr cycle)))))

(defun belugasmie-debug--describe-cycle (table cycle)
  (let ((names
         (mapcar (lambda (val)
                   (let ((res nil))
                     (dolist (elem table)
                       (if (eq (cdr elem) val)
                           (push (concat "." (car elem)) res))
                       (if (eq (cddr elem) val)
                           (push (concat (car elem) ".") res)))
                     (assert res)
                     res))
                 cycle)))
    (mapconcat
     (lambda (elems) (mapconcat 'identity elems "="))
     (append names (list (car names)))
     " < ")))

(defun belugasmie-prec2->grammar (prec2)
  ;; FIXME: Rather than only return an alist of precedence levels, we should
  ;; also extract other useful data from it:
  ;; - matching sets of block openers&closers (which can otherwise become
  ;;   collapsed into a single equivalence class in belugasmie-op-levels) for
  ;;   belugasmie-close-block as well as to detect mismatches in belugasmie-next-sexp
  ;;   or in blink-paren (as well as to do the blink-paren for inner
  ;;   keywords like the "in" of "let..in..end").
  ;; - better default indentation rules (i.e. non-zero indentation after inner
  ;;   keywords like the "in" of "let..in..end") for belugasmie-indent-after-keyword.
  ;; Of course, maybe those things would be even better handled in the
  ;; bnf->prec function.
  "Take a 2D precedence table and turn it into an alist of precedence levels.
PREC2 is a table as returned by `belugasmie-precs->prec2' or
`belugasmie-bnf->prec2'."
  ;; For each operator, we create two "variables" (corresponding to
  ;; the left and right precedence level), which are represented by
  ;; cons cells.  Those are the very cons cells that appear in the
  ;; final `table'.  The value of each "variable" is kept in the `car'.
  (let ((table ())
        (csts ())
        (eqs ())
        tmp x y)
    ;; From `prec2' we construct a list of constraints between
    ;; variables (aka "precedence levels").  These can be either
    ;; equality constraints (in `eqs') or `<' constraints (in `csts').
    (maphash (lambda (k v)
               (if (setq tmp (assoc (car k) table))
                   (setq x (cddr tmp))
                 (setq x (cons nil nil))
                 (push (cons (car k) (cons nil x)) table))
               (if (setq tmp (assoc (cdr k) table))
                   (setq y (cdr tmp))
                 (setq y (cons nil (cons nil nil)))
                 (push (cons (cdr k) y) table))
               (ecase v
                 (= (push (cons x y) eqs))
                 (< (push (cons x y) csts))
                 (> (push (cons y x) csts))))
             prec2)
    ;; First process the equality constraints.
    (let ((eqs eqs))
      (while eqs
        (let ((from (caar eqs))
              (to (cdar eqs)))
          (setq eqs (cdr eqs))
          (if (eq to from)
              nil                   ;Nothing to do.
            (dolist (other-eq eqs)
              (if (eq from (cdr other-eq)) (setcdr other-eq to))
              (when (eq from (car other-eq))
                ;; This can happen because of `assoc' settings in precs
                ;; or because of a rhs like ("op" foo "op").
                (setcar other-eq to)))
            (dolist (cst csts)
              (if (eq from (cdr cst)) (setcdr cst to))
              (if (eq from (car cst)) (setcar cst to)))))))
    ;; Then eliminate trivial constraints iteratively.
    (let ((i 0))
      (while csts
        (let ((rhvs (mapcar 'cdr csts))
              (progress nil))
          (dolist (cst csts)
            (unless (memq (car cst) rhvs)
              (setq progress t)
              ;; We could give each var in a given iteration the same value,
              ;; but we can also give them arbitrarily different values.
              ;; Basically, these are vars between which there is no
              ;; constraint (neither equality nor inequality), so
              ;; anything will do.
              ;; We give them arbitrary values, which means that we
              ;; replace the "no constraint" case with either > or <
              ;; but not =.  The reason we do that is so as to try and
              ;; distinguish associative operators (which will have
              ;; left = right).
              (unless (caar cst)
                (setcar (car cst) i)
                (incf i))
              (setq csts (delq cst csts))))
          (unless progress
            (error "Can't resolve the precedence cycle: %s"
                   (belugasmie-debug--describe-cycle
                    table (belugasmie-debug--prec2-cycle csts)))))
        (incf i 10))
      ;; Propagate equalities back to their source.
      (dolist (eq (nreverse eqs))
        (assert (or (null (caar eq)) (eq (car eq) (cdr eq))))
        (setcar (car eq) (cadr eq)))
      ;; Finally, fill in the remaining vars (which only appeared on the
      ;; right side of the < constraints).
      (dolist (x table)
        ;; When both sides are nil, it means this operator binds very
        ;; very tight, but it's still just an operator, so we give it
        ;; the highest precedence.
        ;; OTOH if only one side is nil, it usually means it's like an
        ;; open-paren, which is very important for indentation purposes,
        ;; so we keep it nil, to make it easier to recognize.
        (unless (or (nth 1 x) (nth 2 x))
          (setf (nth 1 x) i)
          (setf (nth 2 x) i))))
    table))

;;; Parsing using a precedence level table.

(defvar belugasmie-op-levels 'unset
  "List of token parsing info.
Each element is of the form (TOKEN LEFT-LEVEL RIGHT-LEVEL).
Parsing is done using an operator precedence parser.
LEFT-LEVEL and RIGHT-LEVEL can be either numbers or nil, where nil
means that this operator does not bind on the corresponding side,
i.e. a LEFT-LEVEL of nil means this is a token that behaves somewhat like
an open-paren, whereas a RIGHT-LEVEL of nil would correspond to something
like a close-paren.")

(defvar belugasmie-forward-token-function 'belugasmie-default-forward-token
  "Function to scan forward for the next token.
Called with no argument should return a token and move to its end.
If no token is found, return nil or the empty string.
It can return nil when bumping into a parenthesis, which lets SMIE
use syntax-tables to handle them in efficient C code.")

(defvar belugasmie-backward-token-function 'belugasmie-default-backward-token
  "Function to scan backward the previous token.
Same calling convention as `belugasmie-forward-token-function' except
it should move backward to the beginning of the previous token.")

(defalias 'belugasmie-op-left 'car)
(defalias 'belugasmie-op-right 'cadr)

(defun belugasmie-default-backward-token ()
  (forward-comment (- (point)))
  (buffer-substring-no-properties
   (point)
   (progn (if (zerop (skip-syntax-backward "."))
              (skip-syntax-backward "w_'"))
          (point))))

(defun belugasmie-default-forward-token ()
  (forward-comment (point-max))
  (buffer-substring-no-properties
   (point)
   (progn (if (zerop (skip-syntax-forward "."))
              (skip-syntax-forward "w_'"))
          (point))))

(defun belugasmie--associative-p (toklevels)
  ;; in "a + b + c" we want to stop at each +, but in
  ;; "if a then b elsif c then d else c" we don't want to stop at each keyword.
  ;; To distinguish the two cases, we made belugasmie-prec2->grammar choose
  ;; different levels for each part of "if a then b else c", so that
  ;; by checking if the left-level is equal to the right level, we can
  ;; figure out that it's an associative operator.
  ;; This is not 100% foolproof, tho, since the "elsif" will have to have
  ;; equal left and right levels (since it's optional), so belugasmie-next-sexp
  ;; has to be careful to distinguish those different cases.
  (eq (belugasmie-op-left toklevels) (belugasmie-op-right toklevels)))

(defun belugasmie-next-sexp (next-token next-sexp op-forw op-back halfsexp)
  "Skip over one sexp.
NEXT-TOKEN is a function of no argument that moves forward by one
token (after skipping comments if needed) and returns it.
NEXT-SEXP is a lower-level function to skip one sexp.
OP-FORW is the accessor to the forward level of the level data.
OP-BACK is the accessor to the backward level of the level data.
HALFSEXP if non-nil, means skip over a partial sexp if needed.  I.e. if the
first token we see is an operator, skip over its left-hand-side argument.
Possible return values:
  (FORW-LEVEL POS TOKEN): we couldn't skip TOKEN because its back-level
    is too high.  FORW-LEVEL is the forw-level of TOKEN,
    POS is its start position in the buffer.
  (t POS TOKEN): same thing when we bump on the wrong side of a paren.
  (nil POS TOKEN): we skipped over a paren-like pair.
  nil: we skipped over an identifier, matched parentheses, ..."
  (catch 'return
    (let ((levels ()))
      (while
          (let* ((pos (point))
                 (token (funcall next-token))
                 (toklevels (cdr (assoc token belugasmie-op-levels))))
            (cond
             ((null toklevels)
              (when (zerop (length token))
                (condition-case err
                    (progn (goto-char pos) (funcall next-sexp 1) nil)
                  (scan-error (throw 'return
                                     (list t (caddr err)
                                           (buffer-substring-no-properties
                                            (caddr err)
                                            (+ (caddr err)
                                               (if (< (point) (caddr err))
                                                   -1 1)))))))
                (if (eq pos (point))
                    ;; We did not move, so let's abort the loop.
                    (throw 'return (list t (point))))))
             ((null (funcall op-back toklevels))
              ;; A token like a paren-close.
              (assert (funcall op-forw toklevels)) ;Otherwise, why mention it?
              (push toklevels levels))
             (t
              (while (and levels (< (funcall op-back toklevels)
                                    (funcall op-forw (car levels))))
                (setq levels (cdr levels)))
              (cond
               ((null levels)
                (if (and halfsexp (funcall op-forw toklevels))
                    (push toklevels levels)
                  (throw 'return
                         (prog1 (list (or (car toklevels) t) (point) token)
                           (goto-char pos)))))
               (t
                (let ((lastlevels levels))
                  (if (and levels (= (funcall op-back toklevels)
                                     (funcall op-forw (car levels))))
                      (setq levels (cdr levels)))
                  ;; We may have found a match for the previously pending
                  ;; operator.  Is this the end?
                  (cond
                   ;; Keep looking as long as we haven't matched the
                   ;; topmost operator.
                   (levels
                    (if (funcall op-forw toklevels)
                        (push toklevels levels)))
                   ;; We matched the topmost operator.  If the new operator
                   ;; is the last in the corresponding BNF rule, we're done.
                   ((null (funcall op-forw toklevels))
                    ;; It is the last element, let's stop here.
                    (throw 'return (list nil (point) token)))
                   ;; If the new operator is not the last in the BNF rule,
                   ;; ans is not associative, it's one of the inner operators
                   ;; (like the "in" in "let .. in .. end"), so keep looking.
                   ((not (belugasmie--associative-p toklevels))
                    (push toklevels levels))
                   ;; The new operator is associative.  Two cases:
                   ;; - it's really just an associative operator (like + or ;)
                   ;;   in which case we should have stopped right before.
                   ((and lastlevels
                         (belugasmie--associative-p (car lastlevels)))
                    (throw 'return
                           (prog1 (list (or (car toklevels) t) (point) token)
                             (goto-char pos))))
                   ;; - it's an associative operator within a larger construct
                   ;;   (e.g. an "elsif"), so we should just ignore it and keep
                   ;;   looking for the closing element.
                   (t (setq levels lastlevels))))))))
            levels)
        (setq halfsexp nil)))))

(defun belugasmie-backward-sexp (&optional halfsexp)
  "Skip over one sexp.
HALFSEXP if non-nil, means skip over a partial sexp if needed.  I.e. if the
first token we see is an operator, skip over its left-hand-side argument.
Possible return values:
  (LEFT-LEVEL POS TOKEN): we couldn't skip TOKEN because its right-level
    is too high.  LEFT-LEVEL is the left-level of TOKEN,
    POS is its start position in the buffer.
  (t POS TOKEN): same thing but for an open-paren or the beginning of buffer.
  (nil POS TOKEN): we skipped over a paren-like pair.
  nil: we skipped over an identifier, matched parentheses, ..."
  (belugasmie-next-sexp
   (indirect-function belugasmie-backward-token-function)
   (indirect-function 'backward-sexp)
   (indirect-function 'belugasmie-op-left)
   (indirect-function 'belugasmie-op-right)
   halfsexp))

(defun belugasmie-forward-sexp (&optional halfsexp)
  "Skip over one sexp.
HALFSEXP if non-nil, means skip over a partial sexp if needed.  I.e. if the
first token we see is an operator, skip over its left-hand-side argument.
Possible return values:
  (RIGHT-LEVEL POS TOKEN): we couldn't skip TOKEN because its left-level
    is too high.  RIGHT-LEVEL is the right-level of TOKEN,
    POS is its end position in the buffer.
  (t POS TOKEN): same thing but for an open-paren or the beginning of buffer.
  (nil POS TOKEN): we skipped over a paren-like pair.
  nil: we skipped over an identifier, matched parentheses, ..."
  (belugasmie-next-sexp
   (indirect-function belugasmie-forward-token-function)
   (indirect-function 'forward-sexp)
   (indirect-function 'belugasmie-op-right)
   (indirect-function 'belugasmie-op-left)
   halfsexp))

;;; Miscellanous commands using the precedence parser.

(defun belugasmie-backward-sexp-command (&optional n)
  "Move backward through N logical elements."
  (interactive "^p")
  (belugasmie-forward-sexp-command (- n)))

(defun belugasmie-forward-sexp-command (&optional n)
  "Move forward through N logical elements."
  (interactive "^p")
  (let ((forw (> n 0))
        (forward-sexp-function nil))
    (while (/= n 0)
      (setq n (- n (if forw 1 -1)))
      (let ((pos (point))
            (res (if forw
                     (belugasmie-forward-sexp 'halfsexp)
                   (belugasmie-backward-sexp 'halfsexp))))
        (if (and (car res) (= pos (point)) (not (if forw (eobp) (bobp))))
            (signal 'scan-error
                    (list "Containing expression ends prematurely"
                          (cadr res) (cadr res)))
          nil)))))

(defvar belugasmie-closer-alist nil
  "Alist giving the closer corresponding to an opener.")

(defun belugasmie-close-block ()
  "Close the closest surrounding block."
  (interactive)
  (let ((closer
         (save-excursion
           (backward-up-list 1)
           (if (looking-at "\\s(")
               (string (cdr (syntax-after (point))))
             (let* ((open (funcall belugasmie-forward-token-function))
                    (closer (cdr (assoc open belugasmie-closer-alist)))
                    (levels (list (assoc open belugasmie-op-levels)))
                    (seen '())
                    (found '()))
               (cond
                ;; Even if we improve the auto-computation of closers,
                ;; there are still cases where we need manual
                ;; intervention, e.g. for Octave's use of `until'
                ;; as a pseudo-closer of `do'.
                (closer)
                ((or (equal levels '(nil)) (nth 1 (car levels)))
                 (error "Doesn't look like a block"))
                (t
                 ;; FIXME: With grammars like Octave's, every closer ("end",
                 ;; "endif", "endwhile", ...) has the same level, so we'd need
                 ;; to look at the BNF or at least at the 2D prec-table, in
                 ;; order to find the right closer for a given opener.
                 (while levels
                   (let ((level (pop levels)))
                     (dolist (other belugasmie-op-levels)
                       (when (and (eq (nth 2 level) (nth 1 other))
                                  (not (memq other seen)))
                         (push other seen)
                         (if (nth 2 other)
                             (push other levels)
                           (push (car other) found))))))
                 (cond
                  ((null found) (error "No known closer for opener %s" open))
                  ;; FIXME: what should we do if there are various closers?
                  (t (car found))))))))))
    (unless (save-excursion (skip-chars-backward " \t") (bolp))
      (newline))
    (insert closer)
    (if (save-excursion (skip-chars-forward " \t") (eolp))
        (indent-according-to-mode)
      (reindent-then-newline-and-indent))))

(defun belugasmie-down-list (&optional arg)
  "Move forward down one level paren-like blocks.  Like `down-list'.
With argument ARG, do this that many times.
A negative argument means move backward but still go down a level.
This command assumes point is not in a string or comment."
  (interactive "p")
  (let ((start (point))
        (inc (if (< arg 0) -1 1))
        (offset (if (< arg 0) 1 0))
        (next-token (if (< arg 0)
                        belugasmie-backward-token-function
                      belugasmie-forward-token-function)))
    (while (/= arg 0)
      (setq arg (- arg inc))
      (while
          (let* ((pos (point))
                 (token (funcall next-token))
                 (levels (assoc token belugasmie-op-levels)))
            (cond
             ((zerop (length token))
              (if (if (< inc 0) (looking-back "\\s(\\|\\s)" (1- (point)))
                    (looking-at "\\s(\\|\\s)"))
                  ;; Go back to `start' in case of an error.  This presumes
                  ;; none of the token we've found until now include a ( or ).
                  (progn (goto-char start) (down-list inc) nil)
                (forward-sexp inc)
                (/= (point) pos)))
             ((and levels (null (nth (+ 1 offset) levels))) nil)
             ((and levels (null (nth (- 2 offset) levels)))
              (let ((end (point)))
                (goto-char start)
                (signal 'scan-error
                        (list "Containing expression ends prematurely"
                              pos end))))
             (t)))))))

(defvar belugasmie-blink-matching-triggers '(?\s ?\n)
  "Chars which might trigger `blink-matching-open'.
These can include the final chars of end-tokens, or chars that are
typically inserted right after an end token.
I.e. a good choice can be:
    (delete-dups
     (mapcar (lambda (kw) (aref (cdr kw) (1- (length (cdr kw)))))
             belugasmie-closer-alist))")

(defcustom belugasmie-blink-matching-inners t
  "Whether SMIE should blink to matching opener for inner keywords.
If non-nil, it will blink not only for \"begin..end\" but also for \"if...else\"."
  :type 'boolean)

(defun belugasmie-blink-matching-check (start end)
  (save-excursion
    (goto-char end)
    (let ((ender (funcall belugasmie-backward-token-function)))
      (cond
       ((not (and ender (rassoc ender belugasmie-closer-alist)))
        ;; This not is one of the begin..end we know how to check.
        (blink-matching-check-mismatch start end))
       ((not start) t)
       ((eq t (car (rassoc ender belugasmie-closer-alist))) nil)
       (t
        (goto-char start)
        (let ((starter (funcall belugasmie-forward-token-function)))
          (not (member (cons starter ender) belugasmie-closer-alist))))))))

(defun belugasmie-blink-matching-open ()
  "Blink the matching opener when applicable.
This uses SMIE's tables and is expected to be placed on `post-self-insert-hook'."
  (when (and blink-matching-paren
             belugasmie-closer-alist                     ; Optimization.
             (eq (char-before) last-command-event) ; Sanity check.
             (memq last-command-event belugasmie-blink-matching-triggers)
             (not (nth 8 (syntax-ppss))))
    (save-excursion
      (let ((pos (point))
            (token (funcall belugasmie-backward-token-function)))
        (when (and (eq (point) (1- pos))
                   (= 1 (length token))
                   (not (rassoc token belugasmie-closer-alist)))
          ;; The trigger char is itself a token but is not one of the
          ;; closers (e.g. ?\; in Octave mode), so go back to the
          ;; previous token.
          (setq pos (point))
          (setq token (save-excursion
                        (funcall belugasmie-backward-token-function))))
        (when (rassoc token belugasmie-closer-alist)
          ;; We're after a close token.  Let's still make sure we
          ;; didn't skip a comment to find that token.
          (funcall belugasmie-forward-token-function)
          (when (and (save-excursion
                       ;; Trigger can be SPC, or reindent.
                       (skip-chars-forward " \n\t")
                       (>= (point) pos))
                     ;; If token ends with a trigger char, so don't blink for
                     ;; anything else than this trigger char, lest we'd blink
                     ;; both when inserting the trigger char and when
                     ;; inserting a subsequent trigger char like SPC.
                     (or (eq (point) pos)
                         (not (memq (char-before)
                                    belugasmie-blink-matching-triggers)))
                     (or belugasmie-blink-matching-inners
                         (null (nth 2 (assoc token belugasmie-op-levels)))))
            ;; The major mode might set blink-matching-check-function
            ;; buffer-locally so that interactive calls to
            ;; blink-matching-open work right, but let's not presume
            ;; that's the case.
            (let ((blink-matching-check-function #'belugasmie-blink-matching-check))
              (blink-matching-open))))))))

;;; The indentation engine.

(defcustom belugasmie-indent-basic 4
  "Basic amount of indentation."
  :type 'integer)

(defvar belugasmie-indent-rules 'unset
  ;; TODO: For SML, we need more rule formats, so as to handle
  ;;   structure Foo =
  ;;      Bar (toto)
  ;; and
  ;;   structure Foo =
  ;;   struct ... end
  ;; I.e. the indentation after "=" depends on the parent ("structure")
  ;; as well as on the following token ("struct").
  "Rules of the following form.
\((:before . TOK) . OFFSET-RULES)	how to indent TOK itself.
\(TOK . OFFSET-RULES)	how to indent right after TOK.
\(list-intro . TOKENS)	declare TOKENS as being followed by what may look like
			  a funcall but is just a sequence of expressions.
\(t . OFFSET)		basic indentation step.
\(args . OFFSET)		indentation of arguments.
\((T1 . T2) OFFSET)	like ((:before . T2) (:parent T1 OFFSET)).

OFFSET-RULES is a list of elements which can each either be:

\(:hanging . OFFSET-RULES)	if TOK is hanging, use OFFSET-RULES.
\(:parent PARENT . OFFSET-RULES) if TOK's parent is PARENT, use OFFSET-RULES.
\(:next TOKEN . OFFSET-RULES)	if TOK is followed by TOKEN, use OFFSET-RULES.
\(:prev TOKEN . OFFSET-RULES)	if TOK is preceded by TOKEN, use
\(:bolp . OFFSET-RULES)		If TOK is first on a line, use OFFSET-RULES.
OFFSET				the offset to use.

PARENT can be either the name of the parent or a list of such names.

OFFSET can be of the form:
`point'				align with the token.
`parent'				align with the parent.
NUMBER				offset by NUMBER.
\(+ OFFSETS...)			use the sum of OFFSETS.
VARIABLE			use the value of VARIABLE as offset.

The precise meaning of `point' depends on various details: it can
either mean the position of the token we're indenting, or the
position of its parent, or the position right after its parent.

A nil offset for indentation after an opening token defaults
to `belugasmie-indent-basic'.")

(defun belugasmie-indent--hanging-p ()
  ;; A hanging keyword is one that's at the end of a line except it's not at
  ;; the beginning of a line.
  (and (save-excursion
         (when (zerop (length (funcall belugasmie-forward-token-function)))
           ;; Could be an open-paren.
           (forward-char 1))
         (skip-chars-forward " \t")
         (eolp))
       (not (belugasmie-indent--bolp))))

(defun belugasmie-indent--bolp ()
  (save-excursion (skip-chars-backward " \t") (bolp)))

(defun belugasmie-indent--offset (elem)
  (or (cdr (assq elem belugasmie-indent-rules))
      (cdr (assq t belugasmie-indent-rules))
      belugasmie-indent-basic))

(defvar belugasmie-indent-debug-log)

(defun belugasmie-indent--offset-rule (tokinfo &optional after parent)
  "Apply the OFFSET-RULES in TOKINFO.
Point is expected to be right in front of the token corresponding to TOKINFO.
If computing the indentation after the token, then AFTER is the position
after the token, otherwise it should be nil.
PARENT if non-nil should be the parent info returned by `belugasmie-backward-sexp'."
  (let ((rules (cdr tokinfo))
        next prev
        offset)
    (while (consp rules)
      (let ((rule (pop rules)))
        (cond
         ((not (consp rule)) (setq offset rule))
         ((eq (car rule) '+) (setq offset rule))
         ((eq (car rule) :hanging)
          (when (belugasmie-indent--hanging-p)
            (setq rules (cdr rule))))
         ((eq (car rule) :bolp)
          (when (belugasmie-indent--bolp)
            (setq rules (cdr rule))))
         ((eq (car rule) :eolp)
          (unless after
            (error "Can't use :eolp in :before indentation rules"))
          (when (> after (line-end-position))
            (setq rules (cdr rule))))
         ((eq (car rule) :prev)
          (unless prev
            (save-excursion
              (setq prev (belugasmie-indent-backward-token))))
          (when (equal (car prev) (cadr rule))
            (setq rules (cddr rule))))
         ((eq (car rule) :next)
          (unless next
            (unless after
              (error "Can't use :next in :before indentation rules"))
            (save-excursion
              (goto-char after)
              (setq next (belugasmie-indent-forward-token))))
          (when (equal (car next) (cadr rule))
            (setq rules (cddr rule))))
         ((eq (car rule) :parent)
          (unless parent
            (save-excursion
              (if after (goto-char after))
              (setq parent (belugasmie-backward-sexp 'halfsexp))))
          (when (if (listp (cadr rule))
                    (member (nth 2 parent) (cadr rule))
                  (equal (nth 2 parent) (cadr rule)))
            (setq rules (cddr rule))))
         (t (error "Unknown rule %s for indentation of %s"
                   rule (car tokinfo))))))
    ;; If `offset' is not set yet, use `rules' to handle the case where
    ;; the tokinfo uses the old-style ((PARENT . TOK). OFFSET).
    (unless offset (setq offset rules))
    (when (boundp 'belugasmie-indent-debug-log)
      (push (list (point) offset tokinfo) belugasmie-indent-debug-log))
    offset))

(defun belugasmie-indent--column (offset &optional base parent virtual-point)
  "Compute the actual column to use for a given OFFSET.
BASE is the base position to use, and PARENT is the parent info, if any.
If VIRTUAL-POINT is non-nil, then `point' is virtual."
  (cond
   ((eq (car-safe offset) '+)
    (apply '+ (mapcar (lambda (offset) (belugasmie-indent--column offset nil parent))
                      (cdr offset))))
   ((integerp offset)
    (+ offset
       (case base
         ((nil) 0)
         (parent (goto-char (cadr parent))
                 (belugasmie-indent-virtual))
         (t
          (goto-char base)
          ;; For indentation after "(let" in SML-mode, we end up accumulating
          ;; the offset of "(" and the offset of "let", so we use `min' to try
          ;; and get it right either way.
          (min (belugasmie-indent-virtual) (current-column))))))
   ((eq offset 'point)
    ;; In indent-keyword, if we're indenting `then' wrt `if', we want to use
    ;; indent-virtual rather than use just current-column, so that we can
    ;; apply the (:before . "if") rule which does the "else if" dance in SML.
    ;; But in other cases, we do not want to use indent-virtual
    ;; (e.g. indentation of "*" w.r.t "+", or ";" wrt "(").  We could just
    ;; always use indent-virtual and then have indent-rules say explicitly
    ;; to use `point' after things like "(" or "+" when they're not at EOL,
    ;; but you'd end up with lots of those rules.
    ;; So we use a heuristic here, which is that we only use virtual if
    ;; the parent is tightly linked to the child token (they're part of
    ;; the same BNF rule).
    (if (and virtual-point (null (car parent))) ;Black magic :-(
        (belugasmie-indent-virtual) (current-column)))
   ((eq offset 'parent)
    (unless parent
      (setq parent (or (belugasmie-backward-sexp 'halfsexp) :notfound)))
    (if (consp parent) (goto-char (cadr parent)))
    (belugasmie-indent-virtual))
   ((eq offset nil) nil)
   ((and (symbolp offset) (boundp 'offset))
    (belugasmie-indent--column (symbol-value offset) base parent virtual-point))
   (t (error "Unknown indentation offset %s" offset))))

(defun belugasmie-indent-forward-token ()
  "Skip token forward and return it, along with its levels."
  (let ((tok (funcall belugasmie-forward-token-function)))
    (cond
     ((< 0 (length tok)) (assoc tok belugasmie-op-levels))
     ((looking-at "\\s(")
      (forward-char 1)
      (list (buffer-substring (1- (point)) (point)) nil 0)))))

(defun belugasmie-indent-backward-token ()
  "Skip token backward and return it, along with its levels."
  (let ((tok (funcall belugasmie-backward-token-function)))
    (cond
     ((< 0 (length tok)) (assoc tok belugasmie-op-levels))
     ;; 4 == Open paren syntax.
     ((eq 4 (syntax-class (syntax-after (1- (point)))))
      (forward-char -1)
      (list (buffer-substring (point) (1+ (point))) nil 0)))))

(defun belugasmie-indent-virtual ()
  ;; We used to take an optional arg (with value :not-hanging) to specify that
  ;; we should only use (belugasmie-indent-calculate) if we're looking at a hanging
  ;; keyword.  This was a bad idea, because the virtual indent of a position
  ;; should not depend on the caller, since it leads to situations where two
  ;; dependent indentations get indented differently.
  "Compute the virtual indentation to use for point.
This is used when we're not trying to indent point but just
need to compute the column at which point should be indented
in order to figure out the indentation of some other (further down) point."
  ;; Trust pre-existing indentation on other lines.
  (if (belugasmie-indent--bolp) (current-column) (belugasmie-indent-calculate)))

(defun belugasmie-indent-fixindent ()
  ;; Obey the `fixindent' special comment.
  (and (belugasmie-indent--bolp)
       (save-excursion
         (comment-normalize-vars)
         (re-search-forward (concat comment-start-skip
                                    "fixindent"
                                    comment-end-skip)
                            ;; 1+ to account for the \n comment termination.
                            (1+ (line-end-position)) t))
       (current-column)))

(defun belugasmie-indent-bob ()
  ;; Start the file at column 0.
  (save-excursion
    (forward-comment (- (point)))
    (if (bobp) 0)))

(defun belugasmie-indent-close ()
  ;; Align close paren with opening paren.
  (save-excursion
    ;; (forward-comment (point-max))
    (when (looking-at "\\s)")
      (while (not (zerop (skip-syntax-forward ")")))
        (skip-chars-forward " \t"))
      (condition-case nil
          (progn
            (backward-sexp 1)
            (belugasmie-indent-virtual))      ;:not-hanging
        (scan-error nil)))))

(defun belugasmie-indent-keyword ()
  ;; Align closing token with the corresponding opening one.
  ;; (e.g. "of" with "case", or "in" with "let").
  (save-excursion
    (let* ((pos (point))
           (toklevels (belugasmie-indent-forward-token))
           (token (pop toklevels)))
      (if (null (car toklevels))
          (save-excursion
            (goto-char pos)
            ;; Different cases:
            ;; - belugasmie-indent--bolp: "indent according to others".
            ;; - common hanging: "indent according to others".
            ;; - SML-let hanging: "indent like parent".
            ;; - if-after-else: "indent-like parent".
            ;; - middle-of-line: "trust current position".
            (cond
             ((null (cdr toklevels)) nil) ;Not a keyword.
             ((belugasmie-indent--bolp)
              ;; For an open-paren-like thingy at BOL, always indent only
              ;; based on other rules (typically belugasmie-indent-after-keyword).
              nil)
             (t
              ;; We're only ever here for virtual-indent, which is why
              ;; we can use (current-column) as answer for `point'.
              (let* ((tokinfo (or (assoc (cons :before token)
                                         belugasmie-indent-rules)
                                  ;; By default use point unless we're hanging.
                                  `((:before . ,token) (:hanging nil) point)))
                     ;; (after (prog1 (point) (goto-char pos)))
                     (offset (belugasmie-indent--offset-rule tokinfo)))
                (belugasmie-indent--column offset)))))

        ;; FIXME: This still looks too much like black magic!!
        ;; FIXME: Rather than a bunch of rules like (PARENT . TOKEN), we
        ;; want a single rule for TOKEN with different cases for each PARENT.
        (let* ((parent (belugasmie-backward-sexp 'halfsexp))
               (tokinfo
                (or (assoc (cons (caddr parent) token)
                           belugasmie-indent-rules)
                    (assoc (cons :before token) belugasmie-indent-rules)
                    ;; Default rule.
                    `((:before . ,token)
                      ;; (:parent open 0)
                      point)))
               (offset (save-excursion
                         (goto-char pos)
                         (belugasmie-indent--offset-rule tokinfo nil parent))))
          ;; Different behaviors:
          ;; - align with parent.
          ;; - parent + offset.
          ;; - after parent's column + offset (actually, after or before
          ;;   depending on where backward-sexp stopped).
          ;; ? let it drop to some other indentation function (almost never).
          ;; ? parent + offset + parent's own offset.
          ;; Different cases:
          ;; - bump into a same-level operator.
          ;; - bump into a specific known parent.
          ;; - find a matching open-paren thingy.
          ;; - bump into some random parent.
          ;; ? borderline case (almost never).
          ;; ? bump immediately into a parent.
          (cond
           ((not (or (< (point) pos)
                     (and (cadr parent) (< (cadr parent) pos))))
            ;; If we didn't move at all, that means we didn't really skip
            ;; what we wanted.  Should almost never happen, other than
            ;; maybe when an infix or close-paren is at the beginning
            ;; of a buffer.
            nil)
           ((eq (car parent) (car toklevels))
            ;; We bumped into a same-level operator. align with it.
            (if (and (belugasmie-indent--bolp) (/= (point) pos)
                     (save-excursion
                       (goto-char (goto-char (cadr parent)))
                       (not (belugasmie-indent--bolp)))
                     ;; Check the offset of `token' rather then its parent
                     ;; because its parent may have used a special rule.  E.g.
                     ;;    function foo;
                     ;;      line2;
                     ;;      line3;
                     ;; The ; on the first line had a special rule, but when
                     ;; indenting line3, we don't care about it and want to
                     ;; align with line2.
                     (memq offset '(point nil)))
                ;; If the parent is at EOL and its children are indented like
                ;; itself, then we can just obey the indentation chosen for the
                ;; child.
                ;; This is important for operators like ";" which
                ;; are usually at EOL (and have an offset of 0): otherwise we'd
                ;; always go back over all the statements, which is
                ;; a performance problem and would also mean that fixindents
                ;; in the middle of such a sequence would be ignored.
                ;;
                ;; This is a delicate point!
                ;; Even if the offset is not 0, we could follow the same logic
                ;; and subtract the offset from the child's indentation.
                ;; But that would more often be a bad idea: OT1H we generally
                ;; want to reuse the closest similar indentation point, so that
                ;; the user's choice (or the fixindents) are obeyed.  But OTOH
                ;; we don't want this to affect "unrelated" parts of the code.
                ;; E.g. a fixindent in the body of a "begin..end" should not
                ;; affect the indentation of the "end".
                (current-column)
              (goto-char (cadr parent))
              ;; Don't use (belugasmie-indent-virtual :not-hanging) here, because we
              ;; want to jump back over a sequence of same-level ops such as
              ;;    a -> b -> c
              ;;    -> d
              ;; So as to align with the earliest appropriate place.
              (belugasmie-indent-virtual)))
           (tokinfo
            (if (and (= (point) pos) (belugasmie-indent--bolp)
                     (or (eq offset 'point)
                         (and (consp offset) (memq 'point offset))))
                ;; Since we started at BOL, we're not computing a virtual
                ;; indentation, and we're still at the starting point, so
                ;; we can't use `current-column' which would cause
                ;; indentation to depend on itself.
                nil
              (belugasmie-indent--column offset 'parent parent
                                  ;; If we're still at pos, indent-virtual
                                  ;; will inf-loop.
                                  (unless (= (point) pos) 'virtual))))))))))

(defun belugasmie-indent-comment ()
  "Compute indentation of a comment."
  ;; Don't do it for virtual indentations.  We should normally never be "in
  ;; front of a comment" when doing virtual-indentation anyway.  And if we are
  ;; (as can happen in octave-mode), moving forward can lead to inf-loops.
  (and (belugasmie-indent--bolp)
       (let ((pos (point)))
         (save-excursion
           (beginning-of-line)
           (and (re-search-forward comment-start-skip (line-end-position) t)
                (eq pos (or (match-end 1) (match-beginning 0))))))
       (save-excursion
         (forward-comment (point-max))
         (skip-chars-forward " \t\r\n")
         (belugasmie-indent-calculate))))

(defun belugasmie-indent-comment-continue ()
  ;; indentation of comment-continue lines.
  (let ((continue (and comment-continue
                       (comment-string-strip comment-continue t t))))
    (and (< 0 (length continue))
         (looking-at (regexp-quote continue)) (nth 4 (syntax-ppss))
         (let ((ppss (syntax-ppss)))
           (save-excursion
             (forward-line -1)
             (if (<= (point) (nth 8 ppss))
                 (progn (goto-char (1+ (nth 8 ppss))) (current-column))
               (skip-chars-forward " \t")
               (if (looking-at (regexp-quote continue))
                   (current-column))))))))

(defun belugasmie-indent-comment-close ()
  (and (boundp 'comment-end-skip)
       comment-end-skip
       (not (looking-at " \t*$"))       ;Not just a \n comment-closer.
       (looking-at comment-end-skip)
       (nth 4 (syntax-ppss))
       (save-excursion
         (goto-char (nth 8 (syntax-ppss)))
         (current-column))))

(defun belugasmie-indent-comment-inside ()
  (and (nth 4 (syntax-ppss))
       'noindent))

(defun belugasmie-indent-after-keyword ()
  ;; Indentation right after a special keyword.
  (save-excursion
    (let* ((pos (point))
           (toklevel (belugasmie-indent-backward-token))
           (tok (car toklevel))
           (tokinfo (assoc tok belugasmie-indent-rules)))
      ;; Set some default indent rules.
      (if (and toklevel (null (cadr toklevel)) (null tokinfo))
          (setq tokinfo (list (car toklevel))))
      ;; (if (and tokinfo (null toklevel))
      ;;     (error "Token %S has indent rule but has no parsing info" tok))
      (when toklevel
        (unless tokinfo
          ;; The default indentation after a keyword/operator is 0 for
          ;; infix and t for prefix.
          ;; Using the BNF syntax, we could come up with better
          ;; defaults, but we only have the precedence levels here.
          (setq tokinfo (list tok 'default-rule
                              (if (cadr toklevel) 0 (belugasmie-indent--offset t)))))
        (let ((offset
               (or (belugasmie-indent--offset-rule tokinfo pos)
                   (belugasmie-indent--offset t))))
          (let ((before (point)))
            (goto-char pos)
            (belugasmie-indent--column offset before)))))))

(defun belugasmie-indent-exps ()
  ;; Indentation of sequences of simple expressions without
  ;; intervening keywords or operators.  E.g. "a b c" or "g (balbla) f".
  ;; Can be a list of expressions or a function call.
  ;; If it's a function call, the first element is special (it's the
  ;; function).  We distinguish function calls from mere lists of
  ;; expressions based on whether the preceding token is listed in
  ;; the `list-intro' entry of belugasmie-indent-rules.
  ;;
  ;; TODO: to indent Lisp code, we should add a way to specify
  ;; particular indentation for particular args depending on the
  ;; function (which would require always skipping back until the
  ;; function).
  ;; TODO: to indent C code, such as "if (...) {...}" we might need
  ;; to add similar indentation hooks for particular positions, but
  ;; based on the preceding token rather than based on the first exp.
  (save-excursion
    (let ((positions nil)
          arg)
      (while (and (null (car (belugasmie-backward-sexp)))
                  (push (point) positions)
                  (not (belugasmie-indent--bolp))))
      (save-excursion
        ;; Figure out if the atom we just skipped is an argument rather
        ;; than a function.
        (setq arg (or (null (car (belugasmie-backward-sexp)))
                      (member (funcall belugasmie-backward-token-function)
                              (cdr (assoc 'list-intro belugasmie-indent-rules))))))
      (cond
       ((null positions)
        ;; We're the first expression of the list.  In that case, the
        ;; indentation should be (have been) determined by its context.
        nil)
       (arg
        ;; There's a previous element, and it's not special (it's not
        ;; the function), so let's just align with that one.
        (goto-char (car positions))
        (current-column))
       ((cdr positions)
        ;; We skipped some args plus the function and bumped into something.
        ;; Align with the first arg.
        (goto-char (cadr positions))
        (current-column))
       (positions
        ;; We're the first arg.
        (goto-char (car positions))
        ;; FIXME: Use belugasmie-indent--column.
        (+ (belugasmie-indent--offset 'args)
           ;; We used to use (belugasmie-indent-virtual), but that
           ;; doesn't seem right since it might then indent args less than
           ;; the function itself.
           (current-column)))))))

(defvar belugasmie-indent-functions
  '(belugasmie-indent-fixindent belugasmie-indent-bob belugasmie-indent-close
    belugasmie-indent-comment belugasmie-indent-comment-continue belugasmie-indent-comment-close
    belugasmie-indent-comment-inside belugasmie-indent-keyword belugasmie-indent-after-keyword
    belugasmie-indent-exps)
  "Functions to compute the indentation.
Each function is called with no argument, shouldn't move point, and should
return either nil if it has no opinion, or an integer representing the column
to which that point should be aligned, if we were to reindent it.")

(defun belugasmie-indent-calculate ()
  "Compute the indentation to use for point."
  (run-hook-with-args-until-success 'belugasmie-indent-functions))

(defun belugasmie-indent-line ()
  "Indent current line using the SMIE indentation engine."
  (interactive)
  (let* ((savep (point))
         (indent (condition-case-unless-debug nil
		     (save-excursion
                       (forward-line 0)
                       (skip-chars-forward " \t")
                       (if (>= (point) savep) (setq savep nil))
                       (or (belugasmie-indent-calculate) 0))
                   (error 0))))
    (if (not (numberp indent))
        ;; If something funny is used (e.g. `noindent'), return it.
        indent
      (if (< indent 0) (setq indent 0)) ;Just in case.
      (if savep
          (save-excursion (indent-line-to indent))
        (indent-line-to indent)))))

(defun belugasmie-indent-debug ()
  "Show the rules used to compute indentation of current line."
  (interactive)
  (let ((belugasmie-indent-debug-log '()))
    (belugasmie-indent-calculate)
    ;; FIXME: please improve!
    (message "%S" belugasmie-indent-debug-log)))

(defun belugasmie-setup (op-levels indent-rules)
  (set (make-local-variable 'belugasmie-indent-rules) indent-rules)
  (set (make-local-variable 'belugasmie-op-levels) op-levels)
  (set (make-local-variable 'indent-line-function) 'belugasmie-indent-line))



;;; Beluga indentation and navigation via SMIE

(defcustom beluga-indent-basic 4
  "Basic amount of indentation."
  :type 'integer)

(defconst beluga-smie-punct-re
  (regexp-opt '("->" "<-" "=>" "\\" "." "<" ">" "," ";" "..")))

(defun beluga-smie-forward-token ()
  (forward-comment (point-max))
  (if (looking-at "\\.[ \t]*$")
      ;; One of the LF-terminating dots.
      (progn (forward-char 1) ";.")
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
           (looking-at "[ \t]*$") ;; "[ \t]*\\(?:$\\|[0-9]\\(\\)\\)"
           (not (looking-back "\\.\\." (- (point) 2))))
      ;; Either an LF-terminating dot, or a projection-dot.
      (progn (forward-char -1) ";.") ;; (if (match-end 1) ".n" ";.")
    (buffer-substring-no-properties
     (point)
     (progn (cond
             ((looking-back beluga-smie-punct-re (- (point) 2) 'greedy)
              (goto-char (match-beginning 0)))
             ((not (zerop (skip-syntax-backward "w_'"))))
             ;; In case of non-ASCII punctuation.
             ((not (zerop (skip-syntax-backward ".")))))
            (point)))))

(defun beluga-smie-grammar (bnf resolvers precs)
  (if (fboundp 'smie-setup)
      (smie-prec2->grammar
       (smie-merge-prec2s
        (apply #'smie-bnf->prec2 bnf resolvers)
        (smie-precs->prec2 precs)))
    (belugasmie-prec2->grammar
       (belugasmie-merge-prec2s
        (apply #'belugasmie-bnf->prec2 bnf resolvers)
        (belugasmie-precs->prec2 precs)))))


;; FIXME: Use smie functions if applicable.
(defconst beluga-smie-grammar
  ;; The "." used for terminating LF declarations is syntactically completely
  ;; different from the "." used in the binding forms.  Conflating the two
  ;; leads here to a lot of precedence conflicts, so we try and guess the two
  ;; based on a heuristic in the tokenizing code.
  (beluga-smie-grammar
   ;; FIXME: without this dummy, "=>" is marked as "open paren" because it
   ;; can only bind to `atom' on the left.
   '((atom ("--dummy--"))
     (def (exp "=" exp) (atom ":" exp))
     (decl (atom ":" type)
           ("inductive" datatype-def)
	   ("coinductive" datatype-def)
	   ("LF" datatype-def)
	   ("stratified" datatype-def)
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
     (dotted-type (sdecls "|-" type))
     (type (simpletype)
           ("\\" atom "." type)         ;dotted-type
           ("block" sdecls "." type)    ;dotted-type
           ;; ("{" blabla "}" type)  ; FIXME!
           ;; FIXME: the projection via "." creates precedence conflicts.
           ;; (type "." atom)
           )
     (sdef (atom "=" schema))
     (schema (type)
             ;; Not sure if it's correct, and create precedence conflicts.
             ;; ("some" sdecls "block" sdecls "." schema)
             )
     (datatype-name (atom ":" type))
     (datatype-def (datatype-name "=" datatype-branches))
     (datatype-branches (datatype-branches "|" datatype-branches)
                        (atom ":" type))
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
   '(((assoc ";" ";."))
     ((assoc "->" "<-"))
     ((assoc ","))
     ((assoc "and"))
     ((nonassoc "of") (assoc "|"))      ; Trailing | ambiguity.
     ;; '((nonassoc "\\") (nonassoc ".")) ; Trailing . ambiguity.
     ;; '((nonassoc "block") (nonassoc ".")) ; Trailing . ambiguity.
     )

   ;; The above BNF grammar should cover this already, so this ends up only
   ;; useful to check that the BNF entails the expected precedences.
   '((assoc ";")
     (assoc ",")
     (left ":")
     (assoc "<-" "->")
     (nonassoc " -dummy- "))))          ;Bogus anchor at the end.


(defconst beluga-smie-indent-rules
  ;; FIXME: Obsolete; This variable is only used in Emacs<23.4.  Newer versions
  ;; use the beluga-smie-indent-rules function instead, via smie-setup.
  '((list-intro "fn" "FN" "mlam")
    ("of" 2)
    ("in" (:hanging 0) nil)
    ("=" 0)
    ;; FIXME: we'd like some way to specify the indentation after => depending
    ;; on whether it is a "=>" that goes with an "fn" or with a "|".
    ("=>" 0)
    (":")
    ((:before . "case") (:prev "=>" parent) point)
    ((:before . "fn") (:prev "=>" parent) point)
    ((:before . "mlam") (:prev "=>" parent) point)
    ((t . "|") . -2)
    ("let") ("if")
    ))

(defun beluga-smie-indent-rules (method token)
  (cond
   ((eq method :list-intro) (member token '("fn" "FN" "mlam")))
   ((and (eq method :elem) (eq token 'arg)) beluga-indent-basic)
   ((and (eq method :before) (equal token "|") (smie-rule-prev-p "=" "of"))
    ;; Presumable a "datatype foo = | ...".
    (smie-rule-parent))
   ((equal token "|") (smie-rule-separator method))
   ((eq method :after)
    (cond
     ((equal token "of") 2)
     ((equal token "in") (if (smie-rule-hanging-p) 0))
     ((equal token "=") 0)
     ;; FIXME: Specify the indentation after => depending
     ;; on whether it is a "=>" that goes with an "fn" or with a "|".
     ((equal token "=>") 0)
     ((member token '(":" "let" "if")) beluga-indent-basic)))
   ((eq method :before)
    (cond
     ((and (equal token "=") (smie-rule-parent-p "inductive")) 2)
     ((member token '("case" "fn" "mlam"))
      (if (smie-rule-prev-p "=>") (smie-rule-parent)))))))

;; (defcustom beluga-indent-args beluga-indent-basic
;;   "Amount of indentation of args below their function."
;;   :type 'integer)

(provide 'beluga-mode)
;;; beluga-mode.el ends here
