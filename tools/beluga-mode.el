;;; beluga-mode.el --- Major mode for Beluga source code  -*- coding: utf-8 -*-

;; Copyright (C) 2009, 2010, 2012, 2013  Free Software Foundation, Inc.

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
  `(,(concat "\\_<"
             (regexp-opt
              '("FN" "and" "block" "case" "datatype" "else" "ffalse" "fn" "if"
                "in" "impossible" "let" "mlam" "of" "rec" "schema" "some"
                "then" "type" "ttrue" "%name" "%not"))
             "\\_>\\|\\\\")
    (,(concat "^\\(" beluga-syntax-id-re
              "\\)[ \t\n]*:\\([^.]*\\_<type\\_>[ \t\n]*.\\)?")
     ;; This is a regexp that can span multiple lines, so it may not
     ;; always highlight properly.  `font-lock-multiline' tries to help.
     (0 (if (match-end 2) '(face nil font-lock-multiline t)))
     (1 (if (match-end 2)
            font-lock-type-face font-lock-variable-name-face)))
    (,(concat "^\\(?:schema\\|datatype\\)[ \t\n]+\\("
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
     ,(concat "^\\(?:datatype[ \t]+\\(" beluga-syntax-id-re
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

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.bel\\'" . beluga-mode))
(add-to-list 'auto-mode-alist '("\\.sbel\\'" . beluga-mode))

;;;###autoload
(define-derived-mode beluga-mode nil "Beluga"
  "Major mode to edit Beluga source code."
  (set (make-local-variable 'imenu-generic-expression)
       beluga-imenu-generic-expression)
  (set (make-local-variable 'outline-regexp)
       (concat beluga-syntax-fundec-re "\\|^datatype\\_>"))
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
  (if (fboundp 'smie-setup)
      (smie-setup beluga-smie-grammar #'beluga-smie-indent-rules
                  :forward-token #'beluga-smie-forward-token
                  :backward-token #'beluga-smie-backward-token)
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
    (set (make-local-variable 'belugasmie-blink-matching-triggers) '(?>)))

  (set (make-local-variable 'font-lock-defaults)
       '(beluga-font-lock-keywords nil nil () nil
         (font-lock-syntactic-keywords . nil))))

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
           ("datatype" datatype-def)
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
     ((and (equal token "=") (smie-rule-parent-p "datatype")) 2)
     ((member token '("case" "fn" "mlam"))
      (if (smie-rule-prev-p "=>") (smie-rule-parent)))))))

(defcustom beluga-indent-basic 4
  "Basic amount of indentation."
  :type 'integer)

;; (defcustom beluga-indent-args beluga-indent-basic
;;   "Amount of indentation of args below their function."
;;   :type 'integer)

(provide 'beluga-mode)
;;; beluga-mode.el ends here
