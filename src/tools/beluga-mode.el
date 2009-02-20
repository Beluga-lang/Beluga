;;; beluga-mode.el --- Major mode for Beluga source code

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
    (define-key map "\C-c\C-c" 'beluga-compile)
    map))

(defvar beluga-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?% "<" st)
    (modify-syntax-entry ?\n ">" st)
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
  ;; Not sure about fn -> λ, since we could also have \ -> λ.
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
	(list (cons "not" (decode-char 'ucs 172))
              (cons "fn" (decode-char 'ucs 955))
              (cons "FN" (decode-char 'ucs 923))
              (cons "Sigma" (decode-char 'ucs 931))
              (cons "->" (decode-char 'ucs 8594))
	      (cons "<-" (decode-char 'ucs 8592))
	      (cons "=>" (decode-char 'ucs 8658))
              (cons "::" (decode-char 'ucs 8759))
	      ;; (cons ".." (decode-char 'ucs 8230)) ; Actually "..."
	      (cons ".." (decode-char 'ucs 8229))
              ;; (cons "forall" (decode-char 'ucs 8704))
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

(defvar beluga-font-lock-keywords
  `(,(regexp-opt '("FN" "fn" "case" "of" "rec" "schema" "in" "Sigma"
                   "block" "let" "some" "type") 'word)
    (,(concat "\\<rec\\>\\s +\\(" beluga-syntax-id-re "\\)")
     (1 font-lock-function-name-face))
    ,@(beluga-font-lock-symbols-keywords)))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.bel\\'" . beluga-mode))

;;;###autoload
(define-derived-mode beluga-mode nil "Beluga"
  "Major mode to edit Beluga source code."
  (set (make-local-variable 'font-lock-defaults)
       '(beluga-font-lock-keywords nil nil () nil
         (font-lock-syntactic-keywords . nil))))

(provide 'beluga-mode)
;;; beluga-mode.el ends here
