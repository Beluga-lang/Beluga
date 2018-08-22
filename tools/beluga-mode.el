;;; beluga-mode.el --- Major mode for Beluga source code  -*- coding: utf-8; lexical-binding:t -*-

;; Copyright (C) 2009-2018  Free Software Foundation, Inc.

;; Author: Stefan Monnier <monnier@iro.umontreal.ca>
;; Maintainer: beluga-dev@cs.mcgill.ca
;; Version: 0
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
(require 'smie)

(provide 'beluga-unicode-input-method)
(require 'quail)

(defconst beluga-input-method-name
  "beluga-unicode"
  "The name of the Beluga unicode input method.")

(quail-define-package
 beluga-input-method-name ;; name
 "UTF-8"                  ;; language
 "\\"                     ;; mode-line "title"
 t                        ;; guidance
 "Beluga unicode input method: actually replaces keyword strings with
a single unicode character instead of merely representing the keywords
in unicode using Font Lock mode."
  nil nil nil nil nil nil nil nil nil nil t)
;; This very final t is the SIMPLE flag of quail-define-package, and
;; causes Quail to not affect the meanings of C-{f,b,n,p} or TAB.

(quail-define-rules
 ;; Greek letters
 ("\\alpha" ["α"])
 ("\\Alpha" ["Α"])
 ("\\beta" ["β"])
 ("\\Beta" ["Β"])
 ("\\gamma" ["γ"])
 ("\\Gamma" ["Γ"])
 ("\\delta" ["δ"])
 ("\\Delta" ["Δ"])
 ("\\epsilon" ["ε"])
 ("\\Epsilon" ["Ε"])
 ("\\zeta" ["ζ"])
 ("\\Zeta" ["Ζ"])
 ("\\eta" ["η"])
 ("\\Eta" ["Η"])
 ("\\theta" ["θ"])
 ("\\Theta" ["Θ"])
 ("\\iota" ["ι"])
 ("\\Iota" ["Ι"])
 ("\\kappa" ["κ"])
 ("\\Kappa" ["Κ"])
 ("\\lambda" ["λ"])
 ("\\Lambda" ["Λ"])
 ("\\lamda" ["λ"])
 ("\\Lamda" ["Λ"])
 ("\\mu" ["μ"])
 ("\\Mu" ["Μ"])
 ("\\nu" ["ν"])
 ("\\Nu" ["Ν"])
 ("\\xi" ["ξ"])
 ("\\Xi" ["Ξ"])
 ("\\omicron" ["ο"])
 ("\\Omicron" ["Ο"])
 ("\\pi" ["π"])
 ("\\Pi" ["Π"])
 ("\\rho" ["ρ"])
 ("\\Rho" ["Ρ"])
 ("\\sigma" ["σ"])
 ("\\Sigma" ["Σ"])
 ("\\tau" ["τ"])
 ("\\Tau" ["Τ"])
 ("\\upsilon" ["υ"])
 ("\\Upsilon" ["Υ"])
 ("\\phi" ["φ"])
 ("\\Phi" ["Φ"])
 ("\\chi" ["χ"])
 ("\\Chi" ["Χ"])
 ("\\psi" ["ψ"])
 ("\\Psi" ["Ψ"])
 ("\\omega" ["ω"])
 ("\\Omega" ["Ω"])


 ;; Arrows
 ("->" ["→"])
 ("<-" ["←"])
 ("=>" ["⇒"])

 ;;LF
 ("|-" ["⊢"])
 ("\\not" ["¬"])
 ("::" ["∷"])
 ("FN" ["Λ"])
)

(defgroup beluga-mode ()
  "Editing support for the Beluga language."
  :group 'languages)

(defvar beluga-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\C-c\C-c" 'compile)
    (define-key map "\C-c\C-l" 'beluga-highlight-holes)
    (define-key map "\C-c\C-e" 'beluga-erase-holes)
    (define-key map "\C-c\C-x" 'beli-cmd)
    (define-key map "\C-c\C-t" 'beli--type)
    (define-key map "\C-c\C-s" 'beluga-split-hole)
    (define-key map "\C-c\C-i" 'beluga-intro-hole)
    (define-key map "\C-c\C-j" 'beluga-hole-jump)
    (define-key map "\C-c\C-p" 'beluga-hole-info)
    map))

(defvar beluga-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?% "< 14" st)
    (modify-syntax-entry ?\{ "(}2 b" st)
    (modify-syntax-entry ?\} "){3 b" st)
    (modify-syntax-entry ?\n ">" st)
    (modify-syntax-entry ?/ "$/" st)
    ;; For application of dependent arguments "exp A < ctx . term >", we'd want
    ;; <..> to match, but that breaks ->, <-, and other things.
    ;; (modify-syntax-entry ?< "(>" st)
    ;; (modify-syntax-entry ?> ")<" st)
    ; see https://emacs.stackexchange.com/a/4149 for a possible solution
    (modify-syntax-entry ?#  "'" st)
    (modify-syntax-entry ?< "." st)
    (modify-syntax-entry ?> "." st)
    (modify-syntax-entry ?- "." st)
    (modify-syntax-entry ?| "." st)
    (modify-syntax-entry ?= "." st)
    (modify-syntax-entry ?\' "_" st)
    st))

(defun beluga--proc-live-p (process)
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
	`((,(regexp-opt (mapcar #'car alist) t)
	   (0 (beluga-font-lock-compose-symbol ',alist)
              ;; In Emacs-21, if the `override' field is nil, the face
              ;; expressions is only evaluated if the text has currently
              ;; no face.  So force evaluation by using `keep'.
              keep)))))))

(defconst beluga-syntax-id-re
  "[[:alpha:]_][[:alnum:]_']*"
  "A regexp for matching a Beluga identifier.")

(defconst beluga-syntax-fundec-re
  (regexp-opt '("rec" "and") 'symbols)
  "A regexp for matching a function declaration.
 Note that this will also match the 'and' keyword!")

(defvar beluga-imenu-generic-expression
  `(("Schemas"
     ,(concat "^[ \t]*schema[ \t\n]+\\(" beluga-syntax-id-re "\\)") 1)
    ("Constructors"
     ,(concat "^\\(" beluga-syntax-id-re "\\)[ \t\n]*:") 1)
    ("Type Constructors"
     ,(concat "^\\(?:inductive[ \t]+\\(" beluga-syntax-id-re
              "\\)\\|\\(?1:" beluga-syntax-id-re
              "\\)[ \t\n]*:[^.]*\\<type\\>[ \t\n]*.\\)")
     1)
    ("Functions"
     ,(concat beluga-syntax-fundec-re "[ \t\n]+\\(" beluga-syntax-id-re "\\)") 1)))

(define-obsolete-variable-alias 'beluga-interpreter-path
  ;; A "path" is a list of file names, as in $PATH, $MANPATH.
  'beluga-interpreter-name "Sep-2010")
(defcustom beluga-interpreter-name "beluga"
  "Name of the interpreter executable."
  :type 'string)

;;---------------------------- Interactive mode ----------------------------;;

(define-error 'beluga-interactive-error "Beluga interactive error")

(defun beluga-interactive-error (&rest data)
  (signal 'beluga-interactive-error data))

;; ------ process management ----- ;;

(defvar beluga--proc ()
  "Contain the process running beli.")
(make-variable-buffer-local 'beluga--proc)

(defun beluga--proc ()
  (unless (beluga--proc-live-p beluga--proc) (beluga-start))
  beluga--proc)

(defun beluga-start ()
  "Start an inferior beli process with the -emacs option.
The process is put into a buffer called \"*beluga*\".
If a previous beli process already exists, kill it first."
  (interactive)
  (beluga-stop)
  (setq beluga--proc
        (get-buffer-process
         (make-comint "beluga"
		      beluga-interpreter-name
                      nil "-I" "-emacs" ))))

(defun beluga-quit ()
  "Stops the Beluga interactive process by sending the quit
  command. This is a graceful termination."
  (interactive)
  (beluga--rpc "quit"))

(defun beluga-stop ()
  "Stop the beli process."
  (interactive)
  (when (processp 'beluga--proc)
    (kill-process 'beluga--proc)))

;; ----- Stuff for hole overlays ----- ;;

(defvar beluga--holes-overlays ()
  "Will contain the list of hole overlays so that they can be resetted.")
(make-variable-buffer-local 'beluga--holes-overlays)

(defun beluga-sorted-holes ()
  (cl-labels
      ((hole-comp (a b)
                  (let* ((s1 (overlay-start a))
                         (s2 (overlay-start b)))
                    (< s1 s2))))
    (sort beluga--holes-overlays #'hole-comp)))

(defface beluga-holes
  '((t :background "cyan")) ;; :foreground "white"
  "Face used to highlight holes in Beluga mode.")

(defun beluga--pos (line bol offset)
  ;; According to http://caml.inria.fr/mantis/view.php?id=5159,
  ;; `line' can refer to line numbers in various source files,
  ;; whereas `bol' and `offset' refer to "character" (byte?) positions within
  ;; the actual parsed stream.
  ;; So if there might be #line directives, we need to do:
  ;; (save-excursion
  ;;   (goto-char (point-min))
  ;;   (forward-line (1- line)) ;Lines count from 1 :-(
  ;;   (+ (point) (- offset bol))))
  ;; But as long as we know there's no #line directive, we can ignore all that
  ;; and use the more efficient code below.  When #line directives can appear,
  ;; we will need to make further changes anyway, such as passing the file-name
  ;; to select the appropriate buffer.
  ;; Emacs considers the first character in the file to be at index 1,
  ;; but the Beluga lexer starts counting at zero, so we need to add
  ;; one here.
  (+ (point-min) offset))

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

(defun beluga-erase-holes ()
  (interactive)
  (mapc #'delete-overlay beluga--holes-overlays)
  (setq beluga--holes-overlays nil))

;; ----- Interaction with the interactive mode ----- ;;

;; Sending and receiving strings from the inferior process.
;; Ultimately, all you really need to use is beluga--rpc to send a
;; command to the interactive mode and get back a string response.

(defun beluga--wait (proc)
  (assert (eq (current-buffer) (process-buffer proc)))
  (while (and (progn
                (goto-char comint-last-input-end)
                (not (re-search-forward ".*;" nil t)))
              (accept-process-output proc 0.025))))

(defun beluga--chomp (str)
  "Chomp leading and tailing whitespace from STR."
  (replace-regexp-in-string (rx (or (: bos (* (any " \t\n")))
                                    (: (* (any " \t\n")) eos)))
                            ""
                            str))
(defun beluga--trim (str)
  (let ((str2 (beluga--chomp str)))
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
  "Read the last output of beli."
  (let ((proc (beluga--proc)))
    (with-current-buffer (process-buffer proc)
      (beluga--wait proc)
      (beluga--trim (buffer-substring-no-properties comint-last-input-end (point-max))))))

(defun beluga--rpc (cmd)
  (beluga--send cmd)
  (beluga--receive))

(defun beluga--is-response-error (resp)
  "Determine whether a Beluga RPC response is an error."
  (string= "-" (substring resp 0 1)))

(defun beluga--rpc! (cmd)
  "Variant of beluga--rpc that signals an error if the command fails."
  (let ((resp (beluga--rpc cmd)))
    (when (beluga--is-response-error resp)
      (beluga-interactive-error (list (format "%s" (substring resp 2)))))
    resp))

(defvar beluga--last-load-time
  '(0 0 0 0)
  "The last time the file was loaded into the Beluga interpreter.
This variable is updated by `beluga--maybe-save-load-current-buffer'.")
(make-variable-buffer-local 'beluga--last-load-time)

(defun beluga--should-reload-p ()
  "Decide whether the current buffer should be reloaded into the
  Beluga interpreter.
The `visited-file-modtime' is compared to `beluga--last-load-time'.
If the former is greater than the latter, then the former is
returned. Else, `nil' is returned."
  (let ((mtime (visited-file-modtime)))
    (message "Comparing times %s > %s ?" (current-time-string mtime) (current-time-string beluga--last-load-time))
    (when (> (float-time mtime) (float-time beluga--last-load-time))
      (message "Need to reload!")
        mtime)))

;; ----- Beluga Interactive basic functions ----- ;;

;; Each of these functions directly corresponds to a command in src/core/command.ml

;; Since the construction of these functions is totally tedious and
;; straightforward, we define a macro to do the real work.
;; This macro takes:
;;   * the name of the function to define, e.g. beluga--printhole
;;   * the real name of the command to invoke, e.g. "printhole"
;;   * the arguments of the function, e.g. '((hole . "%s"))
;;
;; Note: the type of each argument is specified as a printf-style
;; format code. That's because the construction of the command will
;; construct a string formatting routine using these codes.
;;
;; What about constant portions of the string?
;; If you want to supply a constant portion in the format string,
;; simply provide a string as-is in the argument list.
;; e.g. ((hole . "%s") "with" (exp . "%s"))
;;
;; Two separate functions are generated by the macro invocation. The
;; first uses exactly the given function name, but the second appends
;; "!". This bang-variant will use beluga--rpc! under the hood, so you
;; get an exception-raising variant of every function for free.

(defun beluga--generate-format-string (args)
  "Constructs the format string from the argument list."
  (cons
   "%s"
   (mapcar
    (lambda (x)
      (if (stringp x)
          x
        (cdr x)))
    args)))

(defun beluga--generate-arg-list (args)
  "Constructs a list of symbols representing the function arguments."
  (mapcar 'car (cl-remove-if 'stringp args)))

(defun beluga--define-command (rpc name realname args)
  (let ((arglist (beluga--generate-arg-list args))
        (fmt (beluga--generate-format-string args)))
    `(defun ,name ,arglist
       (,rpc
        (format
         ;; construct the format string
         ,(mapconcat 'identity fmt " ")
         ;; construct the argument list
         ,realname ,@arglist)))))

(defmacro beluga-define-command (name realname args)
  `(progn
     ,(beluga--define-command 'beluga--rpc name realname args)
     ,(beluga--define-command 'beluga--rpc! (intern (concat (symbol-name name) "!")) realname args)))

(beluga-define-command beluga--basic-chatteron "chatteron" nil)
(beluga-define-command beluga--basic-chatteroff "chatteroff" nil)
(beluga-define-command beluga--basic-load "load" ((path . "%s")))
(beluga-define-command beluga--basic-clearholes "clearholes" nil)
(beluga-define-command beluga--basic-numholes "numholes" nil)
(beluga-define-command beluga--basic-numholes-lf "numlfholes" nil)
(beluga-define-command beluga--basic-lochole "lochole" ((hole . "%s")))
(beluga-define-command beluga--basic-lochole-n "lochole" ((hole . "%d")))
(beluga-define-command beluga--basic-lochole-lf "lochole-lf" ((hole . "%s")))
(beluga-define-command beluga--basic-lochole-lf-n "lochole-lf" ((hole . "%d")))
(beluga-define-command beluga--basic-printhole "printhole" ((hole . "%s")))
(beluga-define-command beluga--basic-printhole-n "printhole" ((hole . "%d")))
(beluga-define-command beluga--basic-printhole-lf "printhole-lf" ((hole . "%s")))
(beluga-define-command beluga--basic-printhole-lf-n "printhole-lf" ((hole . "%d")))
(beluga-define-command beluga--basic-types "types" nil)
(beluga-define-command beluga--basic-constructors-lf "constructors" ((type . "%s")))
(beluga-define-command beluga--basic-fill "fill" ((hole . "%s") "with" (exp . "%s")))
(beluga-define-command beluga--basic-split "split" ((hole . "%s") (var . "%s")))
(beluga-define-command beluga--basic-intro "intro" ((hole . "%s")))
(beluga-define-command beluga--basic-constructors "constructors-comp" ((type . "%s")))
(beluga-define-command beluga--basic-signature "fsig" ((fun . "%s")))
(beluga-define-command beluga--basic-printfun "fdef" ((fun . "%s")))
(beluga-define-command beluga--basic-query "query" ((expected . "%s") (tries . "%s") (type . "%s")))
(beluga-define-command beluga--basic-get-type "get-type" ((line . "%d") (col . "%d")))
(beluga-define-command beluga--basic-reset "reset" nil)
(beluga-define-command beluga--basic-quit "quit" nil)
(beluga-define-command beluga--basic-lookuphole "lookuphole" ((hole . "%s")))

;; ----- Higher-level commands ----- ;;

;; These build off the basic commands, and will typically do something
;; like parse the response or display it in a message.

(defun beli ()
  "Start beli mode"
  (interactive)
  (beluga-start))

(defun beli-cmd (cmd)
  "Run a command in beli"
  (interactive "MCommand: ")
  (message "%s" (beluga--rpc cmd)))

(defun beluga--maybe-save ()
  (if (buffer-modified-p)
    (if (y-or-n-p "Save current file?")
      (save-buffer)
      ())))

(defun beluga-get-type ()
  "Get the type at the current cursor position (if it exists)"
  (interactive)
  (message "%s" (beluga--basic-get-type (count-lines 1 (point)) (current-column))))

(defun beluga--load-current-buffer (&optional mtime)
  "Load the current buffer in Beluga Interactive. This command signals
an error if loading fails.
The optional `mtime' parameter, if given, will be written to `beluga--last-load-time'."
  (let ((resp (beluga--basic-load! (buffer-file-name))))
    (when mtime
      (setq beluga--last-load-time mtime))
    resp))

(defun beluga--maybe-save-load-current-buffer ()
  "Loads the current buffer if it has either never been loaded, or
modified since the last time it was loaded.
This will update `beluga--last-load-time' if a load is performed."
  ;; prompt the user to save the buffer if it is modified
  (beluga--maybe-save)
  ;; retrieve the last time the file was written to disk, checking
  ;; whether a reload should occur
  (let ((mtime (beluga--should-reload-p)))
    (when mtime ;; mtime non-nil means we must reload
      (beluga--load-current-buffer mtime))))

(defun beluga--numholes! ()
  (string-to-number (beluga--basic-numholes!)))

(defun beluga--numholes-lf! ()
  (string-to-number (beluga--basic-numholes-lf!)))

(defun beluga--lochole-n! (hole-num)
  (read (beluga--basic-lochole-n! hole-num)))

(defun beluga--lochole-lf-n! (hole-num)
  (read (beluga--basic-lochole-lf-n! hole-num)))

(defun beluga--lookup-hole! (hole)
  "Looks up a hole number by its name"
  (string-to-number (beluga--basic-lookuphole! hole)))

(defun beluga--highlight-holes ()
  "Create overlays for each of the holes and color them."
  (beluga-erase-holes)
  (let ((numholes (beluga--numholes!)))
    (dotimes (i numholes)
      (let* ((pos (beluga--lochole-n! i))
             (ol (beluga--create-overlay pos))
             (info (beluga--basic-printhole-n! i)))
        (overlay-put ol 'help-echo info)
        (push ol beluga--holes-overlays)
        )))
  (let ((numholes (beluga--numholes-lf!)))
    (dotimes (i numholes)
      (let* ((pos (beluga--lochole-lf-n! i))
             (ol (beluga--create-overlay pos))
             (info (beluga--basic-printhole-lf-n! i)))
        (overlay-put ol 'help-echo info)
        (push ol beluga--holes-overlays)))))

(defun beluga--get-hole-overlay! (hole)
  "Gets the overlay associated with a hole."
  (nth (beluga--lookup-hole! hole) (beluga-sorted-holes)))

(defun beluga--apply-quail-completions (str)
  (if (string= current-input-method beluga-input-method-name)
     (replace-regexp-in-string "=>" "⇒"
      (replace-regexp-in-string "|-" "⊢" str))
     str))

(defun beluga--insert-formatted (str start)
  (goto-char start)
  (insert (beluga--apply-quail-completions str))
  (indent-region start (+ start (length str))))

(defun beluga--error-no-such-hole (n)
  (message "Couldn't find hole %s - make sure the file is loaded" n))

(defconst beluga-named-hole-re
  "\\_<?\\(\\sw+\\)\\_>")

(defun beluga-named-hole-at-point ()
  "Retrieves the name of the hole at point, if any. If e.g. point is
  over `?abracadabra`, then this function returns `abracadabra`.
Else, if point is not over a valid hole, then this function returns
nil."
  (let ((thing (thing-at-point 'symbol)))
    (when (and thing (string-match beluga-named-hole-re thing))
      (match-string 1 thing))))

(defun beluga--prompt-with-hole-at-point (prompt)
  "Prompts the user to specify a hole, giving the named hole at point
as the default if any."
  (let ((name (beluga-named-hole-at-point)))
    (if name
        (read-string (format "%s (%s): " prompt name)
                     nil nil name)
      (read-string (format "%s: " prompt)))))

(defun beluga--begin-command ()
  "Performs necessary setup to begin a compound Beluga Interactive
command.
Specifically, the following are performed, if necessary:
  - Starting the Beluga inferior process.
  - Saving the current buffer.
  - Loading the current buffer into Beluga.
  - Highlighting holes."
  (beluga-start)
  (beluga--maybe-save-load-current-buffer)
  (beluga--highlight-holes))

(defun beluga--prompt-string (prompt)
  "Prompts the user to input a string."
  (read-string (format "%s: " prompt)))

;; ----- Top-level commands ----- ;;

(defun beluga-load ()
  "Load the current file in Beluga Interactive. This command will
start the interactive mode if necessary and prompt for saving."
  (interactive)
  (beluga-start)
  (let ((r (beluga--maybe-save-load-current-buffer)))
    (if r
        (message "%s" r)
      (message "Buffer does not require reload."))))

(defun beluga-highlight-holes ()
  "Create overlays for each of the holes and color them."
  (interactive)
  (beluga--begin-command))

(defun beluga-hole-info (hole)
  (interactive
   (list
    (beluga--prompt-with-hole-at-point "Hole to query")))
  (beluga--begin-command)
  (let ((resp (beluga--basic-printhole! hole)))
    (message resp)))

(defun beluga-split-hole (hole var)
  "Split on a hole"
  (interactive
   (list
    (beluga--prompt-with-hole-at-point "Hole to split at")
    (beluga--prompt-string "Variable to split")))
  (beluga--begin-command)
  (let ((resp (beluga--basic-split! hole var))
        (ovr (beluga--get-hole-overlay! hole)))
    (if ovr
        (let ((start (overlay-start ovr))
              (end (overlay-end ovr)))
          (delete-overlay ovr)
          (delete-region start end)
          (beluga--insert-formatted (format "(%s)" resp) start)
          (save-buffer)
          (beluga--load-current-buffer)
          (beluga--highlight-holes))
      (beluga--error-no-such-hole hole))))

(defun beluga-intro-hole (hole)
  "Introduce variables into a hole"
  (interactive
   (list
    (beluga--prompt-with-hole-at-point "Hole to introduce variables into")))
  (beluga--begin-command)
  (let ((resp (beluga--basic-intro! hole))
        (ovr (beluga--get-hole-overlay! hole)))
    (if ovr
        (let ((start (overlay-start ovr))
              (end (overlay-end ovr)))
          (delete-overlay ovr)
          (delete-region start end)
          (beluga--insert-formatted resp start)
          (save-buffer)
          (beluga--load-current-buffer)
          (beluga--highlight-holes))
      (beluga--error-no-such-hole hole))))

(defun beluga-hole-jump (hole)
  (interactive "sHole to jump to: ")
  (beluga--begin-command)
  (let ((ovr (beluga--get-hole-overlay! hole)))
    (if ovr
        (goto-char (+ 1 (overlay-start ovr)))
      (beluga--error-no-such-hole hole))))
(define-obsolete-function-alias 'hole-jump #'beluga-hole-jump "Jul-2018")

;; ----- Beluga indentation and navigation via SMIE ----- ;;

(defconst beluga-syntax-pragma-re
  "--\\(\\(name\\|query\\|infix\\|prefix\\|assoc\\).*?\\.\\|\\w+\\)"
  "A regexp for matching a Beluga pragma. Long pragmas continue until
a `.` is found, e.g. `--name oft D.`. Short pragmas consist of only
one word, e.g. `--nostrengthen`. It's easy to use this regex to check
which type of pragma (long or short) was matched: simply check whether
`match-string' 2 is non-nil. In that case, a long pragma was matched
and the result is the name of the long pragma. Otherwise,
`match-string' 1 will contain the name of the matched short.")

(defconst beluga-slim-arrows
  '("->" "<-" "→" "←")
  "A list of the slim arrow strings.")

(defconst beluga-fat-arrows
  '("=>" "⇒")
  "A list of the fat arrow strings.")

(defconst beluga-punct-re
  (regexp-opt `(,@beluga-fat-arrows ,@beluga-slim-arrows "\\" "." "<" ">" "," ";" "..")))

(defconst beluga-syntax-keyword-re
  (regexp-opt
   '("FN" "and" "block" "case" "inductive" "LF" "coinductive"
     "stratified" "else" "ffalse" "fn" "if" "in" "impossible" "let"
     "mlam" "of" "rec" "schema" "some" "then" "type" "ctype" "ttrue"
     "module" "struct" "end" "#stratified" "#positive" "fun")
   'symbols)
  "A regular expression to match any beluga keyword.")

(defface beluga-font-lock-annotation
  '((t :inherit italic))
  "Face used for Beluga's /.../ annotations.")

(defconst beluga-font-lock-keywords
  `((,beluga-syntax-pragma-re . ,font-lock-warning-face)

    ,beluga-syntax-keyword-re

    ("/\\s-*\\_<\\(total\\)\\_>.*?/"
     (0 'beluga-font-lock-annotation)
     (1 'font-lock-keyword-face prepend))

    (,(concat
       "^\\(" beluga-syntax-id-re "\\)"
       "\\s-*" ":"
       "\\([^.]*\\_<type\\_>\\s-*.\\)?")
     ;; This is a regexp that can span multiple lines, so it may not
     ;; always highlight properly.  `font-lock-multiline' tries to help.
     (0 (if (match-end 2) '(face nil font-lock-multiline t)))
     (1 (if (match-end 2)
            font-lock-type-face font-lock-variable-name-face)))

    (,(concat "^\\(?:schema\\|inductive\\|coinductive\\|LF\\|stratified\\)" "\\s-+"
              "\\(" beluga-syntax-id-re "\\)")
     (1 font-lock-type-face))

    (,(concat beluga-syntax-fundec-re "\\s-+\\(" beluga-syntax-id-re "\\)")
     (2 font-lock-function-name-face))
    ))

(defcustom beluga-indent-basic 4
  "Basic amount of indentation."
  :type 'integer)

(defun beluga-smie-forward-token ()
  ; skip all whitespace and comments
  (forward-comment (point-max))
  (cond
   ((looking-at "\\.[ \t]*$")
      ;; One of the LF-terminating dots.
    (progn (forward-char 1) ";."))
   ((looking-at beluga-syntax-pragma-re)
    ;; move point to the end of the long-pragma name if a long-pragma was matched.
    ;; otherwise, move it to the end of the short pragma name.
    (goto-char (or (match-end 2) (match-end 1)))
    ;; set to non-nil by beluga-syntax-pragma-re if the pragma is a long-form pragma
    (if (match-string 2)
        "--longpragma"
        "--shortpragma"))
   (t
    ; otherwise, we return a chunk of text that starts at point and
    ; ends according to the following `cond` check.
    (buffer-substring-no-properties
     (point)
     (progn
       (cond
        ((looking-at beluga-punct-re) (goto-char (match-end 0)))
        ((not (zerop (skip-syntax-forward "w_'"))))
        ;; In case of non-ASCII punctuation.
        ((not (zerop (skip-syntax-forward ".")))))
       (point))))))

(defun beluga-short-pragma-before-p ()
  "Decides whether there is a short pragma before point. Returns the
starting position of the short pragma; else, nil."
  (save-excursion
    ;; idea: move backward across word-characters, and then check if
    ;; there are two dashes before point.
    (skip-syntax-backward "w")
    (save-match-data
      (when (looking-back "--" (- (point) 2))
        (match-beginning 0)))))

(defun beluga-smie-backward-token ()
  (forward-comment (- (point-max)))
  (cond
   ((and (eq ?\. (char-before))
         (looking-at "[ \t]*$") ;; "[ \t]*\\(?:$\\|[0-9]\\(\\)\\)"
         (not (looking-back "\\.\\." (- (point) 2))))
    ;; Either an LF-terminating dot, or a projection-dot.
    (progn (forward-char -1) ";."))
   ((setq pos (beluga-short-pragma-before-p))
    (goto-char pos)
    "--shortpragma")
   (t
    (buffer-substring-no-properties
     (point)
     (progn
       (cond
        ((looking-back beluga-punct-re (- (point) 2) 'greedy)
         (goto-char (match-beginning 0)))
        ((not (zerop (skip-syntax-backward "w_'"))))
        ;; In case of non-ASCII punctuation.
        ((not (zerop (skip-syntax-backward ".")))))
       (point))))))

(defun beluga-smie-grammar (bnf resolvers precs)
  (smie-prec2->grammar
   (smie-merge-prec2s
    (apply #'smie-bnf->prec2 bnf resolvers)
    (smie-precs->prec2 precs))))

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

     (decl
      (atom ":" type)
      (datatypes)
      ("schema" sdef)
      ("let" def)
      ("--shortpragma")
      ("--longpragma" atom)
      (recs))

     (datatypes
      ("inductive" datatype-def)
      ("coinductive" datatype-def)
      ("LF" datatype-def)
      ("stratified" datatype-def)
      (datatypes "and" datatypes))

     (simpletype
      (simpletype "->" simpletype)
      (simpletype "→" simpletype)
      (simpletype "←" simpletype)
      (simpletype "<-" simpletype))

     (recs
      ("rec" def)
      (recs "and" recs))

     (decls
      (decl)
      (decls ";" decls)
      (decls ";." decls))

     ;; FIXME: only allow simple types here, otherwise we get nasty
     ;; precedence conflicts between "." and ",".  In practice, this seems to
     ;; be sufficient.
     (sdecl
      (atom ":" type))

     (sdecls
      (sdecl)
      (sdecls "," sdecls))

     (dotted-type
      (sdecls "|-" type)
      (sdecls "⊢" type))

     (type
      (simpletype)
      ("\\" atom "." type)         ;dotted-type
      ("block" sdecls "." type)    ;dotted-type
      ;; ("{" blabla "}" type)  ; FIXME!
      ;; FIXME: the projection via "." creates precedence conflicts.
      ;; (type "." atom)
      )

     (sdef
      (atom "=" schema))

     (schema
      (type)
      ;; Not sure if it's correct, and create precedence conflicts.
      ;; ("some" sdecls "block" sdecls "." schema)
      )

     (datatype-name
      (atom ":" type))

     (datatype-def
      (datatype-name "=" datatype-branches))

     (datatype-branches
      (datatype-branches "|" datatype-branches)
      (atom ":" type))

     (exp
      ("if" exp "then" exp "else" exp)
      (type)
      ("let" def "in" exp)
      ("fun" atom "=>" exp)
      ("fun" atom "⇒" exp)
      ("fn" atom "=>" exp)
      ("fn" atom "⇒" exp)
      ("FN" atom "=>" exp)
      ("FN" atom "⇒" exp)
      ("mlam" atom "=>" exp)
      ("mlam" atom "⇒" exp)
      ("<" dotted-type ">")
      ("case" exp "of" cases))

     (exps
      (exps ";" exps)
      (exp))

     ;; Separate cases/branch so that "|" is recognized as associative.
     (cases
      (branch)
      (cases "|" cases))

     (branch
      (atom "=>" exp)
      (atom "⇒" exp)))

   ; resolvers
   `(((assoc ";" ";."))
     ((assoc ,@beluga-slim-arrows))
     ((assoc ","))
     ((assoc "and"))
     ((nonassoc "of") (assoc "|"))      ; Trailing | ambiguity.
     ;; '((nonassoc "\\") (nonassoc ".")) ; Trailing . ambiguity.
     ;; '((nonassoc "block") (nonassoc ".")) ; Trailing . ambiguity.
     )

   ;; The above BNF grammar should cover this already, so this ends up only
   ;; useful to check that the BNF entails the expected precedences.
   ; precs
   `((assoc ";")
     (assoc ",")
     (left ":")
     (assoc ,@beluga-slim-arrows)
     (nonassoc " -dummy- "))))          ;Bogus anchor at the end.

(defconst beluga-pattern-fat-arrow
  `(or ,@beluga-fat-arrows)
  "A pattern for use in pcase that matches any fat arrow string.")

(defun beluga-rule-parent-p (parents)
  `(smie-rule-parent-p ,@parents))

(defun beluga-smie-indent-rules (method token)
  (message (format ">> indenting %s %s" method token))
  (ignore-errors
    (message (format "   parent is %s" (smie-indent--parent))))
  (pcase `(,method . ,token)
    (`(:elem . basic)
     (message "<< basic indent")
     beluga-indent-basic)

    ; describe the tokens that introduce lists (with no separators)
    (`(:list-intro . ,(or ":" "fn" "fun" "FN" "mlam"))
     (message "<< list intro form")
     't)

    ; if the token is a pipe preceded by an '=' or 'of', then we
    ; indent by adding the basic offset
    (`(:before . ,(and "|" (guard (smie-rule-prev-p "=" "of"))))
     (message
      (format
       "<< pipe preceded by = or of with parent %s"
       (smie-indent--parent)))
     beluga-indent-basic)

    ; if the token is a pipe, (and the preceding check didn't pass, so
    ; it isn't the first pipe in a sequence) then we consider it a
    ; separator
    (`(method . ,"|")
     (message "<< pipe is a separator")
     (smie-rule-separator method))

    (`(:after . ,"of")
     (message "<< after of")
     beluga-indent-basic)

    (`(:after . ,"in")
     (when (smie-rule-hanging-p)
       (message "<< hanging in")
       nil))

    (`(:after . ,(and "=" (guard (smie-rule-parent-p "rec"))))
     (message "<< indent after = aligns to rec")
     (smie-rule-parent))

    ; if the token is a form that will use => eventually but is
    ; preceded by a =>, then this is a chain, e.g.
    ; mlam G => mlam Q => fn x => fn y =>
    ; (code should be here, not indented 8 characters)
    (`(:before
       .
       ,(and
         (or "case" "fn" "FN" "mlam" "fun")
         (guard `(smie-rule-prev-p ,@beluga-fat-arrows))))
     (message "<< case fn FN mlam fun chain")
     (smie-rule-parent))

    (`(:after . ".")
     (message "after .")
     (smie-rule-parent))

    (`(:after . ,(and ":" (guard (smie-rule-parent-p "{"))))
     (smie-rule-parent 1))

    (`(:after . ,(or ":" "let" "if"))
     (message "<< : let if basic indent")
     (smie-rule-parent beluga-indent-basic))

    (`(:before
       .
       ,(and "=" (guard `(smie-rule-parent-p ,@beluga-type-declaration-keywords))))
     (message (format "<< parent of = declares a datatype" (smie-indent--parent)))
     (smie-rule-parent))

    ; do not indent anything else
    (_ (message "<< nothing matched") nil)
    ))

;;---------------------------- Loading of the mode ----------------------------;;

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.s?bel\\'" . beluga-mode))

(defconst beluga-type-declaration-keywords
  '("inductive" "coinductive" "LF" "stratified")
  "The different keywords that introduce a type definition.")

(defconst beluga-type-declaration-keywords-re
  (regexp-opt beluga-type-declaration-keywords 'symbols)
  "A regular expression that matches any type definition keyword.")

;;;###autoload
(define-derived-mode beluga-mode prog-mode "Beluga"
  "Major mode to edit Beluga source code."
  (set (make-local-variable 'imenu-generic-expression)
       beluga-imenu-generic-expression)
  (set (make-local-variable 'outline-regexp)
       (concat beluga-syntax-fundec-re "\\|^(inductive\\|coinductive\\|LF\\|stratified)\\_>"))
  (set (make-local-variable 'require-final-newline) t)
  (when buffer-file-name
    (set (make-local-variable 'compile-command)
         ;; Quite dubious, but it's the intention that counts.
         (concat beluga-interpreter-name
                 " "
                 (shell-quote-argument buffer-file-name))))
  (set (make-local-variable 'comment-start) "%")
  (set (make-local-variable 'comment-start-skip) "%[%{]*[ \t]*")
  (set (make-local-variable 'comment-end-skip) "[ \t]*\\(?:\n\\|}%\\)")
  (comment-normalize-vars)
  (set (make-local-variable 'electric-indent-chars)
       (append '(?|) (if (boundp 'electric-indent-chars)
                         electric-indent-chars
                       '(?\n))))
  ;QUAIL
  (add-hook 'beluga-mode-hook
   (lambda () (set-input-method "beluga-unicode")))

  ;Turn off hilighting
  (setq input-method-highlight-flag nil)

  (smie-setup
   beluga-smie-grammar
   'beluga-smie-indent-rules
   :forward-token #'beluga-smie-forward-token
   :backward-token #'beluga-smie-backward-token)

  (set (make-local-variable 'parse-sexp-ignore-comments) t)

  (set
   (make-local-variable 'font-lock-defaults)
   '(beluga-font-lock-keywords
     nil
     nil
     ()
     nil
     (font-lock-syntactic-keywords . nil)))

  (message "beluga-mode loaded"))

(provide 'beluga-mode)
;;; beluga-mode.el ends here
