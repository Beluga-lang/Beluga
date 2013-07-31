;;; Directory Local Variables
;;; See Info node `(emacs) Directory Variables' for more information.

((nil
  (coding . us-ascii)
  (indent-tabs-mode . nil)
  (eval . (add-hook 'before-save-hook 'delete-trailing-whitespace nil t)))
 (tuareg-mode
  (compile-command . "omake -R")))
