;;; Directory Local Variables
;;; See Info node `(emacs) Directory Variables' for more information.

((nil
  (coding . us-ascii)
  (indent-tabs-mode . nil)
  (eval . (add-hook 'write-contents-functions 'delete-trailing-whitespace)))
 (tuareg-mode
  (compile-command . "omake -R")))
