;;; Directory Local Variables
;;; See Info node `(emacs) Directory Variables' for more information.

((nil
  (coding . us-ascii)
  (indent-tabs-mode)
  (eval ignore-errors
      "Write-contents-functions is a buffer-local alternative to before-save-hook"
      (add-hook 'write-contents-functions
                (lambda ()
                  (delete-trailing-whitespace (point-min) (point-max))
                  nil))))
 (tuareg-mode
  (compile-command . "omake -R")))
