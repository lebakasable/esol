(defconst esol-mode-syntax-table
  (with-syntax-table (copy-syntax-table)
    (modify-syntax-entry ?/ ". 12")
    (modify-syntax-entry ?\n ">")
    (modify-syntax-entry ?' "\"")
    (syntax-table)))

(eval-and-compile
  (defconst esol-keywords
    '("type" "var" "trace" "run" "case")))

(defconst esol-highlights
  `((,(regexp-opt esol-keywords 'symbols) . font-lock-keyword-face)))

;;;###autoload
(define-derived-mode esol-mode prog-mode "esol"
  :syntax-table esol-mode-syntax-table
  (setq font-lock-defaults '(esol-highlights))
  (setq-local comment-start "// ")
  (setq-local syntax-propertize-function
              (syntax-propertize-rules ("./\\(/+\\)" (1 ".")))))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.esol\\'" . esol-mode))

(provide 'esol-mode)
