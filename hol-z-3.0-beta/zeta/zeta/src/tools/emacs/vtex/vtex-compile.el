
(setq load-path (cons nil load-path))
(load "vtex-mode.el")

(byte-compile-file "vtex-base.el")
(byte-compile-file "vtex-custom.el")
(byte-compile-file "vtex-faces.el")
(byte-compile-file "vtex-tmpl.el")
(byte-compile-file "vtex-parse.el")
(byte-compile-file "vtex-input.el")
(byte-compile-file "vtex-mode.el")

