
(setq load-path (cons nil load-path))
(load "zeta-base.el")
(load "zeta-mode.el")
(load "zeta-server.el")

(byte-compile-file "zeta-base.el")
(byte-compile-file "zeta-mode.el")
(byte-compile-file "zeta-server.el")
