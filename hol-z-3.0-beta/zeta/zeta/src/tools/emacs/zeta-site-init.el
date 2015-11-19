;; zeta-site-init.el -- site dependend configuration of the zeta and vtex mode 
;; version $Id: zeta-site-init.el,v 1.8 2000/05/14 17:43:32 wg Exp $

(if (not (string-match "XEmacs" emacs-version))
  (error "The ZETA Emacs support currently only works with XEmacs."))

(if (< emacs-major-version 19)
  (error 
   "The ZETA Emacs support requires XEmacs version 19 or later."))

;; this variable needs to be set either here or in your .emacs
;; before requiring 'zeta-site-init
(defvar zeta-dir "@ZETADIR@/")

;; whether ZETA source mod shall be enabled whenever a .tex .zed .zeta
;; .esz .msz file is visited
(defvar zeta-mode-default-on t)

;; whether VTeX shall be enabled whenever a .tex .zed .zeta .esz .msz
;; file is visited
(defvar zeta-vtex-default-on nil)

;; whether activation shall be guided also via AucTeX style hooks
(defvar zeta-style-hook-on nil)



;; extend load-path
(setq load-path (cons (concat (expand-file-name zeta-dir) "lib/emacs/")
		      load-path))

;; autoloading definitions
(autoload 'zeta "zeta-mode" nil t)
(autoload 'zeta-source-mode "zeta-mode" nil t)
(autoload 'vtex-mode "vtex-mode" nil t)
(autoload 'zeta-server-register "zeta-server" nil t)
(autoload 'zeta-server-visit "zeta-server" nil t)
(autoload 'zeta-server-clear "zeta-server" nil t)
(autoload 'zeta-server-open "zeta-server" nil t)
(autoload 'zeta-server-reopen "zeta-server" nil t)
(autoload 'zeta-server-save "zeta-server" nil t)
(autoload 'zeta-server-save-related "zeta-server" nil t)

;; cross reference from zeta-mode (FIXME)
(autoload 'vtex-special-face "vtex-faces" nil t)



;; register minor modes, initially without keymaps 
(if (assq 'zeta-source-mode minor-mode-alist)
    ()
  (setq minor-mode-alist (cons '(zeta-source-mode " ZETA") minor-mode-alist))
  )
(if (or (not (string-match "XEmacs" emacs-version))
	(assq 'vtex-mode minor-mode-alist))
    ()
  (setq minor-mode-alist (cons '(vtex-mode " VTeX") minor-mode-alist))
  )

;; register hooks for activation
(add-hook 'LaTeX-mode-hook 'zeta-guess-activate)
(add-hook 'latex-mode-hook 'zeta-guess-activate)

;; setting up file name extensions for AucTeX
(setq TeX-one-master "\\.tex$\\|\\.zed$\\|\\.zeta$\\|\\.esz$\\|\\.msz$")
(setq TeX-file-extensions '("tex" "sty" "cls" "ltx" "texi" 
	                     "zeta" "esz" "zed" "msz"))

;; register style hooks for AucTeX. FIXME: more names for Z styles
(if (and zeta-style-hook-on (fboundp 'TeX-add-style-hook))
    (progn
      (TeX-add-style-hook "fuzz" 'zeta-activate)
      (TeX-add-style-hook "esz" 'zeta-activate)
      (TeX-add-style-hook "zeta" 'zeta-activate)))


(defun zeta-guess-activate ()
  "Activate zeta mode if buffer name ends with extension."
  (if (string-match TeX-one-master (buffer-name))
      (zeta-activate))
  )

(defun zeta-activate ()
  "Activate zeta minor mode."
  ;; once activated, activate it always if latex mode is enabled
  ;; (remove-hook 'LaTeX-mode-hook 'zeta-guess-activate)
  ;; (remove-hook 'latex-mode-hook 'zeta-guess-activate)
  ;; (add-hook 'LaTeX-mode-hook 'zeta-activate)
  ;; (add-hook 'latex-mode-hook 'zeta-activate)
  (if zeta-mode-default-on (zeta-source-mode t))
  (if zeta-vtex-default-on (vtex-mode t))
  )
  
;; provide it
(provide 'zeta-site-init)
