;; vtex-mode.el
;; MODE INSTALLATION
;; version $Id: vtex-mode.el,v 1.1 1998/09/18 10:12:50 wg Exp $

(provide 'vtex-mode)

(require 'vtex-base)
(require 'vtex-custom)
(require 'vtex-tmpl)
(require 'vtex-parse)
(require 'vtex-input)

(defvar vtex-mode nil
  "Is vtex-mode on or off?")
(make-variable-buffer-local 'vtex-mode)

(defvar vtex-saved-syntax-table nil
  "The original syntax table of the major mode.")
(make-variable-buffer-local 'vtex-saved-syntax-table)
  

(defvar vtex-buffer-extent nil
  "Extent over the entire buffer.")
(make-variable-buffer-local 'vtex-buffer-extent)


(defun vtex-mode (&optional arg)
"A minor mode for visual editing of LaTeX documents.
This mode should be used in conjunction with a TeX major
mode such as AucTEX.

Use \\[vtex-decorate] to completely 
rebuild the current buffers visual decorations. Use
\\[vtex-undecorate] to remove the decorations. 

Use \\[vtex-insert] to insert a LaTeX structure in the current buffer
for which a decoration is known by this mode. You may user other
insertion commands provided by the TeX/LaTeX major mode.

Enabling this mode calls the hooks stored in vtex-on-hooks,
disabling this mode call the hooks stored in vtex-off-hooks.

Key bindings:
\\{vtex-mode-map}
"

  (interactive "P")

  (if (eq arg t) (setq arg 1))
  (if (and arg
	   (or (and (>= arg 0) vtex-mode)
	       (and (< arg  0) (not vtex-mode))))
      ;; nothing changes
      ()
    ;; toogle
    (if vtex-mode
	;; turn it off. 
	(progn
	  (set-syntax-table vtex-saved-syntax-table)
	  (vtex-remove-menu)
	  (vtex-uninstall-input-hooks)
	  (run-hooks 'vtex-mode-off-hooks)
	  (vtex-undecorate)
	  (if vtex-buffer-extent
	      (progn 
		(detach-extent vtex-buffer-extent)
		(delete-extent vtex-buffer-extent)
		(setq vtex-buffer-extent nil)))
	  (setq vtex-mode nil))
      ;; turn it on
      (vtex-load-rc)
      ;; deactivate font-lock mode
      (turn-off-font-lock)
      ;; setup the prefix maps, escaping the
      ;; previous meaning of the the prefix keys (note that we are not
      ;; yet in the minor mode; the variable vtex-mode isn't set).
      (let ((lmap (make-sparse-keymap)) old)
	(set-keymap-parents lmap (list vtex-mode-map))
	(define-key lmap
	  (concat vtex-command-prefix vtex-command-prefix)
	  (key-binding vtex-command-prefix))
	(make-local-variable 'minor-mode-map-alist)
	(setq minor-mode-map-alist (copy-alist minor-mode-map-alist))
	(setq old (assq 'vtex-mode minor-mode-map-alist))
	(if old
	    (setcdr old lmap)
	  (setq minor-mode-map-alist (cons (cons 'vtex-mode lmap)
					   minor-mode-map-alist))))
      ;; save original syntax table, and define modified one
      (setq vtex-saved-syntax-table (syntax-table))
      (set-syntax-table (vtex-extend-syntax-table 
			 (copy-syntax-table vtex-saved-syntax-table)))
      ;; now turn on the mode
      (setq vtex-mode t)
      (setq vtex-buffer-extent (make-extent (point-min) (point-max)))
      (set-extent-property vtex-buffer-extent 'start-open nil)
      (set-extent-property vtex-buffer-extent 'end-open nil)
      (set-extent-property vtex-buffer-extent 'detachable nil)
      (set-extent-property vtex-buffer-extent 'face 'vtex-text)
      ;; add menu
      (vtex-add-menu)
      ;; run the hooks
      (vtex-install-input-hooks)
      (run-hooks 'vtex-mode-on-hooks)
      (vtex-decorate)
      )))

(add-minor-mode 'vtex-mode " VTeX" vtex-mode-map)
