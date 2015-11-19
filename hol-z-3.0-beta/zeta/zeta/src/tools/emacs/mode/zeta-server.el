;;; zeta-server.el --- server for visiting locators from extern ZETA session


;; $Id: zeta-server.el,v 1.5 2000/05/16 08:10:47 wg Exp $
;; by Wolfgang Grieskamp, wg@cs.tu-berlin.de

(require 'zeta-base)

;; (if (not (gnuserv-running-p)) (gnuserv-start))

(make-face 'zeta-server-locator-face)
(set-face-foreground 'zeta-server-locator-face "Red")
(set-face-background 'zeta-server-locator-face "LightYellow")

(defvar zeta-server-selection nil)
(defvar zeta-server-locators (make-hashtable 50 'equal))
(defvar zeta-server-locator-ovls nil)

(defun zeta-server-register (fn l1 c1 l2 c2)
  (zeta-dprint "server register: %s %s %s %s %s" fn l1 c1 l2 c2)
  (if (or (= l1 0) (= c1 0) (= l2 0) (= c2 0))
      t
    (condition-case nil ;; we are in a filter! prevent any traps
	(progn
	  (let* ((h (list fn l1 c1 l2 c2))
		 (ovl (gethash h zeta-server-locators)))
	    (if (not ovl)
		(progn
		  (setq ovl (zeta-server-overlay fn l1 c1 l2 c2))
		  (if ovl
		      (progn 
			(puthash h ovl zeta-server-locators)
			(setq zeta-server-locator-ovls
			      (cons ovl zeta-server-locator-ovls))
			)))
	      )))
      (t nil)
      ))
  "")

(defun zeta-server-clear-locators ()
  (while zeta-server-locator-ovls
    (zeta-overlay-delete (car zeta-server-locator-ovls))
    (setq zeta-server-locator-ovls (cdr zeta-server-locator-ovls)))
  (setq zeta-server-locators (make-hashtable 50 'equal)))

(defun zeta-server-visit (fn l1 c1 l2 c2)
  (zeta-dprint "server visit: %s %s %s %s %s" fn l1 c1 l2 c2)
  (if (or (= l1 0) (= c1 0) (= l2 0) (= c2 0))
      (zeta-server-open fn)
    (condition-case nil 
	(progn
	  (let* ((h (list fn l1 c1 l2 c2))
		 (hovl (gethash h zeta-server-locators)) 
		 ovl 
		 (diag ""))
	    (if (or (not hovl) (not (zeta-overlay-buffer hovl)))
		(setq hovl nil
		      ovl (zeta-server-overlay fn l1 c1 l2 c2))
	      (setq ovl hovl))
	    (if (not ovl)
		(progn
		  (setq diag (format "zeta-server: not found: %s(%d.%d-%d.%d)" 
				     fn l1 c1 l2 c2))
		  (beep)
		  (message diag))
	      (if (not hovl) (puthash h ovl zeta-server-locators))
	      (zeta-server-clear)
	      (zeta-set-overlay-face ovl 'zeta-server-locator-face)
	      (setq zeta-server-selection ovl)
	      (pop-to-buffer (zeta-overlay-buffer ovl))
	      (goto-char (zeta-overlay-start ovl))
	      )
	    diag)
	  )
      (t (zeta-server-clear-locators)
	 "zeta-server: internal error"))
    )
  )

(defun zeta-server-clear ()
  (condition-case nil 
      (progn
	(zeta-dprint "server clear")
	(if zeta-server-selection
	    (zeta-set-overlay-face zeta-server-selection 'default))
	)
    (t nil)
    )
  "")

(defun zeta-server-open (fn &optional revert)
  (condition-case nil
      (progn
	(zeta-server-clear-locators)
	(let ((diag "")
	      (buf (zeta-server-find fn)))
	  (if (not buf)
	      (progn
		(setq diag (format "zeta-server: not found: %s" fn))
		(beep)
		(message diag))
	    (pop-to-buffer buf)
	    (save-excursion 
	      (set-buffer buf)
	      (zeta-server-check-mode)
	      (if revert
		  (revert-buffer t t t))))
	  diag))
    (t "zeta-server: internal error")))

(defun zeta-server-reopen (fn)
  (zeta-server-open fn t))

(defun zeta-server-save (fn &optional noconfirm)
  (condition-case nil
      (let ((diag "")
	    (buf (zeta-server-find fn)))
	(if (not buf)
	    (progn
	      (setq diag (format "zeta-server: not found: %s" fn))
	      (beep)
	      (message diag))
	  (save-current-buffer
	    (set-buffer buf)
	    (if (and (buffer-modified-p buf) 
		     (buffer-file-name buf))
		(if noconfirm
		    (basic-save-buffer)
		  (save-buffer)))
	    (goto-char (point-max))
	    (mark-beginning-of-buffer)))
	diag)
    (t "zeta-server: internal error")))

(defun zeta-server-save-related ()
  (save-current-buffer
    (condition-case nil
	(mapc
	 (lambda (buf)
	   (if (and (buffer-modified-p buf) 
		    (buffer-file-name buf)
		    (progn (set-buffer buf)
			   (or zeta-source-mode zeta-server-mode)))
	       (basic-save-buffer))
	   t)
	 (buffer-list))
      (t nil)))
  "")

(defun zeta-server-find (fn)
  (and fn
       (or (and (file-readable-p fn) 
		(file-regular-p fn)
		(find-file-noselect fn t))
	   (and (file-readable-p (concat fn ".tex")) 
		(file-regular-p (concat fn ".tex"))
		(find-file-noselect (concat fn ".tex") t)))))



(defun zeta-server-overlay (fn l1 c1 l2 c2)
  ;; (zeta-update-scratch-buffers fn)
  (let ((buf (zeta-server-find fn)))
    (if (not buf)
	;; do nothing (?)
	nil
      (let (start end)
	(save-excursion
	  (set-buffer buf)
	  (zeta-server-check-mode)
	  (goto-line l1)  
	  (beginning-of-line)
	  (forward-char (- c1 1))
	  (setq start (point-marker))
	  (goto-line l2)
	  (beginning-of-line)
	  (forward-char (- c2 1))
	  (setq end (+ (point) 1))
	  (zeta-make-overlay start end buf))))
    ))

(defun zeta-server-check-mode ()
  (if (and (boundp 'zeta-source-mode) zeta-source-mode)
      ;; deactivate the source mode
      (zeta-source-mode -1))
  (zeta-server-mode 1))


(defvar zeta-server-mode nil
  "Is ZETA server mode on or off?")
(make-variable-buffer-local 'zeta-server-mode)

(defun zeta-server-mode(&optional arg)
  "Minor mode for buffers visited by an external Z session."
  (make-local-variable 'use-dialog-box)
  (setq use-dialog-box nil)
  (if (eq arg t) (setq arg 1))
  (if (and arg
	   (or (and (>= arg 0) zeta-server-mode)
	       (and (< arg  0) (not zeta-server-mode))))
      ;; nothing changes
      ()
    ;; toggle
    (if zeta-server-mode
	;; turn it off
	(progn
	  (setq zeta-server-mode nil))
      ;; turn it on
      (setq zeta-server-mode t))))

(add-minor-mode 'zeta-server-mode " ZETA-extern")

;; provide it
(provide 'zeta-server)
