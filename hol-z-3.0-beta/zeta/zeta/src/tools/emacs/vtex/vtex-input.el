;; vtex-mode 
;; HANDLING INPUT
;; $Id: vtex-input.el,v 1.3 1998/09/21 08:55:06 wg Exp $

(provide 'vtex-input)

(require 'vtex-base)
(require 'vtex-custom)
(require 'vtex-tmpl)
(require 'vtex-parse)

;;; Buffer Change Hooks

(defvar vtex-auto-delete-extents nil
  "List of extents the contents of which shall be
deleted in `after-change-hook'.")
(make-variable-buffer-local 'vtex-auto-delete-extents)

(defsubst vtex-add-markup (ext exts)
  "Add EXT to EXTS if it isn't already contained and if it has
the property vtex-markup or vtex-markup-optional."
  (if (or (extent-property ext 'vtex-markup)
	  (extent-property ext 'vtex-markup-optional))
      (if (not (memq ext exts))
	  (cons ext exts)
	exts)
    exts))
	

(defun vtex-before-change-hook (from to)
  (call-with-condition-handler 
   (lambda (what-error)
     ;; (vtex-dprint "before change: %s" what-error)
     (setq vtex-auto-delete-extents nil)
     ;; (vtex-reset-parser-globals)
     (if what-error (signal-error (car what-error) (cdr what-error))))
   'vtex-before-change-hook1 from to))

(defun vtex-before-change-hook1 (from to)
  (setq vtex-auto-delete-extents nil)
  ;; (vtex-dprint "last %s this %s" (quote last-command) (quote this-command))
  (if (and vtex-auto-delete-markup
	   (not (eq t this-command)) ;; undo
	   (not (memq this-command 
		      vtex-inhibit-auto-delete-markup-commands)))
      ;; determine extents effected
      (map-extents 
       (lambda (ext arg)
	 (if (extent-property ext 'vtex-markup-optional)
	     ;; record just this extent
	     (setq vtex-auto-delete-extents 
		   (vtex-add-markup ext vtex-auto-delete-extents))
	   ;; take also all other markup of this instance into account
	   (let ((inst (extent-property ext 'vtex-inst)))
	     (setq vtex-auto-delete-extents 
		   (vtex-reduce 'vtex-add-markup
			   (vtex-inst-extents inst)
			   vtex-auto-delete-extents))))
	 nil)
       (current-buffer) from to nil nil 'vtex-markup)))

(defun vtex-after-change-hook (from to del)
  ;; delete extents in vtex-auto-delete-extents
  (call-with-condition-handler 
   (lambda (what-error)
     ;; (vtex-dprint "after change: %s" what-error)
     (setq vtex-auto-delete-extents nil)
     ;; (vtex-reset-parser-globals)
     (if what-error (signal-error (car what-error) (cdr what-error))))
   'vtex-after-change-hook1 from to del))

(defun vtex-after-change-hook1 (from to del)
  ;; delete extents in vtex-auto-delete-extents
  (let (ext efrom eto)
    (while vtex-auto-delete-extents
      (setq ext (car vtex-auto-delete-extents)
	    vtex-auto-delete-extents (cdr vtex-auto-delete-extents))
      (if (and (extent-live-p ext) 
	       (not (extent-property ext 'read-only)))
	  (progn
	    (if (not (extent-detached-p ext))
		(progn
		  (setq efrom (extent-start-position ext)
			eto (extent-end-position ext))
		  (delete-region efrom eto)
		  ;; widden range for auto-parsing
		  (setq from (min from efrom))
		  (setq to (max to eto))))
	    (delete-extent ext)))))
  ;;@? from to del should be synchronized with the deletions.
  ;;at least, ensure them to be in the buffers range
  (setq from (max (point-min) (min (point-max) from)))
  (setq to (max (point-min) (min (point-max) to)))
  ;; register the region for autoparsing 
  (vtex-auto-parse-register from (+ to del)))


;;; Pre- and Post Command Hook

;; realizes:
;; * extent property 'vtex-phantom. Point may not be placed inside of a 
;;   phantom extent. 
;; * extent property 'vtex-atomic. This is similar to the standard 'atomic
;;   property, but is merged within here because of the interdependencies
;;   with 'vtex-phantom.
;; * forcing the auto-parser
;; @NYI: marks, X-selection etc (see atomic-extents.el)

(defvar vtex-visible-phantoms nil
  "Whether VTeX should make phantoms and atomics visible.")
(make-variable-buffer-local 'vtex-input-visible-phantoms)

(defmacro vtex-visible-phantoms (&rest forms) 
  "Evalute FORMS with phantom and atomic extents visible in the current 
buffer. As an effect, 'goto-char sees the actually characters
in the buffer, and doesnt skip over invisible ones."
  `(let ((vtex-input-visible-phantoms t))
     ,@forms))


(defvar vtex-pre-command-point 0
  "The value of point at the time pre-command-hook is called.")
(make-variable-buffer-local 'vtex-pre-command-point)

(defvar vtex-pre-command-mark nil
  "The value of mark at the time pre-command-hook is called.")
(make-variable-buffer-local 'vtex-pre-command-mark)

(defvar vtex-phantom-cursor-extent nil
  "An extent used for programming around a XEmacs cursor display bug  
for phantom extents.")
(make-variable-buffer-local 'vtex-phantom-cursor-extent)

(defvar vtex-phantom-cursor-used nil)
(make-variable-buffer-local 'vtex-phantom-cursor-used)

(defun vtex-pre-command-hook ()
  (setq vtex-pre-command-point (point))
  (setq vtex-pre-command-mark (mark))
  (if vtex-phantom-cursor-used
      (progn
	(detach-extent vtex-phantom-cursor-extent)
	(redisplay-frame)
	(setq vtex-phantom-cursor-used nil)
	(set-specifier text-cursor-visible-p t (current-buffer))
	)))

(defun vtex-post-command-hook ()
  (save-excursion (vtex-auto-parse-force))
  (if (not vtex-visible-phantoms)
      (let ((inhibit-quit t)
	    (pos (point)) (continue t) forward ext inext)
	(setq forward (>= pos vtex-pre-command-point))
	(while continue
	  (setq continue nil)
	  (setq ext (extent-at pos nil 'vtex-phantom))
	  (if ext
	      (if forward
		  (progn
		    (setq pos (extent-end-position ext))
		    (setq continue t))
		(if (> (extent-start-position ext) (point-min))
		    (progn
		      (setq pos (- (extent-start-position ext) 1))
		      (setq continue t))
		  (setq pos (extent-start-position ext))
		  (setq inext ext))))
	  (setq ext (extent-at pos nil 'vtex-atomic))
	  (if ext
	      (if (/= pos (extent-start-position ext))
		  (if forward
		      (progn
			(setq pos (extent-end-position ext))
			(setq continue t))
		    (setq pos (extent-start-position ext))
		    (setq inext ext))
		(setq inext ext)))
	  )
	(goto-char pos)
	(if inext
	    ;; damned cursor bug ...
	    (let ((start (extent-start-position inext))
		  (end (extent-end-position inext)))
	      (set-specifier text-cursor-visible-p nil (current-buffer))
	      (if (not vtex-phantom-cursor-extent)
		  ;; first time used, initialize
		  (progn
		    (setq vtex-phantom-cursor-extent
			  (make-extent start end))
		    (set-extent-property vtex-phantom-cursor-extent
					 'face 'text-cursor)
		    ;; (set-extent-property vtex-phantom-cursor-extent
		;; 			 'priority 10000)
		    )
		;; reuse from the last time
		(set-extent-endpoints vtex-phantom-cursor-extent start end))
	      (setq vtex-phantom-cursor-used t)
	      (redisplay-frame)
		
	      )))))
	  


(defmacro vtex-prevent-auto-delete (&rest forms)
  "Evaluate FORMS with auto-deletion of markups disabled."
  `(let ((vtex-auto-delete-markup nil))
     ,@forms))



;;; Installation

(defun vtex-install-input-hooks ()
  "Install input hooks for the current buffer."
  (make-local-hook 'pre-command-hook)
  (add-hook 'pre-command-hook 'vtex-pre-command-hook nil t)
  (make-local-hook 'post-command-hook)
  (add-hook 'post-command-hook 'vtex-post-command-hook nil t)
  (make-local-hook 'before-change-functions)
  (add-hook 'before-change-functions 'vtex-before-change-hook nil t)
  (make-local-hook 'after-change-functions)
  (add-hook 'after-change-functions 'vtex-after-change-hook nil t)
)

(defun vtex-uninstall-input-hooks ()
  "Uninstall input hooks for the current buffer."
  (remove-hook 'pre-command-hook 'vtex-pre-command-hook t)
  (remove-hook 'post-command-hook 'vtex-post-command-hook t)
  (remove-hook 'before-change-functions 'vtex-before-change-hook t)
  (remove-hook 'after-change-functions 'vtex-after-change-hook t)
)
