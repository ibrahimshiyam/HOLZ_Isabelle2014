;;; zeta-base.el --- basic definitions for commander and server

;; $Id: zeta-base.el,v 1.5 2000/05/14 17:43:32 wg Exp $
;; by Wolfgang Grieskamp, wg@cs.tu-berlin.de

(setq zeta-running-windows (string-match "win.*" (symbol-name system-type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; XEmacs/Emacs compatibility

(setq zeta-running-xemacs (string-match "XEmacs\\|Lucid" emacs-version))



;; we have not everything ported to FSF Emacs currently:

(if (not zeta-running-xemacs)
    (require 'zeta-emacs))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Keymaps

(if zeta-running-xemacs
    (defsubst zeta-set-keymap-name (map name)
      (set-keymap-name map name))
  (defsubst zeta-set-keymap-name (map name)
    () ;; CHECKME
    ))

(if zeta-running-xemacs
    (defsubst zeta-set-keymap-parent (map parent)
      (set-keymap-parents map (list parent)))
  (defsubst zeta-set-keymap-parent (map parent)
    (set-keymap-parent map parent)))

(if (not zeta-running-xemacs)
    ;; taken from the XEmacs library
    (defmacro save-current-buffer (&rest forms)
      "Restore the current buffer setting after executing FORMS.
Does not restore the values of point and mark.
See also: `save-excursion'."
      ;; by Stig@hackvan.com
      (` (let ((_cur_buf_ (current-buffer)))
	   (unwind-protect
	       (progn (,@ forms))
	     (set-buffer _cur_buf_)))))
  )

(if zeta-running-xemacs
    (defsubst zeta-define-button-key (map modifier num binding)
      (define-key map 
	(vector (append modifier 
			(list (intern (concat "button" 
					      (int-to-string num))))))
	binding))
  (defsubst zeta-define-button-key (map modifier num binding)
    (define-key map 
      (vector (append modifier 
		     (list (intern (concat "mouse-" 
					   (int-to-string num))))))
      binding)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Goto char

(if zeta-running-xemacs
    (defsubst zeta-goto-char (pos buf)
      (goto-char pos buf))
  (defsubst zeta-goto-char (pos buf)
    (save-current-buffer
     (set-buffer buf)
     (goto-char pos))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Faces


(if zeta-running-xemacs
    (defsubst zeta-make-face (sym &optional temp)
      (make-face sym temp))
  (defsubst zeta-make-face (sym &optional temp)
    (make-face sym)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; markers
;; FIXME: port this to GNU emacs

(defvar zeta-marker-map
  (let ((map (make-sparse-keymap)))
    (zeta-set-keymap-name map 'zeta-marker-map)
    (define-key map [mouse-1] 'zeta-marker-activate)
;    (define-key map 'button1 'zeta-marker-activate) ; XEmacs
    map))
   
(defun zeta-make-marker (glyph action pos buf)
  (let ((m (make-extent pos pos buf)))
    (set-extent-property m 'end-open t)
    (set-extent-property m 'start-open t)
    (set-extent-property m 'duplicable nil)
    (set-extent-property m 'zeta-marker t)
    (set-extent-property m 'zeta-marker-action action)
    (set-extent-property m 'keymap zeta-marker-map)
    (set-extent-begin-glyph m glyph 'outside-margin)
    m))

(defsubst zeta-get-marker-property (m prop)
  (extent-property m prop))

(defsubst zeta-set-marker-property (m prop data)
  (set-extent-property m prop data))

(defsubst zeta-set-marker-glyph (m glyph)
  (set-extent-begin-glyph m glyph 'outside-margin))

(defsubst zeta-marker-at (pos prop)
  (extent-at pos nil prop))

(defun zeta-map-markers (beg end fun)
  (map-extents 
   (lambda (ext arg) (funcall fun ext))
   nil beg end )) ; nil nil 'zeta-marker))

(defun zeta-marker-activate (e)
  (interactive "e")
  (let ((m (event-glyph-extent e)) act)
    (if (and m (setq act (extent-property m 'zeta-marker-action)))
	(funcall act m)
      (mouse-set-point e))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; overlays
;; FIXME: port this to GNU emacs

(defvar zeta-overlay-map
  (let ((map (make-sparse-keymap)))
    (zeta-set-keymap-name map 'zeta-overlay-map)
    (define-key map [mouse-1] 'zeta-marker-activate)
;    (define-key map 'button1 'zeta-marker-activate) ; XEmacs
    map))

(defsubst zeta-make-overlay (beg end &optional buf)
  (let ((o (make-extent beg end buf)))
    (set-extent-property o 'duplicable nil)
    (set-extent-property o 'zeta-overlay t)
    o))

(defsubst zeta-set-overlay-closed (o)
  (set-extent-property o 'end-open nil)
  (set-extent-property o 'end-closed t)
  (set-extent-property o 'start-open nil))

(defsubst zeta-set-overlay-open (o)
  (set-extent-property o 'end-open t)
  (set-extent-property o 'end-closed nil)
  (set-extent-property o 'start-open t))

(defsubst zeta-set-overlay-face (o face)
  (set-extent-property o 'face face))

(defun zeta-set-overlay-action (o action)
  (set-extent-property o 'zeta-overlay-action action)
  (if action
      (progn
	(set-extent-property o 'keymap zeta-overlay-map)
	(set-extent-property o 'mouse-face 'highlight))
    (set-extent-property o 'keymap nil)
    (set-extent-property o 'mouse-face nil)))

(defsubst zeta-set-overlay-property (o prop data)
  (set-extent-property o prop data))

(defsubst zeta-get-overlay-property (o prop)
  (extent-property o prop))

(defsubst zeta-set-overlay-invisible (o yes)
  (zeta-set-overlay-skip o yes)
  (set-extent-property o 'invisible yes))

(defsubst zeta-get-overlay-invisible (o)
  (extent-property o 'invisible))

(defsubst zeta-set-overlay-skip (o yes)
  (set-extent-property o 'zeta-skip yes))

(defsubst zeta-get-overlay-skip (o)
  (extent-property o 'zeta-skip))

(defsubst zeta-set-overlay-readonly (o yes)
  (set-extent-property o 'read-only yes))

(defsubst zeta-overlay-end (o)
  (extent-end-position o))

(defsubst zeta-overlay-start (o)
  (extent-start-position o))

(defsubst zeta-overlay-buffer (o)
  (extent-buffer o))

(defsubst zeta-overlay-detach (o)
  (detach-extent o))

(defsubst zeta-overlay-delete (o)
  (delete-extent o))

(defun zeta-overlay-activate (e)
  (interactive "e")
  (mouse-set-point e)
  (let* ((o (zeta-overlay-at (point) 'zeta-overlay-action))
	 (act (and o (extent-property o 'zeta-overlay-action))))
    (if act
	(funcall act o))))

(defun zeta-overlay-at (pos prop)
  (extent-at pos nil prop))

(defun zeta-map-overlays (beg end fun)
  (map-extents  
   (lambda (ext arg) (funcall fun ext))
   nil beg end )) ; nil nil nil)) ; 'zeta-overlay))

(defun zeta-overlays-in (beg end &optional prop)
  (let (cands)
    (map-extents
     (lambda (ext arg)
       (setq cands (cons ext cands))
       nil)
     nil beg end ); nil nil prop)
    (reverse cands)
    ))


; old FSF Emacs code:
;  (defsubst zeta-overlay-at (pos prop)
;    (let ((cands (overlays-at (point))) cand)
;      (while cands 
;	(setq cand (car cands))
;	(if (overlay-get cand prop)
;	    (setq cands nil)
;	  (setq cand nil
;		cands (cdr cands))))
;      cand))
;  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Debugging, Erros, and Warnings

(defvar zeta-debug-on nil
  "Whether debug messages shall be printed.")

(defvar zeta-log-buffer "*DEBUG ZETA*"
  "Buffer to log debug message.")

(defun zeta-dprint (msg &rest args)
  "Print a debug message to log buffer if 'zeta-debug-on is none-nil."
  (if zeta-debug-on
      (save-excursion
	(set-buffer (get-buffer-create zeta-log-buffer))
	(goto-char (point-max))
	(insert "ZETA-MODE: " (eval `(format ,@(cons msg args))) "\n"))))

(defun zeta-die (msg &rest args)
  "Print an error message and let the current computation die."
  (eval `(zeta-dprint ,@(cons msg args)))
  (error "zeta-mode: internal error (see log buffer %s)" zeta-log-buffer))

(defun zeta-warn (msg &rest args)
  "Print a warning to the log buffer."
  (save-excursion
    (set-buffer (get-buffer-create zeta-log-buffer))
    (goto-char (point-max))
    (insert "zeta-mode: warning: " (eval `(format ,@(cons msg args))) "\n")))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utilities

(defvar zeta-sym-count 0
  "Temporary symbol counter.")

(defun zeta-make-temp-sym ()
  (setq zeta-sym-count (+ zeta-sym-count 1))
  (intern (concat "zeta-temp-sym-" (int-to-string zeta-sym-count))))


(defun zeta-remove-last-newline (string)
  (let ((newl (string-match "\n$" string)))
    (if newl
	(substring string 0 newl)
      string)))


(defun zeta-prefix-map (prefix map &optional parent oldbinding)
  (if (not oldbinding) (setq oldbinding (key-binding prefix)))
  (let (new)
    (if (not zeta-running-xemacs)
	(progn
	  (setq new (copy-keymap map))
	  (if parent (set-keymap-parent new parent)))
      ;; XEmacs: there is something horrible wrong with copy-keymap,
      ;; such that it would not be correctly displayed in menus
      ;; and help
      (setq new (make-sparse-keymap))
      (set-keymap-parents new (if parent (list map parent) (list map))))
    (if (stringp prefix)
	(define-key new (concat prefix prefix) oldbinding)
      (define-key new (vector prefix prefix) oldbinding))
    new))
      
(defun zeta-trim (str)
  (let ((start 0) (end (- (length str) 1)))
    (while (and (<= start end)
		(string-match "[ \n\t]" (char-to-string (elt str start))))
      (setq start (+ start 1)))
    (while (and (>= end 0)
		(string-match "[ \n\t]" (char-to-string (elt str end))))
      (setq end (- end 1)))
    (substring str start (+ end 1))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Dealing with the ZEXPRn and ZPREDn buffers

(defun zeta-update-scratch-buffers (fn)
  ;; crude hack to revert old buffers ZEXPRn and ZPREDn
  (if (string-match ".*\\(ZEXPR\\|ZPRED\\)[0-9]*" fn)
      (let ((bufs (buffer-list)))
	(while bufs
	  (if (string-match ".*\\(ZEXPR\\|ZPRED\\)[0-9]*" 
			    (buffer-name (car bufs)))
	      (save-excursion
		(set-buffer (car bufs))
		(if (not (verify-visited-file-modtime (car bufs)))
		    (revert-buffer t t t))
		(if (not zeta-source-mode)
		    (zeta-source-mode t))
		))
	  (setq bufs (cdr bufs))))))



;; provide it
(provide 'zeta-base)
