;;; vtex-mode 
;;; CUSTOMIZATION PARAMETERS
;;; (markup templates found in vtex-tmpldef.el)
;;; version $Id: vtex-custom.el,v 1.1 1998/09/18 10:12:48 wg Exp $

(provide 'vtex-custom)
(require 'vtex-base)
(require 'vtex-faces)
(require 'vtex-tmpl)

(load "edit-faces" nil t)

;;; Command Keys

(defvar vtex-command-prefix "\C-q"
  "*Prefix used for VTEX commands.")

;;; Hooks

(defvar vtex-mode-on-hooks nil
  "*Hooks to be called when `vtex-mode' is enabled.")

(defvar vtex-mode-off-hooks nil
  "*Hooks to be called when `vtex-mode' is disabled.")


;;; Parsing

(defvar vtex-auto-parse 'narrow
  "*How to auto-parse buffer after changes. A value of nil means
not to auto-parse, 'narrow to do a fast narrowing of the region effected,
and 'full to completely reparse the entire buffer.")

(defvar vtex-auto-parse-delay 0.33
  "*Delay after which auto-parsing is started.")

(defvar vtex-auto-delete-markup t
  "*Whether deleting a markup component (visible or invisible)
induces to delete the complete markup.")

(defvar vtex-inhibit-auto-delete-markup-commands 
  '(LaTeX-fill-paragraph)
  "*List of commands for which auto-deletion of markup shouldn't be
performed.")

(defvar vtex-parse-warnings t
  "*Generate parsing warnings.")

(defvar vtex-handle-math-layout t
  "*Whether math layout should be handled especially by VTeX.")


;;; Basic TeX Tokens 

(defvar vtex-tok-cmd "\\" 
  "The TeX escape character.")

(defvar vtex-tok-bgroup "{" 
  "The TeX group opening character.")

(defvar vtex-tok-egroup "}" 
  "The TeX group closing character.")

(defvar vtex-tok-boption "[" 
  "The LaTeX option opening character.")

(defvar vtex-tok-eoption "]" 
  "The LaTeX option closing character.")

(defvar vtex-tok-comment "%"
  "The LaTeX comment token.")

(defvar vtex-tok-math "$"
  "The LaTeX math token.")

(defvar vtex-tok-begin (concat vtex-tok-cmd "begin")
  "The LaTeX begin-environment token.")

(defvar vtex-tok-end (concat vtex-tok-cmd "end")
  "The LaTeX end-environment token.")


;;; Keymap table

(defvar vtex-mode-map nil
  "Keymap used for vtex-mode.")

(defun vtex-get-mode-map ()
  vtex-mode-map)

(if vtex-mode-map
    ()

  ;; setup the key maps and the prefixes
  (setq vtex-mode-map (make-sparse-keymap))
  (setq vtex-command-map (make-keymap))
  (define-key vtex-mode-map vtex-command-prefix vtex-command-map)

  ;; define the commands

  (define-key vtex-command-map "\C-d" 'vtex-decorate-context)
  (define-key vtex-command-map "d" 'vtex-decorate)
  (define-key vtex-command-map "\C-u" 'vtex-undecorate)
  (define-key vtex-command-map "\C-i" 'vtex-insert)

  )

;;; Menus

(defun vtex-add-menu (&optional popup-map)
  "Add VTeX menu to global menu bar and bound according popup
menus in POPUP-MAP, if given."
  (let (main)
    (setq main (list "VTeX"
		     ["(Re)decorate buffer" vtex-decorate t]
		     ["(Re)decorate context" vtex-decorate-context t]
		     ["Undecorate" vtex-undecorate t]
		     ["Insert Markup" vtex-insert t]
		     (list "Options" 
			   ["Edit Faces ..." vtex-edit-faces t]
			   ["Reload .vtexrc" vtex-reload-rc t])
		     ;; ["Symbols ..." vtex-create-symb-buffer t]
		     ))
    (if (not (local-variable-p 'current-menubar (current-buffer) t))
	(progn
	  (make-local-variable 'current-menubar)
	  (setq current-menubar (purecopy current-menubar))))
    (add-submenu nil main)
    (set-menubar-dirty-flag)
    ))


(defun vtex-remove-menu()
  (delete-menu-item '("VTeX"))
  (set-menubar-dirty-flag))


;(defun vtex-make-tmpl-menu (filter)
;  (let ((make (lambda (name tmpl rest)
;		(if (funcall filter name tmpl)
;		    (cons (vector key 
;				  (list 'vtex-insert-skeleton tmpl))
;			  rest)
;		  rest))))
;    (vtex-reduce-hashtable make vtex-tmpls
;			   (vtex-reduce-hashtable make vtex-math-tmpls))))

;(defun vtex-latex-env-tmpl-p (name tmpl)
;  ........

  

;;; Syntax table

(defun vtex-extend-syntax-table (stab)
  "Extend the given syntax table for LaTeX syntax. This is crucial
to let the parser work correctly. The standard syntax table setup
e.g. for AUCTeX doesn't handles punctation correctly."
  ;; punctation
  (modify-syntax-entry ?&  "."  stab)
  (modify-syntax-entry ?_  "."  stab)
  (modify-syntax-entry ?^  "."  stab)
  (modify-syntax-entry ?/  "."  stab)
  (modify-syntax-entry ?=  "."  stab)
  (modify-syntax-entry ?*  "."  stab)
  (modify-syntax-entry ?+  "."  stab)
  (modify-syntax-entry ?#  "."  stab)
  (modify-syntax-entry ?-  "."  stab)
  (modify-syntax-entry ?:  "."  stab)
  (modify-syntax-entry ?.  "."  stab)
  (modify-syntax-entry ?\; "."  stab)
  (modify-syntax-entry ?,  "."  stab)
  (modify-syntax-entry ?<  "."  stab)
  (modify-syntax-entry ?>  "."  stab)
  (modify-syntax-entry ?|  "."  stab)
  (modify-syntax-entry ?`  "."  stab)
  (modify-syntax-entry ?@  "."  stab)
  (modify-syntax-entry ?$  "."  stab)
  (modify-syntax-entry ?0  "."  stab)
  (modify-syntax-entry ?1  "."  stab)
  (modify-syntax-entry ?2  "."  stab)
  (modify-syntax-entry ?3  "."  stab)
  (modify-syntax-entry ?4  "."  stab)
  (modify-syntax-entry ?5  "."  stab)
  (modify-syntax-entry ?6  "."  stab)
  (modify-syntax-entry ?7  "."  stab)
  (modify-syntax-entry ?8  "."  stab)
  (modify-syntax-entry ?9  "."  stab)
  
  ;; symbol constituents
  (modify-syntax-entry ?'  "_"  stab)
  (modify-syntax-entry ?!  "_"  stab)
  (modify-syntax-entry ?\?  "_"  stab)
  (modify-syntax-entry ?\" "_"  stab)

  ;; character escapes
  (modify-syntax-entry ?\\ "/"  stab)
  (make-local-variable 'words-include-escapes)
  (setq words-include-escapes t)

  ;; whitespace
  (modify-syntax-entry ?~  " "  stab)

  stab)


;;; Resources

(defvar vtex-rc-name "~/.vtexrc"
  "*Name of the VTeX configuration file.")

(defvar vtex-rc-template-name "vtexrc.dot"
  "*Name of the VTeX configuration template file.")

(defvar vtex-rc-loaded nil)

(defun vtex-load-rc ()
  "Load VTeX configuration file."
  (if (not vtex-rc-loaded)
      (progn
	(let ((rcname (expand-file-name vtex-rc-name)))
	  (if (not (file-exists-p rcname))
	      (let (vtexdir)
		(message "Creating initial VTeX configuration file `%s'"  
			 vtex-rc-name)
		(setq vtexdir (locate-library "vtex-mode"))
		(if (not vtexdir)
		    (error "Cannot locate installation base of VTeX!"))
		(copy-file (concat (file-name-directory vtexdir)
				   vtex-rc-template-name)
			   rcname)))
	  (load rcname)
	  (setq vtex-rc-loaded t)
	  ))))

(defun vtex-reload-rc ()
  "Reload VTeX configuration file, and re-decorate all VTeX buffers."
  (interactive)
  (setq vtex-rc-loaded nil)
  (vtex-load-rc)
  (vtex-decorate-all-buffers))

(defun vtex-decorate-all-buffers ()
  "Decorate all VTeX buffers."
  (let ((bufs (buffer-list)) buf)
    (while bufs
      (setq buf (car bufs))
      (if (symbol-value-in-buffer 'vtex-mode buf)
	  (save-excursion
	    (set-buffer buf)
	    (vtex-decorate)))
      (setq bufs (cdr bufs)))))
      
  


;;; User Level Functions

(defun vtex-decorate ()
  "(Re-)decorate the current buffer."
  (interactive)
  (save-excursion
    (message "Parsing buffer ...")
    (vtex-undecorate-buffer)
    ;; (set-extent-property vtex-buffer-extent 'face 'vtex-text)
    (vtex-parse-region (point-min) (point-max))
    (message "Parsing buffer done.")))

(defun vtex-decorate-context ()
  "Undecorate a narrowed context."
  (interactive)
  (let (start end)
    (save-excursion
      (while (and (> (point) (point-min))
		  (pos-visible-in-window-p))
	(forward-line -1))
      (while (and (> (point) (point-min))
		  (extent-at (point) nil 'vtex-inst))
	(forward-line -1))
      (setq start (point)))
    (save-excursion
      (while (and (< (point) (point-max))
		  (pos-visible-in-window-p))
	(forward-line 1))
      (while (and (< (point) (point-max))
		  (extent-at (point) nil 'vtex-inst))
	(forward-line 1))
      (setq end (point)))
    (save-excursion
      (message "Parsing visible context ...")
      (vtex-undecorate-region start end)
      (vtex-parse-region start end)
      (message "Parsing visible context done.")
      )))

(defun vtex-undecorate ()
  "Undecorate the current buffer."
  (interactive)
  (save-excursion
    ;; (set-extent-property vtex-buffer-extent 'face 'default)
    (vtex-undecorate-buffer)))


(defun vtex-insert ()
  "Insert a markup structure at point."
  (interactive)
  (let* ((inst (vtex-inst-at (point)))
	 (ctx (and inst (vtex-inst-tmpl inst)))
	 (table (if (and ctx
			 (vtex-tmpl-envp ctx)
			 (vtex-tmpl-math-env ctx))
		    vtex-math-tmpls
		  vtex-tmpls))
	 (name 
	  (completing-read "Markup name: "
			   (vtex-reduce-hashtable
			    (lambda (key entry alist)
			      (cons (cons key entry) alist))
			    table))))
    (let ((tmpl (vtex-search-tmpl table name)))
      (if tmpl 
	  (vtex-insert-skeleton tmpl)
	(error "No such template")))))

(defun vtex-edit-faces ()
  "Alter VTeX face characteristics."
  (interactive)
  (pop-to-buffer (get-buffer-create "*VTeX Faces*"))
  (message 
"NOTE: changes cannot be made permanent. Edit .vtexrc for permanent changes.")
  ;; stolen from edit-faces
  (let ((flist (vtex-reduce (lambda (face rest)
			      (if (and (face-property face 'vtex-face)
				       (not (string-match 
					     "vtex-gen"
					     (symbol-name (face-name face)))))
				  (cons face rest)
				rest))
			    (face-list)))
	face)
    (setq flist (sort flist
		      (function
		       (lambda (x y)
			 (string-lessp (symbol-name x) (symbol-name y))))))

    (ef-update-face-description t)      ; insert header line
    (while (setq face (car flist))
      (ef-update-face-description face) 
      (setq flist (cdr flist))
      ))
  (edit-faces-mode)
  )

(defun vtex-patched-ef-font (face)
  "A patch of the original ef-font to make completion on available
font names, installed by VTeX."
  ;; taken from edit-faces.el:
  (interactive (list (ef-face-arg)))
  (let* ((ofont (face-font-instance face))
	 (pattern (read-string "Font pattern (* for any): "))
	 (cands (mapcar (lambda (fname) (cons fname fname))
			(list-fonts pattern)))
	 (font (completing-read (format "Font for `%s': " (symbol-name face))
				cands
				nil nil
				(font-instance-name 
				 (face-font-instance face))))
         others)
    ;; you might think that this could be moved into the loop below, but I
    ;; think that it's important to see the new font before asking if the
    ;; change should be global.
    (set-face-font face (if (and (string= font "")
                                 (not (eq face 'default)))
                            nil font))
    (ef-update-face-description face)
    (setq others (delq nil (mapcar (lambda (f)
                                     (and (equal (face-font-instance f) ofont)
                                          f))
                               (face-list))))
    (if (and others
             (y-or-n-p "Make the same font change for other faces? "))
        (while others
          (setq face (car others)
                others (cdr others))
          (set-face-font face font)
          (ef-update-face-description face)))
    ))

(fset 'ef-font (symbol-function 'vtex-patched-ef-font))

