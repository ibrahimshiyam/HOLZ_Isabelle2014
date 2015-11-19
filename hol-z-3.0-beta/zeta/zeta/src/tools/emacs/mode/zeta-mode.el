;;; zeta-mode.el --- run zeta under XEmacs/Emacs

;; $Id: zeta-mode.el,v 1.30 2000/07/21 06:45:15 wg Exp $
;; by Wolfgang Grieskamp, wg@cs.tu-berlin.de


(require 'comint)
(require 'zeta-base)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Customization variables

(defvar zeta-dir "/usr/local/zeta/"
  "*The base directory of the ZETA installation.")

(setq zeta-dir (file-name-as-directory zeta-dir))

(defvar zeta-command-name 
  (concat zeta-dir
	  (if zeta-running-windows "bin/zeta.bat" "bin/zeta"))
  "*Pathname for executing ZETA.")

(defvar zeta-command-switches '("-b")
  "*Switches to be passed to ZETA.")

(defvar zeta-startup-file nil
  "*Startup file to be feeded to ZETA.")

(defvar zeta-startup-commands "" 
  "*Startup commands to be feeded to ZETA.")

(defvar zeta-prompt-pattern "^[?] "
  "A regexp to recognize the prompt of the ZETA controller.") 

(defvar zeta-prompt-length 2
  "The length of the prompt.")

(defvar zeta-locator-patterns 
  '(("\\(LTX\\|STM\\):\\([-@_+*a-zA-Z0-9./\\]+\\)(\\([0-9]+\\).\\([0-9]+\\)-\\([0-9]+\\).\\([0-9]+\\))"
     2 3 4 5 6))
  "A list of lists describing source locators in messages. The 1st
element of each list is a regular expression matching the locator,
the 2nd a position in this regexp for the file name (or null for
inline messages), the 3rd up to 6th positions in the regexp
for line/column pairs.")

(defvar zeta-diag-line-prefix "^! "
  "Pattern indicating the begin of a diagnostic output line")

(defvar zeta-progress-line-prefix "^+ "
  "Pattern indicating the begin of a progress output line")

(defvar zeta-result-line-prefix "^= "
  "Pattern indicating the begin of a result output line")

(defvar zeta-state-line-prefix "^- "
  "Pattern indicating the begin of a result output line")

(defvar zeta-eval-line-prefix "^[~] "
  "Pattern indicating the begin of a result output line")

(defvar zeta-debug-line-prefix "^@ \\([^ ]*\\): "
  "Pattern indicating the begin of a debug output line. The
  regexp at position 1 matches the tool name.")

(defvar zeta-enrich-locator-pattern 
  "^[ ]*\\(x\\|mcheck\\)[^\"]*\\(\"\\).*$"
  "Pattern describing those commands which get inserted a locator for the
control at second match.")

(defvar zeta-find-focus-pattern
  "\\(\\\\zsection\\|\\\\begin{class}\\)\\(\\[[^]]*\\]\\)?{\\([^}]*\\)}")

(defvar zeta-find-focus-pattern-pos 3)


(defvar zeta-locator-color-or-face "LightYellow"
  "*A string representing a color used for locator backgrounds,
or a face symbol (such as 'bold).")

(defvar zeta-locator-selected-color-or-face "Red"
  "*A string representing a color used for selected locator foregrounds,
or a face symbol (such as 'secondary-selection).")

(defvar zeta-folded-header-face 'zeta-folded-header-face
  "*Face used for folded message headers.")
(zeta-make-face zeta-folded-header-face)
(set-face-foreground zeta-folded-header-face "Gray60")

(defvar zeta-unfolded-header-face 'zeta-unfolded-header-face
  "*Face used for unfolded message headers.")
(zeta-make-face zeta-unfolded-header-face)
(set-face-foreground zeta-unfolded-header-face "DarkRed")

(defvar zeta-command-prefix "\C-q"
  "*A prefix used for reaching ZETA keystroke commands.")

(defvar zeta-result-to-commander nil
  "Whether eval output, if no redirection is active, shall be
inserted in the commander buffer instead of the message buffer.")

(defvar zeta-pop-commander-on-start t
  "*Whether the commander buffer shall be popped up on start of ZETA.")

(defvar zeta-smooth-scroll-delay .015
  "*If non-nil, scrolling will be done line-by-line,
with a delay defined by this value, when adjusting the message window
to make the next locator visible.")
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Glyphs

(defun zeta-glyph (name)
  (make-glyph (vector 'gif :file 
		      (concat zeta-dir "lib/images/" name ".gif"))))

(defvar zeta-progress-glyph (zeta-glyph "progress"))
(defvar zeta-result-glyph (zeta-glyph "result"))
(defvar zeta-diag-glyph (zeta-glyph "warning"))
(defvar zeta-finished-glyph (zeta-glyph "finished"))
(defvar zeta-transaction-expanded-glyph (zeta-glyph "transaction-expanded"))
(defvar zeta-transaction-collapsed-glyph (zeta-glyph "transaction-collapsed"))

(defvar zeta-empty-face
  (let ((face (make-empty-face 'zeta-empty-face))
	(tab (make-display-table)))
    (fillarray tab "")
 ;   (set-face-property face 'display-table tab)
    face))
	 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Key maps

(defvar zeta-keymap nil
  "Keymap used with prefix in diverse ZETA mode related buffers.")

(if (and zeta-keymap (not zeta-debug-on))
    nil
  (setq zeta-keymap (make-sparse-keymap))
  (zeta-set-keymap-name zeta-keymap 'zeta-keymap)
  (define-prefix-command 'zeta-command-prefix-map)

  ;; general
  (define-key zeta-command-prefix-map "s" 'zeta)
  (define-key zeta-command-prefix-map "u" 'zeta-select-focus)
  (define-key zeta-command-prefix-map "l" 'zeta-select-master)
  ;; type-checking and other ops
  (define-key zeta-command-prefix-map "c" 'zeta-type-check)
  (define-key zeta-command-prefix-map "m" 'zeta-make)
  (define-key zeta-command-prefix-map "h" 'zeta-model-check)
  (define-key zeta-command-prefix-map "o" 'zeta-format)
  (define-key zeta-command-prefix-map "v" 'zeta-view)
  ;; interrupt
  (define-key zeta-command-prefix-map "\C-c" 'zeta-interrupt)
  ;; messages
  (define-key zeta-command-prefix-map "\C-p" 'zeta-prev-locator)
  (define-key zeta-command-prefix-map "\C-n" 'zeta-next-locator)
  (define-key zeta-command-prefix-map "f" 'zeta-fold-this-message)
  (define-key zeta-command-prefix-map "\C-f" 'zeta-fold-all-messages)

  ;; evaluating 
  (define-key zeta-command-prefix-map "=" 'zeta-eval-expr)
  (define-key zeta-command-prefix-map "?" 'zeta-eval-predicate)

  (define-key zeta-keymap zeta-command-prefix zeta-command-prefix-map)

  ;; alternates
  (define-key zeta-keymap [(shift up)] 'zeta-prev-locator)
  (define-key zeta-keymap [(shift down)] 'zeta-next-locator)
  
  ;; mouse commands
  (zeta-define-button-key zeta-keymap '(meta) 2 'zeta-eval-expr-region)
  (zeta-define-button-key zeta-keymap '(meta control) 2 
			  'zeta-eval-predicate-region)
  
  )
  
  
  
(defvar zeta-command-mode-map nil
  "Keymap for zeta-command-mode.")

(if (and zeta-command-mode-map (not zeta-debug-on))
    nil
  (setq zeta-command-mode-map 
	(zeta-prefix-map zeta-command-prefix zeta-keymap
			comint-mode-map
			(lookup-key comint-mode-map zeta-command-prefix)))
  (define-key zeta-command-mode-map "\t" 'comint-dynamic-complete)
  (define-key zeta-command-mode-map "\M-?" 'comint-dynamic-list-completions)
  (define-key zeta-command-mode-map "\C-m" 'zeta-send-input)
  (define-key zeta-command-mode-map [(alt up)] 'comint-previous-input)
  (define-key zeta-command-mode-map [(alt down)] 'comint-next-input)
  (zeta-set-keymap-name zeta-command-mode-map 'zeta-command-mode-map)
  )


(defvar zeta-source-mode-map zeta-keymap
  "Keymap for zeta-source-mode")
(make-variable-buffer-local 'zeta-source-mode-map)
  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Menus

(defun zeta-add-menu(&optional map-popup)
  "Add the ZETA menu to the current buffer."
  (if (not zeta-running-xemacs)
      (message 
"NOTE: ZETA mode currently supports menus only when running under XEmacs.")
    (zeta-remove-menu)
    (let ((menu
	   (list "ZETA"
		 ["Load Source" zeta-select-master t]
		 ["Set Default Unit" zeta-select-focus t]
  		 ["Type Check" zeta-type-check t]
		 "---"
		 ["Evaluate Expression" zeta-eval-expr t]
		 ["Evaluate Predicate" zeta-eval-predicate t]
		 ["Region as Expression" zeta-eval-expr-region 
		  (region-exists-p)]
		 ["Region as Predicate" zeta-eval-predicate-region 
		  (region-exists-p)]
		;; "---"
		;; ["Model Check Predicate" zeta-model-check t]
		;; ["Model Check Region as Predicate" zeta-model-check-region 
		;;  (region-exists-p)]
		 "---"
		 ["Run LaTeX" zeta-format t]
		 ["Launch Viewer" zeta-view t]
		 "---"
		 ["Interrupt Computation" zeta-interrupt t]
		 "---"
		 ["Previous Locator" zeta-prev-locator t]
		 ["Next Locator" zeta-next-locator t]
		 ["Fold Here" zeta-fold-this-message t]
		 ["Fold All" zeta-fold-all-messages t]
		 "---"
		 ["(Re)start Session" zeta t] ;; CHECKME
		 )))
      (if (or t ;; FIXME
	      (not (local-variable-p 'current-menubar (current-buffer) t)))
	  (progn
	    (make-local-variable 'current-menubar)
	    (setq current-menubar (purecopy current-menubar))))
      (add-submenu nil menu)
      (add-submenu 
       '("ZETA")
       (list "Options"
	     ["Pop Commander on Start" zeta-toggle-pop-commander-on-start
	      :style toggle :selected zeta-pop-commander-on-start]
	     ))
      (set-menubar-dirty-flag)
      (if (or (not mode-popup-menu) (not map-popup))
	  (setq mode-popup-menu menu)
	(zeta-define-button-key map-popup '(shift) 3 
				`(lambda ()
				   (interactive)
				   (popup-menu (quote ,menu)))))
      (zeta-dprint "turned on ZETA menu")))
  )

(defun zeta-remove-menu()
  (if zeta-running-xemacs
      (progn
	(delete-menu-item '("ZETA"))
	(set-menubar-dirty-flag)
	(zeta-dprint "turned off ZETA menu"))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Global mode variables

(defvar zeta-buf nil)
(defvar zeta-dont-query-kill nil)
(defvar zeta-nextline nil)
(defvar zeta-lastlast-trans nil)
(defvar zeta-last-trans nil)
(defvar zeta-last-context nil)
(defvar zeta-message-context-kind nil)
(defvar zeta-message-context-start nil)
(defvar zeta-message-start nil)
(defvar zeta-last-verbose nil)
(defvar zeta-initial-master nil)
(defvar zeta-seen-prompt nil)
(defvar zeta-focus nil)
(defvar zeta-selected-locator nil)
(defvar zeta-record-output nil)
(defvar zeta-recorded-result nil)
(defvar zeta-input-overlay nil)
(defvar zeta-send-input-tried nil)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Buffer local variables

;; CHECKME: this should be calculated dynamically, but would
;; create lots of temporary faces (emacs isn't fast here)
(defvar zeta-locator-face nil)
;; A face calculated for locators in this buffer.
(make-variable-buffer-local 'zeta-locator-face)

;; CHECKME: this should be calculated dynamically, but would
;; create lots of temporary faces (emacs isn't fast here)
(defvar zeta-locator-selected-face nil)
;; A face calculated for selected locators in this buffer.")
(make-variable-buffer-local 'zeta-locator-selected-face)

(defvar zeta-old-msl-glyph-fun nil)
(make-variable-buffer-local 'zeta-old-msl-glyph-fun)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Initialization and finitialization

(if (boundp 'viper-non-vi-major-modes)
    (setq viper-non-vi-major-modes
	  (cons 'zeta-command-mode viper-non-vi-major-modes)))

(defun zeta ()
  "Start ZETA session."
  (interactive)
  (let ((path
	 (read-file-name "Run ZETA on: " nil nil t
			 (and zeta-source-mode (buffer-name)))))
    ;; check for restart
    (if (and zeta-buf
	     (zeta-running-p)
	     (not (yes-or-no-p
		   "ZETA session is already running. Abort it? ")))
	(error "Don't starting new ZETA session."))
    (zeta-abort)
    ;; analyse argument
    (setq path (expand-file-name (directory-file-name path)))
    (zeta-dprint "path %s" path)
    (if (file-directory-p path)
	(setq path (file-name-as-directory path)
	      zeta-initial-master nil)
      (if (file-regular-p path)
	  (setq zeta-initial-master (file-name-nondirectory path)
		path (file-name-directory path))
	(error "File not found: %s" path)))
    ;; clear some global variables
    (setq zeta-nextline nil
	  zeta-last-trans nil
	  zeta-lastlast-trans nil
	  zeta-last-context nil
	  zeta-message-context-kind nil
	  zeta-message-start nil
	  zeta-last-verbose nil
	  zeta-focus nil
	  zeta-seen-prompt nil
	  zeta-record-output nil
	  zeta-recorded-result nil
	  zeta-selected-locator nil
	  zeta-input-overlay nil
	  zeta-send-input-tried nil
	  )
    ;; make the buffers
    (setq zeta-buf (get-buffer-create "*ZETA*"))
    ;; initialize modes for buffers
    (save-current-buffer
      (set-buffer zeta-buf)
      (setq default-directory path)
      (zeta-command-mode))
    )
  )


(defun zeta-command-mode()
  "Major mode for controlling a ZETA session directly. 
Most commands are inherited from comint mode.

\\{zeta-command-mode-map}
"
  ;; (interactive)
  (make-local-variable 'use-dialog-box)
  (setq use-dialog-box nil)
  (if (not (eq zeta-buf (current-buffer)))
      (error (substitute-command-keys 
	      "Invalid state (use \\[zeta] to invoke a ZETA session).")))
  (if (not (eq major-mode 'zeta-command-mode))
      (progn
	(comint-mode)
	(zeta-install-command-hook)
	(setq major-mode 'zeta-command-mode
	      mode-name "ZETA"
	      comint-prompt-regexp zeta-prompt-pattern
	      )))
  (if (fboundp 'viper-change-state-to-emacs)
      (viper-change-state-to-emacs))
;  (set-specifier left-margin-width 3 zeta-buf)
  (setq truncate-lines t)
  (use-local-map zeta-command-mode-map)
  (setq comint-input-sender 'zeta-send-ignore-filter)
  (setq comint-append-old-input nil)
  ;; (make-local-hook 'kill-buffer-hook)
  ;; (add-hook 'kill-buffer-hook 'zeta-kill-command nil t)
  (goto-char (point-max))
  (or (bolp) (newline))
  (insert "Current directory is " default-directory "\n")
  (if zeta-pop-commander-on-start
      (pop-to-buffer zeta-buf))
  (let ((started-at (point)))
    (comint-exec (current-buffer)
		 "ZETA"
		 (substitute-in-file-name zeta-command-name)
		 zeta-startup-file
		 (if zeta-initial-master
		     (append zeta-command-switches (list zeta-initial-master))
		   zeta-command-switches))
    (set-process-filter (get-buffer-process (current-buffer)) 
			'zeta-filter)
    (process-kill-without-query (get-buffer-process (current-buffer)))
    ;; (zeta-check-startup started-at)
    (setq comint-input-sender 'zeta-send-filter)
    )
  ;; setup options
  (zeta-toggle-pop-commander-on-start t)
  ;; (if zeta-initial-master 
  ;;     (zeta-set-master zeta-initial-master))
  (set-process-sentinel (get-buffer-process (current-buffer)) 
			'zeta-sentinel)
  (zeta-add-menu zeta-command-mode-map)
  (run-hooks 'zeta-command-mode-hook)
  (goto-char (point-max))
  )

(defun zeta-check-startup (started-at)
  ;; Ensure that the zeta process has came up and the prompt is recognised.
  ;; The problem is that our output filter may come in effect
  ;; _after_ output has been produced. (FIXME: use output-filter-functions
  ;; instead of setting an own filter).
  (if (not zeta-buf)
      (return))
  (let ((tries 60)
	(sleep 1)
	found)
    (save-excursion
      (while (and (not found) (> tries 0))
	(set-buffer zeta-buf)
	(goto-char started-at)
	(if (re-search-forward zeta-prompt-pattern nil t)
	    ;; found the prompt; now set focus from it
	    (progn
	      ;; (zeta-set-focus (match-string 1))
	      (setq found t))
	  (sleep-for sleep)
	  ;; (accept-process-output (get-buffer-process zeta-buf) 1)
	  (setq tries (- tries 1))))
      (if (not found)
	  (progn
	    (pop-to-buffer zeta-buf)
	    (error "ZETA session seems not to startup properly?"))))))
 


(defvar zeta-source-mode nil
  "Is ZETA source minor mode on or off?")
(make-variable-buffer-local 'zeta-source-mode)


(defun zeta-source-mode(&optional arg)
  "Minor mode for buffers holding Z sources. This mode
connects to a running ZETA session. 

Use \\[zeta-type-check] to type check.

Use \\[zeta-eval-expr-region] to evaluate the current region
and print the result in the ZETA message buffer. Use \\[universal-argument]
as a prefix to \\[zeta-eval-expr-region] to force enumeration of
evaluated sets.  

Key bindings:

\\{zeta-source-mode-map}
"
  (interactive "P")
  (make-local-variable 'use-dialog-box)
  (setq use-dialog-box nil)
  (if (eq arg t) (setq arg 1))
  (if (and arg
	   (or (and (>= arg 0) zeta-source-mode)
	       (and (< arg  0) (not zeta-source-mode))))
      ;; nothing changes
      ()
    ;; toggle
    (if zeta-source-mode
	;; turn it off
	(progn
	  (run-hooks 'zeta-source-mode-off-hooks)
	  (zeta-remove-menu)
	  (setq vtex-msl-glyph-fun zeta-old-msl-glyph-fun)
	  (setq zeta-source-mode nil))
      ;; turn it on
      ;; dynamically create a keymap, which escapes the current value of
      ;; of zeta-command-prefix
      (setq zeta-source-mode-map
	    (zeta-prefix-map zeta-command-prefix 
			    (default-value 'zeta-source-mode-map)))
      (make-local-variable 'minor-mode-map-alist)
      (let ((old (assq 'zeta-source-mode minor-mode-map-alist)))
	(if old
	    (progn
	      (setq minor-mode-map-alist (copy-alist minor-mode-map-alist))
	      (setcdr (assq 'zeta-source-mode minor-mode-map-alist)
		      zeta-source-mode-map))
	  (setq minor-mode-map-alist
		(cons (cons 'zeta-source-mode zeta-source-mode-map)
		      minor-mode-map-alist))))
      (setq zeta-source-mode t)
      (zeta-add-menu zeta-source-mode-map)
      (make-local-variable 'vtex-msl-glyph-fun)
      (setq zeta-old-msl-glyph-fun 
	    (and (boundp 'vtex-msl-glyph-fun) vtex-msl-glyph-fun))
      (setq vtex-msl-glyph-fun 'zeta-msl-glyph)
      (run-hooks 'zeta-source-mode-on-hooks))
    ;; force update of modeline 
    (force-mode-line-update)))

(if zeta-running-xemacs
    (add-minor-mode 'zeta-source-mode " ZETA" zeta-source-mode-map)
  (if (not (assq 'zeta-source-mode minor-mode-alist))
      (progn
	(setq minor-mode-alist (cons '(zeta-source-mode " ZETA")
				     minor-mode-alist))))
  (if (not (assq 'zeta-source-mode minor-mode-map-alist))
      (setq minor-mode-map-alist (cons '(zeta-source-mode zeta-source-mode-map)
				       minor-mode-map-alist))))



(defun zeta-abort()
  "Abort the running ZETA session."
  (interactive)
  (if (zeta-running-p)
      (progn
	(zeta-call "quit")
	(let ((tries 120))
	  (while (and (get-buffer-process zeta-buf)
		      (eq (process-status (get-buffer-process zeta-buf)) 'run)
		      (> tries 0))
	    (sleep-for 1)
	    ;; (accept-process-output (get-buffer-process zeta-buf) 0.1)
	    (setq tries (- tries 1))
	    )
	  ))))

(defun zeta-running-p ()
  (get-buffer-process zeta-buf))
  
(defun zeta-query-kill (&optional buf)
  (if (not buf) (setq buf zeta-buf))
  (or zeta-dont-query-kill 
      (yes-or-no-p (format "Kill the %s ZETA session? "
			   (if (get-buffer-process buf)
			       "running" "zombie")))))
  
(defun zeta-set-focus (string)
  (if (or (not zeta-focus) (not (string= zeta-focus string)))
      (progn
	(setq zeta-focus (if (= (length string) 0) nil string))
	(set-menubar-dirty-flag)
	(let ((cname "ZETA"))
	  (if zeta-focus
	      (progn
		(zeta-intern-call (concat "default -u " zeta-focus))
		(setq cname (concat cname "[" zeta-focus "]")))
	    (setq cname (concat cname "[no focus]")))
	  (save-current-buffer
	    (set-buffer zeta-buf)
	    (setq mode-name cname)
	    (set-buffer-modified-p (buffer-modified-p))))
	)))
	  

;(defun zeta-set-buffer ()
;  (cond ((eq major-mode 'zeta-command-mode)
;	 ;; (setq zeta-buf (current-buffer))
;	 ;; (if (featurep 'eos-toolbar)
;	 ;;     (set-specifier default-toolbar (cons (current-buffer)
;	 ;; 				  zeta-toolbar))))))
;	 )))


(defun zeta-sentinel (proc msg)
  (cond ((null (buffer-name (process-buffer proc)))
	 ;; buffer killed
	 (set-process-buffer proc nil))
	((and (equal 'exit (process-status proc))
	      (equal 0 (process-exit-status proc)))
	 ;; normal user exit
	 ;; (zeta-put-result "terminated ZETA session")
	 )
	(t
	 ;; Some unusual situation: rename command buffer
	 ;; and show it
	 (if zeta-buf
	     (save-excursion
	       (progn
		 (set-buffer zeta-buf)
		 (insert "\n\nUnexpected termination of ZETA.")
		 (rename-buffer (concat "*ZETA:"
					(symbol-name (process-status proc))
					"*")
				t)
		 (insert "\nRenamed this buffer to " (buffer-name)
			 " for post-mortem analysis."))))
	 (setq zeta-buf nil)
	 (pop-to-buffer (process-buffer proc)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Control process input filtering

(defun zeta-send-ignore-filter (proc input)
  (message "... please wait until ZETA is up"))

(defun zeta-send-filter (proc input)
  (zeta-dprint "send input: '%s'" input)
  (condition-case nil
      (progn
	(zeta-save-related-buffers)
	(zeta-fold-last-messages)
	(zeta-reset-output-filter)
	(if zeta-buf
	    (save-current-buffer
	      (set-buffer zeta-buf)
	      (if (and (> (length input) 0)
		       zeta-input-overlay
		       (string-match zeta-enrich-locator-pattern input))
		  (progn
		    (zeta-dprint "current input: %S" zeta-input-overlay)
		    ;; enrich locators for the source of this input
		    (let* ((i (+ (match-beginning 2) 1))
			   (front (substring input 0 i))
			   (tail (substring input i)))
		      (if (not (string-match "^\$.*$" tail))
			  (let ((loc 
				 (format "$%s(%d.%d)$"
					 (buffer-name zeta-buf)
					 (count-lines (point-min) 
						      (+ 1 (zeta-overlay-start
							    zeta-input-overlay)))
					 (+ (length front) 3))))
			    (zeta-dprint "replaced-input: '%s'" input)
			    (setq input (concat front loc tail)))
			))))))
	(comint-simple-send proc input))
    (quit (beep) (comint-simple-send proc ""))))


(defun zeta-send-input ()
  (interactive)
  (let ((ovl (or (zeta-overlay-at (point) 'zeta-input)
		 (and (> (point) (point-min))
		      (zeta-overlay-at (- (point) 1) 'zeta-input)))))
    (if (not ovl)
	(progn
	  (message "Not over an input line.")
	  (beep))
      (if (not zeta-input-overlay)
	  (zeta-send-input1)
	(let ((start (+ (zeta-overlay-start zeta-input-overlay)
			zeta-prompt-length))
	      (end (zeta-overlay-end zeta-input-overlay)))
	  (if (not (eq ovl zeta-input-overlay))
	      ;; copy from older input line
	      (progn
		(let ((cont (buffer-substring (+ (zeta-overlay-start ovl)
						 zeta-prompt-length)
					      (zeta-overlay-end ovl))))
		  (delete-region start end)
		  (goto-char start)
		  (insert cont)
		  (message "Type RETURN to commit.")
		  ))
	    ;; check for completeness 
	    (let ((complete 
		   (or zeta-send-input-tried
		       (save-excursion
			 (end-of-line)
			 (not (comint-within-quotes start (point)))))))
	      (if complete
		  (zeta-send-input1)
		(setq zeta-send-input-tried t)
		(message 
	  "Type again RETURN to commit, LFD (C-j) to insert a newline.")
		)
	      )))))))
	    
(defun zeta-clear-input ()
  (save-current-buffer
    (set-buffer zeta-buf)
    (if zeta-input-overlay
	(let ((start (+ (zeta-overlay-start zeta-input-overlay)
			zeta-prompt-length))
	      (end (zeta-overlay-end zeta-input-overlay)))
	  (delete-region start end)
	  (goto-char start)
	  (setq zeta-input-tried nil)))))

(defun zeta-send-input1 ()
  (interactive)
  (setq zeta-send-input-tried nil)
  (if zeta-input-overlay
      (progn
	(zeta-set-overlay-open zeta-input-overlay)
	(goto-char (zeta-overlay-end zeta-input-overlay))))
  (comint-send-input))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Control process output filtering

(defun zeta-reset-output-filter ()
  (setq zeta-nextline nil)
  (setq comint-prompt-regexp zeta-prompt-pattern) ; seems to be modified
  )
  
(defun zeta-filter (proc string)
  (if (not zeta-buf)
      (comint-output-filter proc string)
    (save-current-buffer
      (set-buffer (process-buffer proc))
      (zeta-dprint "proc output: '%s'" string)
      (let ((end (length string))
	    (pos 0))
	(while (< pos end)
	  (let ((newl (string-match "\n" string pos)))
	    (if newl
		(progn
		  (zeta-add-word (substring string pos (+ newl 1)))
		  (zeta-flush)
		  (setq pos (+ newl 1)))
	      (zeta-add-word (substring string pos))
	      (setq pos end))))))))

(defun zeta-add-word (string)
  (if zeta-nextline
      (setq zeta-nextline (concat zeta-nextline string))
    (setq zeta-nextline string))
  (if (string-match zeta-prompt-pattern zeta-nextline)
      (progn
	;; (zeta-set-focus (match-string 1 zeta-nextline))
	(zeta-put-progress-done)
	(zeta-end-message-context)
	(setq zeta-seen-prompt t)
	(if (not zeta-record-output)
	    (progn
	      (set-buffer zeta-buf)
	      (setq zeta-lastlast-trans zeta-last-trans)
	      (setq zeta-last-trans
		    (zeta-make-marker zeta-transaction-expanded-glyph
				      'zeta-trans-action
				      (point-max)
				      zeta-buf))
	      (zeta-set-marker-property zeta-last-trans
					'zeta-trans-marker t)
	      (goto-char (point-max))
	      (let ((start (point)) ovl
		    (inhibit-read-only t)
		    )
		(comint-output-filter proc string)
		(setq ovl (zeta-make-overlay start (point-max)))
		(zeta-set-overlay-readonly ovl t)
		(zeta-set-overlay-skip ovl t)
		(zeta-set-overlay-property ovl 'zeta-prompt t)
		(zeta-set-overlay-face ovl zeta-empty-face)
		(setq zeta-input-overlay (zeta-make-overlay start (point-max)))
		(zeta-set-overlay-closed zeta-input-overlay)
		(zeta-set-overlay-property zeta-input-overlay 'zeta-input t)
		)))
	)))

(defun zeta-at-prompt ()
  (save-excursion
    (set-buffer zeta-buf)
    (goto-char (point-max)) ; (process-mark (get-buffer-process zeta-buf)))
    (beginning-of-line)
    (looking-at zeta-prompt-pattern)))

(defun zeta-flush ()
  (let ((line zeta-nextline))
    (setq zeta-nextline nil)
    (cond 
     ((string-match zeta-diag-line-prefix line)
      (zeta-put-diag (substring line (match-end 0))))
     ((string-match zeta-progress-line-prefix line)
      (zeta-put-progress (substring line (match-end 0))))
     ((string-match zeta-result-line-prefix line)
      (zeta-put-result (substring line (match-end 0))))
     ((string-match zeta-state-line-prefix line)
      (zeta-put-debug "SESSION" (substring line (match-end 0))))
     ((string-match zeta-eval-line-prefix line)
      (zeta-put-debug "SESSION" (substring line (match-end 0))))
     ((string-match zeta-debug-line-prefix line)
      (zeta-put-debug (substring line (match-beginning 1) (match-end 1))
		      (substring line (match-end 0))))
     (t
      (zeta-put-progress line)))))

(defun zeta-put-progress (string)
  (setq zeta-last-verbose (zeta-remove-last-newline string))
  ;; (message "%s ... " zeta-last-verbose)
  (if (not zeta-record-output)
      (progn
	(zeta-put-message-context 'progress "messages")
	(zeta-put-message string)
	)
    ))

(defun zeta-put-progress-done ()
  (if (not zeta-last-verbose)
      nil ; (message "ZETA ready.")
    ;; (message "%s over." zeta-last-verbose)
    (setq zeta-last-verbose nil)))
      
  
(defun zeta-put-diag (string)
  (if (not zeta-record-output)
      (progn
	(zeta-put-message-context 'diag "diagnostics")
	(zeta-put-message string)
	)
    ))

(defun zeta-put-result (string)
  (if zeta-record-output
      (setq zeta-recorded-result 
	    (if zeta-recorded-result
		(concat zeta-recorded-result string) 
	      string))
    (zeta-put-message-context 'result "result")
    (zeta-put-message string)
    ))



	
(defun zeta-put-message (string &optional prefix)
  (let ((plist zeta-locator-patterns))
    (save-current-buffer
      (set-buffer zeta-buf)
      (let ((start (point-max)) entry)
	;; (comint-output-filter proc 
	;;		      (if prefix
	;;			  (concat prefix string)
	;;			string))
	;; FIXME: proc bounds out of scope
	;; (comint-output-filter proc "")
	(let ((buffer-read-only nil))
	  (goto-char start)
	  (if prefix (insert prefix))
	  (insert string)
	  (move-marker (process-mark (get-buffer-process zeta-buf)) (point)))
	(while plist
	  (setq entry (car plist))
	  (setq plist (cdr plist))
	  (goto-char start)
	  (while (re-search-forward (nth 0 entry) nil t)
	    (let ((fn (nth 1 entry))
		  (l1 (nth 2 entry))
		  (c1 (nth 3 entry))
		  (l2 (nth 4 entry))
		  (c2 (nth 5 entry))
		  mstart mend)
	      (goto-char (match-beginning 0))
	      (setq mstart (point-marker))
	      (goto-char (match-end 0))
	      (setq mend (point-marker))
	      (setq start (match-end 0))
	      (if fn (setq fn (match-string fn)))
	      (if l1 (setq l1 (string-to-int (match-string l1))))
	      (if c1 (setq c1 (string-to-int (match-string c1))))
	      (if l2 (setq l2 (string-to-int (match-string l2))))
	      (if c2 (setq c2 (string-to-int (match-string c2))))
	      (zeta-add-locator mstart mend fn l1 c1 l2 c2)
	      ))
	  )
	(let ((window (display-buffer zeta-buf)))
	  (set-window-point window (point-max))
	  ;; (shrink-window-if-larger-than-buffer window)
	  )))))
	 

(defun zeta-put-debug (tool string)
  (save-excursion
    (set-buffer (get-buffer-create zeta-log-buffer))
    (goto-char (point-max))
    (insert tool ": ")
    (let ((start (point-max)))
      (insert string)
      (let (entry (plist zeta-locator-patterns))
	(while plist
	  (setq entry (car plist))
	  (setq plist (cdr plist))
	  (goto-char start)
	  (while (re-search-forward (nth 0 entry) nil t)
	    (let ((fn (nth 1 entry))
		  (l1 (nth 2 entry))
		  (c1 (nth 3 entry))
		  (l2 (nth 4 entry))
		  (c2 (nth 5 entry))
		  mstart mend)
	      (goto-char (match-beginning 0))
	      (setq mstart (point-marker))
	      (goto-char (match-end 0))
	      (setq mend (point-marker))
	      (setq start (match-end 0))
	      (if fn (setq fn (match-string fn)))
	      (if l1 (setq l1 (string-to-int (match-string l1))))
	      (if c1 (setq c1 (string-to-int (match-string c1))))
	      (if l2 (setq l2 (string-to-int (match-string l2))))
	      (if c2 (setq c2 (string-to-int (match-string c2))))
	      (zeta-add-locator mstart mend fn l1 c1 l2 c2))))))))

(defun zeta-clear-debug-locators ()
  (interactive)
  (save-current-buffer
    (set-buffer (get-buffer-create zeta-log-buffer))
    (zeta-map-overlays 
     (point-min) (point-max)
     (lambda (ovl)
       (zeta-del-locator ovl)))))
		       
  


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Message folding

(defun zeta-put-message-context (kind string)
  (if (not (eq zeta-message-context-kind kind))
      (progn
	(zeta-end-message-context)
	(save-excursion
	  (set-buffer zeta-buf)
	  (goto-char (point-max))
	  (beginning-of-line)
	  (if (looking-at zeta-prompt-pattern)
	      (progn
		(end-of-line)
		(zeta-put-message "\n"))))
	(setq zeta-message-start
	      (save-current-buffer
		(set-buffer zeta-buf)
		(point-max)
		))
	(let* ((glyph
		(cond
		 ((eq kind 'diag) zeta-diag-glyph)
		 ((eq kind 'progress) zeta-progress-glyph)
		 ((eq kind 'result) zeta-result-glyph)
		 (t zeta-result-glyph)
		 )))
	  (setq zeta-last-context
		(zeta-make-marker glyph 
				  'zeta-message-action
				  zeta-message-start
				  zeta-buf)))
	(if zeta-last-trans
	    (zeta-set-marker-property 
	     zeta-last-trans
	     'zeta-messages
	     (cons zeta-last-context
		   (zeta-get-marker-property zeta-last-trans 'zeta-messages))))
	(setq zeta-message-context-kind kind))))

(defun zeta-end-message-context ()
  (if zeta-last-context
      (save-current-buffer
	(set-buffer zeta-buf)
	(let ((content (zeta-make-overlay zeta-message-start (point-max))))
	  (zeta-set-overlay-readonly content t)
	  (zeta-set-overlay-property content 
				     'zeta-trans-marker zeta-last-trans)
	  (zeta-set-marker-property zeta-last-context 'zeta-content content)
	  (setq zeta-message-context-kind nil)
	  (setq zeta-message-start nil)
	  (setq zeta-last-context nil)
	  ))))

(defun zeta-fold-last-messages ()
  (interactive)
  (if zeta-lastlast-trans
      (zeta-fold-trans zeta-lastlast-trans 1)))
      
(defun zeta-fold-all-messages ()
  (interactive)
  (save-excursion
    (set-buffer zeta-buf)
    (zeta-map-markers 
     (point-min) (point-max)
     (lambda (marker)
       (if (zeta-get-marker-property marker 'zeta-trans-marker)
	   (zeta-fold-trans marker 1))
       nil))))

(defun zeta-fold-this-message ()
  (interactive)
  (save-excursion
    (set-buffer zeta-buf)
    (let ((cand (zeta-overlay-at (point) 'zeta-trans-marker)))
      (if cand
	  (zeta-fold-trans (zeta-get-overlay-property cand 'zeta-trans-marker)
			   1)))))


(defun zeta-fold-trans (trans &optional set)
  (let* ((messages (zeta-get-marker-property trans 'zeta-messages))
	 (invisible (or (and set (>= set 0))
			(and (not set) 
			     (not (zeta-get-marker-property 
				   trans 'zeta-folded))))))
    (while messages
      (zeta-fold-message (car messages) (if invisible 1 -1))
      (setq messages (cdr messages)))
    (zeta-set-marker-property trans 'zeta-folded invisible)
    (if invisible
	(zeta-set-marker-glyph trans zeta-transaction-collapsed-glyph)
      (zeta-set-marker-glyph trans zeta-transaction-expanded-glyph)
      )))

(defun zeta-trans-action (marker)
  (zeta-fold-trans marker))


(defun zeta-fold-message (context &optional set)
  (let ((content (zeta-get-marker-property context 'zeta-content)))
    (zeta-dprint "fold %s" 'context)
    (if content
	(progn
	  (let ((invisible (zeta-get-overlay-invisible content)))
	    (if (or (and set (>= set 0))
		    (and (not set) (not invisible)))
		(progn
		  (zeta-reset-selected-locator)
		  (zeta-set-overlay-invisible content t)
		  )
	      (zeta-set-overlay-invisible content nil)
	      ))))))

(defun zeta-message-action (marker)
  ;; nothing, currently
  )

  
(defun zeta-visible-pos (pos)
  "Check if the given position in command buffer is visible."
  (save-excursion
    (set-buffer zeta-buf) 
    (not (zeta-overlay-at pos 'zeta-skip))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Locators


(defun zeta-add-locator (mstart mend fn l1 c1 l2 c2)
  "Add a locator to messages."
  (zeta-dprint "add loc: %s %s %s %s %s %s %s" mstart mend fn l1 c1 l2 c2)
  ;; (zeta-update-scratch-buffers fn)
  (setq fn (and fn
		(or (get-buffer fn)
		    (and (file-readable-p fn) 
			 (file-regular-p fn)
			 (find-file-noselect fn t))
		    (and (file-readable-p (concat fn ".tex")) 
			 (file-regular-p (concat fn ".tex"))
			 (find-file-noselect (concat fn ".tex") t))
		    )))
  (if fn
      (condition-case nil
	  (let (sstart send)
	    (save-excursion
	      (set-buffer fn)
	      (save-excursion
		(goto-line l1)  
		(beginning-of-line)
		(forward-char (- c1 1))
		(setq sstart (point-marker))
		(if (and l2 c2)
		    (progn
		      (goto-line l2)
		      (beginning-of-line)
		      (forward-char (- c2 1))
		      (setq send (+ (point) 1)))
		  (setq send (+ sstart 1)))
		(let ((sovl (zeta-make-overlay sstart send 
					       (marker-buffer sstart)))
		      (dovl (zeta-make-overlay mstart mend 
					       (marker-buffer mstart))))
		  (zeta-set-overlay-open sovl)
		  (zeta-set-overlay-face dovl (zeta-get-locator-face 
					       (zeta-overlay-buffer dovl)))
		  (zeta-set-overlay-action dovl
					   'zeta-select-locator-action)
		  (zeta-set-overlay-property dovl 'locator-source sovl)
		  ))))
	(t nil))))


(defun zeta-del-locator (dovl)
  (let ((sovl (zeta-get-overlay-property dovl 'locator-source)))
    (if sovl (zeta-overlay-delete sovl))
    (zeta-overlay-delete dovl)))
    

(defun zeta-get-locator-face (&optional buf)
  (if (symbolp zeta-locator-color-or-face)
      ;; explicit face given
      zeta-locator-color-or-face
    (if buf
	(save-excursion
	  (set-buffer buf)
	  (zeta-get-locator-face1))
      (zeta-get-locator-face1))))

(defun zeta-get-locator-face1 ()
  (if (not zeta-locator-face)
      (progn 
	(setq zeta-locator-face (zeta-make-temp-sym))
	(zeta-make-face zeta-locator-face nil)
	(set-face-background zeta-locator-face zeta-locator-color-or-face)))
  zeta-locator-face)


(defun zeta-get-locator-selected-face (&optional buf)
  (if (symbolp zeta-locator-selected-color-or-face)
      ;; explicit face given
      zeta-locator-selected-color-or-face
    (if buf
	(save-excursion
	  (set-buffer buf)
	  (zeta-get-locator-selected-face1))
      (zeta-get-locator-selected-face1))))

(defun zeta-get-locator-selected-face1 ()
  (if (not zeta-locator-selected-face)
      (progn 
	(setq zeta-locator-selected-face (zeta-make-temp-sym))
	(zeta-make-face zeta-locator-selected-face nil)
	;; (copy-face 'default zeta-locator-selected-face)
	(set-face-foreground zeta-locator-selected-face 
			     zeta-locator-selected-color-or-face)
	(if (stringp zeta-locator-color-or-face)
	    (set-face-background zeta-locator-selected-face 
				 zeta-locator-color-or-face))))
  zeta-locator-selected-face)


(defun zeta-select-locator-action (dovl)
  (let ((sovl (zeta-get-overlay-property dovl 'locator-source)))
    (zeta-select-locator dovl sovl)))


(defun zeta-select-locator (dovl sovl)
  "Select the locator at DOVL which points to SOVL. "
  (let* ((dovl-buf (zeta-overlay-buffer dovl))
	 (sovl-buf (zeta-overlay-buffer sovl))
	 (dovl-start (zeta-overlay-start dovl))
	 (sovl-start (zeta-overlay-start sovl))
	 )
    (if (not (and dovl-buf dovl-start sovl-buf sovl-start))
	(progn
	  (message "Locator not longer pertinent, removed.")
	  (zeta-dprint "%S %S %S %S, %S" dovl-buf dovl-start sovl-buf sovl-start sovl)
	  (zeta-overlay-detach dovl)
	  (zeta-overlay-detach sovl)
	  )
      (zeta-reset-selected-locator)
      (setq zeta-selected-locator dovl)
      (zeta-set-overlay-face dovl (zeta-get-locator-selected-face dovl-buf))
      (zeta-set-overlay-face sovl (zeta-get-locator-selected-face sovl-buf))
      (pop-to-buffer sovl-buf)
      (goto-char sovl-start)
      )
    ))

(defun zeta-reset-selected-locator ()
  "Reset the currently selected locator."
  (if zeta-selected-locator
      (let* ((dovl zeta-selected-locator)
	     (sovl (zeta-get-overlay-property dovl 'locator-source)))
	(setq zeta-selected-locator nil)
	(if dovl
	    (progn
	      (zeta-set-overlay-face dovl  
				 (zeta-get-locator-face
				  (zeta-overlay-buffer dovl)))
	      ))
	(if sovl
	    (progn
	      (zeta-set-overlay-face sovl nil)
	      ))
	)))
	

(defun zeta-next-locator ()
  "Go to the next visible locator after the selected locator or at
the beginning."
  (interactive)
  (let ((cands 
	 (save-excursion
	   (set-buffer zeta-buf)
	   (if zeta-selected-locator
	       (zeta-overlays-in (zeta-overlay-end zeta-selected-locator)
				 (point-max)
				 'locator-source)
	     (zeta-overlays-in (point-min) (point-max) 'locator-source)))))
    (zeta-try-locator-cands cands)
    ))

(defun zeta-prev-locator ()
  "Go to the previous visible locator after the selected locator or at
the end."
  (interactive)
  (let ((cands 
	 (save-excursion
	   (set-buffer zeta-buf)
	   (if zeta-selected-locator
	       (reverse 
		(zeta-overlays-in (point-min)
				  (- (zeta-overlay-start 
				      zeta-selected-locator) 1)
				  'locator-source))
	     (reverse (zeta-overlays-in (point-min) (point-max)
					'locator-source))))))
    (zeta-try-locator-cands cands)
    ))

(defun zeta-try-locator-cands (cands)
  (let (dovl sovl found)
    (while cands
      (setq dovl (car cands))
      (if (and (setq sovl (zeta-get-overlay-property dovl 'locator-source))
	       (zeta-visible-pos (zeta-overlay-start dovl)))
	  (progn
	    (pop-to-buffer zeta-buf)
	    (goto-char (zeta-overlay-start dovl))
	    (zeta-select-locator dovl sovl)
	    (setq cands nil)
	    (setq found t))
	(setq cands (cdr cands))))
    (if (not found)
	(error "No more visible locators.")
      )))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Commands 


;; high level

(defun zeta-select-focus ()
  "Set the focused unit."
  (interactive)
  (zeta-set-focus
   (completing-read
    "Enter default unit: "
    (zeta-get-units))))

(defun zeta-set-master (master)
  "Set a master file."
  (interactive "fLoad master source file: ")
  (if (file-name-directory master)
      (save-current-buffer
	(set-buffer zeta-buf)
	(if (string-match (concat "^" 
				  (regexp-quote (file-name-directory master)))
			  default-directory)
	    (setq master (file-name-nondirectory master))))
    )
  (zeta-call (concat "load " master)))

(defun zeta-select-master ()
  "Set a master file."
  (interactive)
  (zeta-set-master 
   (read-file-name "Load (master) source file: " nil nil t
		   (and zeta-source-mode (buffer-name)))))

(defun zeta-get-units ()
  (let ((str (zeta-intern-call "list units")))
    (zeta-dprint str)
    (let ((pos 0) (end (length str)) res pos1 name)
      (while (< pos end)
	(setq pos1 (string-match "," str pos))
	(if pos1 
	    (progn
	      (setq name (zeta-trim (substring str pos pos1)))
	      (setq pos (+ pos1 1)))
	  (setq name (zeta-trim (substring str pos end)))
	  (setq pos end))
	(setq res (cons (cons name name) res))
	)
      (zeta-dprint "list %S" 'res)
      res)
    ))

      
(defun zeta-interrupt ()
  "Interrupt the current computation."
  (interactive)
  (process-send-string (get-buffer-process zeta-buf) "interrupt\n"))


(defun zeta-type-check ()
  "Type-check the focused document."
  (interactive)
  ;; (zeta-save-related-buffers)
  (zeta-call "c $U"))

(defun zeta-format ()
  "Format the focused document."
  (interactive)
  ;; (zeta-save-related-buffers)
  (zeta-call "latex $U"))

(defun zeta-view ()
  "Launch viewer for the focused document."
  (interactive)
  ;; (zeta-save-related-buffers)
  (zeta-call "view $U"))

(defun zeta-model-check ()
  "Model-check the focused document."
  (interactive)
  ;; (zeta-save-related-buffers)
  (zeta-call "mcheck $U \"$I\""))

(defun zeta-model-check-region (prefix beg end)
  "Model check predicate found at region."
  (interactive "p\nr")
  (zeta-eval-region beg end "mcheck"))

(defun zeta-eval-expr (prefix)
  "Evaluate an expression. 
With prefix argument of one (default),
do normal evaluation. Otherwise, with positive prefix,
the enumerated result will be displayed. With negative prefix, just
display the unevaluated result."
  (interactive "p")
  ;; (zeta-save-related-buffers)
  (let ((cmd 
	 (if (= prefix 1) "e $U -t"
	   (if (< prefix 0) "e $U -r" "e $U -f"))))
    (zeta-call (concat cmd " \"\n$I\n\""))
    ))

(defun zeta-eval-predicate ()
  "Evaluate an predicate."
  (interactive)
  ;; (zeta-save-related-buffers)
  (zeta-call "p $U \"$I\"")
  )

(defun zeta-eval-expr-region (prefix beg end)
  "Evaluate expression found at region.
With prefix argument of one (default),
do normal evaluation. Otherwise, with positive prefix,
the enumerated result will be displayed. With negative prefix, just
display the unevaluated result."
  (interactive "p\nr")
  (let ((mod 
	 (if (= prefix 1) "-t"
	   (if (< prefix 0) "-r" "-f"))))
    (zeta-eval-region beg end "e" mod)))

(defun zeta-eval-predicate-region (prefix beg end)
  "Evaluate predicate found at region."
  (interactive "p\nr")
  (zeta-eval-region beg end "p" ""))




;; Options

(defun zeta-toggle-pop-commander-on-start (&optional set)
  (interactive)
  (if (not set)
      (setq zeta-pop-commander-on-start (not zeta-pop-commander-on-start))))




;; low level

(defun zeta-call (command)
  "Call a ZETA command. The command string may contain the
following placeholders: $U for guessing the unit this command works on
and $I to set point to this position for user input. If $I is not contained
in the command, then it will be immediatly send."
  (zeta-check-session)
  (zeta-clear-debug-locators)
  (zeta-clear-input)
  ;; (accept-process-output (get-buffer-process zeta-buf) 0.0 1)
  (let ((i (string-match "$U" command)))
    (if i
	(setq command
	      (concat (substring command 0 i)
		      "-u " (zeta-find-focus)
		      (substring command (+ i 2)))))
    (let ((j (string-match "$I" command))
	  inspoint)
      (save-current-buffer
	(set-buffer zeta-buf)
	(goto-char (process-mark (get-buffer-process zeta-buf)))
	(if j
	    (progn
	      (insert (substring command 0 j))
	      (setq inspoint (point))
	      (insert (substring command (+ j 2)))
	      )
	  (insert command)
	  (zeta-send-input1)
	  )
	)
      (if inspoint
	  (progn
	    (pop-to-buffer zeta-buf)
	    (goto-char inspoint))))))


(defun zeta-intern-call (command)
  "Call a ZETA command and return its result as a three-element
list of strings containing progress messages, diagnostics, and result (in this
order)."
  (zeta-check-session)
  (zeta-clear-input)
  ;; (accept-process-output (get-buffer-process zeta-buf) 0.5)
  (zeta-reset-output-filter)
  (let ((zeta-record-output t)
	(zeta-recorded-result "")
	)
    (setq zeta-seen-prompt nil)
    (process-send-string (get-buffer-process zeta-buf)
     			 (concat command "\n"))
    (zeta-wait-ready)
    (zeta-trim zeta-recorded-result)))

(defun zeta-wait-ready ()
  ;; wait some time to let a command be completed
  (setq zeta-seen-prompt nil)
  (let ((tries 600)
	(sleep 0.1)
	found)
    (while (and (not zeta-seen-prompt) (> tries 0))
      ;; (accept-process-output (get-buffer-process zeta-buf) sleep 0)
      (sleep-for sleep)
      (setq tries (- tries 1)))))

(defun zeta-find-focus ()
  "Find the focused unit."
  (if zeta-source-mode
      ;; search backward for possible focus
      (save-excursion
	(if (re-search-backward zeta-find-focus-pattern nil t)
	    (if (match-string zeta-find-focus-pattern-pos)
		(zeta-set-focus (match-string zeta-find-focus-pattern-pos))))))
  (if (not zeta-focus)
      (zeta-select-focus))
  (or zeta-focus "<unit>"))



(defun zeta-eval-region (beg end command option)
  "Evaluate the current region with the given MODE (such as eval, test, and
so on)."
  (interactive "r\nsEnter ZETA evaluation command: ")
  (zeta-check-session)
  (zeta-clear-debug-locators)
  (zeta-clear-input)
  ;; (zeta-save-related-buffers)
  ;; (accept-process-output (get-buffer-process zeta-buf) 0.0 1)
  (zeta-dprint "zeta-eval-region ....")
  (let ((buf (current-buffer))
	(unit (zeta-find-focus))
	line column)
    (if (and beg end (< beg end))
	(progn
	  (save-excursion
	    (goto-char beg)
	    (beginning-of-line)
	    (setq column (+ (- beg (point)) 1))
	    (forward-char)
	    (setq line (count-lines (point-min) (point))))
	  (save-current-buffer
	    (set-buffer zeta-buf)
	    (insert
	     (format "%s -u %s %s \"$%s(%d.%d)$%s\""
		     command
		     unit
		     option
		     (buffer-name buf)
		     line 
		     column
		     (zeta-quote-quotes (buffer-substring beg end buf))))
	    (zeta-send-input1)
	    )))))

  
(defun zeta-save-related-buffers ()
  "Save buffers which may be required as persistent files to execute a command."
  (interactive)
  (save-excursion
    (map-y-or-n-p
     (function
      (lambda (buf)
	(if (and (buffer-modified-p buf) (buffer-file-name buf))
	    (progn
	      (set-buffer buf)
	      (if zeta-source-mode 
		  (format "Save file %s? " (buffer-file-name buf))
		nil))
	  nil)))
     (function
      (lambda (buf)
	(set-buffer buf)
	(condition-case nil
	    (save-buffer)
	  (error nil))))
     (buffer-list)
     '("file" "files" "save") ; FSF emacs: requires this if called from mouse!
     )))

(defun zeta-check-session ()
  "Check if ZETA session is active, and possibly activate one. "
  (if (or (not zeta-buf)
	  (and zeta-buf (not (get-buffer-process zeta-buf))))
      (if (y-or-n-p "ZETA session not running. Start one? ")
	  (save-excursion
	    (zeta))
	(error "ZETA session not running"))))
	  
(defun zeta-quote-quotes (string)
  "Quote quotes in string."
  (mapconcat 
   (function (lambda (ch) 
	       (if (= ch ?\") "\\\"" (char-to-string ch))))
   string ""))

    
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Model Inclusion

(defun zeta-msl-glyph (msl)
  "Make a glyph for preview of given MSL."
  (if zeta-running-xemacs
      (if (zeta-running-p)
	  (let ((gifname (zeta-intern-call (concat "msl-preview-gif " msl))))
	    (if (or (not gifname) (string= gifname "")) 
		(make-glyph (vector 'string :data " <preview not available>"))
	      (let ((glyph (make-glyph (vector 'gif :file gifname))))
		(zeta-dprint "model view %s -> %s" gifname glyph)
		(remove-glyph-property glyph 'contrib-p)
		(set-glyph-property glyph 'baseline 50)
		glyph)))
	(make-glyph (vector 'string :data " <preview not available>"))
	)))

  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pre- and Post Command Hook

;; for realizing cursor movements over folded messages

(defvar zeta-pre-command-point 0
  "The value of point at the time pre-command-hook is called.")
(make-variable-buffer-local 'zeta-pre-command-point)

(defun zeta-pre-command-hook ()
  ;; something else ..
  (if (not (eq last-command 'zeta-send-input))
      (setq zeta-send-input-tried nil))
  (setq zeta-pre-command-point (point)))

(defun zeta-post-command-hook ()
  (let ((pos (point)) ext)
    ;; (zeta-dprint "post command")
    (setq ext (zeta-overlay-at pos 'zeta-skip))
    (if ext 
	(progn
	  (if (zeta-get-overlay-property ext 'zeta-prompt)
	      (setq pos (zeta-overlay-end ext))
	    (if (>= pos zeta-pre-command-point)
		(while ext
		  (setq pos (zeta-overlay-end ext))
		  (setq ext (and (< pos (point-max))
				 (zeta-overlay-at pos 'zeta-skip))))
	      (while ext
		(setq pos (- (zeta-overlay-start ext) 1))
		(if (> pos (point-min))
		    (setq ext (zeta-overlay-at pos 'zeta-skip))
		  (setq ext nil)
		  (setq pos (point-min))))))
	  (goto-char pos)))))
	  

(defun zeta-install-command-hook ()
  "Install command hook for the current buffer."
  (make-local-hook 'pre-command-hook)
  (add-hook 'pre-command-hook 'zeta-pre-command-hook nil t)
  (make-local-hook 'post-command-hook)
  (add-hook 'post-command-hook 'zeta-post-command-hook nil t)
  )

(defun zeta-uninstall-command-hook ()
  "Uninstall input hooks for the current buffer."
  (remove-hook 'pre-command-hook 'zeta-pre-command-hook t)
  (remove-hook 'post-command-hook 'zeta-post-command-hook t)
  )



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; zeta-mode.el end

(provide 'zeta-mode)

