;; vtex-mode 
;; LaTeX PARSING 
;; $Id: vtex-parse.el,v 1.1 1998/09/18 10:12:50 wg Exp $ 

(provide 'vtex-parse)
(require 'vtex-base)
(require 'vtex-tmpl)
(require 'vtex-custom)


(defvar vtex-tmpls-rex nil
  "Regular expression which matches tokens 
relevant for `vtex-tmpls'. It is calculated on demand. 
This variable should be set to `nil' if the value of
`vtex-tmpls' has changed")

(defvar vtex-math-tmpls-rex nil
  "Regular expression which matches tokens 
relevant for `vtex-math-tmpls'. It is calculated on demand. 
This variable should be set to `nil' if the value of
`vtex-math-tmpls' has changed")

(defvar vtex-tmpl-math nil
  "The environment template for \begin{math}...\end{math}, used to
implement the abbreviation $...$.")

(defvar vtex-tmpl-displaymath nil
  "The environment template for \begin{displaymath}...\end{displaymath}, 
used to implement the abbreviation $$...$$.")

(defvar vtex-arg-rex 
  (setq vtex-argstart-rex (concat "\\( \\)*\\(\\(" 
				  (regexp-quote vtex-tok-bgroup)
				  "\\)\\|"
				  (regexp-quote vtex-tok-cmd)
				  "\\(\\w+\\|\W\\)\\|.\\)"))
  "Regular expression to match a TeX argument,
including any whitespace up to the argument. The next argument
is either a bgroup, an escaped TeX token, or any single character.
If match 3 is defined, then the matched argument was a bgroup.")

(defvar vtex-math-layout-rex
  "\\(^[ ]+\\)\\|\\s-+\\|\\\\\\\\[ ]*\\(\\\\t\\([0-9]\\|{[0-9]+}\\)\\)?[ ]*\n"
  "Regular expression to match white-space, newlines, and
cr-tab sequences in math mode.")


(defun vtex-calc-tmpls-rex (table &optional outer-table)
  "Calculate regular expression matching tokens for templates in TABLE.
For an environment, the tokens
are `\\begin{envname}', the separator and `\\end{envname}'. For a command, 
the token is `\\cmdname'. Furthermore, the TeX begin and
end group characters and the math character are included. 
Match 1 in the regexp describes the 
environment name matched in a `\\begin{env}', match 2 in a `\\end{env}'
Match 3 represents a separator.

If OUTER-TABLE is given, then all `\\end{env}' and separator
tokens from this table are also included in the regular expression."
  (let* ((env-names (vtex-env-names-rex table))
	 (all-env-names 
	  (if outer-table 
	      (concat env-names "\\|" (vtex-env-names-rex outer-table))
	    env-names))
	 (separator-names (vtex-separator-names-rex table))
	 (all-separator-names 
	  (if outer-table 
	      (concat separator-names "\\|" 
		      (vtex-separator-names-rex outer-table))
	    separator-names))
	 (bgroup (regexp-quote vtex-tok-bgroup))
	 (egroup (regexp-quote vtex-tok-egroup))
	 (math (regexp-quote vtex-tok-math))
	 (begin-expr (concat (regexp-quote vtex-tok-begin) 
			     " *" bgroup "\\s-*\\(" 
			     env-names "\\)\\s-*" egroup))
	 (end-expr (concat (regexp-quote vtex-tok-end) 
			   " *" bgroup "\\s-*\\(" 
			   all-env-names "\\)\\s-*" egroup))
	 (cmd-expr (vtex-cmd-names-rex table))
	 (separator-expr (concat "\\(" all-separator-names "\\)")))
    (concat bgroup "\\|" egroup "\\|" math "\\|"
	    cmd-expr "\\|" begin-expr "\\|" end-expr "\\|" separator-expr)))


(defun vtex-env-names-rex (table &optional right)
  "Get environment names from template TABLE as an or'd regular expression.
If the string RIGHT is given, prepend it to it."
  (let ((strings (vtex-reduce-hashtable 
		  (lambda (key tmpl rest) 
		    (if (vtex-tmpl-envp tmpl)
			;; (let ((ename (regexp-quote (vtex-tmpl-name tmpl))))
			(let ((ename (vtex-tmpl-name tmpl)))
			  (cons ename rest))
		      rest))
		  table)))
    (setq strings (remove-duplicates strings))
    (if strings
	(if right
	    (concat (vtex-regexp-opt strings) "\\|" right)
	  (vtex-regexp-opt strings))
      (if right 
	  right
	;; never result an expression which matches the empty string
	"\\9"))))

(defun vtex-cmd-names-rex (table &optional right)
  "Get command names from template TABLE as an or'd regular expression.
If the string RIGHT is given, prepend it to it."
  (let ((strings (vtex-reduce-hashtable
		   (lambda (key tmpl rest)
		     (if (vtex-tmpl-cmdp tmpl)
			 (let ((cname (vtex-tmpl-name tmpl)))
			   (cons cname rest))
		       rest))
		   table)))
    (vtex-tokens-rex (remove-duplicates strings) right)))

(defun vtex-separator-names-rex (table &optional right)
  "Get separator names from template TABLE as an or'd regular expression.
If the string RIGHT is given, prepend it to it."
  (let ((strings (vtex-reduce-hashtable
		   (lambda (key tmpl rest)
		     (if (and (vtex-tmpl-envp tmpl) (vtex-tmpl-separator tmpl))
			 (let ((cname (vtex-tmpl-separator tmpl)))
			   (if (not (string= cname ""))
			       (cons cname rest)
			     rest))
		       rest))
		   table)))
    (vtex-tokens-rex (remove-duplicates strings) right))) 
    
(defun vtex-tokens-rex (strings &optional right)
  (let ((words (vtex-reduce
		(lambda (tok rest)
		  (if (vtex-word-p tok)
		      (cons tok rest)
		    rest))
		strings))
	(specials (vtex-reduce
		   (lambda (tok rest)
		     (if (vtex-word-p tok)
			 rest
		       (cons tok rest)))
		   strings)))
    (let ((rex
	   (cond
	    ((and words specials)
	     (concat (vtex-regexp-opt specials) 
		     "\\|" (vtex-regexp-opt words t)))
	    (words (vtex-regexp-opt words t)) 
	    (specials (vtex-regexp-opt specials))
	    (t nil))))
      (if rex
	  (if right (concat rex "\\|" right) rex)
	(if right right "\\9")))))

(defun vtex-word-p (tok)
  (let ((class (if (string= (substring tok 0 1) vtex-tok-cmd)
		   (char-syntax (aref tok 1))
		 (char-syntax (aref tok 0)))))
    (or (= class ?_) (= class ?w))))

(defun vtex-regexp-opt (strings &optional wordend)
  (if (fboundp 'regexp-opt)
      (if wordend
	  (concat "\\(?:" (regexp-opt strings) "\\)\\b")
	(regexp-opt strings))
    (vtex-reduce 
     (lambda (str rest)
       (setq str (if wordend
		     (concat (regexp-quote str) "\\b")
		   (regexp-quote str)))
       (if rest 
	   (concat str "\\|" rest)
	 str))
     strings)))


(defsubst vtex-update-tmpls-rex ()
  "Update regular expressions for template tables."
  (if (or (not vtex-tmpls-rex) (not vtex-math-tmpls-rex))
      ;; CHECKME: we should be always run with the correct syntax
      ;; table, but this seems to be not the case sometimes. So set it
      ;; now.
      (let ((old (syntax-table)))
	(set-syntax-table (vtex-extend-syntax-table (copy-syntax-table old)))
	(setq vtex-tmpls-rex (vtex-calc-tmpls-rex vtex-tmpls))
	(setq vtex-math-tmpls-rex 
	      (if vtex-handle-math-layout
		  (concat (vtex-calc-tmpls-rex vtex-math-tmpls vtex-tmpls)
			  "\\|\\("
			  vtex-math-layout-rex
			  "\\)")
		(vtex-calc-tmpls-rex vtex-math-tmpls vtex-tmpls)))
	(setq vtex-tmpl-math (vtex-search-tmpl vtex-tmpls "math"))
	(setq vtex-tmpl-displaymath (vtex-search-tmpl vtex-tmpls 
						      "displaymath"))
	(set-syntax-table old)
	)))


(defsubst vtex-decorate-inst (tmpl inst)
  ;; (vtex-dprint "decorating %s" inst)
  (funcall (vtex-tmpl-decorate tmpl) inst)
  ;; (vtex-dprint "post-decorating %s" inst)
  (if (vtex-tmpl-post-decorate tmpl)
      (funcall (vtex-tmpl-post-decorate tmpl) inst)))

(defvar vtex-parse-warncnt 0)

(defvar vtex-parse-active nil)

(defsubst vtex-parse-warn (form &optional arg1 arg2)
  (if vtex-parse-warnings
      (vtex-warn form arg1 arg2))
  (setq vtex-parse-warncnt (+ vtex-parse-warncnt 1)))

(defsubst vtex-parse-para-start (inst)
  ;; Calculate the start of the next paragraph from an environment
  ;; instance. This either at the end of the last separator,
  ;; at the end of the last space (the closing }) of an argument,
  ;; or at the end of the \\begin{env} token.
  (cond
   ((vtex-inst-separators inst)
    (cdr (car (vtex-inst-separators inst))))
   ((vtex-inst-spaces inst)
    (cdr (car (vtex-inst-spaces inst))))
   (t
    (cdr (vtex-inst-begin inst)))))


(defsubst vtex-add-arg (stack range &optional spaces)
  ;; Add an argument at RANGE, with optional SPACES,
  ;; STACK beeing (ARGC INST ...).
  ;; If the given instance doesn't expect any more arguments,
  ;; remove ARGC from stack. If the given instance is furthermore a command,
  ;; decorate it and remove it from stack.
  ;; Yields new stack.
  (let* ((argc (car stack))
	 (inst (car (cdr stack)))
	 (args (vtex-inst-args inst))
	 (tmpl (vtex-inst-tmpl inst)))
    (vtex-inst-args! inst (cons range args))
    (if spaces
	(vtex-inst-spaces! inst
			   (append spaces (vtex-inst-spaces inst))))
    (setq argc (- argc 1))
    (if (not (zerop argc))
	;; expecting more arguments
	(cons argc (cdr stack))
      ;; no more arguments expected
      (if (vtex-inst-cmdp inst)
	  ;; decorate a command, pop number and instance
	  (progn
	    (vtex-inst-region! inst
			       (cons (car (vtex-inst-tok inst))
				     (if spaces 
					 ;; we assume space to be `last',
					 ;; if given
					 (cdr (car spaces))
				       (cdr range))))
	    (vtex-decorate-inst tmpl inst)
	    (cdr (cdr stack)))
	;; pop number, leave environment instance
	(cdr stack))))
  )




(defun vtex-parse-region (from to)
  "Parse region and decorate it."
  (vtex-update-specials)
  (vtex-update-tmpls-rex)
  (setq vtex-parse-warncnt 0)
  (setq vtex-parse-active t)
  (goto-char from)
  ;; determine initial math count
  (if (vtex-inst-at from nil nil nil 
		    (lambda (inst) 
		      (and (vtex-inst-envp inst)
			   (vtex-tmpl-math-env (vtex-inst-tmpl inst)))))
      (vtex-parse-region1 from to 1)
    (vtex-parse-region1 from to 0))
  (setq vtex-parse-active nil)
  vtex-parse-warncnt)

(defun vtex-parse-region1 (from to mathcnt)
  ;; A stack is used to represent context information.
  ;; The stack contains either ranges, representing 
  ;; the beginning of a group, numbers, representing a number of
  ;; arguments to add to the instance on the stack below the number,
  ;; or instances themselves."
  ;; @NYI: options [...]
  ;; @NYI: $$...$$
  ;; @? partition into more auxiliary defsubst ...
  (let (stack (continue t) (case-fold-search nil) 
	      tok top locked lockexts pos1 pos2 pos3)
    
    (while continue
      (setq top (and stack (car stack)))
      
      (if (numberp top)
	  ;; argument group expect mode =========================
	  (if (looking-at vtex-argstart-rex)
	      (if (match-beginning 3)
		  ;; push a bgroup to stack and continue
		  (progn 
		    (goto-char (match-end 0))
		    (setq stack 
			  (cons (cons (match-beginning 0) (match-end 0))
				stack)))
		;; take the matched text as an argument
		(setq stack 
		      (vtex-add-arg stack
				    (cons (match-beginning 0) 
					  (match-end 0))))
		)
	    ;; error: cannot find arguments for instance below top
	    ;; remove top and instance and continue
	    (let ((inst (car (cdr stack))))
	      (if (vtex-inst-cmdp inst)
		  (progn
		    (vtex-parse-warn 
		     "missing arguments for command %S at %S, command ignored"
		     (vtex-tmpl-name (vtex-inst-tmpl inst))
		     (car (vtex-inst-tok inst)))
		    (setq stack (cdr (cdr stack))))
		(vtex-parse-warn 
		 "missing arguments for environment %S at %S, environment ignored"
		 (vtex-tmpl-name (vtex-inst-tmpl inst))
		 (car (vtex-inst-begin inst)))
		(setq stack (cdr (cdr stack))))))

	;; normal mode ===================================
	(if (not (and (> to (point))
		      (re-search-forward 
		       (if (> mathcnt 0) vtex-math-tmpls-rex vtex-tmpls-rex)
		       to t)))
	    ;; end of parsing
	    (setq continue nil)

	  ;; found something
	  (goto-char (match-end 0))
	  (setq tok (match-string 0))

	  (setq locked 
		(map-extents 
		 (lambda (ext arg)
		   (let ((inst (extent-property ext 'vtex-inst)))
		     (if (vtex-get-inst-prop inst 'locked)
			 inst
		       nil)))
		 nil (match-beginning 0) (match-end 0) nil
		 'start-and-end-in-region 'vtex-inst))
					 
	  (cond

	   ;; handle locked instances ----------------------------
	   (locked
	    (if (vtex-inst-envp locked)
		(setq lockexts
		      (append (if (vtex-inst-opt locked)
				  (list (vtex-inst-opt locked))
				nil)
			      (vtex-inst-args locked)
			      (vtex-inst-paragraphs locked)))
	      (setq lockexts
		    (append (if (vtex-inst-opt locked)
				  (list (vtex-inst-opt locked))
			      nil)
			    (vtex-inst-args locked))))
	    ;; recursively call parser for all regions of lockexts
	    (while lockexts
	       (setq pos1 (extent-start-position (car lockexts))
		     pos2 (extent-end-position (car lockexts)))
	       (goto-char pos1)
	       (vtex-parse-region1 pos1 pos2 mathcnt)
	       (setq lockexts (cdr lockexts)))
	    ;; point at end of locked instance
	    (goto-char (extent-end-position (vtex-inst-region locked))))

	      
	   ;; handle $ -------------------------------------------
	   ((string= tok vtex-tok-math)

	    (if (and top 
		     (vtex-inst-envp top)
		     (eq (vtex-inst-tmpl top) vtex-tmpl-math))
		;; closing $
		(progn
		  (vtex-inst-region! top
				    (cons (car (vtex-inst-begin top))
					  (match-end 0)))
		  (vtex-inst-end! top
				 (cons (match-beginning 0) (match-end 0)))
		  (vtex-inst-paragraphs! top
				  (list
				   (cons
				    (cdr (vtex-inst-begin top))
				    (match-beginning 0))))
		  (vtex-decorate-inst vtex-tmpl-math top)
		  (setq mathcnt (- mathcnt 1))
		  (setq stack (cdr stack)))
	      ;; opening $
	      (let ((inst (vtex-inst-env
			   vtex-tmpl-math
			   nil nil nil nil nil
			   (cons (match-beginning 0) (match-end 0))
			   nil nil nil)))
		(setq mathcnt (+ mathcnt 1))
		(setq stack (cons inst stack)))))

	   ;; handle a bgroup ---------------------------
	   ((string= tok vtex-tok-bgroup)
	    ;; push the range of the bgroup
	    (setq stack 
		  (cons (cons (match-beginning 0) (match-end 0))
			stack)))

	   ;; handle an egroup -------------------------
	   ((string= tok vtex-tok-egroup)
	    ;; pop a bgroup from stack 
	    ;; if there is an argument number afterwards on the stack,
	    ;; add the group to the instance below the
	    ;; number. If no more arguments are expected, remove
	    ;; the number and -- in case of a command -- decorate it.

	    (if (not (consp top))
		(vtex-parse-warn "unmatched %S at %S, ignored" vtex-tok-egroup
				 (match-beginning 0))
	      (setq stack (cdr stack))
	      (if (numberp (car stack))
		  ;; instance on stack which awaits arguments
		  (setq stack
			(vtex-add-arg stack
				      (cons (cdr top) (match-beginning 0))
				      (list
				       (cons (match-beginning 0) 
					     (match-end 0))
				       top)))
		;; not a number on stack: ignore group
		)))
	   
	   ;; handle a begin ------------------------
	   ((match-beginning 1) ; => must be a \begin{envname}
	    (let* ((tmpl 
		    (if (> mathcnt 0)
			(vtex-search-tmpl vtex-math-tmpls (match-string 1))
		      (vtex-search-tmpl vtex-tmpls (match-string 1))))
		   (inst
		    (vtex-inst-env 
		     tmpl nil nil nil nil nil
		     (cons (match-beginning 0) (match-end 0))
		     nil nil nil))
		   (argc (vtex-tmpl-argc tmpl)))
	      (if (vtex-tmpl-math-env tmpl)
		  (setq mathcnt (+ mathcnt 1)))
	      (if (zerop argc)
		  (setq stack (cons inst stack))
		(setq stack (cons argc (cons inst stack))))))
	   
	   ;; handle an end -------------------------
	   ((match-beginning 2) ; => must be a \end{envname}
	    ;; pop an environment inst from stack, complete and decorate it.
	    (setq pos1 (match-beginning 0))
	    (setq pos2 (match-end 0))
	    (if (not (and (vtex-inst-envp top)
			  (string= (vtex-tmpl-name (vtex-inst-tmpl top))
				   (match-string 2))))
		(vtex-parse-warn "unmatched end of %S at %S, ignored" 
				(match-string 2) pos1)
	      
	      (vtex-inst-region! top
				(cons (car (vtex-inst-begin top))
				      pos2))
	      (vtex-inst-end! top 
			     (cons pos1 pos2))
	      (vtex-inst-paragraphs! top
				     (cons 
				      (cons (vtex-parse-para-start top)
					    pos1)
				      (vtex-inst-paragraphs top)))
	      (vtex-decorate-inst  (vtex-inst-tmpl top) top)
	      (if (vtex-tmpl-math-env (vtex-inst-tmpl top))
		  (setq mathcnt (- mathcnt 1)))
	      (setq stack (cdr stack))))

	   ;; handle a separator -------------------------
	   ((match-beginning 3)  ; ==> must be a separator
	    
	    (if (not (and (vtex-inst-envp top)
			  (string= (vtex-tmpl-separator (vtex-inst-tmpl top))
				   (match-string 3))))
		(vtex-parse-warn "unmatched separator %S at %S, ignored" 
				 (match-string 3) (match-beginning 0))
	      (setq pos1 (vtex-parse-para-start top))
	      (setq pos2 (match-beginning 3))
	      (setq pos3 (match-end 3))
	      (vtex-inst-paragraphs! top
				     (cons
				      (cons pos1 pos2)
				      (vtex-inst-paragraphs top)))
	      (vtex-inst-separators! top
				     (cons
				      (cons pos2 pos3)
				      (vtex-inst-separators top)))
	      ))
	   
	   ;; handle math layout ---------------------------------
	   ((match-beginning 4)
	    (cond
;	     ((string= tok "\n")
;	      (let* ((region (cons (match-beginning 0)
;				   (match-end 0)))
;		     (inst (vtex-inst-cmd 
;			    vtex-math-newline-tmpl
;			    nil
;			    region
;			    nil nil nil
;			    region)))
;		(vtex-decorate-inst vtex-math-newline-tmpl inst)))
;	     ((match-beginning 5)
;	      (let* ((region (cons (match-beginning 0)
;				   (match-end 0)))
;		     (inst (vtex-inst-cmd 
;			    vtex-math-leading-space-tmpl
;			    nil
;			    region
;			    nil nil nil
;			    region)))
;		(vtex-decorate-inst vtex-math-leading-space-tmpl inst)))
	     ((= (char-syntax (aref tok 0)) ? )
	      (let* ((start (match-beginning 0))
		     (end (match-end 0))
		     (region (cons start end))
		     (tok (cons start (+ start 1)))
		     (space (cons (+ start 1) end))
		     (inst (vtex-inst-cmd 
			    vtex-math-space-tmpl
			    nil
			    region
			    nil
			    (list space)
			    nil 
			    tok)))
		(vtex-decorate-inst vtex-math-space-tmpl inst)))
	     ((= (aref tok 0) ?\\)
	      (let* ((start (match-beginning 0))
		     (end (match-end 0))
		     (region (cons start end))
		     (tok (cons start (+ start 1)))
		     (space1 (cons (+ start 1) (- end 1)))
		     (space2 (cons (- end 1) end ))
		     (inst (vtex-inst-cmd 
			    vtex-math-crtab-tmpl
			    nil
			    region
			    nil
			    (list space1 space2)
			    nil
			    tok)))
		(vtex-decorate-inst vtex-math-crtab-tmpl inst)))
	     (t
	      (vtex-die "not a legal math layout: `%S'" tok))))
	     
	    
	   ;; handle a command ----------------------
	   (t ; => must be a command
	    ;; if the command expects no arguments, decorate it immediatly,
	    ;; otherwise push it and its argument count on the stack
	    (let* ((inst (vtex-inst-cmd
			  (if (> mathcnt 0)
			      (vtex-search-tmpl vtex-math-tmpls tok)
			    (vtex-search-tmpl vtex-tmpls tok))
			  nil nil nil nil nil
			  (cons (match-beginning 0) (match-end 0))))
		   (argc (vtex-tmpl-argc (vtex-inst-tmpl inst))))
	      (if (zerop argc)
		  (progn
		    (vtex-inst-region! inst (vtex-inst-tok inst))
		    (vtex-decorate-inst (vtex-inst-tmpl inst) inst))
		(setq stack (cons argc (cons inst stack))))))
	   
	   ) ; cond
	  ) ; if (not (re-search ...)
	) ; if (numberp top)
      ) ; while (continue)
    
    ;; check for unclosed context =================
    (setq stack (reverse stack))
    (while stack
      (let ((top (car stack)))
	(cond   
	 ((consp top)
	  (vtex-parse-warn "unclosed %S at %S, ignored"
		    vtex-tok-bgroup (car top))
	  (setq stack (cdr stack)))
	 ((vtex-inst-envp top)
	  (vtex-parse-warn 
	   "missing argument or unclosed environment %S at %S, ignored"
		    (vtex-tmpl-name (vtex-inst-tmpl top))
		    (car (vtex-inst-begin top)))
	  (if (numberp (car (cdr stack)))
	      (setq stack (cdr (cdr stack)))
	    (setq stack (cdr stack))))
	 ((vtex-inst-cmdp top)
	  (vtex-parse-warn "missing arguments for command %S at %S, ignored"
		    (vtex-tmpl-name (vtex-inst-tmpl top))
		    (car (vtex-inst-tok top)))
	  (if (numberp (car (cdr stack)))
	      (setq stack (cdr (cdr stack)))
	    (setq stack (cdr stack)))))))

    ;; call post-parse hooks
    (map-extents 
     (lambda (ext arg)
       (funcall (extent-property ext 'vtex-post-parse-function) 
		(extent-property ext 'vtex-inst)
		(max from (extent-start-position ext))
		(min to (extent-end-position ext)))
       nil)
     nil from to nil nil 'vtex-post-parse-function)
    vtex-parse-warncnt
  ))


;;; Working with extent Lists (used for auto-parsing)


;;@TODO: make them sorted for speedup

(defun vtex-extent-list-add (list from to)
  (let ((exts list) (search t) ext ext-from ext-to)
    (while (and exts search)
      (setq ext (car exts)   
	    ext-from (extent-start-position ext)
	    ext-to (extent-end-position ext))
      (if (and (>= from ext-from) (<= from ext-to))
	  ;; start-point in extent
	  (if (and (>= to ext-from) (<= to ext-to))
	      ;; end-point also in extent: all done
	      (setq search nil)
	    ;; extent the extent at the end
	    (set-extent-endpoints ext ext-from to)
	    (setq search nil))
	;; start-point not in extent
	(if (and (>= to ext-from) (<= to ext-to))
	    ;; end-point in extent: extent the extent at the start 
	    (progn 
	      (set-extent-endpoints ext from ext-to)
	      (setq search nil))
	  ;; try next one in list
	  (setq exts (cdr exts)))))
    (if search
	;; have to create a new extent
	(cons (make-extent from to) list)
      list)))

;(defun vtex-extent-list-transform (list fun)
;  (let (res ext)
;    (while list
;      (setq ext (car list)
;	    list (cdr list)
;	    region (funcall fun 
;			    (extent-start-position ext)
;			    (extent-end-position ext))
;	    res (vtex-extent-list-add res (car region) (cdr region))))))


(defun vtex-closeup-line (from to)
  (save-excursion
    (let (from1)
      (goto-char from)
      (beginning-of-line)
      (if (> (point) (point-min))
	  (backward-char))
      (setq from1 (point))
      (goto-char to)
      (end-of-line)
      (cons from1 (point)))))


;;; Auto Parsing

(defvar vtex-auto-parse-exts nil
  "List of extent used to record the regions to be reparsed.")
(make-variable-buffer-local 'vtex-auto-parse-exts)

    
(defun vtex-auto-parse-register (from to)
  "Register region to be autoparsed."
  (let ((closeup (vtex-closeup-line from to)))
    (setq vtex-auto-parse-exts 
	  (vtex-extent-list-add vtex-auto-parse-exts 
				(car closeup) (cdr closeup)))))

(defun vtex-auto-parse-force ()
  "Force auto-parse actions."
  (if (not vtex-auto-parse-exts)
      ;; nothing to do
      nil
    ;; process extent list
    (let (ext ext-from ext-to)
      (while vtex-auto-parse-exts
	(setq ext (car vtex-auto-parse-exts)
	      vtex-auto-parse-exts (cdr vtex-auto-parse-exts)
	      ext-from (extent-start-position ext)
	      ext-to (extent-end-position ext))
	(delete-extent ext)
	(vtex-undecorate-region ext-from ext-to)
	(vtex-parse-region ext-from ext-to))
      t)))


;(defvar vtex-auto-parse-timeout nil
;  "Timeout registered for asynchronous auto-parse parsing.")
;(make-variable-buffer-local 'vtex-auto-parse-timeout)


;(defun vtex-reset-auto-parse-globals ()
;  "Reset global data of the after change parser in case of an error condition."
;  (setq vtex-auto-parse-ext nil)
;  (setq vtex-auto-parse-full-ext nil)
;  (if vtex-auto-parse-timeout
;      (progn
;	(disable-timeout vtex-auto-parse-timeout)
;	(setq vtex-auto-parse-timeout nil))))


;(defun vtex-delayed-parse-auto-parse (buf)
;  (call-with-condition-handler
;   (lambda (what-error)
;     (vtex-dprint "async parse: %s" (quote what-error))
;     (vtex-reset-parser-globals)
;     (if what-error (signal-error (car what-error) (cdr what-error))))
;   'vtex-delayed-parse-auto-parse1 buf))

;(defun vtex-delayed-parse-auto-parse1 (buf)
;  ;; (remove-hook 'pre-idle-hook 'vtex-delayed-parse-auto-parse)
;  ;; (vtex-dprint "timeout for buffer %s" buf)
;  (save-excursion
;    (set-buffer buf)
;    (disable-timeout vtex-auto-parse-timeout)
;    (setq vtex-auto-parse-timeout nil)
;    (if (and (extent-live-p vtex-auto-parse-ext)
;	     (not (extent-detached-p vtex-auto-parse-ext)))
;	(if vtex-parse-active ;; and (not (sit-for 0 t))
;	    ;; parser is currently active or user input is available
;	    ;; postpone parsing 
;	    (setq vtex-auto-parse-timeout
;		  (add-timeout vtex-auto-parse-delay 
;			       'vtex-delayed-parse-auto-parse nil))
;	  (let ((from (extent-start-position vtex-auto-parse-ext))
;		(to (extent-end-position vtex-auto-parse-ext)))
;	    (cond 
;	     ((eq vtex-auto-parse 'full)
;	      (let ((vtex-parse-warnings nil))
;		(vtex-undecorate-region (point-min) (point-max))
;		(vtex-parse-region (point-min) (point-max))))
;	     ((eq vtex-auto-parse 'narrow)
;	      (let ((vtex-parse-warnings nil) inst)
;		(goto-char from)
;		(beginning-of-line)
;		(setq from (point))
;		(goto-char to)
;		(end-of-line)
;		(setq to (point))
		
;		;; take the next enclosing environment into account
;		(setq inst (vtex-inst-at from nil nil nil 'vtex-inst-envp))
;		(if inst
;		    (setq from (extent-start-position 
;				(vtex-inst-region inst))))
;		(setq inst (vtex-inst-at to nil nil nil 'vtex-inst-envp))
;		(if inst
;		    (setq to (extent-end-position 
;			      (vtex-inst-region inst))))
		
;		(vtex-undecorate-region from to)
;		(vtex-parse-region from to)
;		(detach-extent vtex-auto-parse-ext)
;		))))))))




;;; Removing Decoration  

(defun vtex-undecorate-inst (inst)
  "Remove all extents belonging to INST."
  (vtex-reduce
   (lambda (ext unused)
     (if (extent-live-p ext)
	 (delete-extent ext)))
   (vtex-inst-extents inst)))

(defun vtex-undecorate-region (from to)
  "Remove all extents created by decoration which are
in the given region and which don't belong to a locked
instance."
  (map-extents
   (lambda (ext arg) 
     (let ((inst (extent-property ext 'vtex-inst)))
       (if (not (vtex-get-inst-prop inst 'locked))
	   (vtex-undecorate-inst inst)))
     nil)
   (current-buffer) from to nil 
   'start-and-end-in-region 'vtex-inst-region))

(defun vtex-undecorate-buffer ()
  "Unconditionally delete all extents created by VTEX in buffer."
  (map-extents
   (lambda (ext arg) 
     (delete-extent ext)
     nil)
   (current-buffer) nil nil nil 
   'start-and-end-in-region 'vtex-inst))
