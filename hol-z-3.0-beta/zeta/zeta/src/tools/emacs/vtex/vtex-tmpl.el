;; TEMPLATES AND DECORATION
;; $Id: vtex-tmpl.el,v 1.6 1998/12/15 18:23:45 wg Exp $ 

(provide 'vtex-tmpl)
(require 'vtex-base)
(require 'vtex-faces)

;;; ------------------------------------------------------------------------
;;; TEMPLATES


;;; Types of Templates and Instances

(defabstype vtex-tmpl-type
  (vtex-tmpl-env 
   vtex-tmpl-name     
   vtex-tmpl-argc
   vtex-tmpl-decorate
   vtex-tmpl-post-decorate
   vtex-tmpl-prop
   vtex-tmpl-math-env
   vtex-tmpl-separator)
  (vtex-tmpl-cmd
   vtex-tmpl-name
   vtex-tmpl-argc
   vtex-tmpl-decorate
   vtex-tmpl-post-decorate
   vtex-tmpl-prop)
  "The type of templates.

There are several predefined functions to create templates:
this type represents the raw interface usually not of interest
to the user.

vtex-tmpl-name is a string representing an environment name or 
command name (in the latter case, inclusive of the command token \\). 

vtex-tmpl-argc is the number of TeX argument groups expected by the
\\begin{...} command or by the plain command.

vtex-tmpl-decorate is a function (lambda (INST)), where 
INST is an instance of a template as described below. It usually creates
extents to decorate INST in the current buffer. vtex-tmpl-post-decorate
is a function (lambda (INST)) which is called after vtex-tmpl-decorate.

vtex-tmpl-prop is a property list belonging to the template.

vtex-tmpl-math-env, if non-nil, specifies that inside of this
environment math templates are active.

vtex-tmpl-separator, if non-nil, specifies a token which is used
to separate paragraphs of the contents of an environment 
(e.g. a \\item token).")


(defabstype vtex-inst-type
  (vtex-inst-env
   vtex-inst-tmpl
   vtex-inst-prop
   vtex-inst-region
   vtex-inst-opt
   vtex-inst-spaces
   vtex-inst-args
   vtex-inst-begin
   vtex-inst-end
   vtex-inst-paragraphs
   vtex-inst-separators)
  (vtex-inst-cmd
   vtex-inst-tmpl
   vtex-inst-prop
   vtex-inst-region
   vtex-inst-opt
   vtex-inst-spaces
   vtex-inst-args
   vtex-inst-tok)
"The type of instances of templates.

vtex-inst-tmpl is the template this instance is derived from.
All other components are either ranges or lists of
such ranges. A range is either a pair of positions,
`(FROM . TO)'  or an extent. Positions are created
initially be the template parser; the decoration functions
turn them into an extent, if they set an extent at the given position.

For an environment, the ranges stored in an instance are 
defined as follows:

\\begin{env}[opt]{arg1}...{argn}par1 \\sep...\\sep parn\\end{env}
bbbbbbbbbbbooooosaaaas...saaaaspppp xxxx   xxxx ppppeeeeeeeee
rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr

For a command, they are given as follows:

\\cmd[opt]{arg1}...{argn}
ccccooooosaaaas...saaaas
rrrrrrrrrrrrrrrrrrrrrrrr


Hereby, 's' is a member of vtex-inst-spaces, 'o' is a member of
vtex-insts-opts, 'a' is a member of vtex-inst-args, 'b' is
vtex-inst-begin, 'e' is vtex-inst-end, 'c' is vtex-inst-tok, 'p' is
a member of vtex-inst-paragraphs, 'x' a member of vtex-inst-separators,
and 'r' is vtex-inst-region. For lists (vtex-inst-spaces,
vtex-inst-args, vtex-inst-paragraphs and vtex-inst-separators), 
the contiguous ranges are stored in reverse order of
their textual appearence. Note that the TeX group braces 
are considered as whitespace, but not the LaTeX option braces. Between
the arguments, additional whitespace may be present.")


(defsubst vtex-get-tmpl-prop (tmpl prop)
  "Get the property PROP of TMPL."
  (plist-get (vtex-tmpl-prop tmpl) prop))

(defsubst vtex-set-tmpl-prop (tmpl prop value)
  "Set the property PROP of TMPL to VALUE."
  (vtex-tmpl-prop! tmpl (plist-put (vtex-tmpl-prop tmpl) prop value)))

(defsubst vtex-remove-tmpl-prop (tmpl prop)
  "Remove the property PROP of TMPL."
  (vtex-tmpl-prop! tmpl (plist-remprop (vtex-tmpl-prop tmpl) prop)))


(defsubst vtex-get-inst-prop (inst prop)
  "Get the property PROP of INST."
  (plist-get (vtex-inst-prop inst) prop))

(defsubst vtex-set-inst-prop (inst prop value)
  "Set the property PROP of INST to VALUE."
  (vtex-inst-prop! inst (plist-put (vtex-inst-prop inst) prop value)))

(defsubst vtex-remove-inst-prop (inst prop)
  "Remove the property PROP of INST."
  (vtex-inst-prop! inst (plist-remprop (vtex-inst-prop inst) prop)))



;;; The Template Tables

(defvar vtex-tmpls (make-hashtable 100 'equal)
  "Global variable holding the hash table of templates.
Entries in the table are hashed according to a command or
environment name.
See functions `vtex-def-....' how to add templates to table.")

(defvar vtex-math-tmpls (make-hashtable 100 'equal)
  "Global variable holding the hash table of templates used
in math mode. Entries in the table are hashed according to a command or
environment name.
See functions `vtex-def-....' how to add templates to table.")


(defsubst vtex-add-tmpl (table tmpl)
  "Add template TMPL to TABLE."
  (puthash (vtex-tmpl-name tmpl) tmpl table)
  (if (eq table vtex-tmpls)
      (setq vtex-tmpls-rex nil)
    (if (eq table vtex-math-tmpls)
	(setq vtex-math-tmpls-rex nil))))
	
(defsubst vtex-search-tmpl (table name)
  "Search for a template named NAME in TABLE."
  (gethash name table))



;;; Working with Template Instances

(defun vtex-insert-skeleton (tmpl &optional opt args text)
  "Creates skelton text of template TMPL and inserts it in
the current buffer at point.
Optional OPT is an option, ARGS is a list of strings to insert as arguments,
optional TEXT a string to be inserted as contents for
environment templates. Point is placed at the first
position for which an argument or a text is not given;
if all are given, at the end of the skeleton.

Note that this function does not create an vtex-inst itself,
which instead is created asynchronously by the autoparser." 
  (let (pos (argc (vtex-tmpl-argc tmpl)))
    (if (vtex-tmpl-envp tmpl)
	(insert-string (concat vtex-tok-begin vtex-tok-bgroup
			       (vtex-tmpl-name tmpl) vtex-tok-egroup))
      (insert-string (vtex-tmpl-name tmpl)))
    (if opt (insert-string opt))
    (while (> argc 0)
      (if args
	  (progn
	    (insert-string (concat vtex-tok-bgroup (car args)
				   vtex-tok-egroup))
	    (setq args (cdr args)))
	(insert-string vtex-tok-bgroup)
	(if (not pos) (setq pos (point)))
	(insert-string vtex-tok-egroup))
      (setq argc (- argc 1)))
    (if (vtex-tmpl-envp tmpl)
	(progn
	  (insert-string "\n")
	  (if text 
	      (insert-string text)
	    (if (not pos) (setq pos (point))))
	  (insert-string "\n")
	  (insert-string (concat vtex-tok-end vtex-tok-bgroup
				 (vtex-tmpl-name tmpl) vtex-tok-egroup))))
    (if pos (goto-char pos))))



(defun vtex-inst-at (pos &optional obj before at-flag pred)
  "Find an instance at POS. See `extent-at' for the meaning of OBJ and 
AT-FLAG. If BEFORE is given, it must be an
instance, and the region covered by the returned instance 
preceeds the region of BEFORE in the display order. 
Effectively, any returned instance is the innermost one covering the
region of BEFORE, with its start position nearest to POS.
If PRED is given, it must be a function (lambda (INST)),
which will be `t' for the returned instance; instance candidates
satisfying PRED are tried innermost-out."
  ;; the display order:
  ;; xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
  ;;    xxxxxxxxxxxxxxxxxxxxxxxxxx
  ;;    xxxxxxxxxxxxxxxxxxxxxx
  ;;    xxxxxxxxxxxxxxx
  (let ((ext (and before (vtex-inst-region before))) 
	 (cont t)
	 inst)
    (while cont
      (setq ext (extent-at pos obj 'vtex-inst-region ext at-flag))
      (if ext
	  (progn
	    (setq inst (extent-property ext 'vtex-inst))
	    (if (and pred (not (funcall pred inst)))
		;; this one isn't accepted
		(setq inst nil)
	      ;; this one is OK
	      (setq cont nil)))
	;; no more candidates
	(setq cont nil)))
    inst))
    
(defun vtex-extent-at (pos &optional obj at-flag pred)
  "Find an extent at POS which has attached a 'vtex-inst and which fulfills
PRED. See extent-at for the meaning of OBJ and AT-FLAG. PRED
is a function (lambda (EXT)). Extents at POS are tried in display order 
unless one is found satisfying PRED."
  (let ((ext (extent-at pos obj 'vtex-inst nil at-flag)))
    (if pred
	(while (and ext (not (funcall pred ext)))
	  (setq ext (extent-at pos obj 'vtex-inst ext at-flag))))
    ext))


(defun vtex-inst-extents (inst)
  "Return all extents associated with INST."
  (if (vtex-inst-envp inst)
      (cons
       (vtex-inst-region inst)
       (cons
	(vtex-inst-begin inst)
	(cons 
	 (vtex-inst-end inst)
	 (append
	  (if (vtex-inst-opt inst)
	      (list (vtex-inst-opt inst))
	    nil)
	  (vtex-inst-separators inst)
	  (vtex-inst-spaces inst)
	  (vtex-inst-args inst)
	  (vtex-inst-paragraphs inst)
	  (vtex-get-inst-prop inst 'vtex-extra-extents)))))
    (cons
     (vtex-inst-region inst)
     (cons
      (vtex-inst-tok inst)
      (append
       (if (vtex-inst-opt inst)
	   (list (vtex-inst-opt inst))
	 nil)
       (vtex-inst-spaces inst)
       (vtex-inst-args inst)
       (vtex-get-inst-prop inst 'vtex-extra-extents))))))
    


;;; ------------------------------------------------------------------------
;;; BASIC TEMPLATES

;;; Basic Decoration Functions

(defun vtex-decorate-phantom (inst ranges &optional moreprops)
  ;; Decorate RANGES as phantoms; return list of extents created.
  (mapcar 
   (lambda (range)
     (let ((ext (make-extent (car range) (cdr range))))
       (set-extent-property ext 'duplicable nil)
       (set-extent-property ext 'invisible t)
       (set-extent-property ext 'vtex-phantom t)
       (set-extent-property ext 'start-open t)
       (set-extent-property ext 'vtex-inst inst)
       (set-extent-property ext 'vtex-markup t)
       (set-extent-properties ext moreprops)
       ext))
   ranges))

(defun vtex-decorate-markup (inst face range &optional moreprops)
  ;; Decorate RANGE to be displayed as an atomic markup. 
  ;; Return the created extent.
  (if t ; vtex-show-markup
      (let ((ext (make-extent (car range) (cdr range))))
	(set-extent-property ext 'duplicable nil)
	(set-extent-property ext 'face face)
	(set-extent-property ext 'vtex-atomic t)
	(set-extent-property ext 'start-open t)
	(set-extent-property ext 'end-open t)
	(set-extent-property ext 'vtex-inst inst)
	(set-extent-property ext 'vtex-markup t)
	(set-extent-properties ext moreprops)
	ext)
    (car (vtex-decorate-phantom inst (list range) moreprops))))


(defun vtex-decorate-face (inst face ranges &optional moreprops)
  ;; Decorate RANGES to be displayed under FACE. Return list of 
  ;; created extents.
  (mapcar
   (lambda (range)
     (let ((ext (make-extent (car range) (cdr range))))
       (set-extent-property ext 'duplicable nil)
       (set-extent-property ext 'face face)
       (set-extent-property ext 'end-closed t)
       (set-extent-property ext 'vtex-inst inst)
       ;; (set-extent-property ext 'priority 100)
       (set-extent-properties ext moreprops)
       ext))
   ranges))

(defsubst vtex-decorate-inst-region (inst range &optional moreprops)
  ;; Decorate RANGE to be the instance region. Return created extent.
  (let ((ext (make-extent (car range) (cdr range))))
    (set-extent-property ext 'duplicable nil)
    (set-extent-property ext 'vtex-inst inst)
    (set-extent-property ext 'vtex-inst-region t)
    (set-extent-properties ext moreprops)
    (set-extent-properties ext
			   (vtex-get-tmpl-prop (vtex-inst-tmpl inst) 
					       'vtex-inst-region-props))
    ext))

(defsubst vtex-decorate-some (inst range &optional moreprops)
  ;; Decorate RANGE in some way.
  (let ((ext (make-extent (car range) (cdr range))))
    (set-extent-property ext 'duplicable nil)
    (set-extent-property ext 'vtex-inst inst)
    (set-extent-properties ext moreprops)
    ext))


;;; Template for General Commands

(defun vtex-def-command (name face markupface begin end 
                         &optional post-decorate props math)
  "*Define a template describing a one-argument command with
specific decoration of markups.
NAME is the name of the command,
FACE describes how its argument should be displayed.
BEGIN and END are characters or strings to be displayed under MARKUPFACE for 
the markup.

If POST-DECORATE is given, it must be a function (lambda (INST))
which is called after an instance of the template is created.

If optional PROPS is given, it must be a property list which will 
be attached to the template.

If optional MATH is `nil', define it
only for text mode. If it is `t', define it
only for math mode. Otherwise define it both for
text and math mode.
"
  (let* ((markup-begin
	  (vtex-special-face markupface `(("\\" . ,begin))))
	 (markup-end
	  (vtex-special-face markupface `(("}" . ,end))))
	 (tmpl (vtex-tmpl-cmd name 1 'vtex-decorate-command post-decorate
			      (plist-put 
			       (plist-put 
				(plist-put props 
					   'face face)
				'markup-begin markup-begin)
			       'markup-end markup-end)))
	 )
    (if math
	(if (eq math t)
	    (vtex-add-tmpl vtex-math-tmpls tmpl)
	  (vtex-add-tmpl vtex-tmpls tmpl)
	  (vtex-add-tmpl vtex-math-tmpls tmpl))
      (vtex-add-tmpl vtex-tmpls tmpl))))

(defun vtex-decorate-command (inst)
  ;; Decoration function used for a general command.
  (let* ((tmpl (vtex-inst-tmpl inst))
	 (face (vtex-get-tmpl-prop tmpl 'face))
	 (markup-begin (vtex-get-tmpl-prop tmpl 'markup-begin))
	 (markup-end (vtex-get-tmpl-prop tmpl 'markup-end))
	 )
    (if (not face) (setq face 'default))
    (vtex-inst-region! inst
		      (vtex-decorate-inst-region inst 
						 (vtex-inst-region inst)))
    (let ((endmarkup (car (vtex-inst-spaces inst)))
					; the car element 
					; (the egroup of the argument)
					; is used for the end of markup
	  (spaces (cdr (vtex-inst-spaces inst))))
      (setq spaces (vtex-decorate-phantom inst spaces))
      (vtex-inst-tok! inst
		     (vtex-decorate-markup inst 
					  markup-begin
					  (vtex-inst-tok inst)))
      (setq endmarkup
	    (vtex-decorate-markup inst markup-end
				  endmarkup))
      (vtex-inst-spaces! inst (cons endmarkup spaces))
      (vtex-inst-args! inst
		      (vtex-decorate-face inst face 
					  (vtex-inst-args inst))))))


;;; Template for Figures

(defun vtex-def-figure (name face glyphfun
			     &optional post-decorate props math) 
  "Define a template describing a one-argument command which
is displayed as a figure displaying a glyph.  
NAME is the name of the command,
FACE describes how the name of the figure is displayed.
The name thereby is the argument of the command.
GLYPHFUN is a function which gets passed the picture
name and must return a glyph for the contents of the figure.

If POST-DECORATE is given, it must be a function (lambda (INST))
which is called after an instance of the template is created.

If optional PROPS is given, it must be a property list which will 
be attached to the template.
If optional MATH is `nil', define it
only for text mode. If it is `t', define it
only for math mode. Otherwise define it both for
text and math mode.
"
  (let ((tmpl (vtex-tmpl-cmd name 1 'vtex-decorate-figure post-decorate
			     (plist-put 
			      (plist-put props 'face face)
			      'glyphfun glyphfun)
			     )))
    (if math
	(if (eq math t)
	    (vtex-add-tmpl vtex-math-tmpls tmpl)
	  (vtex-add-tmpl vtex-tmpls tmpl)
	  (vtex-add-tmpl vtex-math-tmpls tmpl))
      (vtex-add-tmpl vtex-tmpls tmpl))))

(defun vtex-decorate-figure (inst)
  ;; Decoration function used for figures
  (let* ((tmpl (vtex-inst-tmpl inst))
	 (face (vtex-get-tmpl-prop tmpl 'face))
	 (glyphfun (vtex-get-tmpl-prop tmpl 'glyphfun))
	 )
    (if (not face) (setq face 'default))
    (vtex-inst-region! inst
		      (vtex-decorate-inst-region inst 
						 (vtex-inst-region inst)))
    (vtex-inst-args! inst
		     (vtex-decorate-face inst face 
					 (vtex-inst-args inst)))
    (vtex-inst-tok! inst
		    (vtex-decorate-markup inst
					  vtex-style-markup-begin-face
					  ;; FIXME: introduce own markup 
					  (vtex-inst-tok inst)))
    (let* ((arg (extent-string (car (vtex-inst-args inst))))
	   (replace (vector " " (funcall glyphfun arg)))
	   (markup (vtex-special-face face `(("}" . ,replace))))
	   (endmarkup (car (vtex-inst-spaces inst)))
					; the car element 
					; (the egroup of the argument)
					; is used for the end of markup
	   (spaces (cdr (vtex-inst-spaces inst))))
      (setq spaces (vtex-decorate-phantom inst spaces))
      (setq endmarkup (vtex-decorate-markup inst markup endmarkup))
      (vtex-inst-spaces! inst (cons endmarkup spaces))
      )))


;;; Template for Style Commands

(defvar vtex-style-markup-begin-face nil
  ;; Special face used to display command begin markups, 
  ;; remapping `\\'.
  )

(defvar vtex-style-markup-end-face nil
  ;; Special face used to display command end markups, 
  ;; remapping `}'.
  )

(defun vtex-def-style-markup (face begin end)
  "*Set the begin and end markups to be used for style commands.
BEGIN and END are characters or strings to be displayed under FACE for 
the markup."
  (setq vtex-style-markup-begin-face 
	(vtex-special-face face `(("\\" . ,begin))))
  (setq vtex-style-markup-end-face 
	(vtex-special-face face `(("}" . ,end)))))


(defun vtex-decorate-style (inst)
  ;; Decoration function used for a style command.
  (let* ((tmpl (vtex-inst-tmpl inst))
	 (face (vtex-get-tmpl-prop tmpl 'face)))
    (if (not face) (setq face 'default))
    (vtex-inst-region! inst
		      (vtex-decorate-inst-region inst 
						 (vtex-inst-region inst)))
    (let ((endmarkup (car (vtex-inst-spaces inst)))
					; the car element 
					; (the egroup of the argument)
					; is used for the end of markup
	  (spaces (cdr (vtex-inst-spaces inst))))
      (setq spaces (vtex-decorate-phantom inst spaces))
      (vtex-inst-tok! inst
		     (vtex-decorate-markup inst 
					  vtex-style-markup-begin-face
					  (vtex-inst-tok inst)))
      (setq endmarkup
	    (vtex-decorate-markup inst vtex-style-markup-end-face
				 endmarkup))
      (vtex-inst-spaces! inst (cons endmarkup spaces))
      (vtex-inst-args! inst
		      (vtex-decorate-face inst face 
					  (vtex-inst-args inst))))))

(defun vtex-def-style (name face &optional post-decorate props math)
  "*Define a template describing a style command such
as \\emph{...}. NAME is the name of the command,
FACE describes how its argument should be displayed.

If POST-DECORATE is given, it must be a function (lambda (INST))
which is called after an instance of the template is created.

If optional PROPS is given, it must be a property list which will 
be attached to the template.

If optional MATH is `nil', define it
only for text mode. If it is `t', define it
only for math mode. Otherwise define it both for
text and math mode.
"
  (let ((tmpl (vtex-tmpl-cmd name 1 'vtex-decorate-style post-decorate
			     (plist-put props 'face face))))
    (if math
	(if (eq math t)
	    (vtex-add-tmpl vtex-math-tmpls tmpl)
	  (vtex-add-tmpl vtex-tmpls tmpl)
	  (vtex-add-tmpl vtex-math-tmpls tmpl))
      (vtex-add-tmpl vtex-tmpls tmpl))))

;;; Template for Sectioning Commands

(defvar vtex-section-markup-begin-face nil
  ;; Special face used to display command begin markups, 
  ;; remapping `\\'.
  )

(defvar vtex-section-markup-end-face nil
  ;; Special face used to display command end markups, 
  ;; remapping `}'.
  )

(defun vtex-def-section-markup (face begin end)
  "*Set the begin and end markups to be used for style commands.
BEGIN and END are characters or strings to be displayed under FACE for 
the markup."
  (setq vtex-section-markup-begin-face 
	(vtex-special-face face `(("\\" . ,begin))))
  (setq vtex-section-markup-end-face 
	(vtex-special-face face `(("}" . ,end)))))


(defun vtex-decorate-section (inst)
  ;; Decoration function used for a style command.
  (let* ((tmpl (vtex-inst-tmpl inst))
	 (face (vtex-get-tmpl-prop tmpl 'face)))
    (if (not face) (setq face 'default))
    (vtex-inst-region! inst (vtex-decorate-inst-region 
			     inst (vtex-inst-region inst)))
    (let ((endmarkup (car (vtex-inst-spaces inst)))
					; the car element 
					; (the egroup of the argument)
					; is used for the end of markup
	  (spaces (cdr (vtex-inst-spaces inst))))
      (setq spaces (vtex-decorate-phantom inst spaces))
      (vtex-inst-tok! inst
		     (vtex-decorate-markup inst 
					  vtex-section-markup-begin-face
					  (vtex-inst-tok inst)))
      (setq endmarkup
	    (vtex-decorate-markup inst vtex-section-markup-end-face
				 endmarkup))
      (vtex-inst-spaces! inst (cons endmarkup spaces))
      (vtex-inst-args! inst
		      (vtex-decorate-face inst face 
					  (vtex-inst-args inst))))))

(defun vtex-def-section (name face &optional post-decorate props)
  "*Define a template describing a sectioning command such
as \\section{...}. NAME is the name of the command,
FACE describes how its argument should be displayed.

If POST-DECORATE is given, it must be a function (lambda (INST))
which is called after an instance of the template is created.

If optional PROPS is given, it must be a property list which will 
be attached to the template."
  (vtex-add-tmpl vtex-tmpls 
		 (vtex-tmpl-cmd name 1 'vtex-decorate-section post-decorate
				(plist-put props 'face face))))



;;; Template for Plain Environments

(defvar vtex-env-markup-begin-face nil
  ;; Special face used to display environment begin markups, 
  ;; remapping `\\'.
  )

(defvar vtex-env-markup-end-face nil
  ;; Special face used to display environment end markups, 
  ;; remapping `\\'.
  )

(defun vtex-def-env-markup (face begin end)
  "*Set the begin and end markups to be used for environments.
BEGIN and END are characters or strings to be displayed under FACE for 
the markup."
  (setq vtex-env-markup-begin-face 
	(vtex-special-face face `(("\\" . ,begin)
				 ("\$" . ,begin))))
  (setq vtex-env-markup-end-face 
	(vtex-special-face face `(("\\" . ,end)
				 ("\$" . ,end)))))


(defun vtex-decorate-env (inst)
  ;; decoration function used for a plain environment template instance.
  (let* ((tmpl (vtex-inst-tmpl inst))
	 (face (vtex-get-tmpl-prop tmpl 'face)))
    (if (not face) (setq face 'default))
    (vtex-inst-region! 
     inst
     (vtex-decorate-inst-region inst (vtex-inst-region inst)))
    (vtex-inst-spaces! inst
		       (vtex-decorate-phantom inst (vtex-inst-spaces inst)))
    (vtex-inst-begin! inst
		      (vtex-decorate-markup inst vtex-env-markup-begin-face
					    (vtex-inst-begin inst)))
    (vtex-inst-end! inst
		   (vtex-decorate-markup inst vtex-env-markup-end-face
					    (vtex-inst-end inst)))
    (vtex-inst-paragraphs! 
     inst
     (vtex-decorate-face inst face (vtex-inst-paragraphs inst)))
    ))

(defun vtex-def-env (name face 
			  &optional math mathenv post-decorate props)
  "*Define a template describing a plain environment NAME whose contents
shall be displayed with FACE. If optional MATH is `nil', define it
only for text mode. If it is `t', define it
only for math mode. Otherwise define it both for
text and math mode. If optional MATHENV is non-nil, then the contents
of this environment is processed in math mode.

If POST-DECORATE is given, it must be a function (lambda (INST))
which is called after an instance of the template is created.

If optional PROPS is given, it must be a property list which will 
be attached to the template."

  (let ((tmpl (vtex-tmpl-env name 0 
			     'vtex-decorate-env post-decorate
			     (plist-put 
			      (if mathenv 
				  (append vtex-electric-props props)
				props)
			      'face face)
			     mathenv
			     nil)))
    (if math
	(if (eq math t)
	    (vtex-add-tmpl vtex-math-tmpls tmpl)
	  (vtex-add-tmpl vtex-tmpls tmpl)
	  (vtex-add-tmpl vtex-math-tmpls tmpl))
      (vtex-add-tmpl vtex-tmpls tmpl))))



;;; Template for Special Symbols

(defun vtex-decorate-special (inst)
  ;; decoration function used for special symbols. 
  (let* ((tmpl (vtex-inst-tmpl inst))
	 (face (vtex-get-tmpl-prop tmpl 'face)))
    (if (not face) (setq face 'default))
    (vtex-inst-region! 
     inst
     (vtex-decorate-inst-region inst (vtex-inst-region inst)))
    (vtex-inst-tok! 
     inst
     (car 
      (vtex-decorate-face inst face  
			  (list (vtex-inst-tok inst))
			  '((vtex-atomic . t)
			    ;; (priority . 200)
			    (end-open . t) 
			    (vtex-markup . t) 
					;@? makes symbols disappear completely
					; on deletion. if not set, 
					; backward-deleting e.g.
					; at the end of "\forall" yields 
					; "\foral"
			    (start-open . t)))))))

(defun vtex-def-sym (token face obj)
 "Define a template describing a command TOKEN with no arguments
which shall be substituted by displaying OBJ under FACE when in math mode.
OBJ may be a character, a string, or a glyph, and is displayed with FACE."
 (vtex-def-special token face obj t))

(defun vtex-def-special (token face obj 
			      &optional math post-decorate props)
 "Define a template describing a command TOKEN with no arguments
which shall be substituted by displaying OBJ under FACE.
OBJ may be a character, a string, or a glyph, displayed with FACE. 
If optional MATH is `nil', define it only for text mode.
If it is `t', define it only for math mode. Otherwise
define it both for text and math mode.
 
If POST-DECORATE is given, it must be a function (lambda (INST))
which is called after an instance of the template is created.

If optional PROPS is given, it must be a property list which will 
be attached to the template."

;; since the creation of specials is so expansive, we actually
;; do the job lazily

  (setq vtex-specials-list 
	(cons (list token face obj math
		    post-decorate props) vtex-specials-list)))

(defvar vtex-specials-list nil)

(defun vtex-update-specials ()
  "Calculate specials of template table."
  (if vtex-specials-list
      (let ((leng (length vtex-specials-list)) (cnt 0)
	    elem name face obj math post-decorate props)
	(while vtex-specials-list
	  (setq elem (car vtex-specials-list)
		vtex-specials-list (cdr vtex-specials-list))
	  (message "Initializing VTeX symbols (%s%%)" (/ (* cnt 100) leng))
	  (setq cnt (+ cnt 1))
	  (setq name (nth 0 elem)
		face (nth 1 elem)
		obj  (nth 2 elem)
		math (nth 3 elem)
		post-decorate (nth 4 elem)
		props (nth 5 elem))
	  (let ((tmpl (vtex-tmpl-cmd 
		       name 
		       0 'vtex-decorate-special post-decorate
		       (plist-put props 'face
				  (vtex-special-face 
				   face 
				   (list (cons (char-to-string (aref name 0)) 
					       obj)))))))
	    (if math
		(if (eq math t)
		    (vtex-add-tmpl vtex-math-tmpls tmpl)
		  (vtex-add-tmpl vtex-tmpls tmpl)
		  (vtex-add-tmpl vtex-math-tmpls tmpl))
	      (vtex-add-tmpl vtex-tmpls tmpl)))))))


;; Template for list-like environments

(defun vtex-def-list-env (name face labelfun labelface
			       &optional post-decorate props)
  "*Define a template describing a list environment such as itemize
or enumerate with given NAME whose contents shall be displayed with 
FACE. 

LABELFUN is a function (lambda (NUMBER)) which, given a number of an
item (starting at 1), should return a string or a glyph representing
the label for this item which is displayed under LABELFACE.

If POST-DECORATE is given, it must be a function (lambda (INST))
which is called after an instance of the template is created.

If optional PROPS is given, it must be a property list which will 
be attached to the template."

  (let ((tmpl (vtex-tmpl-env name 0 
			     'vtex-decorate-list-env post-decorate
			     (plist-put 
			      (plist-put 
			       (plist-put props 'face face)
			       'labelfun labelfun)
			      'labelface labelface)
			     nil
			     "\\item")))
    (vtex-add-tmpl vtex-tmpls tmpl)))

(defvar vtex-list-env-cache (make-hashtable 40 'equal)
  "Hash table indexed by pairs '(name . num) holding special
faces for labels of list environments.")

(defun vtex-get-list-env-face (name num labelfun labelface)
  "Get special face for displaying label."
  (let ((face (gethash (cons name num) vtex-list-env-cache)))
    (if (not face)
	(progn
	  (setq face (vtex-special-face 
		      labelface
		      `(("\\" . ,(funcall labelfun num)))))
	  (puthash (cons name num) face vtex-list-env-cache)))
    face))

(defun vtex-decorate-list-env (inst)
  ;; decoration function used for a list environment instances.
  (let* ((tmpl (vtex-inst-tmpl inst))
	 (face (vtex-get-tmpl-prop tmpl 'face))
	 (labelfun (vtex-get-tmpl-prop tmpl 'labelfun))
	 (labelface (vtex-get-tmpl-prop tmpl 'labelface))
	 (seps (reverse (vtex-inst-separators inst)))
	 (sepcnt 1) (sepexts nil) 
	 (name (vtex-tmpl-name tmpl)))
    (if (not face) (setq face 'default))
    (vtex-inst-region! 
     inst
     (vtex-decorate-inst-region inst (vtex-inst-region inst)))
    (vtex-inst-spaces! inst
		       (vtex-decorate-phantom inst (vtex-inst-spaces inst)))
    (vtex-inst-begin! inst
		      (vtex-decorate-markup inst vtex-env-markup-begin-face
					    (vtex-inst-begin inst)))
    (vtex-inst-end! inst
		   (vtex-decorate-markup inst vtex-env-markup-end-face
					    (vtex-inst-end inst)))
    (vtex-inst-paragraphs! 
     inst
     (vtex-decorate-face inst face (vtex-inst-paragraphs inst)))
    (while seps
      (setq sepexts (cons 
		     (vtex-decorate-markup
		      inst
		      (vtex-get-list-env-face name sepcnt 
					      labelfun labelface)
		      (car seps)
		      '((vtex-markup-optional . t)))
		     sepexts)
	    seps (cdr seps)
	    sepcnt (+ sepcnt 1)))
    (vtex-inst-separators! inst sepexts)))



;;; ------------------------------------------------------------------------
;;; Z TEMPLATES (AND MATH)


;; Parameters

(defvar vtex-zbox-width 60)
(defvar vtex-zbox-before-name-width 2)
(defvar vtex-zbox-where-width 15)


(defvar vtex-zbox-ruler-face nil
  ;; Face used for Z box rulers
  )

(defvar vtex-zbox-type-face nil
  ;; Face used for Z box type keywords
  )

(defvar vtex-zbox-vline-ruler nil
  ;; Ruler used for vertical lines
  )

(defvar vtex-zbox-hline-ruler nil
  ;; Ruler used for horicontal lines
  )

(defvar vtex-zbox-ucorner-ruler nil
  ;; Ruler used for upper corners
  )

(defvar vtex-zbox-mcorner-ruler nil
  ;; Ruler used for middle corners
  )

(defvar vtex-zbox-lcorner-ruler nil
  ;; Ruler used for lower corners
  )

(defvar vtex-zbox-vline-glyph nil
  ;; Glyph used for vertical lines
  )


;; State Variables

(defvar vtex-zbox-end-face nil
  ;; Markup for the end of a Z box:
  ;;   \------------------------------------ 
  ;; remapping `\\' 
  )

(defvar vtex-zbox-where-face nil
  ;; Markup for the \\where of a Z box:
  ;;   |-----------------
  ;; remapping `\\' 
  )


(defvar vtex-zbox-named-begin-cache nil
  ;; Hashtable of special faces used for the beginning of named Z boxes:
  ;;   /---- KEY
  ;; indexed by KEY (which may be nil)
  ;; it remaps `\\' to the hline rulers and `b' (if KEY is not nil)
  ;; to the type key
  )

(defvar vtex-zbox-unnamed-begin-cache nil
  ;; Hashtable of special face used for the beginning of an unnamed Z box:
  ;;   /-----KEY ------------------------------- 
  ;; indexed by KEY (which may be nil)
  ;; it remaps `\\' to the first block of hline rulers,
  ;; `b' (if KEY is not nil) to the type key and `e' to the
  ;; remaining hline rulers.
  )

(defvar vtex-zbox-hline-cache nil
  ;; Hashtable of special faces for hlines:
  ;; ------------------------...
  ;; indexed by length, remapping `}' 
  )


(defun vtex-def-zbox-rulers (face ucorner lcorner mcorner vline hline)
  "*Define the rulers to be used for Z boxes. FACE is the face
where they are taken from. UCORNER is an upper corner ruler,
MCORNER is a middle corner ruler (used for \\where),
LCORNER is a lower corner ruler, VLINE is a vertical line ruler,
and HLINE an horicontal line ruler."
  (setq vtex-zbox-end-face
	(vtex-special-face 
	 face
	 `(("\\" . ,(concat (make-string 1 lcorner)
			    (make-string vtex-zbox-width hline))))))
  (setq vtex-zbox-where-face
	(vtex-special-face 
	 face
	 `(("\\" . ,(concat (make-string 1 mcorner)
			    (make-string vtex-zbox-where-width hline))))))
  (setq vtex-zbox-vline-glyph (make-glyph (make-string 1 vline)))
  (set-glyph-face vtex-zbox-vline-glyph face)
  (setq vtex-zbox-named-begin-cache (make-hashtable 40))
  (setq vtex-zbox-unnamed-begin-cache (make-hashtable 40))
  (setq vtex-zbox-hline-cache (make-hashtable 40))
  (setq vtex-zbox-ruler-face face)
  (setq vtex-zbox-hline-ruler hline)
  (setq vtex-zbox-vline-ruler vline)
  (setq vtex-zbox-ucorner-ruler ucorner)
  (setq vtex-zbox-lcorner-ruler lcorner)
  (setq vtex-zbox-mcorner-ruler mcorner)
  )

(defun vtex-def-zbox-type-face (face)
  "*Set the face to be used for type keywords of boxes."
  (setq vtex-zbox-type-face face))





(defun vtex-get-zbox-named-begin-face (&optional typekey)
  ;; Retrieve or create a face for a named Z box begin
  (let ((face (gethash typekey vtex-zbox-named-begin-cache)))
    (if (not face)
	(let ((line (concat (make-string 1 vtex-zbox-ucorner-ruler)
			    (make-string vtex-zbox-before-name-width 
					 vtex-zbox-hline-ruler)
			    " ")))
	  (if (not typekey)
	      (setq face (vtex-special-face 
			  vtex-zbox-ruler-face
			  `(("\\" . ,line))))
	    (let ((glyph (make-glyph (concat typekey " "))))
	      (set-glyph-face glyph vtex-zbox-type-face)
	      (setq face (vtex-special-face 
			  vtex-zbox-ruler-face
			  `(("\\" . ,line)
			    ("{"  . ,glyph))))))
	  (puthash typekey face vtex-zbox-named-begin-cache)))
    face))

(defun vtex-get-zbox-unnamed-begin-face (&optional typekey)
  ;; Retrieve or create a face for an unnamed Z box begin
  (let ((face (gethash typekey vtex-zbox-unnamed-begin-cache)))
    (if (not face)
	(progn
	  (if (not typekey)
	      (let ((line (concat (make-string 1 vtex-zbox-ucorner-ruler)
				  (make-string vtex-zbox-width
					       vtex-zbox-hline-ruler))))
		(setq face (vtex-special-face 
			    vtex-zbox-ruler-face
			    `(("\\" . ,line)))))
	    (let ((line1 (concat (make-string 1 vtex-zbox-ucorner-ruler)
				 (make-string vtex-zbox-before-name-width
					      vtex-zbox-hline-ruler)
				 " "))
		  (glyph (make-glyph typekey))
		  (line2 (concat " "
				 (make-string
				  (max 1
				       (- vtex-zbox-width
					  vtex-zbox-before-name-width
					  (length typekey)
					  1))
				  vtex-zbox-hline-ruler))))
	      (set-glyph-face glyph vtex-zbox-type-face)
	      (setq face (vtex-special-face 
			  vtex-zbox-ruler-face
			  `(("\\" . ,line1)
			    ("{"  . ,glyph)
			    ("}"  . ,line2))))))
	  (puthash typekey face vtex-zbox-unnamed-begin-cache)))
    face))


(defun vtex-get-zbox-hline-face (leng)
  ;; Retrieve or create a face for a horizontal line of LENG.
  (let ((face (gethash leng vtex-zbox-hline-cache)))
    (if (not face)
	(progn
	  (setq face (vtex-special-face
		      vtex-zbox-ruler-face
		      `(("}" . 
			 ,(concat " "
				  (make-string leng vtex-zbox-hline-ruler))))))
	  (puthash leng face vtex-zbox-hline-cache)))
    face))



;; Decoration Functions

(defun vtex-zbox-named-decorate-begin (inst &optional typekey)
  ;; Decorate \begin and argument of a named Z box
  ;; the face for the argument is expected in the property list
  ;; of the template.
  (let ((name-end (car (vtex-inst-spaces inst)))
	(name-leng (- (cdr (car (vtex-inst-args inst)))
		      (car (car (vtex-inst-args inst)))))
	(spaces (cdr (vtex-inst-spaces inst)))
	(face (vtex-get-tmpl-prop (vtex-inst-tmpl inst) 'face)))

    ;; \begin{zbox}
    ;; ^^^^^^^^^^^^
    (vtex-inst-begin! inst
		     (vtex-decorate-markup
		      inst
		      (vtex-get-zbox-named-begin-face typekey)
		      (vtex-inst-begin inst)
		      `((vtex-zbox-hline . t))))

    ;; \begin{zbox}{
    ;;             ^
    (setq spaces (vtex-decorate-phantom inst spaces))

    ;; \begin{schema}{Name
    ;;                ^^^^
    (vtex-inst-args! inst
		    (vtex-decorate-face
		     inst face (vtex-inst-args inst)))

    ;; \begin{schema}{Name}
    ;;                    ^
    (let ((end-leng (max 1
			 (- vtex-zbox-width 
			    name-leng
			    (if typekey (length typekey) 0)
			    vtex-zbox-before-name-width
			    1 ; for spaces
			    ))))
      (setq name-end
	    (vtex-decorate-markup 
	     inst
	     (vtex-get-zbox-hline-face end-leng)
	     name-end
	     `(( vtex-zbox-hline . t))))
      
      (vtex-inst-spaces! inst (cons name-end spaces)))))


(defsubst vtex-zbox-unnamed-decorate-begin 
  (inst &optional typekey)
  ;; Decorate \begin of an unnamed Z box
  ;; \begin{zbox}
  ;; ^^^^^^^^^^^^
  (vtex-inst-begin! inst
		   (vtex-decorate-markup
		    inst
		    (vtex-get-zbox-unnamed-begin-face typekey)
		    (vtex-inst-begin inst)
		    `((vtex-zbox-hline . t)))))



(defsubst vtex-zbox-decorate-end (inst)
  ;; Decorate \end of a Z box
  ;; ... \end{zbox}
  ;;     ^^^^^^^^^
  (vtex-inst-end! inst
		 (vtex-decorate-markup
		  inst
		  vtex-zbox-end-face
		  (vtex-inst-end inst)
		  `((vtex-zbox-hline . t)))))


(defun vtex-zbox-decorate-paragraphs (inst)
  ;; Decorate paragraphs of a Z box
  (let* ((tmpl (vtex-inst-tmpl inst))
	 (face (vtex-get-tmpl-prop tmpl 'face)))
    (vtex-inst-paragraphs! 
     inst
     (vtex-decorate-face inst face (vtex-inst-paragraphs inst)
			 '((vtex-post-parse-function 
			    . vtex-zbox-post-parse))))
    (vtex-inst-separators!
     inst
     (mapcar
      (lambda (range)
	(vtex-decorate-markup
	 inst
	 vtex-zbox-where-face
	 range
	 `((vtex-zbox-hline  . t)
	   (vtex-markup-optional . t)
	   )))
      (vtex-inst-separators inst)))
    ))


(defun vtex-zbox-post-parse (inst from to)
  ;; (vtex-dprint "zbox-post-parse %s %s %s" inst from to)
  (if (< from to)
      (save-excursion
	(goto-char from)
	(let (pos isset onhline ext)
	  (while (search-forward "\n" to t)
	    (setq pos (point))
	    ;;	(vtex-dprint "found newline at %s" pos)
	    (setq isset 
		  (vtex-extent-at 
		   pos nil 'before
		   (lambda (ext) 
		     (and 
		      (extent-property ext 'vtex-zbox-vline)
		      (eq (extent-property ext 'vtex-inst) inst))))
		  onhline 
		  (vtex-extent-at 
		   pos nil nil
		   (lambda (ext) 
		     (and 
		      (extent-property ext 'vtex-zbox-hline)
		      (eq (extent-property ext 'vtex-inst) inst)))))
	    (if (or isset onhline)
		(if (and isset onhline)
		    ;; remove this vline
		    (detach-extent isset)
		  ;; do nothing
		  nil)
	      ;; (vtex-dprint "decorating")
	      (setq ext
		    (vtex-decorate-some 
		     inst 
		     (cons (- pos 1) pos)
		     `((end-glyph . ,vtex-zbox-vline-glyph)
		       ;; (priority . 400)
		       (start-open . t)
		       (vtex-zbox-vline . t))))
	      (vtex-set-inst-prop 
	       inst 'vtex-extra-extents
	       (cons ext 
		     ;; on the fly, garbage collect all detached extents
		     (vtex-reduce
		      (lambda (ext1 res)
			(if (extent-live-p ext1)
			    (if (extent-detached-p ext1)
				(delete-extent ext1)
			      (cons ext1 res))))
		      (vtex-get-inst-prop inst 'vtex-extra-extents)))))
	    )))))


(defun vtex-decorate-zbox-named (inst)
  ;; decoration function used for named Z boxes
  (vtex-inst-region! inst
		    (vtex-decorate-inst-region inst (vtex-inst-region inst)))
  (vtex-zbox-named-decorate-begin 
   inst 
   (vtex-get-tmpl-prop (vtex-inst-tmpl inst) 'type))
  (vtex-zbox-decorate-end inst)
  (vtex-zbox-decorate-paragraphs inst))

(defun vtex-decorate-zbox-unnamed (inst)
  ;; decoration function used for unnamed Z boxes
  (vtex-inst-region! inst
		    (vtex-decorate-inst-region inst (vtex-inst-region inst)))
  (vtex-zbox-unnamed-decorate-begin 
   inst 
   (vtex-get-tmpl-prop (vtex-inst-tmpl inst) 'type))
  (vtex-zbox-decorate-end inst)
  (vtex-zbox-decorate-paragraphs inst))


(defun vtex-decorate-zbox-axdef (inst)
  ;; decoration function used for open Z boxes such as axdef
  (vtex-inst-region! inst
		    (vtex-decorate-inst-region inst (vtex-inst-region inst)))
  (vtex-inst-spaces! inst
		     (vtex-decorate-phantom inst (vtex-inst-spaces inst)))
  (vtex-inst-begin! inst
		    (vtex-decorate-markup inst vtex-env-markup-begin-face
					  (vtex-inst-begin inst)
					  '((vtex-zbox-hline . t))))
  (vtex-inst-end! inst
		  (vtex-decorate-markup inst vtex-env-markup-end-face
					(vtex-inst-end inst)
					'((vtex-zbox-hline . t))))
  (vtex-zbox-decorate-paragraphs inst))

(defun vtex-def-zbox (name face 
			   &optional type anon nested post-decorate props)
  "*Define a template describing a Z schema-style environment of
name NAME, displayed in a Z box. 
The contents of the environment is displayed with FACE. 
If TYPE is given, it specifies a string such as \"Op\", \"Trans\", etc.
which is used to display the type of the box.
If ANON is non-nil, then the environment takes no argument,
otherwise it takes one argument specifying the name of the Z box.
If NESTED is non-nil, then the environment may be also used inside
of math environments, in particular within other boxes.

If POST-DECORATE is given, it must be a function (lambda (INST))
which is called after an instance of the template is created.

If optional PROPS is given, it must be a property list which will 
be attached to the template."

  (setq props (plist-put (plist-put props 'face face) 'type type))
  (setq props (append vtex-electric-props props))
  (let ((tmpl (if anon
		  (vtex-tmpl-env name 0 'vtex-decorate-zbox-unnamed 
				 post-decorate props 
				 t "\\where")
		(vtex-tmpl-env name 1 'vtex-decorate-zbox-named
			      post-decorate props t "\\where"))))
    (vtex-add-tmpl vtex-tmpls tmpl)
    (if nested (vtex-add-tmpl vtex-math-tmpls tmpl))))


(defun vtex-def-zbox-axdef (name face
				 &optional nested post-decorate props)
  "*Define a template describing a Z axdef-style environment.
The contents of the environment is displayed with FACE. 
If NESTED is non-nil, then the environment may be also used inside
of math environments, in particular within other boxes.

If POST-DECORATE is given, it must be a function (lambda (INST))
which is called after an instance of the template is created.

If optional PROPS is given, it must be a property list which will 
be attached to the template."

  (setq props (plist-put props 'face face))
  (setq props (append vtex-electric-props props))
  (let ((tmpl (vtex-tmpl-env name 0 'vtex-decorate-zbox-axdef
			     post-decorate props t "\\where")))
    (vtex-add-tmpl vtex-tmpls tmpl)
    (if nested (vtex-add-tmpl vtex-math-tmpls tmpl))))



;;; -------------------------------------------------------------------------
;;; MATH LAYOUT

(defvar vtex-space-face nil)
(defvar vtex-crtab-face nil)
(defvar vtex-tab-face nil)
(defvar vtex-tab-str nil)
(defvar vtex-tab-cache nil)

(defun vtex-def-math-layout (crface crobj tabface tabstr 
				    &optional spface spobj)
  "Enable special handling of math layout, and define markups used
for it. This feature substitutes occurences of `\\\\' and `\\\\\\tN'
at the end of a line by the object CROBJ (which might be the empty 
string) displayed under CRFACE. The following line is 
indended by N instances of TABSTR (a string) displayed under TABFACE. 

[NOTE: Because of a bug in XEmacs-20, TABFACE is actually ignored,
and TABSTR is displayed in the default font.]

If optional SPFACE is given, then any consecutive
sequences of spaces will be substituted
by one single instance of SPOBJ under SPFACE."
  (setq vtex-crtab-face (vtex-special-face crface `(("\\" . ,crobj))))
  (setq vtex-tab-face tabface)
  (setq vtex-tab-str tabstr)
  (if (and spface spobj)
      (setq vtex-space-face 
	    (vtex-special-face spface `((" " . ,spobj)
					("~" . ,spobj))))
    (setq vtex-space-face nil))
  (setq vtex-tab-cache (make-hashtable 10))
  (setq vtex-handle-math-layout t)
  (setq vtex-math-tmpls-rex nil)
  )


;; keep this for possible reanimation
;(defvar vtex-math-newline-tmpl
;  (vtex-tmpl-cmd
;   "*math-newline*"
;   0
;   'vtex-math-newline-decorate
;   nil
;   nil)
;  "A special template for handling hard newlines in math mode.")
;(defvar vtex-math-leading-space-tmpl
;  (vtex-tmpl-cmd
;   "*math-space*"
;   0
;   'vtex-math-leading-space-decorate
;   nil
;   nil)
;  "A special template for handling spaces at the beginning of a line
;in math mode.")

(defvar vtex-math-space-tmpl
  (vtex-tmpl-cmd
   "*math-space*"
   0
   'vtex-math-space-decorate
   nil
   nil)
  "A special template for handling spaces in math mode.")

(defvar vtex-math-crtab-tmpl
  (vtex-tmpl-cmd
   "*math-cr-tab*"
   0
   'vtex-math-crtab-decorate
   nil
   nil)
  "A special template for handling CR/TAB sequences in math mode.")


;;; Spaces

(defun vtex-math-space-decorate (inst)
  (vtex-inst-region! 
   inst
   (vtex-decorate-inst-region inst (vtex-inst-region inst)))
  (if vtex-space-face
      (progn
	(vtex-inst-tok! 
	 inst
	 (car 
	  (vtex-decorate-face inst vtex-space-face
			      (list (vtex-inst-tok inst))
			      '((vtex-atomic . t)
				;; (priority . 200)
				(end-open . t) 
				(vtex-markup . nil) 
				(start-open . t)))))
	;; ... remaining spaces as phantoms
	(vtex-inst-spaces!
	 inst
	 (vtex-decorate-phantom inst (vtex-inst-spaces inst)))))
  )
  

;;; CR-TAB Sequences
  
(defun vtex-math-crtab-decorate (inst)
  (vtex-inst-region! 
   inst
   (vtex-decorate-inst-region inst (vtex-inst-region inst)))
  (vtex-inst-tok! 
   inst
   (car 
    (vtex-decorate-face inst vtex-crtab-face
			(list (vtex-inst-tok inst))
			'((vtex-atomic . t)
			  ;; (priority . 200)
			  (end-open . t) 
			  (vtex-crtab . t)
			  (vtex-markup . t) 
			  (start-open . t)))))
  (let ((tabPart (car (vtex-inst-spaces inst)))
	(crPart (car (cdr (vtex-inst-spaces inst))))
	tab indent)
    (setq tab (buffer-substring (+ 1 (car tabPart)) (cdr tabPart)))
    (if (string-match "\\\\t{?\\([0-9]+\\)}?" tab)
	(setq indent (vtex-get-tab-glyph 
		      (string-to-int (match-string 1 tab)))))
    (vtex-inst-spaces!
     inst
     (list
      (car (vtex-decorate-phantom inst (list tabPart)))
      (vtex-decorate-some 
       inst 
       crPart
       (if indent
	   `((end-glyph . ,indent)
	     (vtex-markup . t)
	     (vtex-phantom .t )
	     (start-open . t))
	 `((vtex-markup . t)
	   (vtex-phantom .t )
	   (start-open . t))))))
    )
  ;; we have to ensure that any vline-extents at newline
  ;; preced this extent in display order
  ;; CHECKME: nested boxes
  (let ((crExt (car (cdr (vtex-inst-spaces inst)))) vlExt putinfront)
    (while (setq vlExt (extent-at (extent-start-position crExt)
				  (current-buffer)
				  'vtex-zbox-vline
				  vlExt))
      (setq putinfront (cons vlExt putinfront)))
    (while putinfront
      (let* ((ext (car putinfront))
	     (start (extent-start-position ext))
	     (end (extent-end-position ext)))
	;; to change display order, detach it and set its position again
	(detach-extent ext)
	(set-extent-endpoints ext start end)
	(setq putinfront (cdr putinfront))
	)
      )
    )
  )
      

(defun vtex-get-tab-glyph (leng)
  ;; Retrieve or create a glyph for a tabulator position of LENG.
  (let ((glyph (gethash leng vtex-tab-cache)))
    (if (not glyph)
	(let ((i leng)
	      (str ""))
	  (while (> i 0)
	    (setq str (concat str vtex-tab-str)
		  i (- i 1)))
	  (setq glyph (make-glyph str))
	  ;; Crashes XEmacs-20!!!! 
	  (set-glyph-face glyph vtex-tab-face)
	  (puthash leng glyph vtex-tab-cache)))
    glyph))
  


;;; -------------------------------------------------------------------------
;;; MATH ELECTRICS


(defun vtex-electric-indent (&optional prefix)
  "Indent in Z/LaTeX environment. With prefix reindent.
Works on a \\tN at the end of the proceeding line."
  (interactive "_P")
  (let ((step (if prefix -1 1)) (mark (point-marker)))
    (save-excursion
      (vtex-visible-phantoms
       (vtex-prevent-auto-delete
	(vtex-do-with-indent
	 (lambda (beg end ind)
	   (goto-char beg)
	   (delete-region beg end)
	   (let ((newind (+ ind step)))
	     (cond
	      ((<= newind 0)
	       ;; do nothing
	       nil)
	      ((<= newind 9)
	       (insert (concat "\\t" (int-to-string newind))))
	      (t
	       (insert (concat "\\t{" (int-to-string newind) "}"))))))
	 (lambda (beg end)
	   (goto-char beg)
	   (delete-region beg end)
	   (insert "\\\\\\t1"))
	 ))
       (goto-char mark)))))
	      
;       (goto-char mark)
;       (if (and (> ind 0) (looking-at "\\\\t[0-9]"))
;	   (forward-char))
;       ))))

(defvar vtex-crtab-rex ".*\\(\\\\\\\\[ ]*\\(\\\\t{?\\([0-9]+\\)}?\\)\\)[ ]*$")
(defvar vtex-cr-rex ".*\\(\\\\\\\\\\)[ ]*$")

(defun vtex-do-with-indent (modifier creater)
  (if (eq (forward-line -1) 0)
      (if (looking-at vtex-crtab-rex)
	  (funcall modifier 
		   (match-beginning 2) (match-end 2)
		   (string-to-int (match-string 3)))
	(if (looking-at vtex-cr-rex)
	    (funcall creater (match-beginning 1) (match-end 1))))))


(defun vtex-electric-delete-backward (&optional arg)
  (interactive "p")
  (if (bolp)
      (let (haveind)
	(save-excursion
	  (vtex-visible-phantoms
	   (vtex-do-with-indent
	    (lambda (beg end ind) (setq haveind t))
	    (lambda (beg end) (setq haveind nil)))))
	(if haveind
	    (vtex-electric-indent -1)
	  (delete-backward-char arg)))
    (delete-backward-char arg))
  )
	   
(defun vtex-electric-delete-forward (&optional arg)
  (interactive "p")
  (if (and (extent-at (point) nil 'vtex-crtab)
	   (looking-at vtex-crtab-rex))
      (save-excursion
	(vtex-visible-phantoms
	 (forward-line 1)
	 (vtex-electric-indent -1)))
    (delete-char arg)))
      
(defun vtex-electric-newline (&optional arg)
  (interactive "p")
  (insert "\\\\\n"))

(defun vtex-escaped-newline (&optional arg)
  (interactive "p")
  (insert "\n"))

(defun vtex-electric-kill-line (&optional arg)
  (interactive "p")
  (if (looking-at vtex-crtab-rex)
      (delete-region (point) (match-beginning 1))
    (kill-line arg)))



;; Electric keymap

(defvar vtex-electric-keymap (make-sparse-keymap))
(define-key vtex-electric-keymap "\C-i" 'vtex-electric-indent)
(define-key vtex-electric-keymap "\C-d" 'vtex-electric-delete-forward)
(define-key vtex-electric-keymap [(delete)] 'vtex-electric-delete-backward)
(define-key vtex-electric-keymap [(return)] 'vtex-electric-newline)
(define-key vtex-electric-keymap [(shift return)] 'vtex-escaped-newline)
(define-key vtex-electric-keymap "\C-k" 'vtex-electric-kill-line)

(defvar vtex-electric-props
  `(vtex-inst-region-props ((keymap . ,vtex-electric-keymap))))

;; -------------------------------------------------------------------------
;; RESETTING 

(defun vtex-reset-tmpls ()
  (setq vtex-tmpls (make-hashtable 100 'equal))
  (setq vtex-math-tmpls (make-hashtable 100 'equal))
  (setq vtex-tmpls-rex nil)
  (setq vtex-math-tmpls-rex nil)
  ;; resetting all this caches. This should be probably organized
  ;; with a rest-hook.
  (setq vtex-list-env-cache (make-hashtable 40 'equal))
  (setq vtex-zbox-named-begin-cache nil)
  (setq vtex-zbox-unnamed-begin-cache nil)
  (setq vtex-zbox-hline-cache nil)
  (setq vtex-zbox-hline-cache nil)
  (setq vtex-tab-cache (make-hashtable 10))
  )
