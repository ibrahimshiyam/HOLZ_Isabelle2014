;; vtex-base.el
;; REQUIREMENTS, ADAPTIONS, AND GENERAL UTILITIES
;; $Id: vtex-base.el,v 1.3 1998/11/25 07:57:04 wg Exp $

(provide 'vtex-base)


;;; Check for XEmacs
 
(if (not (string-match "XEmacs" emacs-version))
  (error "Sorry, the VTeX package only works with XEmacs."))

;;; Install Z Symbols

(if (boundp 'zeta-dir)
  (exec-to-string (concat zeta-dir "/bin/instzsymb")))


;;;  Increase max eval depth

(setq max-lisp-eval-depth 2000)


;;;  Debugging, Errors and Warnings

(defconst vtex-debug-on nil)

;(fset 'defvar-orig (symbol-function 'defvar))

;(if vtex-debug-on
;    (progn
;      (defmacro defvar (sym init &optional doc)
;	"Redefinition of defvar to defconst, to allow overwriting of variables 
;during interactive development."
;	`(defconst ,sym ,init ,doc))
;      ))



(defvar vtex-log-buffer "*VTeX Messages*"
  "Buffer to log warnings and debug message.")

(defsubst vtex-dprint (msg &rest args)
  "Print a debug message to log buffer if 'vtex-debug-on is none-nil."
  (if vtex-debug-on
      (save-excursion
	(set-buffer (get-buffer-create vtex-log-buffer))
	(goto-char (point-max))
	(insert "vtex debug: " (eval `(format ,@(cons msg args))) "\n"))))

(defun vtex-die (msg &rest args)
  "Print an error message and let the current computation die."
  (eval `(vtex-dprint ,@(cons msg args)))
  (error "vtex internal error (see log buffer %s)" vtex-log-buffer))

(defun vtex-warn (msg &rest args)
  "Print a warning to the log buffer."
  (save-excursion
    (set-buffer (get-buffer-create vtex-log-buffer))
    (goto-char (point-max))
    (insert "warning: " (eval `(format ,@(cons msg args))) "\n")))


;;; Getting some Functional Flavour into ELISP

(defun curry (fun &rest args)
  "Curry a function. FUN may be either a symbol or a function object.
ARGS is a partial list of arguments to be applied to FUN. The result is the 
function resulting from the application of ARGS (with their bindings at the time of
the call to curry) to FUN."
  ;@? more efficient solution
  (if (symbolp fun)
      `(lambda (&rest restargs) (eval (append (list (quote ,fun) ,@args) restargs)))
    `(lambda (&rest restargs) (eval (append (list 'funcall ,fun ,@args) restargs)))))

(defun vtex-reduce (fun list &optional init)
  "Reduce LIST using FUN with initial value INIT. (vtex-reduce '(a b c) FUN INIT) 
equals to (FUN a (FUN b (FUN c INIT)))."
  (if (consp list)
      (funcall fun (car list) (vtex-reduce fun (cdr list) init))
    init))

(defun fold (fun list)
  "Fold LIST using FUN. (fold '(a b c) FUN) equals to (FUN a (FUN b c))."
  (if (consp list)
      (if (consp (cdr list))
	  (funcall fun (car list) (fold fun (cdr list)))
	(funcall fun (car list) (car (cdr list))))
    (vtex-die "fold applied to non-list")))

(defun zip (list1 list2 fun)
  "Zip together LIST1 and LIST2 by FUN."
  (let ((r nil) (p nil))
    (while list1
      (if (not list2)
	  (vtex-die "zip: second argument smaller then first one")
	(if r
	    (progn 
	      (setcdr p (cons (funcall fun (car list1) (car list2)) nil))
	      (setq p (cdr p)))
	  (setq r (cons (funcall fun (car list1) (car list2)) nil))
	  (setq p r))
	(setq list1 (cdr list1))
	(setq list2 (cdr list2))))
    (if list2
	(vtex-die "zip: first argument smaller then second one")
      r)))

(defun upto (n1 n2)
  "Generate list of numbers from N1 upto N2."
  (if (> n1 n2)
      nil
    (cons n1 (upto (+ n1 1) n2))))

;;; Getting Free Types into ELISP

(defmacro defabstype (name &rest variants)
  "Generate a free type named NAME with VARIANTS.
VARIANTS is a list of lists each of which describes one variant of the 
type. The last element of VARIANTS may be a documentation string. For 
each variant, the first name is the constructor, and
the remaining ones are the selectors. A typical usage is as in

   (defabstype myseq (mycons mycar mycdr) (mynil) \"My type of lists\".)

which introduces a free type named 'mylist (presented as a variable
with value 'mylist), constructors 'mycons 
and 'mynil, predicates 'myconsp and 'mynilp, selectors 'mycar and 'mycdr, 
and updaters 'mycar! and 'mycdr!. Note that selectors may occure in several 
variants at different positions; however, if they appear at the same position,
they are generally more efficient (if debugging is not enabled, then applying
a selector which has the same position whereever it occures in VARIANTS
is just an 'aref on a vector.)."

  (let (doc)
    (setq variants (reverse variants))
    (if (not (stringp (car variants)))
	(setq doc nil)
      (setq doc (car variants))
      (setq variants (cdr variants)))
    `(progn
       (defvar ,name (quote ,variants) ,doc)
       ,@(mapcar
	  (lambda (variant)
	    (let ((csym (car variant)))
	      `(progn
		 (defsubst ,csym (&optional ,@(cdr variant))
		   ,(format "Free type constructor %S." csym)
		   (vector (quote ,csym) ,@(cdr variant)))
		 (defsubst ,(intern (concat (symbol-name csym) "p")) (obj)
		   ,(format "Free type test for constructor %S." csym)
		   (and (vectorp obj) (eq (quote ,csym) (aref obj 0)))))))
	  variants)
       ,@(mapcar
	  (lambda (selinfo)
	    (let* ((selsym (car selinfo))
		   (updsym (intern (concat (symbol-name selsym) "!")))
		   (selcases (cdr selinfo))
		   (consnames 
		    (vtex-reduce (lambda (selcase rest) (append (cdr selcase) rest))
			    selcases nil)))
	      `(progn
		 (defsubst ,selsym (obj)
		   ,(format "Free type selector %S for constructors %S" 
			    selsym consnames)
		   (cond 
		    ,@(mapcar 
		       (lambda (selcase)
			 `(,(deftype-maketest (cdr selcase))
			   (aref obj ,(car selcase))))
		       (cdr selcases))
		    ,@(if vtex-debug-on
			  `((,(deftype-maketest (cdr (car selcases)))
			     (aref obj ,(car (car selcases))))
			    (t (vtex-die "selection %S undefined" 
					 ,(symbol-name selsym))))
			`((t (aref obj ,(car (car selcases))))))))
		 (defsubst ,updsym (obj val)
		   ,(format "Free type update %S for constructors %S" 
			    updsym consnames)
		   (cond 
		    ,@(mapcar 
		       (lambda (selcase)
			 `(,(deftype-maketest (cdr selcase))
			   (aset obj ,(car selcase) val)))
		       (cdr selcases))
		    ,@(if vtex-debug-on
			  `((,(deftype-maketest (cdr (car selcases)))
			     (aset obj ,(car (car selcases)) val))
			    (t (vtex-die "update %S undefined" 
					 ,(symbol-name updsym))))
			`((t (aset obj ,(car (car selcases)) val))))))
		 )))
	  (deftype-makesels variants)))))
	       
(defun deftype-makesels (variants)
  "Make a list which contains for each selector in VARIANTS an
entry ('sel (indx ('cons)*)*)."
  (vtex-reduce 
   (lambda (variant result)
     (vtex-reduce 
      (lambda (selindx result1)
	(deftype-insertsel result1 (car selindx) (car variant) (cdr selindx)))
      (zip (cdr variant) (upto 1 (length (cdr variant))) 'cons)
      result))
   variants nil))

(defun deftype-insertsel (l selsym conssym indx)
  (if l
      (if (eq selsym (car (car l)))
	  (progn
	    (setcdr (car l) (deftype-insertsel1 (cdr (car l)) conssym indx))
	    l)
	(cons (car l) (deftype-insertsel (cdr l) selsym conssym indx)))
    `(( ,selsym ,@(deftype-insertsel1 nil conssym indx)))))

(defun deftype-insertsel1 (l conssym indx)
  (if l
      (if (equal indx (car (car l)))
	  (progn 
	    (setcdr (car l) (cons conssym (cdr (car l))))
	    l)
	(cons (car l) (deftype-insertsel1 (cdr l) conssym indx)))
    `((,indx ,conssym))))

(defun deftype-maketest (cases)
  `(and (arrayp obj)
	(or ,@(mapcar 
	      (lambda (csym) 
		`(eq (aref obj 0) (quote ,csym)))
	      cases))))



;;; Generating Symbols

(defvar vtex-sym-count 0
  "Counter for internal symbols")

(defun vtex-gen-symbol (&optional prefix)
  "Generate a new internal symbol."
  (setq vtex-sym-count (+ vtex-sym-count 1))
  (intern (concat "vtex-gen-" (or prefix "") (int-to-string vtex-sym-count))))



;;; More Functions on Hashtables

(defun vtex-reduce-hashtable (fun table &optional init)
  "Reduce over a hashtable. Function FUN is of type
`(lambda (KEY ENTRY RES))'."
  (maphash
   (lambda (key entry) 
     (setq init (funcall fun key entry init)))
   table)
  init)


;;; More Functions on Extents

(defsubst set-extent-properties (ext props)
  "Set PROPS, a list of pairs consisting of the symbol for
the property and its value, for extent EXT."
  ;;@TODO for efficiency reasons, make a macro of this
  (while props
    (set-extent-property ext (car (car props)) (cdr (car props)))
    (setq props (cdr props))))


