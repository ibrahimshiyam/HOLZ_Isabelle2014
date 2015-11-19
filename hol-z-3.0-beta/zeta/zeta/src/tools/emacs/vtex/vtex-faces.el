;; FACES
;; $Id: vtex-faces.el,v 1.1 1998/09/18 10:12:48 wg Exp $ 

(provide 'vtex-faces)
(require 'vtex-base)

;;; Face manipulation

(defun vtex-make-face (name &optional doc-string temporary)
  "Defines and returns a new FACE described by DOC-STRING.
If the face already exists, its properties will be reset
as if it has been newly created. See also `make-face'."
  (let (fobj)
    (if (setq fobj (find-face name))
	(progn
	  (reset-face name)
	  (set-face-doc-string name doc-string))
      (setq fobj (make-face name doc-string temporary)))
    (set-face-property name 'vtex-face t)
    fobj))

(defun vtex-make-nonstandard-face (name &optional doc-string temporary)
  "Defines and returns a new FACE described by DOC-STRING.
If the face already exists, its properties will be reset
as if it has been newly created. See also `make-face'.

This function should be used for making faces which do not have a
standard encoding (such as symbol faces), and should not be displayed in
the VTeX face editor."
  (let (fobj)
    (if (setq fobj (find-face name))
	(progn
	  (reset-face name)
	  (set-face-doc-string name doc-string))
      (setq fobj (make-empty-face name doc-string temporary)))
    (set-face-property name 'vtex-nonstandard-face t)
    fobj))

  
(defun vtex-derive-bold (face &optional sym docstring)
  "Return a newly created face symbol. The returned face inherits
all characteristics from FACE, and will be in addition made bold,
if possible (see `make-face-bold'). 
If optional SYM is given, it will be used as the symbol for the
returned face, otherwise a symbol will be generated."
  (let ((new (vtex-derive-face face sym docstring)))
    (make-face-bold new)
    new))

(defun vtex-derive-unbold (face &optional sym docstring)
  "Return a newly created face symbol. The returned face inherits
all characteristics from FACE, and will be in addition made unbold,
if possible (see `make-face-unbold'). 
If optional SYM is given, it will be used as the symbol for the
returned face, otherwise a symbol will be generated."
  (let ((new (vtex-derive-face face sym docstring)))
    (make-face-unbold new)
    new))

(defun vtex-derive-italic (face &optional sym docstring)
  "Return a newly created face symbol. The returned face inherits
all characteristics from FACE, and will be in addition made italic,
if possible (see `make-face-italic'). 
If optional SYM is given, it will be used as the symbol for the
returned face, otherwise a symbol will be generated."
  (let ((new (vtex-derive-face face sym docstring)))
    (make-face-italic new)
    new))

(defun vtex-derive-unitalic (face &optional sym docstring)
  "Return a newly created face symbol. The returned face inherits
all characteristics from FACE, and will be in addition made unitalic,
if possible (see `make-face-unitalic'). 
If optional SYM is given, it will be used as the symbol for the
returned face, otherwise a symbol will be generated."
  (let ((new (vtex-derive-face face sym docstring)))
    (make-face-unitalic new)
    new))

(defun vtex-derive-size (face magnification &optional sym docstring)
  "Return a newly created face symbol. The returned face inherits
all characteristics from FACE, and will be in addition made larger
or smaller according to the parameter MAGNIFICATION. If MAGNIFICATION
is greater then 0, `make-face-larger' will be called MAGNIFICATION
times; if it is less then 0, `make-face-smaller' will be called
-MAGNIFICATION times.
If optional SYM is given, it will be used as the symbol for the
returned face, otherwise a symbol will be generated."
  (let ((new (vtex-derive-face face sym docstring)))
    (while (< magnification 0)
      (make-face-smaller new)
      (setq magnification (+ magnification 1)))
    (while (> magnification 0)
      (make-face-larger new)
      (setq magnification (- magnification 1)))
    new))


(defun vtex-derive-face (face &optional sym docstring)
  "Return a newly created face symbol. The returned face inherits
all characteristics from FACE.
If optional SYM is given, it will be used as the symbol for the
returned face, otherwise a symbol will be generated."
  (if (not sym) 
      (progn 
	(setq sym (vtex-gen-symbol "face"))
	(vtex-make-face sym docstring)
	(set-face-property face 'vtex-face nil))
    (vtex-make-face sym docstring))
  (set-face-parent sym face)
  sym)
  


;;; Special Faces

(defun vtex-special-face (face remap) 
  "Make a temporary face which remaps the characters in REMAP.
REMAP is a sequence of pairs of strings and objects. For each pair 
(STRING . OBJ), the character specified by string is displayed as 
OBJ under FACE; all other characters are invisible. Objects
are entries for the display table, that is strings,
glyphs or vectors of strings and glyphs. A single character may be
also given as OBJ; it is converted into a string."
  (let* ((name (vtex-gen-symbol "special-face"))
	 (table (make-display-table))
	 (tface (vtex-make-nonstandard-face name 
					    (concat "VTeX-face-based-on-" 
						    (face-font-name face))
					    t)))
    (fillarray table "")
    (while remap
      (let ((chr (string-to-char (car (car remap))))
	    (obj (cdr (car remap))))
	(aset table chr (if (characterp obj) (make-string 1 obj) obj))
	(setq remap (cdr remap))))
    (set-face-property tface 'display-table table)
    (set-face-property tface 'font (face-font-name face))
    tface))
    

