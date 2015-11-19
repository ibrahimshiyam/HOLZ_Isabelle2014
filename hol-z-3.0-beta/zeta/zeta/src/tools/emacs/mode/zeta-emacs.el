;;; zeta-emacs.el --- running zeta using GNU/FSF emacs 21

;; $Id: zeta-base.el,v 1.5 2000/05/14 17:43:32 wg Exp $
;; by Achim D. Brucker, brucker@inf.ethz.ch
 (require 'x-symbol)
(require 'lucid)
 (require 'lmenu)
 (require 'lselect)



(defalias 'map-extents 'cl-map-overlays)
(defalias 'make-glyph 'identity)
(defalias 'extent-start-position 'overlay-start)
(defalias 'extent-end-position 'overlay-end)

;;(defalias 'make-extent 'make-overlay)
(defun make-extent (beg end &optional buffer) (make-overlay beg end buffer))
(defalias 'extent-buffer 'overlay-buffer)

(defvar setnu-begin-glyph-property (if (fboundp 'extent-property)
				                                           'begin-glyph
									                                        'before-string)
  "Property name to use to set the begin glyph of an extent.")




(defalias'set-extent-property 'overlay-put)

 (defun set-extent-begin-glyph (e g foo)
       (overlay-put e setnu-begin-glyph-property g))

;; provide it
(provide 'zeta-emacs)
