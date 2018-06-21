(in-package #:org.shirakumo.fasz)

(defun mkarr (type &rest contents)
  (make-array (length contents) :element-type type :initial-contents contents))

(define-compiler-macro mkarr (type &rest contents)
  `(make-array ,(length contents) :element-type ,type :initial-contents ',contents))
