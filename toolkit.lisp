(in-package #:org.shirakumo.fasz)

(defun mkarr (type &rest contents)
  (make-array (length contents) :element-type type :initial-contents contents))

(define-compiler-macro mkarr (type &rest contents)
  `(make-array ,(length contents) :element-type ,type :initial-contents ',contents))

(defmacro clear-array (array start stop)
  `(progn
     ,@(loop for i from start below stop
             collect `(setf (aref ,array ,i) 0))))
