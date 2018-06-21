(in-package #:org.shirakumo.fasz)

(defconstant ADLER-BASE 65521)
(defconstant ADLER-NMAX 5552)

(defun adler32 (data start end prev-sum)
  (declare (type (simple-array (unsigned-byte 8) 1) data))
  (let ((s1 (logand prev-sum #xFFFF))
        (s2 (ash prev-sum -16))
        (length (- end start))
        (index start))
    (flet ((buf (i)
             (aref data (+ index i))))
      (loop while (< 0 length)
            for k = (if (< length ADLER-NMAX) length ADLER-NMAX)
            do (loop for i downfrom (/ k 16) above 0
                     do (macrolet ((expand (n)
                                     `(progn
                                        (incf s1 (buf ,n))
                                        (incf s2 s1)
                                        (incf s1 (buf ,(1+ n)))
                                        (incf s2 s1)))
                                   (expand-all ()
                                     `(progn
                                        ,@(loop for n from 0 below 16 by 2
                                                collect `(expand ,n)))))
                          (expand-all))
                        (incf index 16))
               (loop for i downfrom (mod k 16) above 0
                     do (incf s1 (buf 0))
                        (incf s2 s1)
                        (incf index))
               (setf s1 (mod s1 ADLER-BASE))
               (setf s2 (mod s2 ADLER-BASE))
               (decf length k)))
    (logior (ash s2 16) s1)))
