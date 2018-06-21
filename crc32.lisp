(in-package #:org.shirakumo.fasz)

(defvar *crc32tab* (mkarr '(unsigned-byte 32)
                          #x00000000 #x1db71064 #x3b6e20c8 #x26d930ac #x76dc4190
                          #x6b6b51f4 #x4db26158 #x5005713c #xedb88320 #xf00f9344
                          #xd6d6a3e8 #xcb61b38c #x9b64c2b0 #x86d3d2d4 #xa00ae278
                          #xbdbdf21c))

(defun crc32 (data start end crc)
  (declare (type (simple-array (unsigned-byte 8) 1) data))
  (loop for i from start below end
        do (setf crc (logxor crc (aref data i)))
           (setf crc (logxor (aref *crc32tab* (logand crc #x0F)) (ash crc -4)))
           (setf crc (logxor (aref *crc32tab* (logand crc #x0F)) (ash crc -4))))
  crc)
