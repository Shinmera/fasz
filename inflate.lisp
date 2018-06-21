(in-package #:org.shirakumo.fasz)

(defvar *length-bits*
  (mkarr '(unsigned-byte 8)
         0 0 0 0 0 0 0 0
         1 1 1 1 2 2 2 2
         3 3 3 3 4 4 4 4
         5 5 5 5))

(defvar *length-base*
  (mkarr '(unsigned-byte 16)
         3 4 5 6 7 8 9 10
         11 13 15 17 19 23 27 31
         35 43 51 59 67 83 99 115
         131 163 195 227 258))

(defvar *dist-bits*
  (mkarr '(unsigned-byte 8)
         0 0 0 0 1 1 2 2
         3 3 4 4 5 5 6 6
         7 7 8 8 9 9 10 10
         11 11 12 12 13 13))

(defvar *dist-base*
  (mkarr '(unsigned-byte 16)
         1 2 3 4 5 6 7 9 13
         17 25 33 49 65 97 129 193
         257 385 513 769 1025 1537 2049 3073
         4097 6145 819 12289 16385 24577))

(defvar *clcidx*
  (mkarr '(unsigned-byte 8)
         16 17 18 0 8 7 9 6
         10 5 11 4 12 3 13 2
         14 1 15))

(defun checksum-type (type)
  (ecase type
    (0 :none)
    (1 :adler)
    (2 :crc)))

(deftype tree ()
  `(simple-array (unsigned-byte 16) (304)))

(defstruct (data (:constructor make-data (stream destination &optional dict-ring)))
  (stream NIL :type fast-io:input-buffer)
  (tag 0 :type (unsigned-byte 32))
  (bitcount 0 :type (unsigned-byte 32))
  (destination NIL :type (simple-array (unsigned-byte 8) 1))
  (index 0 :type (unsigned-byte 32))
  (checksum 0 :type (unsigned-byte 32))
  (checksum-type :none :type keyword)
  (btype -1 :type (signed-byte 32))
  (bfinal 0 :type (signed-byte 32))
  (curlen 0 :type (unsigned-byte 32))
  (lz-off 0 :type (signed-byte 32))
  (dict-ring NIL :type (or null (simple-array (unsigned-byte 8) 1)))
  (dict-index 0 :type (unsigned-byte 32))
  (ltree (make-array 304 :element-type '(unsigned-byte 16)) :type tree)
  (dtree (make-array 304 :element-type '(unsigned-byte 16)) :type tree))

(defmethod print-object ((data data) stream)
  (print-unreadable-object (data stream :type T :identity T)))

(defun build-fixed-trees (lt dt)
  (declare (type tree lt dt))
  ;; Length Tree
  (clear-array lt 0 7)
  (setf (aref lt 7) 24)
  (setf (aref lt 8) 152)
  (setf (aref lt 9) 112)
  (dotimes (i 24) (setf (aref lt (+ i 16)) (+ 256 i)))
  (dotimes (i 144) (setf (aref lt (+ i 16 24)) i))
  (dotimes (i 8) (setf (aref lt (+ i 16 24 144)) (+ 280 i)))
  (dotimes (i 112) (setf (aref lt (+ i 16 24 144 8)) (+ 144 i)))
  ;; Distance Tree
  (clear-array dt 0 5)
  (setf (aref dt 5) 32)
  (dotimes (i 32) (setf (aref dt (+ i 16)) i)))

(defun build-tree (tr lengths num offset)
  (let ((offs (make-array 16 :element-type '(unsigned-byte 16) :initial-element 0)))
    (declare (dynamic-extent offs))
    (dotimes (i num) (incf (aref tr (aref lengths (+ offset i)))))
    (setf (aref tr 0) 0)
    ;; Offset table for distribution sort
    (loop with sum = 0
          for i from 0 below 16
          do (setf (aref offs i) sum)
             (incf sum (aref tr i)))
    ;; Code->Symbol table
    (dotimes (i num)
      (when (/= 0 (aref lengths (+ offset i)))
        (let* ((length (aref lengths (+ offset i)))
               (offset (aref offs length)))
          (setf (aref offs length) (1+ offset))
          (setf (aref tr (+ 16 offset)) i))))))

(defun getbit (data)
  (cond ((= 0 (data-bitcount data))
         (setf (data-tag data) (fast-io:readu8 (data-stream data)))
         (setf (data-bitcount data) 7))
        (T
         (decf (data-bitcount data))))
  (let ((bit (logand (data-tag data) #x01)))
    (setf (data-tag data) (ash (data-tag data) -1))
    bit))

(defun read-bits (data num base)
  (if (= 0 num)
      base
      (let ((limit (ash 1 num))
            (mask 1)
            (val 0))
        (loop while (< mask limit)
              do (setf mask (* mask 2))
                 (when (/= 0 (getbit data))
                   (incf val mask)))
        (+ val base))))

(defun decode-symbol (data tr)
  (let ((sum 0) (cur 0) (len 0))
    (loop do (setf cur (+ (* 2 cur) (getbit data)))
             (when (<= 16 (incf len))
               (error "Bad data."))
             (incf sum (aref tr len))
             (decf cur (aref tr len))
          while (<= 0 cur))
    (incf sum cur)
    (when (or (< sum 0)
              (<= 288 sum))
      (error "Bad data."))
    (aref tr (+ 16 sum))))

(defun decode-trees (data lt dt)
  (let ((lengths (make-array (+ 288 32) :element-type '(unsigned-byte 8) :initial-element 0))
        (hlit (read-bits data 5 257))
        (hdist (read-bits data 5 1))
        (hclen (read-bits data 4 4)))
    (declare (dynamic-extent lengths))
    (loop for i from 0 below hclen
          for clen = (read-bits data 3 0)
          do (setf (aref lengths (aref *clcidx* i)) clen))
    (build-tree lt lengths 19 0)
    (loop with hlimit = (+ hlit hdist)
          with num = 0
          while (< num hlimit)
          for sym = (decode-symbol data lt)
          for fill-value = 0
          for lbase = 3
          do (flet ((handle-special (lbits)
                      (let ((length (read-bits data lbits lbase)))
                        (when (<= hlimit (+ num length)) (error "Bad data."))
                        (loop while (< 0 length)
                              do (decf length)
                                 (setf (aref lengths num) fill-value)
                                 (incf num)))))
               (case sym
                 (16
                  (setf fill-value (aref lengths (1- num)))
                  (handle-special 2))
                 (17
                  (handle-special 3))
                 (18
                  (setf lbase 11)
                  (handle-special 7))
                 (T
                  (setf (aref lengths num) sym)
                  (incf num)))))
    (build-tree lt lengths hlit 0)
    (build-tree dt lengths hdist hlit)))

(defun put (data c)
  (setf (aref (data-destination data) (data-index data)) c)
  (incf (data-index data))
  (when (data-dict-ring data)
    (setf (aref (data-dict-ring data) (data-dict-index data)) c)
    (setf (data-dict-index data) (mod (1+ (data-dict-index data)) (length (data-dict-ring data))))))

(defun inflate-block-data (data lt dt)
  (when (= 0 (data-curlen data))
    (let ((sym (decode-symbol data lt)))
      (when (< sym 256)
        (put data sym)
        (return-from inflate-block-data))
      (when (= 256 sym)
        (return-from inflate-block-data :done))
      (decf sym 257)
      (setf (data-curlen data) (read-bits data (aref *length-bits* sym) (aref *length-base* sym)))
      (let* ((dist (decode-symbol data dt))
             (offs (read-bits data (aref *dist-bits* dist) (aref *dist-base* dist))))
        (cond ((data-dict-ring data)
               (when (< (length (data-dict-ring data)) offs)
                 (error "Dictionary error."))
               (setf (data-lz-off data) (- (data-dict-index data) offs))
               (when (< (data-lz-off data) 0)
                 (incf (data-lz-off data) (length (data-dict-ring data)))))
              (T
               (setf (data-lz-off data) (- offs)))))))
  (let ((dest (data-destination data)))
    (cond ((data-dict-ring data)
           (setf (aref dest (data-index data)) (aref dest (data-lz-off data)))
           (incf (data-index data)))
          (T
           (put data (aref (data-dict-ring data) (data-lz-off data)))
           (when (= (length (data-dict-ring data)) (incf (data-lz-off data)))
             (setf (data-lz-off data) 0)))))
  (decf (data-curlen data)))

(defun inflate-uncompressed-block (data)
  (when (= 0 (data-curlen data))
    (let* ((length (fast-io:readu8 (data-stream data)))
           (length (+ length (* 256 (fast-io:readu8 (data-stream data)))))
           (invlength (fast-io:readu8 (data-stream data)))
           (invlength (+ invlength (* 256 (fast-io:readu8 (data-stream data))))))
      (when (/= length (logand (lognot invlength) #x0000FFFF))
        (error "Bad data."))
      (setf (data-curlen data) (+ length 1))
      (setf (data-bitcount data) 0)))
  (if (= 0 (decf (data-curlen data)))
      :done
      (put data (fast-io:readu8 (data-stream data)))))

(defun uncompress (data)
  (let ((res ()))
    (tagbody
     :start
       (when (/= -1 (data-btype data))
         (go :current-block))
     :next-block
       (setf (data-bfinal data) (getbit data))
       (setf (data-btype data) (read-bits data 2 0))
       (case (data-btype data)
         (1
          (build-fixed-trees (data-ltree data) (data-dtree data)))
         (2
          (setf res (decode-trees data (data-ltree data) (data-dtree data)))))
     :current-block
       (case (data-btype data)
         (0
          (setf res (inflate-uncompressed-block data)))
         ((1 2)
          (inflate-block-data data (data-ltree data) (data-dtree data)))
         (T
          (error "Bad data.")))
       (when (eql res :done)
         (when (= 0 (data-bfinal data))
           (go :next-block))
         (return-from uncompress :done)))))

(defun uncompress-checksum (data)
  (let ((index (data-index data))
        (res (uncompress data)))
    (case (data-checksum-type data)
      (:adler
       (setf (data-checksum data) (adler32 (data-destination data) index (data-index data) (data-checksum data))))
      (:crc
       (setf (data-checksum data) (crc32 (data-destination data) index (data-index data) (data-checksum data)))))
    (when (eq res :done)
      (case (data-checksum-type data)
        (:adler
         (when (/= (data-checksum data)
                   (fast-io:readu32-be (data-stream data)))
           (error "Checksum mismatch.")))
        (:crc
         (when (/= (logand (lognot (data-checksum data)) #xFFFFFFFF)
                   (fast-io:readu32-le (data-stream data)))
           (error "Checksum mismatch."))))
      :done)))

(defun parse-gzip-header (data)
  (let ((stream (data-stream data)))
    ;; Tag
    (when (or (/= #x1F (fast-io:readu8 stream))
              (/= #x8B (fast-io:readu8 stream)))
      (error "Bad data. Non-GZIP file header."))
    ;; Method
    (when (/= 8 (fast-io:readu8 stream))
      (error "Bad data. Compression method is not deflate."))
    (let ((flag (fast-io:readu8 stream)))
      (when (/= 0 (logand #xE0 flag))
        (error "Bad data. Reserved flag bits are non-zero."))
      (dotimes (i 6) (fast-io:readu8 stream))
      ;; Extra data chunk
      (when (/= 0 (logand #x04 flag))
        (dotimes (i (fast-io:read16-be stream))
          (fast-io:readu8 stream)))
      ;; Name chunk
      (when (/= 0 (logand #x08 flag))
        (loop for read = (fast-io:readu8 stream)
              until (= 0 read)))
      ;; Comment chunk
      (when (/= 0 (logand #x16 flag))
        (loop for read = (fast-io:readu8 stream)
              until (= 0 read)))
      ;; Header CRC
      (when (/= 0 (logand #x02 flag))
        (fast-io:read16-be stream))
      (setf (data-checksum-type data) :crc)
      (setf (data-checksum data) #xFFFFFFFF)
      data)))

(defun parse-zlib-header (data)
  (let* ((stream (data-stream data))
         (cmf (fast-io:readu8 stream))
         (flg (fast-io:readu8 stream)))
    (when (/= 0 (mod (+ (* 256 cmf) flg) 31))
      (error "Bad data. Zlib header checksum test failed."))
    (when (/= 8 (logand cmf #x0F))
      (error "Bad data. Compression method is not deflate."))
    (when (< 7 (ash cmf -4))
      (error "Bad data. Invalid window size."))
    (when (/= 0 (logand flg #x20))
      (error "Bad data. Preset dictionary."))
    (setf (data-checksum-type data) :adler)
    (setf (data-checksum data) 1)
    (ash cmf -4)))

(defun gunzip (source &key (if-exists :error))
  (with-open-file (in source :element-type '(unsigned-byte 8))
    (fast-io:with-fast-input (in-buffer NIL in)
      (let* ((out-buffer (make-array (* 4096 8) :element-type '(unsigned-byte 8)))
             (data (make-data in-buffer out-buffer)))
        (parse-gzip-header data)
        (loop until (eq :done (uncompress-checksum data)))
        (data-index data)))))
