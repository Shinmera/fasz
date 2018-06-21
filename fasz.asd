(asdf:defsystem fasz
  :serial T
  :components ((:file "package")
               (:file "toolkit")
               (:file "adler32")
               (:file "crc32")
               (:file "inflate"))
  :depends-on (:fast-io))
