;;;; SHA3 --- Secure Hash Algorithm 3 (Keccak) Implementation
;;;;
;;;; Copyright (C) 2012 -- 2016 PMSF IT Consulting Pierre R. Mai.
;;;;
;;;; Permission is hereby granted, free of charge, to any person obtaining
;;;; a copy of this software and associated documentation files (the
;;;; "Software"), to deal in the Software without restriction, including
;;;; without limitation the rights to use, copy, modify, merge, publish,
;;;; distribute, sublicense, and/or sell copies of the Software, and to
;;;; permit persons to whom the Software is furnished to do so, subject to
;;;; the following conditions:
;;;;
;;;; The above copyright notice and this permission notice shall be
;;;; included in all copies or substantial portions of the Software.
;;;;
;;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
;;;; IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY CLAIM, DAMAGES OR
;;;; OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
;;;; ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
;;;; OTHER DEALINGS IN THE SOFTWARE.
;;;;
;;;; Except as contained in this notice, the name of the author shall
;;;; not be used in advertising or otherwise to promote the sale, use or
;;;; other dealings in this Software without prior written authorization
;;;; from the author.
;;;; 
;;;; $Id$

(cl:in-package #:cl-user)

;;;; %File Description:
;;;; 
;;;; This file contains the system definition form for the SHA3
;;;; Library.  System definitions use the ASDF system definition
;;;; facility.
;;;; 

(asdf:defsystem "sha3"
  :description "Secure Hash Algorithm 3 (Keccak) Implementation"
  :author "Pierre R. Mai <pmai@pmsf.de>"
  :maintainer "Pierre R. Mai <pmai@pmsf.de>"
  :licence "MIT/X11"
  :version "1.1.0"
  #+sbcl :depends-on #+sbcl ("sb-rotate-byte")
  :components ((:file "pkgdef")
               (:file "common" :depends-on ("pkgdef"))
               #+(and :sbcl (or :x86-64 :alpha))
               (:file "keccak-64bit" :depends-on ("pkgdef" "common"))
               #+(or (and :sbcl (not (or :x86-64 :alpha))) 
                     :cmucl
                     (and :ccl :64-bit-target)
                     (and :lispworks :lispworks-64bit))
               (:file "keccak-32bit" :depends-on ("pkgdef" "common"))
               #-(or :sbcl :cmucl (and :ccl :64-bit-target) 
                     (and :lispworks :lispworks-64bit))
               (:file "keccak-16bit" :depends-on ("pkgdef" "common"))
               (:file "sha3" 
                      :depends-on ("pkgdef" 
                                   "common"
                                   #+(and :sbcl (or :x86-64 :alpha))
                                   "keccak-64bit"
                                   #+(or (and :sbcl (not (or :x86-64 :alpha)))
                                         :cmucl
                                         (and :ccl :64-bit-target)
                                         (and :lispworks :lispworks-64bit))
                                   "keccak-32bit"
                                   #-(or :sbcl :cmucl (and :ccl :64-bit-target)
                                         (and :lispworks :lispworks-64bit))
                                   "keccak-16bit"))))
