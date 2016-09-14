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

(cl:in-package #:sha3)

;;;; %File Description:
;;;; 
;;;; This file contains an implementation of Keccak 1600 tuned to
;;;; implementations that support unboxed arithmetic on (unsigned-byte
;;;; 32).
;;;; 
;;;; Implementation Choices:
;;;;
;;;; This is a fairly straightforward implementation of Keccak 1600,
;;;; mostly tuned to sbcl for x86, and to some degree to cmucl for
;;;; x86.  It employs a bit of loop unrolling at compile-time, and
;;;; splits the 64bit Keccak 1600 lanes into two 32 bit words with bit
;;;; interleaving, thereby being able to still use hardware rotate
;;;; support where possible.  More advanced implementation techniques
;;;; like plane-per-plane processing, lane complementing and early
;;;; parity (c.f. the Keccak implementation overview) did not seem to
;;;; work well with SBCL's compiler, resulting in slower, less
;;;; readable code.
;;;;

#+cmu
(eval-when (:compile-toplevel)
  (defparameter *old-expansion-limit* ext:*inline-expansion-limit*)
  (setq ext:*inline-expansion-limit* (max ext:*inline-expansion-limit* 1000)))

;;;
;;; Additional Keccak-f-1600 definitions
;;;

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defconstant +keccak-state-splits+ 2
    "Number of lane splits")
  
  (defconstant +keccak-state-parts+ (* +keccak-state-lanes+ +keccak-state-splits+)
    "Total number of partial lanes in Keccak state")
  
  (defconstant +keccak-1600-part-width+ 32
    "Partial lane width for Keccak-1600.")
  
  (defconstant +keccak-1600-part-byte-width+ (truncate +keccak-1600-part-width+ 8)
    "Partial lane width in bytes for Keccak-1600."))

(deftype keccak-1600-part ()
  "Type of a partial keccak lane for Keccak-1600."
  `(unsigned-byte ,+keccak-1600-part-width+))

(deftype keccak-1600-state ()
  "Type of a keccak working state object for Keccak-1600."
  `(simple-array keccak-1600-part
                 (,+keccak-state-parts+)))

(declaim (inline make-keccak-1600-state)
         (ftype (function () keccak-1600-state) make-keccak-1600-state))
(defun make-keccak-1600-state ()
  (declare #.*optimize-declaration*)
  (make-array '(#.+keccak-state-parts+)
              :element-type 'keccak-1600-part
              :initial-element 0))

;;;
;;; De/Interleaving of bytes
;;;

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun make-interleave-table ()
    (loop with result = (make-array 256 :element-type '(unsigned-byte 8))
          for value from 0 to 255
          for entry = 0
          do
       (loop for bit-index from 0 to 7
             do
          (setf (ldb (byte 1 (+ (truncate bit-index 2) (* 4 (mod bit-index 2)))) 
                     entry)
                (ldb (byte 1 bit-index) value)))
       (setf (aref result value) entry)
          finally
       (return result)))
  
  (defun make-deinterleave-table ()
    (loop with result = (make-array 256 :element-type '(unsigned-byte 8))
          for value from 0 to 255
          for entry = 0
          do
       (loop for bit-index from 0 to 7
             do
          (setf (ldb (byte 1 (+ (truncate bit-index 2) (* 4 (mod bit-index 2)))) 
                     entry)
                (ldb (byte 1 bit-index) value)))
       (setf (aref result entry) value)
          finally
       (return result))))

;;;
;;; Transforming linear input/output to state array
;;;

(defun keccak-state-merge-input (state bit-rate input start)
  (declare (type keccak-1600-state state) (type (integer 0 1600) bit-rate)
           (type (simple-array (unsigned-byte 8) (*)) input)
           (type fixnum start)
           #.*optimize-declaration*)
  (let ((rate-bytes (truncate bit-rate 8))
        (interleave-lookup (load-time-value (make-interleave-table) t)))
    (declare (type (integer 0 200) rate-bytes)
             (type (simple-array (unsigned-byte 8) (256)) interleave-lookup))
    (dotimes (y #.+keccak-state-rows+)
      (declare (fixnum y))
      (dotimes (x #.+keccak-state-columns+)
        (declare (fixnum x))
        (let* ((element (+ (the fixnum (* y +keccak-state-columns+)) x))
               (part (* element +keccak-state-splits+))
               (offset (* element +keccak-1600-lane-byte-width+))
               (index (the fixnum (+ start offset))))
          (declare (fixnum element part offset index))
          (when (>= offset rate-bytes)
            (return-from keccak-state-merge-input))
          (setf (aref state part)
                (logxor 
                 (aref state part)
                 . 
                 #.(loop for byte-index from 0 
                           below +keccak-1600-lane-byte-width+
                         collect 
                         `(the keccak-1600-part
                            (ash (ldb (byte 4 0)
                                      (aref interleave-lookup
                                            (aref input (+ index ,byte-index))))
                                 ,(* byte-index 4)))))
                (aref state (1+ part))
                (logxor 
                 (aref state (1+ part))
                 . 
                 #.(loop for byte-index from 0 
                           below +keccak-1600-lane-byte-width+
                         collect 
                         `(the keccak-1600-part
                            (ash (ldb (byte 4 4)
                                      (aref interleave-lookup 
                                            (aref input (+ index ,byte-index))))
                                 ,(* byte-index 4)))))))))))

(defun keccak-state-extract-output (state output-bits)
  (let* ((output-bytes (truncate output-bits 8))
         (digest (make-array (list output-bytes) :element-type '(unsigned-byte 8)))
         (deinterleave-lookup (load-time-value (make-deinterleave-table) t)))
    (dotimes (x +keccak-state-columns+)
      (dotimes (y +keccak-state-rows+)
        (let* ((element (+ (* y +keccak-state-columns+) x))
               (part (* element +keccak-state-splits+))
               (offset (* element +keccak-1600-lane-byte-width+)))
          (unless (>= offset output-bytes)
            (loop with value-even = (aref state part)
                  with value-odd = (aref state (1+ part))
                  for index from offset 
                    below (min (+ offset +keccak-1600-lane-byte-width+) output-bytes)
                  do
               (setf (aref digest index) 
                     (aref deinterleave-lookup (dpb (ldb (byte 4 0) value-odd)
                                                    (byte 4 4)
                                                    (ldb (byte 4 0) value-even)))
                     value-even (ash value-even -4)
                     value-odd (ash value-odd -4)))))))
    digest))

;;;
;;; Keccak Constants
;;;

(declaim (inline keccak-f-round-constant)
         (ftype (function ((integer 0 23) (integer 0 1)) keccak-1600-part) 
                keccak-f-round-constant))
(defun keccak-f-round-constant (i p)
  (declare (type (integer 0 23) i) (type (integer 0 1) p) 
           #.*optimize-declaration*)
  (let ((constants
         (load-time-value 
          (make-array #.(* 24 +keccak-state-splits+)
                      :element-type 'keccak-1600-part
                      :initial-contents
                      (loop with itable = (make-interleave-table)
                            for rc across *keccak-f-round-constants*
                            nconc
                            (loop with even = 0
                                  with odd = 0
                                  for bit-offset from 0 below 64 by 8
                                  for value = (aref itable 
                                                    (ldb (byte 8 bit-offset) rc))
                                  do
                               (setf (ldb (byte 4 (truncate bit-offset 2)) even)
                                     (ldb (byte 4 0) value)
                                     (ldb (byte 4 (truncate bit-offset 2)) odd)
                                     (ldb (byte 4 4) value))
                                  finally
                               (return (list even odd)))))
          t)))
    (declare (type (simple-array keccak-1600-part (#.(* 24 +keccak-state-splits+)))
                   constants))
    (aref constants (+ (* i +keccak-state-splits+) p))))

;;;
;;; Helper: Rotation
;;;

(declaim (inline keccak-f-rot-part)
         (ftype (function (keccak-1600-part (integer 0 32)) keccak-1600-part)
                keccak-f-rot-part))
(defun keccak-f-rot-part (value offset)
  (declare (type (integer 0 32) offset)
           (type keccak-1600-part value)
           #.*optimize-declaration*
           #+sbcl
           (sb-ext:muffle-conditions sb-ext:code-deletion-note))
  #+sbcl
  (if (or (zerop offset) (= offset 32))
      value
      (sb-rotate-byte:rotate-byte offset (byte 32 0) value))
  #-sbcl
  (if (or (zerop offset) (= offset 32))
      value
      #+ccl
      (logior (the keccak-1600-part (ash (ldb (byte (- 32 offset) 0) value) offset))
              (ash value (- offset 32)))
      #-ccl
      (logior (ldb (byte 32 0) (ash value offset))
              (ash value (- offset 32)))))

(declaim (inline keccak-f-rot)
         (ftype (function (keccak-1600-part keccak-1600-part (integer 0 63))
                          (values keccak-1600-part keccak-1600-part))
                keccak-f-rot))
(defun keccak-f-rot (value-even value-odd offset)
  (declare (type (integer 0 63) offset)
           (type keccak-1600-part value-even value-odd)
           #.*optimize-declaration*
           #+sbcl
           (sb-ext:muffle-conditions sb-ext:code-deletion-note))
  (if (evenp offset)
      (values
        (keccak-f-rot-part value-even (truncate offset 2))
        (keccak-f-rot-part value-odd (truncate offset 2)))
      (values
        (keccak-f-rot-part value-odd (1+ (truncate offset 2)))
        (keccak-f-rot-part value-even (truncate offset 2)))))

;;;
;;; State and Temporary Variable Accessors
;;;

(defmacro with-state-accessors ((&rest states) &body body)
  "Bind the contents of the state(s) array(s) to local variables, and save 
the content on normal form exit."
  (let ((bindings nil) (mappings nil) (save-forms nil))
    (loop for state in states
          for map = (make-array '(#.+keccak-state-columns+ #.+keccak-state-rows+ 
                                  #.+keccak-state-splits+))
          do
       (dotimes (y +keccak-state-rows+)
         (dotimes (x +keccak-state-columns+)
           (dotimes (p +keccak-state-splits+)
             (let ((sym (make-symbol (format nil "~A-~D-~D-~D" state x y p))))
               (setf (aref map x y p) sym)
               (push `(,sym (aref ,state ,(+ p (* (+ x (* y +keccak-state-columns+))
                                                  +keccak-state-splits+))))
                     bindings)
               (push `(setf (aref ,state ,(+ p (* (+ x (* y +keccak-state-columns+))
                                                  +keccak-state-splits+)))
                            ,sym)
                     save-forms)))))
       (push (cons state map) mappings))
    `(let (,@bindings)
       (declare (ignorable ,@(mapcar #'car bindings))
                (type keccak-1600-part ,@(mapcar #'car bindings)))
       (macrolet ((state-aref (state x y p &environment env)
                    (let ((entry (assoc state ',mappings)))
                      (unless entry (error "Strange: ~S!" state))
                      (aref (cdr entry) 
                            (eval (trivial-macroexpand-all x env))
                            (eval (trivial-macroexpand-all y env))
                            (eval (trivial-macroexpand-all p env))))))
         (multiple-value-prog1 (progn ,@body)
           ,@save-forms)))))

(defmacro with-temp-state ((&rest temps) &body body)
  "Bind local variables for each temporary state."
  (let ((bindings nil) (mappings nil))
    (loop for temp in temps
          for map = (make-array '(#.+keccak-state-columns+ #.+keccak-state-rows+ 
                                  #.+keccak-state-splits+))
          do
       (dotimes (y +keccak-state-rows+)
         (dotimes (x +keccak-state-columns+)
           (dotimes (p +keccak-state-splits+)
             (let ((sym (make-symbol (format nil "~A-~D-~D-~D" temp x y p))))
               (setf (aref map x y p) sym)
               (push `(,sym 0) bindings)))))
       (push (cons temp map) mappings))
    `(let (,@bindings)
       (declare (ignorable ,@(mapcar #'car bindings))
                (type keccak-1600-part ,@(mapcar #'car bindings)))
       (macrolet ((temp-state-aref (temp x y p &environment env)
                    (let ((entry (assoc temp ',mappings)))
                      (unless entry (error "Strange: ~S!" temp))
                      (aref (cdr entry) 
                            (eval (trivial-macroexpand-all x env))
                            (eval (trivial-macroexpand-all y env))
                            (eval (trivial-macroexpand-all p env))))))
         ,@body))))

(defmacro with-temp-rows ((&rest rows) &body body)
  "Bind local variables for each temporary row."
  (let ((bindings nil) (mappings nil))
    (loop for row in rows
          for map = (make-array '(#.+keccak-state-columns+ #.+keccak-state-splits+))
          do
       (dotimes (x +keccak-state-columns+)
         (dotimes (p +keccak-state-splits+)
           (let ((sym (make-symbol (format nil "~A-~D-~D" row x p))))
             (setf (aref map x p) sym)
             (push `(,sym 0) bindings))))
       (push (cons row map) mappings))
    `(let (,@bindings)
       (declare (ignorable ,@(mapcar #'car bindings))
                (type keccak-1600-part ,@(mapcar #'car bindings)))
       (macrolet ((temp-row-aref (row x p &environment env)
                    (let ((entry (assoc row ',mappings)))
                      (unless entry (error "Strange: ~S!" row))
                      (aref (cdr entry) 
                            (eval (trivial-macroexpand-all x env))
                            (eval (trivial-macroexpand-all p env))))))
         ,@body))))

;;;
;;; Keccak-f permutation
;;;

(declaim (ftype (function (keccak-1600-state) keccak-1600-state) keccak-f))
(defun keccak-f (a)
  (declare (type keccak-1600-state a)
           #.*optimize-declaration*)
  (with-state-accessors (a)
    (with-temp-state (b)
      (with-temp-rows (c d)
        (dotimes (i #.(+ 12 (* 2 (truncate (log +keccak-1600-lane-width+ 2)))))
          (dotimes-unrolled (x +keccak-state-columns+)
            (dotimes-unrolled (p +keccak-state-splits+)
              (setf (temp-row-aref c x p)
                    (logxor (state-aref a x 0 p)
                            (state-aref a x 1 p)
                            (state-aref a x 2 p)
                            (state-aref a x 3 p)
                            (state-aref a x 4 p)))))
          (dotimes-unrolled (x +keccak-state-columns+)
            (setf (temp-row-aref d x 0)
                  (logxor (temp-row-aref c (mod (+ +keccak-state-columns+ (1- x)) 
                                                +keccak-state-columns+)
                                         0)
                          (keccak-f-rot-part
                           (temp-row-aref c (mod (1+ x) +keccak-state-columns+) 1)
                           1))
                  (temp-row-aref d x 1)
                  (logxor (temp-row-aref c (mod (+ +keccak-state-columns+ (1- x)) 
                                                +keccak-state-columns+)
                                         1)
                          (temp-row-aref c (mod (1+ x) +keccak-state-columns+) 0))))
          (dotimes-unrolled (x +keccak-state-columns+)
            (dotimes-unrolled (y +keccak-state-rows+)
              (dotimes-unrolled (p +keccak-state-splits+)
                (setf (state-aref a x y p)
                      (logxor (state-aref a x y p) (temp-row-aref d x p))))))
          (dotimes-unrolled (x +keccak-state-columns+)
            (dotimes-unrolled (y +keccak-state-rows+)
              (setf (values 
                      (temp-state-aref b y 
                                       (mod (+ (* 2 x) (* 3 y)) +keccak-state-rows+)
                                       0)
                      (temp-state-aref b y 
                                       (mod (+ (* 2 x) (* 3 y)) +keccak-state-rows+)
                                       1))
                    (keccak-f-rot (state-aref a x y 0)  (state-aref a x y 1)
                                  (get-rotate-offset x y)))))
          (dotimes-unrolled (x +keccak-state-columns+)
            (dotimes-unrolled (y +keccak-state-rows+)
              (dotimes-unrolled (p +keccak-state-splits+)
                (setf (state-aref a x y p)
                      (logxor (temp-state-aref b x y p)
                              (logandc1 
                               (temp-state-aref b (mod (1+ x) +keccak-state-columns+) 
                                                y p)
                               (temp-state-aref b (mod (+ x 2) +keccak-state-columns+)
                                                y p)))))))
          (dotimes-unrolled (p +keccak-state-splits+)
            (setf (state-aref a 0 0 p) 
                  (logxor (state-aref a 0 0 p) 
                          (keccak-f-round-constant i p)))))))
    a))

#+cmu
(eval-when (:compile-toplevel)
  (setq ext:*inline-expansion-limit* *old-expansion-limit*))
