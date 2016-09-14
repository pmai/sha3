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
;;;; 64).
;;;; 
;;;; Implementation Choices:
;;;;
;;;; This is a fairly straightforward implementation of Keccak 1600,
;;;; mostly tuned to sbcl for x86-64.  It employs a bit of loop
;;;; unrolling at compile-time.  More advanced implementation
;;;; techniques like plane-per-plane processing, lane complementing
;;;; and early parity (c.f. the Keccak implementation overview) did
;;;; not seem to work well with SBCL's compiler, resulting in slower,
;;;; less readable code.
;;;;

;;;
;;; Additional Keccak-f-1600 definitions
;;;

(deftype keccak-1600-state ()
  "Type of a keccak working state object for Keccak-1600."
  `(simple-array keccak-1600-lane
                 (,+keccak-state-lanes+)))

(declaim (inline make-keccak-1600-state)
         (ftype (function () keccak-1600-state) make-keccak-1600-state))
(defun make-keccak-1600-state ()
  (declare #.*optimize-declaration*)
  (make-array '(#.+keccak-state-lanes+)
              :element-type 'keccak-1600-lane
              :initial-element 0))

;;;
;;; Transforming linear input/output to state array
;;;

(defun keccak-state-merge-input (state bit-rate input start)
  (declare (type keccak-1600-state state) (type (integer 0 1600) bit-rate)
           (type (simple-array (unsigned-byte 8) (*)) input)
           (type fixnum start)
           #.*optimize-declaration*)
  (let ((rate-bytes (truncate bit-rate 8)))
    (declare (type (integer 0 200) rate-bytes))
    (dotimes (y +keccak-state-rows+)
      (dotimes (x +keccak-state-columns+)
        (let* ((element (+ (the fixnum (* y +keccak-state-columns+)) x))
               (offset (* element +keccak-1600-lane-byte-width+))
               (index (the fixnum (+ start offset))))
          (when (>= offset rate-bytes)
            (return-from keccak-state-merge-input))
          (setf (aref state element)
                (logxor 
                 (aref state element)
                 . 
                 #.(loop for byte-index from 0 
                           below +keccak-1600-lane-byte-width+
                         collect 
                         `(the keccak-1600-lane
                            (ash (aref input (+ index ,byte-index))
                                 ,(* byte-index 8)))))))))))

(defun keccak-state-extract-output (state output-bits)
  (let* ((output-bytes (truncate output-bits 8))
         (digest (make-array (list output-bytes) :element-type '(unsigned-byte 8))))
    (dotimes (x +keccak-state-columns+)
      (dotimes (y +keccak-state-rows+)
        (let* ((element (+ (* y +keccak-state-columns+) x))
               (offset (* element +keccak-1600-lane-byte-width+)))
          (unless (>= offset output-bytes)
            (loop with value = (aref state element)
                  for index from offset 
                    below (min (+ offset +keccak-1600-lane-byte-width+) output-bytes)
                  do
               (setf (aref digest index) (ldb (byte 8 0) value)
                     value (ash value -8)))))))
    digest))

;;;
;;; Keccak Constants
;;;

(declaim (inline keccak-f-round-constant)
         (ftype (function ((integer 0 23)) keccak-1600-lane) keccak-f-round-constant))
(defun keccak-f-round-constant (i)
  (declare (type (integer 0 23) i) 
           #.*optimize-declaration*)
  (let ((constants (load-time-value *keccak-f-round-constants* t)))
    (declare (type (simple-array keccak-1600-lane (24)) constants))
    (aref constants i)))

;;;
;;; Helper: Rotation
;;;

(declaim (inline keccak-f-rot)
         (ftype (function (keccak-1600-lane (integer 0 63)) keccak-1600-lane)
                keccak-f-rot))
(defun keccak-f-rot (value offset)
  (declare (type (integer 0 63) offset)
           (type keccak-1600-lane value)
           #.*optimize-declaration*)
  #+sbcl
  (sb-rotate-byte:rotate-byte offset (byte 64 0) value)
  #-sbcl
  (if (zerop offset)
      value
      (logior (ldb (byte 64 0) (ash value offset))
              (ash value (- offset 64)))))

;;;
;;; State and Temporary Variable Accessors
;;;

(defmacro with-state-accessors ((&rest states) &body body)
  "Bind the contents of the state(s) array(s) to local variables, and save 
the content on normal form exit."
  (let ((bindings nil) (mappings nil) (save-forms nil))
    (loop for state in states
          for map = (make-array '(#.+keccak-state-columns+ #.+keccak-state-rows+))
          do
       (dotimes (y +keccak-state-rows+)
         (dotimes (x +keccak-state-columns+)
           (let ((sym (make-symbol (format nil "~A-~D-~D" state x y))))
             (setf (aref map x y) sym)
             (push `(,sym (aref ,state ,(+ x (* y +keccak-state-columns+))))
                   bindings)
             (push `(setf (aref ,state ,(+ x (* y +keccak-state-columns+))) ,sym)
                   save-forms))))
       (push (cons state map) mappings))
    `(let (,@bindings)
       (declare (ignorable ,@(mapcar #'car bindings))
                (type keccak-1600-lane ,@(mapcar #'car bindings)))
       (macrolet ((state-aref (state x y &environment env)
                    (let ((entry (assoc state ',mappings)))
                      (unless entry (error "Strange: ~S!" state))
                      (aref (cdr entry) 
                            (eval (trivial-macroexpand-all x env))
                            (eval (trivial-macroexpand-all y env))))))
         (multiple-value-prog1 (progn ,@body)
           ,@save-forms)))))

(defmacro with-temp-state ((&rest temps) &body body)
  "Bind local variables for each temporary state."
  (let ((bindings nil) (mappings nil))
    (loop for temp in temps
          for map = (make-array '(#.+keccak-state-columns+ #.+keccak-state-rows+))
          do
       (dotimes (y +keccak-state-rows+)
         (dotimes (x +keccak-state-columns+)
           (let ((sym (make-symbol (format nil "~A-~D-~D" temp x y))))
             (setf (aref map x y) sym)
             (push `(,sym 0) bindings))))
       (push (cons temp map) mappings))
    `(let (,@bindings)
       (declare (ignorable ,@(mapcar #'car bindings))
                (type keccak-1600-lane ,@(mapcar #'car bindings)))
       (macrolet ((temp-state-aref (temp x y &environment env)
                    (let ((entry (assoc temp ',mappings)))
                      (unless entry (error "Strange: ~S!" temp))
                      (aref (cdr entry) 
                            (eval (trivial-macroexpand-all x env))
                            (eval (trivial-macroexpand-all y env))))))
         ,@body))))

(defmacro with-temp-rows ((&rest rows) &body body)
  "Bind local variables for each temporary row."
  (let ((bindings nil) (mappings nil))
    (loop for row in rows
          for map = (make-array '(#.+keccak-state-columns+))
          do
       (dotimes (x +keccak-state-columns+)
         (let ((sym (make-symbol (format nil "~A-~D" row x))))
           (setf (aref map x) sym)
           (push `(,sym 0) bindings)))
       (push (cons row map) mappings))
    `(let (,@bindings)
       (declare (ignorable ,@(mapcar #'car bindings))
                (type keccak-1600-lane ,@(mapcar #'car bindings)))
       (macrolet ((temp-row-aref (row x &environment env)
                    (let ((entry (assoc row ',mappings)))
                      (unless entry (error "Strange: ~S!" row))
                      (aref (cdr entry) 
                            (eval (trivial-macroexpand-all x env))))))
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
            (setf (temp-row-aref c x)
                  (logxor (state-aref a x 0)
                          (state-aref a x 1)
                          (state-aref a x 2)
                          (state-aref a x 3)
                          (state-aref a x 4))))
          (dotimes-unrolled (x +keccak-state-columns+)
            (setf (temp-row-aref d x)
                  (logxor (temp-row-aref c (mod (+ +keccak-state-columns+ (1- x)) 
                                                +keccak-state-columns+))
                          (keccak-f-rot 
                           (temp-row-aref c (mod (1+ x) +keccak-state-columns+))
                           1))))
          (dotimes-unrolled (x +keccak-state-columns+)
            (dotimes-unrolled (y +keccak-state-rows+)
              (setf (state-aref a x y)
                    (logxor (state-aref a x y) (temp-row-aref d x)))))
          (dotimes-unrolled (x +keccak-state-columns+)
            (dotimes-unrolled (y +keccak-state-rows+)
              (setf (temp-state-aref b y 
                                     (mod (+ (* 2 x) (* 3 y)) +keccak-state-rows+))
                    (keccak-f-rot (state-aref a x y)
                                  (get-rotate-offset x y)))))
          (dotimes-unrolled (x +keccak-state-columns+)
            (dotimes-unrolled (y +keccak-state-rows+)
              (setf (state-aref a x y)
                    (logxor (temp-state-aref b x y)
                            (logandc1 
                             (temp-state-aref b (mod (1+ x) +keccak-state-columns+) y)
                             (temp-state-aref b (mod (+ x 2) +keccak-state-columns+)
                                              y))))))
          (setf (state-aref a 0 0) (logxor (state-aref a 0 0) 
                                           (keccak-f-round-constant i))))))
    a))
