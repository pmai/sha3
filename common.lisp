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
;;;; This file contains common definitions and utility macros/functions
;;;; used in the specifically optimized implementations of keccak.
;;;; 

;;;
;;; Optimization
;;;

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defvar *optimize-declaration* 
    '(optimize (speed 3) (space 0) (safety 0) (debug 0))
    "Global optimize declaration used for performance critical functions.
This can be changed prior to compiling the package for debugging/testing
purposes."))

;;;
;;; LOGXOR Reduction Hack for certain lisps
;;;

#+(or lispworks ccl)
(defun logxor (&rest args)
  (apply #'cl:logxor args))

#+(or lispworks ccl)
(define-compiler-macro logxor (&whole form &rest args)
  (labels ((binarify (list)
             (if (rest list)
                 `(cl:logxor ,(car list) ,(binarify (rest list)))
               (first list))))
    (if (null args)
        form
        (binarify args))))

;;;
;;; Partial Evaluation Helpers
;;;

(defun trivial-macroexpand-all (form env)
  "Trivial and very restricted code-walker used in partial evaluation macros.
Only supports atoms and function forms, no special forms."
  (let ((real-form (macroexpand form env)))
    (cond
      ((atom real-form)
       real-form)
      (t
       (list* (car real-form)
              (mapcar #'(lambda (x) (trivial-macroexpand-all x env)) 
                      (cdr real-form)))))))

(defmacro dotimes-unrolled ((var limit) &body body &environment env)
  "Unroll the loop body at compile-time."
  (loop for x from 0 below (eval (trivial-macroexpand-all limit env))
        collect
        `(symbol-macrolet ((,var ,x)) ,@body)
          into forms
        finally
     (return `(progn ,@forms))))

;;;
;;; Keccak-f-1600 definitions
;;;

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defconstant +keccak-state-columns+ 5
    "Width of Keccak state in the x axis")
  (defconstant +keccak-state-rows+ 5
    "Width of Keccak state in the y axis")
  
  (defconstant +keccak-state-lanes+ (* +keccak-state-columns+ +keccak-state-rows+)
    "Total number of lanes in Keccak state")

  (defconstant +keccak-1600-lane-width+ 64
    "Lane width for Keccak-1600.")
  
  (defconstant +keccak-1600-lane-byte-width+ (truncate +keccak-1600-lane-width+ 8)
    "Lane width in bytes for Keccak-1600."))

(deftype keccak-1600-lane ()
  "Type of a keccak lane for Keccak-1600."
  `(unsigned-byte ,+keccak-1600-lane-width+))

;;;
;;; Keccak Constants
;;;

(defparameter *keccak-f-round-constants*
  (make-array '(24) :element-type 'keccak-1600-lane
              :initial-contents
              #-sha3-fixed-constants
              (loop with lfrstate = #x01
                    for i from 0 below 24
                    collect
                 (loop with const = 0
                       for j from 0 below 7
                       for bit-position = (1- (ash 1 j))
                       when (logbitp 0 lfrstate)
                         do (setq const (logxor const (ash 1 bit-position)))
                       do (setq lfrstate (if (logbitp 7 lfrstate)
                                             (logxor (ldb (byte 8 0) (ash lfrstate 1))
                                                     #x71)
                                             (ash lfrstate 1)))
                       finally (return const)))
              #+sha3-fixed-constants
              '(#x0000000000000001
                #x0000000000008082
                #x800000000000808a
                #x8000000080008000
                #x000000000000808b
                #x0000000080000001
                #x8000000080008081
                #x8000000000008009
                #x000000000000008a
                #x0000000000000088
                #x0000000080008009
                #x000000008000000a
                #x000000008000808b
                #x800000000000008b
                #x8000000000008089
                #x8000000000008003
                #x8000000000008002
                #x8000000000000080
                #x000000000000800a
                #x800000008000000a
                #x8000000080008081
                #x8000000000008080
                #x0000000080000001
                #x8000000080008008))
  "Keccak Round Constants")

(defparameter *keccak-f-rotate-offsets*
  (make-array (list +keccak-state-columns+ +keccak-state-rows+)
              :element-type '(unsigned-byte 8)
              :initial-contents
              '(( 0 36  3 41 18)
                ( 1 44 10 45  2)
                (62  6 43 15 61)
                (28 55 25 21 56)
                (27 20 39  8 14)))
  "Keccak Rotate Offsets")

(defmacro get-rotate-offset (x y &environment env)
  (aref *keccak-f-rotate-offsets* 
        (eval (trivial-macroexpand-all x env))
        (eval (trivial-macroexpand-all y env))))

;;;
;;; Message Padding for last block
;;;

(defun pad-message-to-width (message bit-width add-fips-202-suffix-p)
  "Destructively pad the given message to the given bit-width according to 
the Keccak 10*1 padding rules, optionally appending the FIPS 202/SHA-3
mandated 01 suffix first, and return the padded message."
  (let ((message-byte-length (length message))
        (width-bytes (truncate bit-width 8)))
    (setq message (adjust-array message (list width-bytes)))
    ;; FIPS 202 SHA-3 mandates the appending of a 01 suffix prior to the
    ;; final Keccak padding so that the first byte following the message
    ;; will be #b00000101 instead of #b00000001 for raw Keccak.
    (setf (aref message message-byte-length) (if add-fips-202-suffix-p #x06 #x01))
    (loop for index from (1+ message-byte-length) below width-bytes
          do (setf (aref message index) #x00)
          finally
       (setf (aref message (1- width-bytes))
             (logior #x80 (aref message (1- width-bytes))))))
  message)
