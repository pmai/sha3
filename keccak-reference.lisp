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

(cl:defpackage #:keccak-reference
  (:use #:common-lisp)
  (:nicknames #:keccak)
  (:export #:keccak
           #:print-digest
           #:test-with-testsuite
           #:read-testsuite-from-file
           #:test-with-testsuite-from-file
           #:test-keccak-msgkat
           #:test-sha3-msgkat))

(cl:in-package #:keccak-reference)

;;;; %File Description:
;;;; 
;;;; This file contains a simple and unoptimized reference
;;;; implementation of the Keccak secure hash algorithm (which forms
;;;; the basis of the SHA-3 Secure Hash Algorithm Standard).
;;;;
;;;; It is used as a reference for the more optimized and specialized
;;;; implementations of the SHA-3 standard contained in this package.
;;;; 
;;;; The main entry point is the functions keccak which calculates a
;;;; keccak hash for a given set of parameters and a given input
;;;; vector and returns both the extracted output hash and the state
;;;; after hashing as its values.
;;;;

;;;
;;; Keccak state and parametes
;;;

(defconstant +keccak-state-columns+ 5
  "Width of Keccak state in the x axis")
(defconstant +keccak-state-rows+ 5
  "Width of Keccak state in the y axis")

(defconstant +keccak-state-lanes+ (* +keccak-state-columns+ +keccak-state-rows+)
  "Total number of lanes in Keccak state")

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun keccak-lane-width (total-bits)
    (multiple-value-bind (width rest) 
        (truncate total-bits +keccak-state-lanes+)
      (assert (zerop rest) (total-bits)
              "Illegal Keccak Total-Bits value: ~S. Must be a multiple of ~D."
              total-bits +keccak-state-lanes+)
      width)))

(deftype keccak-lane (total-bits)
  "Type of a keccak lane for a given total bit number."
  `(unsigned-byte ,(keccak-lane-width total-bits)))

(deftype keccak-state (total-bits)
  "Type of a keccak working state object for a given total bit number."
  `(simple-array (keccak-lane ,total-bits)
                 (,+keccak-state-columns+ ,+keccak-state-rows+)))

(defun make-keccak-state (total-bits)
  (make-array (list +keccak-state-columns+ +keccak-state-rows+)
              :element-type `(keccak-lane ,total-bits)
              :initial-element 0))

;;;
;;; Transforming linear input/output to state array
;;;

(defun keccak-state-merge-input (state total-bits bit-rate input start)
  (let ((lane-width (keccak-lane-width total-bits))
        (rate-bytes (truncate bit-rate 8)))
    (dotimes (x +keccak-state-columns+)
      (dotimes (y +keccak-state-rows+)
        (let ((offset (truncate (* (+ (* y +keccak-state-columns+) x) lane-width) 8)))
          (unless (>= offset rate-bytes)
            (setf (aref state x y)
                  (logxor (aref state x y)
                          (loop with value = 0
                                for index from (1- (+ start offset 
                                                            (ceiling lane-width 8)))
                                  downto (+ start offset)
                                do
                             (setq value (logior (ash value 8) (aref input index)))
                                finally
                             (return value))))))))))

(defun keccak-state-extract-output (state total-bits output-bits)
  (let* ((lane-width (keccak-lane-width total-bits))
         (output-bytes (truncate output-bits 8))
         (digest (make-array (list output-bytes) :element-type '(unsigned-byte 8))))
    (dotimes (x +keccak-state-columns+)
      (dotimes (y +keccak-state-rows+)
        (let ((offset (truncate (* (+ (* y +keccak-state-columns+) x) lane-width) 8)))
          (unless (>= offset output-bytes)
            (loop with value = (aref state x y)
                  for index from offset below (min (+ offset (ceiling lane-width 8))
                                                   output-bytes)
                  do
               (setf (aref digest index) (ldb (byte 8 0) value)
                     value (ash value -8)))))))
    digest))

;;;
;;; Keccak Constants
;;;

(defparameter *keccak-f-round-constants*
  (make-array (list 24) :element-type '(unsigned-byte 64)
              :initial-contents
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
                #x8000000080008008)))

(defun keccak-f-round-constant (total-bits i)
  (let ((lane-width (keccak-lane-width total-bits)))
    (ldb (byte lane-width 0) (aref *keccak-f-round-constants* i))))

(defparameter *keccak-f-rotate-offsets*
  (make-array (list +keccak-state-columns+ +keccak-state-rows+)
              :element-type '(unsigned-byte 8)
              :initial-contents
              '(( 0 36  3 41 18)
                ( 1 44 10 45  2)
                (62  6 43 15 61)
                (28 55 25 21 56)
                (27 20 39  8 14))))

;;;
;;; Helper: Rotation
;;;

(defun keccak-f-rot (total-bits value offset)
  (let ((lane-width (keccak-lane-width total-bits)))
    (logior (ldb (byte lane-width 0) (ash value (mod offset lane-width)))
            (ash value (- (mod offset lane-width) lane-width)))))

;;;
;;; Single Keccak-f round
;;;

(defun keccak-f-round (total-bits a rc)
  (macrolet ((modref (array &rest indices)
               `(aref ,array 
                      ,@(mapcar #'(lambda (idx)
                                    `(mod ,idx +keccak-state-columns+)) indices))))
    (let ((c (make-array (list +keccak-state-columns+)
                         :element-type `(keccak-lane ,total-bits)))
          (d (make-array (list +keccak-state-columns+)
                         :element-type `(keccak-lane ,total-bits)))
          (b (make-array (list +keccak-state-columns+ +keccak-state-rows+)
                         :element-type `(keccak-lane ,total-bits))))
      (dotimes (x +keccak-state-columns+)
        (setf (aref c x) 
              (logxor (aref a x 0) (aref a x 1) (aref a x 2)
                      (aref a x 3) (aref a x 4))))
      (dotimes (x +keccak-state-columns+)
        (setf (aref d x) 
              (logxor (modref c (1- x))
                      (keccak-f-rot total-bits (modref c (1+ x)) 1))))
      (dotimes (x +keccak-state-columns+)
        (dotimes (y +keccak-state-rows+)
          (setf (aref a x y)
                (logxor (aref a x y) (aref d x)))))
      (dotimes (x +keccak-state-columns+)
        (dotimes (y +keccak-state-rows+)
          (setf (modref b y (+ (* 2 x) (* 3 y)))
                (keccak-f-rot total-bits
                              (aref a x y)
                              (aref *keccak-f-rotate-offsets* x y)))))
      (dotimes (x +keccak-state-columns+)
        (dotimes (y +keccak-state-rows+)
          (setf (aref a x y)
                (logxor (aref b x y)
                        (logandc1 (modref b (1+ x) y) (modref b (+ x 2) y))))))
      (setf (aref a 0 0)
            (logxor (aref a 0 0) rc))
      a)))

;;;
;;; Keccak-f permutation
;;;

(defun keccak-f (total-bits a)
  (assert (member total-bits '(25 50 100 200 400 800 1600)) (total-bits)
          "Illegal bit-width ~S!" total-bits)
  (let ((rounds (+ 12 (* 2 (truncate (log (keccak-lane-width total-bits) 2))))))
    (dotimes (i rounds a)
      (keccak-f-round total-bits a (keccak-f-round-constant total-bits i)))))

;;;
;;; Message Padding for last block
;;;

(defun pad-message-to-width (message bit-width)
  (let ((message-byte-length (length message))
        (width-bytes (truncate bit-width 8)))
    (setq message (adjust-array message (list width-bytes)))
    (setf (aref message message-byte-length) #x01)
    (loop for index from (1+ message-byte-length) below width-bytes
          do (setf (aref message index) #x00)
          finally
       (setf (aref message (1- width-bytes))
             (logior #x80 (aref message (1- width-bytes))))))
  message)

;;;
;;; Main Entry Point: Keccak
;;;

(defun keccak (total-bits bit-rate output-bits message)
  (assert (member total-bits '(25 50 100 200 400 800 1600)) (total-bits)
          "Illegal bit-width ~S!" total-bits)
  (let ((state (make-keccak-state total-bits))
        (rate-bytes (truncate bit-rate 8))
        (length (length message)))
    (loop for block-offset from 0 to length by rate-bytes
          do
       (if (<= (+ block-offset rate-bytes) length)
           (keccak-state-merge-input state total-bits bit-rate message block-offset)
           (keccak-state-merge-input state total-bits bit-rate 
                                     (pad-message-to-width
                                      (subseq message block-offset)
                                      bit-rate)
                                     0))
       (setq state (keccak-f total-bits state)))
    (let ((digest (keccak-state-extract-output state total-bits output-bits)))
      (values digest state))))

;;;
;;; Utility functions
;;;

(defun print-digest (digest &optional (stream *standard-output*))
  (format stream "~{~2,'0X~}~%" (coerce digest 'list)))

(defun pprint-keccak-state (state &optional (stream *standard-output*))
  (dotimes (y +keccak-state-rows+) 
    (dotimes (x +keccak-state-columns+)
      (format stream "~16,'0X " (aref state x y)))
    (format stream "~%")))

;;;
;;; Testing
;;;

(defun test-with-testsuite (testsuite function)
  (flet ((from-hex (hex-string)
           (loop with result = (make-array (list (truncate (length hex-string) 2))
                                           :element-type '(unsigned-byte 8))
                 for char-index from 0 below (length hex-string) by 2
                 for result-index upfrom 0
                 do
              (setf (aref result result-index)
                    (parse-integer hex-string :start char-index :end (+ char-index 2)
                                   :radix 16))
                 finally (return result)))
         (to-hex (vector)
           (format nil "~{~2,'0X~}" (map 'list #'identity vector))))
    (loop for count from 1
          for (source . digest) in testsuite
          for binary-source = (from-hex source)
          for binary-digest = (from-hex digest)
          for test-digest = (funcall function binary-source)
          do
       (format
         *trace-output*
         "~2&Test-Case ~D:~%  Input: ~A~%  Required: ~A~%  Returned: ~A~%"
         count source digest (to-hex test-digest))
          when (equalp binary-digest test-digest)
            do (format *trace-output* "  OK~%")
          else
            count 1 into failed
            and do (format *trace-output* "  FAILED~%")
          finally
       (format *trace-output*
               "~2&~[All ~D test cases succeeded~:;~:*~D of ~D test cases failed~].~%"
               failed (1- count))
       (return (zerop failed)))))

(defun read-testsuite-from-file (file)
  (with-open-file (in file)
    (loop with testsuite = nil
          with skip = nil
          with length = nil
          with message = nil
          for line = (read-line in nil nil)
          until (null line)
          do
       (cond
         ((zerop (length line)))
         ((char= (char line 0) #\#))
         ((and (>= (length line) 6)
               (string= line "Len = " :end1 6))
          (setq length (ignore-errors (parse-integer line :start 6))
                skip (or (null length)
                         (not (zerop (mod length 8))))))
         ((and (not skip)
               (>= (length line) 6)
               (string= line "Msg = " :end1 6))
          (setq message (if (zerop length) "" (subseq line 6))))
         ((and (not skip) message
               (>= (length line) 5)
               (string= line "MD = " :end1 5))
          (push (cons message (subseq line 5)) testsuite)))
          finally
       (return (nreverse testsuite)))))
          
(defun test-with-testsuite-from-file (file function)
  (let ((testsuite (read-testsuite-from-file file)))
    (test-with-testsuite testsuite function)))

(defun test-keccak-msgkat (directory &optional function)
  (loop with result = t
        for (filename total-bits bit-rate output-bits) in
        '(("ShortMsgKAT_224.txt" 1600 1152 224)
          ("ShortMsgKAT_256.txt" 1600 1088 256)
          ("ShortMsgKAT_384.txt" 1600  832 384)
          ("ShortMsgKAT_512.txt" 1600  576 512)
          ("LongMsgKAT_224.txt" 1600 1152 224)
          ("LongMsgKAT_256.txt" 1600 1088 256)
          ("LongMsgKAT_384.txt" 1600  832 384)
          ("LongMsgKAT_512.txt" 1600  576 512))
        do
     (unless
         (test-with-testsuite-from-file
          (merge-pathnames filename directory)
          (if (null function)
              (lambda (message) (keccak total-bits bit-rate output-bits message))
              (lambda (message)
                (funcall function total-bits bit-rate output-bits message))))
       (setq result nil))
        finally
     (return result)))

(defun test-sha3-msgkat (directory &optional function)
  (loop with result = t
        for (filename total-bits bit-rate output-bits) in
        '(("ShortMsgKAT_SHA3-224.txt" 1600 1152 224)
          ("ShortMsgKAT_SHA3-256.txt" 1600 1088 256)
          ("ShortMsgKAT_SHA3-384.txt" 1600  832 384)
          ("ShortMsgKAT_SHA3-512.txt" 1600  576 512))
        do
     (unless
         (test-with-testsuite-from-file
          (merge-pathnames filename directory)
          (if (null function)
              (lambda (message) (keccak total-bits bit-rate output-bits message))
              (lambda (message)
                (funcall function total-bits bit-rate output-bits message))))
       (setq result nil))
        finally
     (return result)))
