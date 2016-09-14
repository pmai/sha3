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
;;;; This file contains the implementation of mid- and high-level
;;;; SHA-3 functions based on the optimized Keccak implementations.
;;;; 
;;;; The main entry points are the mid-level functions sha3-init,
;;;; sha3-update and sha3-final to initialize, update and finalize an
;;;; sha3 hash, and sha3-copy in order to copy a sha3 state.
;;;;
;;;; For convenience high-level functions to hash a given vector,
;;;; stream or file are provided as sha3-digest-vector,
;;;; sha3-digest-stream and sha3-digest-vector.
;;;;

;;;
;;; Mid-Level Routines
;;;

(defstruct (sha3-state
             (:constructor make-sha3-state (bit-rate))
             (:copier))
  (state (make-keccak-1600-state) :type keccak-1600-state :read-only t)
  (bit-rate 1024 :type (integer 0 1600) :read-only t)
  (buffer (make-array 200 :element-type '(unsigned-byte 8)) :read-only t
         :type (simple-array (unsigned-byte 8) (200)))
  (buffer-index 0 :type (integer 0 199))
  (finalized-p nil))

(defun sha3-init (&key (output-bit-length nil output-bit-length-p)
                  (bit-rate (if (and output-bit-length-p
                                     output-bit-length)
                                (- 1600 (* 2 output-bit-length))
                                1024)))
  "Create and return a new SHA-3 state.  If `output-bit-length' is specified
then the state will run at the bit rate specified for the given output bit
length.  If `output-bit-length' is unspecified, `bit-rate' can be specified
to select a suitable bit rate.  If both are left unspecified then a default
bit rate of 1024 bits is selected, which is suitable for arbitrary output
bit lengths of up to 288 bits."
  (check-type output-bit-length (member nil 224 256 288 384 512)
              "Legal output-bit-length specifier for SHA-3/Keccak-1600")
  (check-type bit-rate (member 576 832 1024 1088 1152)
              "Legal bit-rate for SHA-3/Keccak-1600")
  (if (or (null output-bit-length)
          (= bit-rate (- 1600 (* 2 output-bit-length)))
          (= bit-rate 1024))
      (make-sha3-state bit-rate)
      (error "Illegal combination of output-bit-length ~D and bit-rate ~D."
             output-bit-length bit-rate)))

(defun sha3-copy (state)
  "Return an independent copy of the SHA-3 state `state'."
  (let ((result (make-sha3-state (sha3-state-bit-rate state))))
    (setf (sha3-state-buffer-index result) (sha3-state-buffer-index state)
          (sha3-state-finalized-p result) (sha3-state-finalized-p state))
    (replace (sha3-state-buffer result) (sha3-state-buffer state))
    (replace (sha3-state-state result) (sha3-state-state state))
    result))

(defun sha3-update (state vector &key (start 0) (end (length vector)))
  "Update the given SHA-3 state `state' from `vector', which must be
a simple-array with element-type (unsigned-byte 8), bounded by `start'
and `end', which must be numeric bounding-indices."
  (declare (type sha3-state state) 
           (type (simple-array (unsigned-byte 8) (*)) vector)
           (type fixnum start end)
           (optimize (speed 3) (safety 1) (space 0) (debug 1)))
  (let* ((keccak-state (sha3-state-state state))
         (buffer (sha3-state-buffer state))
         (buffer-index (sha3-state-buffer-index state))
         (bit-rate (sha3-state-bit-rate state))
         (rate-bytes (truncate bit-rate 8)))
    (declare (type keccak-1600-state keccak-state)
             (type (simple-array (unsigned-byte 8) (200)) buffer)
             (type (integer 0 199) buffer-index)
             (type (integer 0 1600) bit-rate)
             (type (integer 0 200) rate-bytes)
             #.*optimize-declaration*)
    ;; Handle potential remaining bytes
    (unless (zerop buffer-index)
      (let ((remainder (- rate-bytes buffer-index))
            (length (- end start)))
        (declare (type fixnum remainder length))
        (replace buffer vector :start1 buffer-index :start2 start :end2 end)
        ;; Return if still unfilled buffer
        (when (< length remainder)
          (incf (sha3-state-buffer-index state) length)
          (return-from sha3-update))
        ;; Else handle now complete buffer
        (keccak-state-merge-input keccak-state bit-rate buffer 0)
        (keccak-f keccak-state)
        (setf (sha3-state-buffer-index state) 0
              start (+ start remainder))))
    ;; Now handle full blocks, stuff any remainder into buffer
    (loop for block-offset of-type fixnum from start below end by rate-bytes
          do
       (cond
         ((<= (+ block-offset rate-bytes) end)
          (keccak-state-merge-input keccak-state bit-rate vector block-offset)
          (keccak-f keccak-state))
         (t
          (replace buffer vector :start1 0 :start2 block-offset)
          (setf (sha3-state-buffer-index state) (- end block-offset)))))))

(defun sha3-final (state &key (output-bit-length nil output-bit-length-p) raw-keccak-p)
  "If the given SHA-3 state `state' has not already been finalized,
finalize it by processing any remaining input in its buffer, with
the specified suffix of 01 and suitable padding as specified by the
SHA-3 standard (the specified SHA-3 suffix can be elided with the
optional keyword argument `raw-keccak-p' to generate digests as the
initial Keccak submission would have generated).   Returns the
message digest as a simple-array of (unsigned-byte 8).  The length
of the returned digest is determined either by the output bit length
or bit rate specified on state creation, or for the special case of
default parameters being used, by the optional keyword argument
`output-bit-length'.  If the state has previously been finalized,
the function will return the digest again."
  (declare (type sha3-state state)
           (type (or null (integer 0 1600)) output-bit-length)
           (optimize (speed 3) (safety 1) (space 0) (debug 1)))
  (let ((keccak-state (sha3-state-state state))
        (buffer (sha3-state-buffer state))
        (buffer-index (sha3-state-buffer-index state))
        (bit-rate (sha3-state-bit-rate state))
        (finalized-p (sha3-state-finalized-p state)))
    (declare (type keccak-1600-state keccak-state)
             (type (simple-array (unsigned-byte 8) (200)) buffer)
             (type (integer 0 199) buffer-index)
             (type (integer 0 1600) bit-rate)
             (type (or null (simple-array (unsigned-byte 8) (*))) finalized-p)
             #.*optimize-declaration*)
    ;; Determine output-bit-length
    (if output-bit-length-p
        (unless (or (= bit-rate 1024)
                    (= (* 2 output-bit-length) (- 1600 bit-rate)))
          (error "Illegal output-bit-length ~D specified!" output-bit-length))
        (setq output-bit-length (truncate (- 1600 bit-rate) 2)))
    (cond
      ;; Check if already finalized
      (finalized-p
       (unless (= (* (length finalized-p) 8) output-bit-length)
         (error "Mismatch in output-bit-length ~D in repeated call to sha3-final! ~
                 Should be: ~D!"
                output-bit-length (* (length finalized-p) 8)))
       finalized-p)
      ;; Finalize
      (t
       (keccak-state-merge-input keccak-state bit-rate 
                                 (pad-message-to-width
                                  (subseq buffer 0 buffer-index)
                                  bit-rate
                                  (not raw-keccak-p))
                                 0)
       (keccak-f keccak-state)
       (setf (sha3-state-buffer-index state) 0
             (sha3-state-finalized-p state)
             (keccak-state-extract-output keccak-state output-bit-length))))))

;;;
;;; High-Level Routines
;;;

(defun sha3-digest-vector (vector &key (start 0) end 
                           (output-bit-length 512)
                           raw-keccak-p)
  "Calculate an SHA-3 message-digest of data in `vector', which should
be a 1d simple-array with element type (unsigned-byte 8), bounded by
`start' and `end'.  The bit length of the message digest produced is
controlled by `output-bit-length', which can take on the values 224,
256, 288, 384 and 512, which is the default value.  Using the optional
`raw-keccak-p' keyword argument the SHA-3 mandated 01 suffix that is
appended to the actual message prior to padding can be elided to yield
message digests that match the original Keccak submission instead of
the actual SHA-3 standard.  Use this option only for compatibility
with historical implementations."
  (declare (optimize (speed 3) (safety 3) (space 0) (debug 1))
           (type (simple-array (unsigned-byte 8) (*)) vector)
           (type fixnum start)
           (type (or null fixnum) end)
           (type (integer 0 1600) output-bit-length))
  (locally
      (declare (optimize (safety 1) (debug 0)))
    (let ((state (sha3-init :output-bit-length output-bit-length)))
      (declare (type sha3-state state))
      (let ((real-end (or end (length vector))))
        (declare (type fixnum real-end))
        (sha3-update state vector :start start :end real-end))
      (sha3-final state :raw-keccak-p raw-keccak-p))))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defconstant +buffer-size+ (* 128 1024)
    "Size of internal buffer to use for `sha3-digest-stream' and 
`sha3-digest-file' operations."))

(deftype buffer-index () `(integer 0 ,+buffer-size+))

(defun sha3-digest-stream (stream &key (output-bit-length 512) raw-keccak-p)
  "Calculate an SHA-3 message-digest of data read from `stream', which
should be a stream with element type (unsigned-byte 8).  The bit
length of the message digest produced is controlled by
`output-bit-length', which can take on the values 224, 256, 288, 384
and 512, which is the default value.  Using the optional `raw-keccak-p'
keyword argument the SHA-3 mandated 01 suffix that is appended to the
actual message prior to padding can be elided to yield message digests
that match the original Keccak submission instead of the actual SHA-3
standard.  Use this option only for compatibility with historical
implementations."
  (declare (optimize (speed 3) (safety 3) (space 0) (debug 1))
           (type stream stream)
           (type (integer 0 1600) output-bit-length))
  (locally
      (declare (optimize (safety 1) (debug 0)))
    (unless (equal (stream-element-type stream) '(unsigned-byte 8))
      (error "Illegal stream-element-type ~S, must be ~S."
             (stream-element-type stream) '(unsigned-byte 8)))
    (let ((buffer (make-array '(#.+buffer-size+) :element-type '(unsigned-byte 8)))
          (state (sha3-init :output-bit-length output-bit-length)))
      (declare (type sha3-state state)
               (type (simple-array (unsigned-byte 8) (#.+buffer-size+)) buffer))
      (loop for bytes of-type buffer-index = (read-sequence buffer stream)
            do (sha3-update state buffer :end bytes)
            until (< bytes +buffer-size+)
            finally
         (return (sha3-final state :raw-keccak-p raw-keccak-p))))))

(defun sha3-digest-file (pathname &key (output-bit-length 512) raw-keccak-p)
  "Calculate an SHA-3 message-digest of the file specified by
`pathname'.  The bit length of the message digest produced is
controlled by `output-bit-length', which can take on the values 224,
256, 288, 384 and 512, which is the default value.  Using the optional
`raw-keccak-p' keyword argument the SHA-3 mandated 01 suffix that is
appended to the actual message prior to padding can be elided to yield
message digests that match the original Keccak submission instead of
the actual SHA-3 standard.  Use this option only for compatibility
with historical implementations."
  (declare (optimize (speed 3) (safety 3) (space 0) (debug 1))
           (type (integer 0 1600) output-bit-length))
  (locally
      (declare (optimize (safety 1) (debug 0)))
    (with-open-file (stream pathname :element-type '(unsigned-byte 8))
      (sha3-digest-stream stream :output-bit-length output-bit-length :raw-keccak-p raw-keccak-p))))
