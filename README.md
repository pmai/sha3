[![Build Status](https://travis-ci.org/pmai/sha3.svg?branch=master)](https://travis-ci.org/pmai/sha3)

This library is an implementation of the Secure Hash Algorithm 3
([SHA-3][]), also known as [Keccak][].  The implementation is
constrained to messages with an integral number of octets, i.e.
sub-byte length messages are not supported.

**NOTE** that prior to release 1.0.2 this package had a bug in the
generation of message digests where multiple calls to sha3-update
with partial buffers could lead to input data being ignored and
therefore erroneous message digests being generated.  Uses with
only one call to sha3-update and the high-level routines were not
affected by this bug.

**NOTE** that prior to release 1.1.0 this package computed digests
based on the Keccak submission to the SHA-3 contest and did not
yet take into account the added suffix that the FIPS 202 SHA-3
final standard adds to messages prior to calculating the digest,
since this was not part of the Keccak submission.  Starting with
1.1.0 the functions in the sha3 package do by default calculate
disgests that match the FIPS 202 standard, and will calculate
the old pre-standard digests only if the new optional keyword
argument `:raw-keccak-p` is passed with a true value.

The code should be portable across nearly all ANSI compliant CL
implementations with specialized versions tuned for implementations
that offer unboxed 64bit arithmetic, unboxed 32bit arithmetic and for
implementations with efficient fixnum arithmetic (requiring fixnums
that can represent (unsigned-byte 16)).  Especially the 64 and 32bit
implementations have been mostly optimized for SBCL and CMU CL.  For
those implementations, digests with a 1024 bit-rate (and 288 bit
digest output) can be generated in between 30 (64bit SBCL) to around
100 (32bit CMU CL) cycles/byte on an i7-640M; whereas optimized
C/assembler implementations reach around 12 to 50 cycles/byte on 64/32
bit Intel hardware.  The reason for the discrepancy probably lies in
missing peephole and dependency optimizations in the SBCL/CMU CL
compiler backend.

The mid-level interfaces to the digest routines are the functions

- `sha3:sha3-init &key output-bit-length bit-rate`
  
  Create and return a new SHA-3 state.  If `output-bit-length` is
  specified then the state will run at the bit rate specified for the
  given output bit length.  If `output-bit-length` is unspecified,
  `bit-rate` can be specified to select a suitable bit rate.  If both
  are left unspecified then a default bit rate of 1024 bits is
  selected, which is suitable for arbitrary output bit lengths of up
  to 288 bits.

- `sha3:sha3-copy state`
  
  Return an independent copy of the SHA-3 state `state`.

- `sha3:sha3-state-p state`
  
  Test whether a given object is a SHA-3 state, i.e. is an instance of
  the class `sha3:sha3-state`.

- `sha3:sha3-update state vector &key (start 0) (end (length vector))`
  
  Update the given SHA-3 state `state` from `vector`, which must be a
  simple-array with element-type (unsigned-byte 8), bounded by `start`
  and `end`, which must be numeric bounding-indices.

- `sha3:sha3-final state &key output-bit-length raw-keccak-p`
  
  If the given SHA-3 state `state` has not already been finalized,
  finalize it by processing any remaining input in its buffer, with
  the specified suffix of 01 and suitable padding as specified by the
  SHA-3 standard (the specified SHA-3 suffix can be elided with the
  optional keyword argument `raw-keccak-p` to generate digests as the
  initial Keccak submission would have generated).  Returns the
  message digest as a `simple-array` of `(unsigned-byte 8)`.  The
  length of the returned digest is determined either by the output bit
  length or bit rate specified on state creation, or for the special
  case of default parameters being used, by the optional keyword
  argument `output-bit-length`.  If the state has previously been
  finalized, the function will return the digest again.

For convenience the following high-level functions produce digests in
one step from 1d simple-arrays and streams with element-type
`(unsigned-byte 8)`, as well as files:

- `sha3:sha3-digest-vector vector &key (start 0) end (output-bit-length 512) raw-keccak-p`
  
  Calculate an SHA-3 message-digest of data in `vector`, which should
  be a 1d simple-array with element type `(unsigned-byte 8)`, bounded
  by `start` and `end`.  The bit length of the message digest produced
  is controlled by `output-bit-length`, which can take on the values
  224, 256, 288, 384 and 512, which is the default value.  Using the
  optional `raw-keccak-p` keyword argument the SHA-3 mandated 01 suffix
  that is appended to the actual message prior to padding can be elided
  to yield message digests that match the original Keccak submission
  instead of the actual SHA-3 standard.  Use this option only for
  compatibility with historical implementations.

- `sha3:sha3-digest-stream stream &key (output-bit-length 512) raw-keccak-p`
  
  Calculate an SHA-3 message-digest of data read from `stream`, which
  should be a `stream` with element type `(unsigned-byte 8)`. The bit
  length of the message digest produced is controlled by
  `output-bit-length`, which can take on the values 224, 256, 288, 384
  and 512, which is the default value. Using the optional `raw-keccak-p`
  keyword argument the SHA-3 mandated 01 suffix that is appended to the
  actual message prior to padding can be elided to yield message digests
  that match the original Keccak submission instead of the actual SHA-3
  standard.  Use this option only for compatibility with historical
  implementations.  

- `sha3:sha3-digest-file pathname &key (output-bit-length 512) raw-keccak-p`
  
  Calculate an SHA-3 message-digest of the file specified by
  `pathname`.  The bit length of the message digest produced is
  controlled by `output-bit-length`, which can take on the values 224,
  256, 288, 384 and 512, which is the default value. Using the optional
  `raw-keccak-p` keyword argument the SHA-3 mandated 01 suffix that is
  appended to the actual message prior to padding can be elided to yield
  message digests that match the original Keccak submission instead of
  the actual SHA-3 standard.  Use this option only for compatibility
  with historical implementations.

Note that in order to generate a message digest of a string it will
have to be converted to a `simple-array` with element-type
`(unsigned-byte 8)` in the proper output-encoding.  This will have to
rely on implementation-specific functions and is not part of the SHA3
library.

The file `keccak-reference.lisp` contains a slow simple reference
implementation, and testdriver code, which allows testing of the tuned
implementations against this reference and against test data available
from the Keccak Site at: http://keccak.noekeon.org/KeccakKAT-3.zip

The testcases from the Keccak test data can be run with the following
form:

```lisp
(keccak:test-keccak-msgkat 
 "/Path/To/MsgKatDirectory"
 (lambda (total-bits bit-rate output-bits message)
   (declare (ignore total-bits bit-rate))
   (sha3:sha3-digest-vector message :output-bit-length output-bits :raw-keccak-p t)))
```

The adapted SHA-3 testcases from the Keccak Code Package test vectors
available under https://github.com/gvanas/KeccakCodePackage/tree/master/TestVectors
can be run with the following form:

```lisp
(keccak:test-sha3-msgkat 
 "/Path/To/MsgKatDirectory"
 (lambda (total-bits bit-rate output-bits message)
   (declare (ignore total-bits bit-rate))
   (sha3:sha3-digest-vector message :output-bit-length output-bits)))
```

This SHA-3 implementation is licensed under the MIT-style license
contained in the file COPYING and the header of each source file.
Many thanks go to the Keccak Team (Guido Bertoni, Joan Daemen, Michaël
Peeters and Gilles Van Assche, cf. http://keccak.team) for
their algorithm and excellent documentation and reference
implementations.

Please direct any feedback to pmai@pmsf.de.  A git repository of this
library is available under git://github.com/pmai/sha3.git

[SHA-3]: https://en.wikipedia.org/wiki/SHA-3
[Keccak]: https://keccak.team/
