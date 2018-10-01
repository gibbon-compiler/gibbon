#lang racket

;; Laith, this is an example of how to pack binary data for benchmark inputs.

;; Bring in the data type definitions, including pack-Tree:
(require "./traversal.gib")


(define x (Leaf 3.3 4.4 1))

(define bytestring (pack-Tree x))

(call-with-output-file "out.bin"
  (lambda (port) (write-bytes bytestring port)))
