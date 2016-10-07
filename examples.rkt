#lang racket/base

(require "spore.rkt"
         racket/contract)

(define cell 0)

(define-spore count
  ([cell integer? #:mutable]
   [+ (-> integer? integer? integer?)])
  ()
  (integer?)
  (set! cell (+ cell 1))
  cell)

(define-spore outer
  ([cell integer?]
   [integer? any/c])
  ()
  (any/c)
  (spore ([cell integer?]) () (integer?) cell))

(define-spore get
  ([cell integer? #:mutable])
  ()
  (integer?)
  cell)

(define/contract test
  (spore/c #:opaque-ok? #f any/c (between/c 0 3) any/c)
  get)

(test)
(count)
(count)
(count)
(count)
(test)
