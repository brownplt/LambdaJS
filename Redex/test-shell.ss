#!/usr/bin/env mzscheme
#lang scheme

(require "interp.ss")

(define total 0)
(define errors 0)
(define failures 0)

; JavaScript's object graph has cycles (see desugaring of the .constructor 
; fields).  We either do a lot of work to test cycles correctly, or hack 
; this test.
(define (equal-0? v1 v2)
  (or (equal? v1 v2)
      (and (box? v1) (box? v2)
           (equal-0? (unbox v1) (unbox v2)))
      (and (procedure? v1) (procedure? v2))
      (and (hash? v1) (hash? v2))))

; Test if v1 and v2 are equal.  Caveats:
;
; 1. Assumes that all procedures are equal. 
; 2. Recurs into references, without checking for loops (very unlikely).
; 3. If v1 and v2 are objects, their fields are compared, but nested objects are
;    assumed equal (using equal-0?).
(define (equal-1? v1 v2)
  (or (equal? v1 v2)
      (and (box? v1) (box? v2)
           (equal-1? (unbox v1) (unbox v2)))
      (and (procedure? v1) (procedure? v2))
      (and (hash? v1)(hash? v2)
           (for/last [(item (map cons (hash-map v1 cons) (hash-map v2 cons)))]
             (match item
               [`((,k1 . ,v1) . (,k2 . ,v2))
                (and (equal? k1 k2)
                     (equal-0? v1 v2))]
               [_ false])))))

(for ([test-case (read)])
  (match test-case
    [`(,source ,lhs ,rhs)
     (with-handlers
         ([exn? (λ (exn)
                  (set! errors (add1 errors))
                  (printf "FAILED ~a; signalled an exception:~n~a~n" source exn))])
       (set! total (add1 total))
       (let ([result ((interp empty-env) lhs)]
             [expected ((interp empty-env) rhs)])
         (unless (equal-1? result expected)
           (set! failures (add1 failures))
           (printf "FAILED ~a; got:~n~a~nExpected:~n~a~n" source result expected))))]))

(printf "Testing Complete.~nTotal: ~a, Failures ~a, Exceptions: ~a~n"
        total failures errors)