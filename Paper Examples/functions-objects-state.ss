#lang scheme

(require "../Redex/jscore.ss")

;;; From Section 2.1

(test
 (let ([obj (object ["x" 500] ["y" 100])])
   (let ([select (lambda (name) (get-field obj name))])
     (+ (select "x") (select "y"))))
 600)

(test
 (get-field (object ["x" 7]) "y")
 undefined)

(test
 (update-field (object ["x" 0]) "x" 10)
 (object ["x" 10]))

(test
 (update-field (object ["x" 0]) "z" 20)
 (object ["z" 20] ["x" 0]))

(test
 (delete-field (object ["x" 7] ["y" 13]) "x")
 (object ["y" 13]))


;;; Subject Reduction example

(trace
 (let ([window (alloc (object ["XMLHttpRequest" "DANGER"]))]
       [lookup (lambda (obj field)
                 (if (=== field "XMLHttpRequest")
                     undefined
                     (get-field (deref obj) field)))])
   (lookup window "XMLHttpRequest")))
   