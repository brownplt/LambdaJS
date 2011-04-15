#lang scheme
(require redex
         "jscore.ss")


(test (< 10 0) #f)
(test ((lambda (x y) (+ x y)) 90 (+ 1 2)) 93) 
(test (object ["x" 23] ["y" (+ 1 2)]) (object ["x" 23] ["y" 3]))
(test (object ["x" (alloc "orig")]) (object ["x" (ref 1)]))
(test
 ((lambda (obj v) (get-field obj "x")) (object ["x" (alloc "orig")]) "new")
 (ref 1))
(test
 (deref ((lambda (obj v) (set! (get-field obj "x") v)) (object ["x" (alloc "orig")]) "new"))
 "new")
(test
 (deref (get-field
         (deref
          ((lambda (obj v) (set! obj (update-field (deref obj) "x" v)))
           (alloc (object ["y" (alloc "other")]))
           (alloc "new")))
         "x"))
 "new")

(test
 (throw "success")
 (err "success"))

(test
 (try-catch (throw "success") (lambda (x) x))
 "success")

(test
 (try-catch
  (throw "failure")
  (lambda (x) (throw "success")))
 (err "success"))

(test
 (try-catch
  (try-catch
   (throw "exception")
   (lambda (x) "success"))
  (lambda (x) "failure"))
 "success")

 (test
   (try-catch
    (try-finally
     (throw "failure")
     (throw "success"))
    (lambda (x) x))
   "success")

 (test
   (try-finally
    (try-catch
     (throw "failure")
     (lambda (x) "success"))
    "epic failure")
   "success")
 
 (test 
  (label l (break l "success"))
  "success")
 
 (test
  (label l1
         (begin
           (label l2
                  (break l1 "success"))
           (break l2 "failure")))
  "success")
 
 (test
  (label look-no-catch
         (try-finally (throw "failure") 
                      (break look-no-catch "success")))
  "success") 

 (test
   (try-finally
    (label l
           (+ 1 (break l "success")))
    "failure")
   "success")
 
 (test
   (label l
          (try-finally
           (+ 1 (break l "success"))
           "failure"))
   "success")
 
 (test (label x (break y (break x "success")))
       "success")
 
#|
(test
 (get-field ((function (obj v) (set-field! obj "x" v)) (object ["y" "other"]) "new") "x")
 "new")

(test
 (let ([x "call-by-value"])
   (begin
     ((lambda (this y) (set! y "call-by-ref")) x)
     x))
 "call-by-value")

(test
 (let ([obj0 (object ["y" "hello"])])
   (let ([obj (object ["x" obj0])])
     (begin
       (set-field! (get-field obj "x") "y" "new")
       (get-field obj0 "y"))))
 "new")

(test
 (let ([obj0 (object ["x" "initial"])])
   (let ([obj1 (object ["y" obj0])])
     (let ([obj2 (object ["z" (get-field obj1 "y")])])
       ; obj2.z == obj0
       (begin
         (set-field! (get-field obj2 "z") "x" "final")
         (get-field obj0 "x")))))
 "final")


(test
 (let ([animal (alloc (object ["length" 50]))])
   (let ([dog (object ["$proto" animal])])
     (get-field dog "length")))
 50)

(test
 (let ([animal (alloc (object ["length" 50]))])
   (let ([dog (alloc (object ["$proto" animal]))])
     (begin
       (set! dog (update-field (deref dog) "length" 200))
       (= (get-field (deref dog) "length") (get-field (deref animal) "length")))))
 #f)

(test
 (let ([animal (alloc (object ["length" 50]))])
   (let ([dog (object ["$proto" animal])])
     (begin
       (set! animal (update-field (deref animal) "width" "serpents only have length"))
       (get-field dog "width"))))
 "serpents only have length")

(test
 (let ([x 4])
   (begin
     (while (> x 0)
            (set! x (- x 1)))
     x))
 0)

(test
 (let ([f (function (x) (set-field! this "x" x))])
   (* 10 10))
 100)

(test
 (get-field
  (let ([fn (function (x) (set-field! this "x" x))])
    (new fn (+ 90 1)))
  "x")
 91)

(test
 (let ([fn (function (x) (set-field! this "x" x))])
   (instanceof (new fn (+ 90 1)) fn))
 #t)

;;sanity checking
(test (typeof null) "object")
(test (typeof undefined) "undefined")

;;tests messing with 'arguments'
(test
 (let ([fn (function (a b c) (get-field arguments "length"))])
   (fn 100 200 300 400 500))
 5)

(test
 (let ([obj (object ["x" (object ["y" "Hello"])])])
   (begin
     ((lambda (this arguments) 
        (let ([o (get-field arguments "0")])
          (set-field! (get-field o "x") "y" "new"))) obj)
     (get-field (get-field obj "x") "y")))
 "new")

(test ((function() undefined)) undefined)
(test ((function() ((function () undefined)))) undefined)
(test ((function() ((function (x) x) 5))) 5)
(test ((function(y) ((function (x) x) y)) 5) 5)

#;(test
 (let ([to-be-f undefined])
   (let ([f (function (x) 
            (get-field (get-field to-be-f arguments) |0|))])
     (begin
       (set! to-be-f f)
       (f 100))))
 100)

;;let-rec??
#;(test
 (let ([b (function (x) (begin (a) x))]
       [a (function () undefined)])
   (b 100))
 100)

#;(test
 (let ([b (function (x) (begin (a) x))]
       [a (function () (set-field! (get-field b arguments) |0| 400))])
   (b 100))
 400)
       |#
;;modelling return as break
