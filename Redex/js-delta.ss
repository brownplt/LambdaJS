#lang scheme

(require (lib "13.ss" "srfi"))
(require (lib "14.ss" "srfi"))
(require (lib "pregexp.ss"))

(provide λJS-operator? λJS-δ)

(define (λJS-operator? x)
  (member x
   '(+ string-+ 
      % - * / === ==
      < string-< 
      & \| ^ ~ << >> >>>
      to-integer to-uint-32 to-int-32
      = 
      typeof surface-typeof
      prim->number prim->string prim->bool
      has-own-prop?
      print-string
      str-contains str-startswith str-length str-split-regexp str-split-strexp
      regexp-quote regexp-match
      obj-iterate-has-next? obj-iterate-next obj-iterate-key
      obj-delete obj-can-delete?
      math-sin math-cos math-log math-exp math-abs math-pow
      prim?)))

(define to-integer
  (lambda (number)
    (* (if (> number 0.0) 1 -1)
       (inexact->exact (floor (abs number))))))

;;9.8.1, steps 5-10
;still not fully followed spec yet
(define js-number->string
  (lambda (m)
    (if (= (floor m) m)
        (number->string (inexact->exact (floor m)))
        (number->string m))))

;;helper to turn a scheme list into an array-like internal object
;;its just used to pass array-like values like from str-split
(define list->jsobj_helper
  (lambda (l i)
    (if (empty? l) 
        `()
        (let ([res (list->jsobj_helper (rest l) (+ i 1))])
          (cons `(,(number->string i) ,(first l)) res)))))
(define list->jsobj
  (lambda (l)
    `(object ,(cons `("length" ,(length l)) (list->jsobj_helper l 0)))))

;;and the hash/interp version:
(define list->jsobjhash_helper
  (lambda (l i h)
    (if (empty? l) 
        h
        (let ([res (list->jsobjhash_helper (rest l) (+ i 1) h)])
          (hash-set res (number->string i) (first l))))))

(define list->jsobjhash
  (lambda (l)
    (let ([reshash (make-immutable-hash `())])
      (hash-set (list->jsobjhash_helper l 0 reshash)
                "length" (length l)))))
      

(define λJS-δ
  (match-lambda
    [`(+ ,(? number? x) ,(? number? y)) (+ x y)]
    [`(string-+ ,(? string? x) ,(? string? y)) (string-append x y)]
    [`(- ,(? number? x) ,(? number? y)) (- x y)]
    [`(* ,(? number? x) ,(? number? y)) (* x y)]
    [`(/ ,(? number? x) 0) '(err "division by zero")]
    [`(/ ,(? number? x) ,(? number? y)) (/ x y)]
    ; TODO: bitwise operators require integers.  Instead of restricting the arguments to integers,
    ; why not have the float->int conversion done here?
    [`(& ,(? number? x) ,(? number? y)) (bitwise-and x y)]
    [`(\| ,(? number? x) ,(? number? y)) (bitwise-ior x y)]
    [`(^ ,(? number? x) ,(? number? y)) (bitwise-xor x y)]
    [`(~ ,(? number? x)) (bitwise-not x)]
    ;;TODO: should these truncate the rhs to 0x1F, or should that be desugarr?
    [`(<< ,(? number? x) ,(? number? y)) (arithmetic-shift x y)]
    [`(>> ,(? number? x) ,(? number? y)) (arithmetic-shift x (- y))]
    ;;TODO: make >>> zero-fill instead of sign-preserve
    [`(>>> ,(? number? x) ,(? number? y)) (arithmetic-shift x (- y))]
    ; Section 11.5.3
    [`(% +nan.0 ,(? number? y)) +nan.0]
    [`(% ,(? number? x) +nan.0) +nan.0]
    [`(% +inf.0 ,(? number? y)) +nan.0]
    [`(% ,(? number? x) +0.0) +nan.0]
    [`(% ,(? number? x) -0.0) +nan.0]
    [`(% ,(? number? x) +inf.0) x]
    [`(% ,(? number? x) -inf.0) x]
    [`(% +0.0 ,(? number? y)) +0.0]
    [`(% -0.0 ,(? number? y)) -0.0]
    [`(% ,(? number? x) ,(? number? y))
     (let ((nOverD (/ x y)))
       (let ((q (if (> nOverD 0.0) (floor nOverD) (ceiling nOverD))))
         (- x (* y q))))]
  [`(=== ,x ,y)
   (if (and (number? x) (number? y))
       ; Turns out that Scheme's = function is identical to the algorithm in 11.9.6 of ECMA262.
       (= x y)
       (equal? x y))]
  ; Algorithm 11.9.3, steps 1 through 19.  Steps 20 and 21 have to be desugared to access the heap.
  [`(== ,v1 ,v2)
   (or
    (equal? v1 v2)
    (and (number? v1) (number? v2) (= v1 v2))
    (and (equal? v1 'null) (equal? v2 'undefined))
    (and (equal? v1 'undefined) (equal? v1 'null))
    (and (number? v1) (string? v2) (= v1 (λJS-δ `(prim->number ,v2))))
    (and (string? v1) (number? v2) (= (λJS-δ `(prim->number ,v1)) v2))
    (and (boolean? v1) (number? v2) (= (if v1 1 0) v2))
    (and (number? v1) (boolean? v2) (= v1 (if v2 1 0))))]
  [`(< +nan.0 ,(? number? y)) 'undefined]
  [`(< ,(? number? x) +nan.0) 'undefined]
  [`(< ,(? number? x) ,(? number? y)) (< x y)]
  ;9.4, 9.5, 9.6
  ;these to-ints act on the #s. code that uses ToInt32 as in ECMA must do toNumber first
  ;not sure why to-integer returns infinity, sometimes.  TODO: This is by the spec, right?
  [`(to-integer +nan.0) 0.0]
  [`(to-integer +0.0) +0.0]
  [`(to-integer -0.0) -0.0]
  [`(to-integer +inf.0) +inf.0]
  [`(to-integer -inf.0) -inf.0]
  [`(to-integer ,(? number? x)) (to-integer x)]
  ;this is different from the ToUInt32 in ECMA in that it must have had ToNumber called on it
  ;already.
  [`(to-uint-32 +nan.0) 0]
  [`(to-uint-32 +0.0) 0]
  [`(to-uint-32 -0.0) 0]
  [`(to-uint-32 +inf.0) 0]
  [`(to-uint-32 -inf.0) 0]
  [`(to-uint-32 ,(? number? x)) (modulo (to-integer x) (expt 2 32))]
  [`(to-int-32 +nan.0) 0]
  [`(to-int-32 +0.0) 0]
  [`(to-int-32 -0.0) 0]
  [`(to-int-32 +inf.0) 0]
  [`(to-int-32 -inf.0) 0]
  [`(to-int-32 ,(? number? x))
   (let ((n (modulo (to-integer x) (expt 2 32))))
     (if (> n (expt 2 31))
         (- n (expt 2 32))
         n))]
  [`(string-< ,(? string? x) ,(? string? y)) (string<? x y)]
  [`(surface-typeof (object [,_ ,_] ... ["$code" ,_] [,_ ,_] ...)) "function"]
  [`(surface-typeof (object [,_ ,_] ...)) "object"]
  [`(surface-typeof null) "object"]
  [`(surface-typeof undefined) "undefined"]
  [`(surface-typeof null) "object"]
  [`(surface-typeof ,(? number? _)) "number"]
  [`(surface-typeof ,(? string? _)) "string"]
  [`(surface-typeof ,(? boolean? _)) "boolean"]
  [`(surface-typeof ,(? hash? obj))
   (if (hash-has-key? obj "$code")
       "function"
       "object")]
  [`(surface-typeof ,x) `(err ,(format "surface-typeof applied to ~a" x))]
  [`(typeof (lambda (,x ...) ,e)) "lambda"]
  [`(typeof ,(? number? _)) "number"]
  [`(typeof ,(? string? _)) "string"]
  [`(typeof ,(? boolean? _)) "boolean"]
  [`(typeof null) "null"]
  [`(typeof (object (,_ ,_) ...)) "object"]
  [`(typeof undefined) "undefined"]
  [`(typeof (ref ,(? integer? _))) "location"]
  ; for our interpreter
  [`(typeof ,(? box? _)) "location"] 
  [`(typeof ,(? hash? _)) "object"]
  [`(typeof ,(? procedure? _)) "lambda"]
  ; Section 9.3, excluding objects
  [`(prim->number undefined) +nan.0]
  [`(prim->number null) +0.0]
  [`(prim->number #t) 1]
  [`(prim->number #f) +0.0]
  [`(prim->number ,(? number? x)) (+ x 0.0)] ;make sure it's floating point
  ; TODO: This should be algorithm 9.3.1
  [`(prim->number ,(? string? x)) 
   (let ([res (string->number x)])
     (if (eq? res #f) +nan.0 res))]
  [`(prim->string undefined) "undefined"]
  [`(prim->string null) "null"]
  [`(prim->string #t) "true"]
  [`(prim->string #f) "false"]
  [`(prim->string +nan.0) "NaN"] ;number cases are algorithm 9.8.1
  [`(prim->string +0.0) "0"]
  [`(prim->string -0.0) "0"]
  [`(prim->string +inf.0) "Infinity"]
  [`(prim->string -inf.0) "Infinity"]
  [`(prim->string ,(? number? x)) (js-number->string x)]
  [`(prim->string ,(? string? x)) x]
  [`(prim->string ,x) `(err ,(format "TypeError: prim->string received ~a" x))]
  [`(prim->bool undefined) #f]
  [`(prim->bool null) #f]
  [`(prim->bool #t) #t]
  [`(prim->bool #f) #f]
  [`(prim->bool +nan.0) #f]
  [`(prim->bool +0.0) #f]
  [`(prim->bool -0.0) #f]
  [`(prim->bool ,(? number? _)) #t]
  [`(prim->bool ,(? string? x)) (not (zero? (string-length x)))]
  [`(prim->bool (object (,_ ,_) ...)) #t]
  [`(prim->bool ,(? hash? _)) #t]
  [`(prim->bool ,(? box? _)) #t] ; an object reference
  [`(prim? ,x)
   (or (number? x) (string? x) (boolean? x) (eq? 'undefined x) (eq? 'null x))]
  [`(has-own-prop? (object [,field-names ,_] ...) ,(? string? x))
   (and (member x field-names) #t)]
  [`(has-own-prop? ,(? hash? obj) ,(? string? x))
   (hash-has-key? obj x)]
  [`(print-string ,(? string? s))
   (begin
     (display s)
     (newline)
     'undefined)]
  [`(str-contains ,(? string? a) ,(? string? b))
   (not (eq? (string-contains a b) #f))]
  [`(str-startswith ,(? string? a) ,(? string? b))
   (and (> (string-length a) 0)
        (> (string-length b) 0)
        (eq? (string-ref a 0) (string-ref b 0)))]
  ;;TODO: make the following work for Redex objects too
  ;;'undefined' is the initial iterator. makes the Desugar code cleaner.
  [`(obj-iterate-has-next? ,(? hash? obj) undefined)
   (not (eq? (hash-iterate-first obj) #f))]
  [`(obj-iterate-has-next? ,(? hash? obj) ,(? number? cur))
   (not (eq? (hash-iterate-next obj cur) #f))]
  [`(obj-iterate-next ,(? hash? obj) undefined)
   (hash-iterate-first obj)]
  [`(obj-iterate-next ,(? hash? obj) ,(? number? cur))
   (hash-iterate-next obj cur)]
  [`(obj-iterate-key ,(? hash? obj) ,(? number? cur))
   (hash-iterate-key obj cur)]
  [`(str-length ,(? string? a)) (string-length a)]
  ;;TODO: make this splice capturing parens or w/e
  ;;TODO: make a non-hash version......
  [`(str-split-strexp ,(? string? a) ,(? string? b))
   (list->jsobjhash (pregexp-split (pregexp (pregexp-quote b)) a))]
  [`(str-split-regexp ,(? string? a) ,(? string? b))
   (list->jsobjhash (pregexp-split (pregexp b) a))]  
  ;;return true or false depending on 8.6.2.5
  ;;TODO: right now it assumes $-starters are not deletable,
  ;;but some other things like Object.prototype should also  ;;not be deletable
  [`(obj-can-delete? ,(? hash? obj) ,(? string? name))
   (not (and (> (string-length name) 0)
            (eq? (string-ref name 0) #\$)))]

  ;;Math operators
  [`(math-sin ,(? number? n)) (sin n)]  
  [`(math-cos ,(? number? n)) (cos n)]
  [`(math-log ,(? number? n)) (log n)]
  [`(math-exp ,(? number? n)) (exp n)]
  [`(math-abs ,(? number? n)) (abs n)]
  [`(math-pow ,(? number? n) ,(? number? m)) (expt n m)]
  
  ;;using b as an unquoted regexp, find match in the
  ;;string a, return a list w/ all captures etc.
  ;;return undefined if no match found.
  [`(regexp-match ,(? string? a) ,(? string? b))
   (let ([result (pregexp-match (pregexp b) a)])
     (if (eq? #f result) 'undefined (list->jsobjhash result)))]

  ;;quote the given string
  [`(regexp-quote ,(? string? a))
   (pregexp-quote a)]

  [xs `(err ,(format "invalid primitive application: ~a" xs))]))











