#lang scheme

; TODO : specify substitution in full
(require redex)
(require "js-delta.ss")
(provide (all-defined-out))

(define-language lambdaJS
  (σ ((loc val) ...))
  (loc natural)
  (prim number string #t #f undefined null)
  (prim+prim-object prim (object [string prim+prim-object] ...))
  ((val obj) prim (lambda (x ...) e) (ref loc) (object [string val] ...))
  (error (err val))
  (prim+prim-object+error prim+prim-object error)
  (prim+error prim error)
  
  ;;strictly for errors:
  (not-object loc prim (lambda (x ...) e) (ref loc))
  (not-string loc number #t #f undefined null (lambda (x ...) e) (ref loc) (object [string val] ...))
  (not-lambda loc prim (ref loc) (object [string val] ...))
  (not-ref loc prim (lambda (x ...) e) (object [string val] ...))
  (not-bool loc number string undefined null (lambda (x ...) e) (ref loc) (object [string val] ...))
  
  (op + string-+ 
      % - * / === ==
      < string-< 
      & \| ^ ~ << >> >>>
      to-integer to-uint-32 to-int-32
      = 
      typeof surface-typeof
      prim->number prim->string prim->bool
      has-own-prop?
      prim?)
  
  (lbl x)
  (e val
     error
     x 
     (op e ...)
     (e e ...)
     (let ([x e] ...) e)
     (set! e e) 
     (alloc e) 
     (deref e) 
     (object [string e] ...)
     (get-field e e) 
     (update-field e e e)
     (delete-field e e)
     (begin e e ...) 
     (if e e e)
     (while e e) 
     (try-catch e (lambda (x) e))
     (try-finally e e)
     (throw e)
     (label lbl e) 
     (break lbl e))
  ((f g x y z) variable-not-otherwise-mentioned)
  
  ; Contexts within try-catch blocks
  (F hole 
     (op val ... F e ...)
     (val ... F e ...)
     (let ([x val] ... [y F] [z e] ...) e)
     (alloc F)
     (deref F)
     (break lbl F)
     (throw F)
     (set! F e) (set! val F)
     (object [string val] ... [string F] [string e] ...)
     (get-field F e)
     (get-field val F)
     (update-field e e F)
     (update-field e F val)
     (update-field F val val)
     (delete-field F e)
     (delete-field val F)
     (begin val ... F e ...)
     (if F e e)
     (label lbl F))
  
  (H hole 
     (op val ... H e ...)
     (val ... H e ...)
     (let ([x val] ... [y H] [z e] ...) e)
     (alloc H)
     (deref H)
     (throw H)
     (set! H e) (set! val H)
     (object [string val] ... [string H] [string e] ...)
     (get-field H e)
     (get-field val H)
     (update-field e e H)
     (update-field e H val)
     (update-field H val val)
     (delete-field F e)
     (delete-field val F)
     (begin val ... H e ...)
     (if H e e)
     (try-catch H (lambda (x) e)))
  
  (E hole 
     (op val ... E e ...)
     (val ... E e ...)
     (let ([x val] ... [y E] [z e] ...) e)
     (alloc E)
     (deref E)
     (break lbl E)
     (throw E)
     (set! E e) (set! val E)
     (object [string val] ... [string E] [string e] ...)
     (get-field E e)
     (get-field val E)
     (update-field e e E)
     (update-field e E val)
     (update-field E val val)
     (delete-field E e)
     (delete-field val E)
     (begin val ... E e ...)
     (if E e e)
     (label lbl E)
     (try-finally E e)
     (try-catch E (lambda (x) e)))
  )
(define-metafunction lambdaJS
  δ : op val ... -> prim+prim-object+error
  [(δ op val ...)
   ,(λJS-δ (term (op val ...)))])

(define-metafunction lambdaJS
  subst-n : (x any) ... any -> any
  [(subst-n (x_1 any_1) (x_2 any_2) ... any_3)
   (subst x_1 any_1 (subst-n (x_2 any_2) ... 
                             any_3))]
  [(subst-n any_3) any_3])

(define-metafunction lambdaJS
  subst : x any any -> any
  ;;don't sub label or break names:
  [(subst x_1 any_1 (break any_2 e_2))
   (break any_2 (subst x_1 any_1 e_2))]
  [(subst x_1 any_1 (label any_2 e_2)) 
   (label any_2 (subst x_1 any_1 e_2))]
  [(subst x_1 any_1 (object [any_15 any_2] ...))
   (object [(subst x_1 any_1 any_15) (subst x_1 any_1 any_2)] ...)]
  [(subst y any_1 (let ([x_2 e_2] ... 
                        [y e_y] 
                        [x_3 e_3] ...) 
                    e_4))
   (let ([x_2 (subst y any_1 e_2)] ... 
         [y (subst y any_1 e_y)] 
         [x_3 (subst y any_1 e_3)] ...)
     e_4)
   (side-condition (not (member (term x_1) (term (x_2 ...)))))]
  [(subst x_1 any_1 (let ([x_2 e_2] ...) e_3))
   ,(term-let ([(x_new ...) (variables-not-in (term (x_1 any_1 e_3)) (term (x_2 ...)))])
              (term 
               (let ([x_new (subst x_1 any_1 e_2)] ...)
                 (subst x_1 any_1 (subst-vars (x_2 x_new) ... e_3)))))]
  [(subst x_1 any_1 (lambda (x_2 ... x_1 x_3 ...) any_2))
   (lambda (x_2 ... x_1 x_3 ...) any_2)
   (side-condition (not (member (term x_1) (term (x_2 ...)))))]
  
  [(subst x_1 any_1 (lambda (x_2 ...) any_2))
   ,(term-let ([(x_new ...)
                (variables-not-in
                 (term (x_1 any_1 any_2)) 
                 (term (x_2 ...)))])
              (term 
               (lambda (x_new ...) 
                 (subst x_1 any_1
                        (subst-vars (x_2 x_new) ... 
                                    any_2)))))]
  [(subst x_1 any_1 x_1) any_1]
  [(subst x_1 any_1 x_2) x_2]
  [(subst x_1 any_1 (any_2 ...))
   ((subst x_1 any_1 any_2) ...)]
  [(subst x_1 any_1 any_2) any_2])

(define-metafunction lambdaJS
  subst-vars : (x any) ... any -> any
  [(subst-vars (x_1 any_1) ... (label x_2 any_2))
   (label x_2 (subst-vars (x_1 any_1) ... any_2))]
  [(subst-vars (x_1 any_1) ... (break x_2 any_2))
   (break x_2 (subst-vars (x_1 any_1) ... any_2))]
  [(subst-vars (x_1 any_1) ... (object [x_2 any_2] ...))
   (object [x_2 (subst-vars (x_1 any_1) ... any_2)] ...)]
  [(subst-vars (x_1 any_1) x_1) any_1]
  [(subst-vars (x_1 any_1) (any_2 ...)) 
   ((subst-vars (x_1 any_1) any_2) ...)]
  [(subst-vars (x_1 any_1) any_2) any_2]
  [(subst-vars (x_1 any_1) (x_2 any_2) ... any_3) 
   (subst-vars (x_1 any_1) 
               (subst-vars (x_2 any_2) ... any_3))]
  [(subst-vars any) any])


(define-metafunction lambdaJS
  alloc-def : val σ -> (loc σ)
  [(alloc-def val_new ((loc val) ...))
   ,(term-let ([loc_new (+ 1 (apply max (term (0 loc ...))))])
              (term (loc_new ((loc_new val_new) (loc val) ...))))])

;;----------------------------------------
;;error-free relation:
(define eval-lambdaJS
  (reduction-relation
   lambdaJS
   (--> (((loc_1 val_1) ... (loc val_old) (loc_3 val_3) ...) 
         (in-hole E (set! (ref loc) val_new)))
        (((loc_1 val_1) ... (loc val_new) (loc_3 val_3) ...) 
         (in-hole E (ref loc)))
        "E-Assign")
   (==> (op val ...) (δ op val ...) 
        "E-Prim")
   (==> ((lambda (x ...) e) val ...)
        (subst-n (x val) ... e)
        "E-Beta")
   (==> (let ([x val] ...) e)
        (subst-n (x val) ... e)
        "E-Let")
   (--> (σ_1 (in-hole E (alloc val)))
        (σ_2 (in-hole E (ref loc)))
        "E-Alloc"
        (where (loc σ_2) (alloc-def val σ_1)))
   (--> (((loc_1 val_1) ... (loc_2 val_2) (loc_3 val_3) ...) (in-hole E (deref (ref loc_2))))
        (((loc_1 val_1) ... (loc_2 val_2) (loc_3 val_3) ...) (in-hole E val_2))
        "E-Deref")
   (==> (get-field (object [string_x val_x] ... [string_y val_y] [string_z val_z] ...) string_y)
        val_y
        "E-GetField")
   (==> (get-field (object [string_x val] ...) string_y)
        undefined
        "E-GetField-NotFound"
        (side-condition
         (and (not (member (term string_y) (term (string_x ...))))
              (not (member (term "$proto") (term (string_x ...)))))))
   (==> (get-field (object [string_x val_x] ... ["$proto" val_prot] [string_z val_z] ...) string_y)
        (get-field (deref val_prot) string_y)
        "E-GetFieldPrototype"
        (side-condition 
         (not (member (term string_y) (term (string_x ... string_z ...))))))   
   (==> (update-field (object [string_x val_x] ... [string_y val_old] [string_z val_z] ...) string_y val_new)
        (object [string_x val_x] ... [string_y val_new] [string_z val_z] ...)
        "E-UpdateField")
   (==> (update-field (object [string_x val] ...) string_y val_new)
        (object [string_y val_new] [string_x val] ...)
        "E-CreateField"
        (side-condition (not (member (term string_y) (term (string_x ...))))))
   (==> (delete-field (object [string_x val_x] ... [string val] [string_y val_y] ...)
                      string)
        (object [string_x val_x] ... [string_y val_y] ...)
        "E-DeleteField")
   (==> (delete-field (object [string_x val_x] ...)
                      string_y)
        (object [string_x val_x] ...)
        "E-DeleteField-NotFound"
        (side-condition (not (member (term string_y) (term (string_x ...))))))
   (==> (begin val ... val_r)
        val_r
        "E-BeginResult")
   (==> (if #t e_1 e_2)
        e_1
        "E-IfTrue")
   (==> (if #f e_1 e_2)
        e_2
        "E-IfFalse")
   (==> (while e_1 e_2) 
        (if e_1 (begin e_2 (while e_1 e_2)) undefined) 
        "E-While")
   (==> (label lbl (in-hole H (break lbl val)))
        val
        "E-Label-Match")
   (==> (label lbl_1 (in-hole H (break lbl_2 val)))
        (break lbl_2 val)
        "E-Label-Pop"
        (side-condition (not (equal? (term lbl_1) (term lbl_2)))))
   (==> (label lbl_1 val)
        val
        "E-Label-Pop-NoBreak")
   (==> (throw val)
        (err val)
        "E-Throw")
   (==> (try-catch (in-hole F (err val)) (lambda (x) e))
        (subst x val e)
        "E-Throw-Caught")
   (==> (try-catch val (lambda (x) e))
        val
        "E-Catch-Pop")
   (--> (σ (in-hole F (err val)))
        (err val)
        "E-Throw-Uncaught")
   (==> (try-finally (in-hole F (err val)) e)
        (begin e (err val))
        "E-Finally-Err")
   (==> (try-finally (in-hole H (break lbl val)) e)
        (begin e (break lbl val))
        "E-Finally-Break")
   (==> (try-finally val e)
        (begin e val)
        "E-Finally-Pop")
   (--> (σ (in-hole E eval-semantic-bomb))
        eval-semantic-bomb
        "E-Eval")
   with
   [(--> (σ (in-hole E e_1)) (σ (in-hole E e_2)))
    (==> e_1 e_2)]))

;;----------------------------------------
;;error reductions:
(define eval-lambdaJS-errors
  (extend-reduction-relation 
   eval-lambdaJS
   lambdaJS
   (--> (((loc_1 val_1) ... ) 
         (in-hole E (set! (ref loc) val_new)))
        (err "Setting invalid ref")
        (side-condition (not (memq (term loc) (term (loc_1 ...)))))
        "E-Assign-NotFound")
   (==> (set! not-ref val)
        (err "Setting a not-ref")
        "E-Assign-NotRef")

   (==> ((lambda (x ...) e) val ...)
        (subst-n (x val) ... e) 
        "E-Beta"
        (side-condition (= (length (term (x ...)))
                           (length (term (val ...))))))   
   (==> ((lambda (x ...) e) val ...)
        (err "Wrong number of args to lambda")
        "E-Beta-Error"
        (side-condition (not (= (length (term (x ...)))
                                (length (term (val ...)))))))
   (==> (not-lambda val ...)
        (err "Not given lambda in function application position")
        "E-Beta-NotLambda")
   
   (--> (((loc_1 val_1) ...) (in-hole E (deref (ref loc))))
        (err "deref of an invalid location")
        (side-condition (not (memq (term loc) (term (loc_1 ...)))))
        "E-Deref-NotFound")
   (==> (deref not-ref)
        (err "deref of a not-ref")
        "E-Deref-NotRef")
   
   (==> (get-field not-object val)
        (err "GetField not given object")
        "E-GetField-NotObject")
   (==> (get-field (object [string val] ...) not-string)
        (err "GetField not given string")
        "E-GetField-NotString")
   
   (==> (update-field not-object val val_2)
        (err "UpdateField not given object")
        "E-UpdateField-NotObject")
   (==> (update-field (object [string val] ...) not-string val_2)
        (err "GetField not given string")
        "E-UpdateField-NotString")
   
   (==> (delete-field not-object val)
        (err "delete-field expects an object as first argument")
        "E-DeleteField-NotObject")
   (==> (delete-field (object [string val] ...) not-string)
        (err "delete-field expects a string as second argument")
        "E-DeleteField-NotString")

   (==> (if not-bool e_1 e_2)
        (err "if not given a boolean test")
        "E-If-NotBool")
   ;no need for a separate while reduction rule
   
   ;eval fails explicitly:
   (==> eval-semantic-bomb
        (err "Eval was called")
        "E-Eval")
   with
   [(--> (σ (in-hole E e_1)) (σ (in-hole E e_2)))
    (==> e_1 e_2)]
   ))

;;----------------------------------------
;;testing funcs:
(define-syntax trace
  (syntax-rules ()
    [(_ exp)
     (traces eval-lambdaJS (term (() exp)))]))

(define-syntax trace-errs    
  (syntax-rules ()
    [(_ exp)
     (traces eval-lambdaJS-errors (term (() exp)))]))

;
(define-syntax trace-errs-p
  (syntax-rules ()
    [(_ p)
     (traces eval-lambdaJS-errors (term p))]))

(define-syntax test
  (syntax-rules ()
    [(_ e1 e2)
     (test-predicate
      (lambda (result)
        (and 
         ; Ensure we have a unique result from evaluation.
         (list? result) (= 1 (length result))
         (or
          ; e2 may specify the entire result (including, possibly, the heap)
          (equal? (first result) (term e2))
          ; if not, attempt to match just the resulting term with e2 (i.e. drop the heap)
          (and (list? (first result))
               (= 2 (length (first result)))
               (equal? (second (first result)) (term e2))))))
      (apply-reduction-relation*
       eval-lambdaJS (term (() e1))))]))