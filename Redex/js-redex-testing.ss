#lang scheme

(require redex)
(require "jscore.ss")
(require "js-delta.ss")
(provide (all-defined-out))

;;safety? is what we are testing for. the helpers that well-formed? uses are defined later
;;-----------------------
;;progress and preservation:
;;if p is a closed program, then either it is a result or it takes a unique step which
;;results in a program that is also well-formed
;;Defined at ht
(define (safety? p)
  (or (not (well-formed? p))
      (result? p)
      (let ((results (apply-reduction-relation eval-lambdaJS-errors p)))
              (and (= (length results) 1)
                   (well-formed? (first results))))))

;;a program is well formed if it either it is an error without a store, or:
;;it has correct syntax, it 
;;has no free variables, all references are in the domain of the store,
;;the store only has one value per memory location, and
;;the breaks are valid
(define (well-formed? p)
  (or (redex-match lambdaJS error p)
      (and (correct-syntax? (second p))
           (obj-unique-names? p)
           (not (open? p))
           (valid-refs? p)
           (unique? (map first (first p)))
           (valid-breaks? p)
           )))

;;----------------------------------------
;;general helpers:
(define (setsub a b)
  (if (empty? b) a
      (setsub (filter (lambda (x) (not (eq? x (first b)))) a) (rest b))))
(define (subset? a b)
  (= (length (setsub a b)) 0))
(define (all l)
  (foldl (lambda (x y) (and x y)) #t l))
(define (unique? l) ;#t iff l contains unique elements
  (if (or (empty? l)
          (= (length l) 1))
      #t
      (and (not (member (first l) (rest l)))
           (unique? (rest l)))))
(define (random-choice l)
  (list-ref l (random (length l))))

;;----------------------------------------
;;----------------------------------------
;;check for free variables
(define (free-vars-expr expr)
  (match expr
    [(? symbol? id) (if (or (eq? id 'eval-semantic-bomb)
                            (eq? id 'undefined)
                            (eq? id 'null))
                        '() 
                        (list id))]
    [`(,(? λJS-operator? op) ,e ...) (apply append (map free-vars-expr e))]
    [`(set! ,e1 ,e2) (append (free-vars-expr e1) (free-vars-expr e2))]
    [`(alloc ,e) (free-vars-expr e)]
    [`(deref ,e) (free-vars-expr e)]
    [`(ref ,loc) '()]
    [`(object [,str ,e] ...) (apply append (map free-vars-expr e))]
    [`(get-field ,e1 ,e2)  (append (free-vars-expr e1) (free-vars-expr e2))]
    [`(update-field ,e1 ,e2 ,e3) (append (free-vars-expr e1) (free-vars-expr e2) (free-vars-expr e3))]
    [`(begin ,e1 ,e2 ...) (append (free-vars-expr e1) (apply append (map free-vars-expr e2)))]
    [`(if ,e1 ,e2 ,e3) (append (free-vars-expr e1) (free-vars-expr e2) (free-vars-expr e3))]
    [`(while ,e1 ,e2) (append (free-vars-expr e1) (free-vars-expr e2))]
    [`(label ,lbl ,e) (free-vars-expr e)]
    [`(break ,lbl ,e) (free-vars-expr e)]
    [`(try-catch ,e1 ,e2) (append (free-vars-expr e1) (free-vars-expr e2))]
    [`(try-finally ,e1 ,e2) (append (free-vars-expr e1) (free-vars-expr e2))]
    [`(throw ,e1) (free-vars-expr e1)]
    [`(let ([,x ,e1] ...) ,e2) (append (apply append (map free-vars-expr e1))
                                       (setsub (free-vars-expr e2) x))]
    [`(lambda (,x ...) ,e) (setsub (free-vars-expr e) x)]
    [`(err ,e) (free-vars-expr e)]
    [`(delete-field ,e1 ,e2) (append (free-vars-expr e1) (free-vars-expr e2))]
    [`(,e ...) (apply append (map free-vars-expr e))]
    [else '()]
    ))
;;the free variables in a store.
(define (free-vars-store store)
  (apply append (map free-vars-expr (map second store))))

;;----------------------------------------
;;stuff to deal with refs being valid

(define ((collect-invalid-refs storedomain) expr)
  (match expr
    [`(ref ,loc) (if (memq loc storedomain)
                     '()
                     (list loc))]
    [`(,e ...) (apply append (map (collect-invalid-refs storedomain) e))]
    [else '()]))

;;all refs in an expression are in the domain of the store
(define ((valid-refs-expr? storedomain) expr)
  (= (length ((collect-invalid-refs storedomain) expr)) 0))
;;all refs in the store are in the domain of the store
(define (valid-refs-store? store)
  (all (map (valid-refs-expr? (map first store)) (map second store))))

;;----------------------------------------
;;stuff to deal with breaks being valid
(define ((collect-invalid-breaks curlabels) expr)
  (match expr
    [`(break ,x ,e) (append (if (memq x curlabels) '() (list x))
                            ((collect-invalid-breaks curlabels) e))]
    [`(label ,x ,e) ((collect-invalid-breaks (cons x curlabels)) e)]
    ;can't break across lambdas:
    [`(lambda (,x ...) ,e) ((collect-invalid-breaks '()) e)]
    [`(,e ...) (apply append (map (collect-invalid-breaks curlabels) e))]
    [else '()]
    ))

(define ((valid-breaks-expr? curlabels) expr)
  (= (length ((collect-invalid-breaks curlabels) expr)) 0))
(define (valid-breaks-store? store)
  (all (map (valid-breaks-expr? '()) (map second store))))

;;----------------------------------------
;;all object literals have unique names
(define (obj-unique-names-expr? expr)
  (match expr
    [`(object [,str ,e] ...) (and (unique? str) (all (map obj-unique-names-expr? e)))]
    [`(,e ...) (all (map obj-unique-names-expr? e))]
    [else #t]))
(define (obj-unique-names-store? store)
  (all (map obj-unique-names-expr? (map second store))))

;;----------------------------------------
;;----------------------------------------
;;WELL-FORMED:

;;program contains free vars:
(define (open? p)
  (not (= 0 (+ (length (free-vars-expr (second p)))
               (length (free-vars-store (first p)))))))
;;object lits have unique names
(define (obj-unique-names? p)
  (and (obj-unique-names-expr? (second p))
       (obj-unique-names-store? (first p))))
;;program contains valid refs
(define (valid-refs? p)
  (and ((valid-refs-expr? (map first (first p))) (second p))
       (valid-refs-store? (first p))))
;;program has good syntax
(define (correct-syntax? expr)
  (redex-match lambdaJS e expr))
;;program contains only valid breaks (breaks to labels within lambdas)
(define (valid-breaks? p)
  (and ((valid-breaks-expr? '()) (second p))
       (valid-breaks-store? (first p))))

;;----------------------------------------
;;----------------------------------------
;;PROGRESS + PRESERVATION TOGETHER:
;;a result is a program that is entirely an error, or
;;where the expression is a value
(define (result? p)
  (or (redex-match lambdaJS error p)
      (redex-match lambdaJS val (second p))))

;safety? is defined at the top
;;----------------------------------------
;;----------------------------------------
;;TESTING
;;same as above but print etc
(define num-wellformed-inputs 0)
(define (safety-debug? p)
  (if (not (well-formed? p))
      #t ;;vacuously true
      (begin
        ;(print p) (display "\n")
        (set! num-wellformed-inputs (+ num-wellformed-inputs 1))
        (or (result? p) ;;either a result, or it reduces in 1 way to a well-formed result
            (let ((results (apply-reduction-relation eval-lambdaJS-errors p)))
              (and (= (length results) 1)
                   (well-formed? (first results))))))))

;;----------------------------------------
;;redex testing to cover all cases we expect:
(define coverage (make-coverage eval-lambdaJS-errors))

(define num-rules 37)
(define (redex-test attempts repeats)
  (if (<= repeats 0) void
      (begin
        (set! num-wellformed-inputs 0)
        (parameterize ([relation-coverage (list coverage)])
          (check-reduction-relation eval-lambdaJS-errors safety-debug? #:attempts (round attempts)))
        (display (format "Repeat -~a: Had ~a/~a well-formed inputs\n" 
                         repeats num-wellformed-inputs (* num-rules attempts)))
        (redex-test (+ attempts 1) (- repeats 1)))))

;;----------------------------------------
;;----------------------------------------
;;----------------------------------------
;;----------------------------------------
;;MY OWN TESTS - IGNORE

;;my own testing which constructs less
;;constrained expressions 
;;TODO: use these functions to convert a redex
;;test into a well-formed program, instead of
;;doing it all here.

;add let bindings to cover all free vars. just let-bind
;them to an existing valid var
;if no valid vars available then generate a very simple closed val
(define (cover-free-vars valid-vars expr)
  (define fvs (setsub (free-vars-expr expr) valid-vars))
  (if (empty? fvs) expr
      (let ((cover-var (if (empty? valid-vars) 
                           (generate-closed-value '() 1)
                           (random-choice valid-vars))))
        (cover-free-vars valid-vars
                         `(let ((,(first fvs) ,cover-var))
                            ,expr)
                         ))))

;;generate a value that has no additional free variables
;;the new value might have its own free variables. if this
;;is the case, it covers those free vars by binding
;;them to one of the vars in valid-vars
(define (generate-closed-value valid-vars value-size)
  (define res (generate-term lambdaJS val value-size #:retries 100))  
  (if (> (length (free-vars-expr res)) 0)
      (if (empty? valid-vars)
          (generate-closed-value valid-vars 1)
          (cover-free-vars valid-vars res))
      res))

;add let bindings to cover all the free variables. generate
;new values to cover them. the new values can be 'interesting'
(define (cover-free-vars-vals expr value-size)
  (define fvs (free-vars-expr expr))
  (if (empty? fvs) expr
      (cover-free-vars-vals
       `(let ((,(first fvs) ,(generate-closed-value (rest fvs) value-size)))
          ,expr)
       value-size)))

;;generate a value with no invalid references and no free variables
;;TODO: make this sub invalid refs with valid refs
(define (generate-validref-value storedomain value-size)
  (define res (generate-term lambdaJS val value-size #:retries 100))
  (if (not ((valid-refs-expr? storedomain) res))
      (generate-validref-value storedomain (max 1 (- value-size 1)))
      (if (not (empty? (free-vars-expr res)))
          (generate-validref-value storedomain (max 1 (- value-size 1)))
          res)))
;;      (cover-free-vars-vals res 1)))

;create a store to cover all refs in the expr
(define (cover-refs-store store expr value-size)
  (define refs ((collect-invalid-refs (map first store)) expr))
  (if (empty? refs) 
      store
      (cover-refs-store
       (cons (list (first refs) (generate-validref-value (map first store) value-size))
             store)
       expr value-size)))

;create labels to cover all breaks
;doesn't always work as invalid breaks could be in a lambda
(define (cover-breaks expr)
  (define breaks ((collect-invalid-breaks '()) expr))
  (if (empty? breaks)
      expr
      (cover-breaks `(label ,(first breaks) ,expr))))

;;the following generates a very-likely-correct program and runs it through
;;generate a value with no free variables:
(define (generate-well-formed-prog expr-size value-size)
  (define term (generate-term lambdaJS e expr-size #:retries 100))
  ;add let bindings for all the free variables
  (define closed-term (cover-free-vars-vals term value-size))
  ;add labels to cover the bad breaks
  (define good-term (cover-breaks closed-term))
  ;create a store which has something in each referenced location
  (define store (cover-refs-store '() good-term value-size))
  (define res (list store good-term))
  ;;we don't account for invalid braeks, so just repaet if that happens:
  (if (well-formed? res)
      res
      (begin
        (display "re-try")
        (generate-well-formed-prog expr-size value-size))))

;apply safety until the term reduces no more
;so each valid case ends up being several valid cases
;takes twice as long as it should since safety-debug also applies the reduction
(define (run-test* p)  
  (if (result? p) (list #t p)
      (if (not (safety-debug? p))
          (list #f p)
          (let ((result (first (apply-reduction-relation eval-lambdaJS-errors p))))
            (run-test* result)))))

(define (disp-cov)
   (display (format "Coverage now:\n~a" (covered-cases coverage))))

(define (my-test expr-size value-size)
  (define p (generate-well-formed-prog expr-size value-size))
  (print p) 
  (display "\n")
  (parameterize ([relation-coverage (list coverage)])
    (let ((res (run-test* p)))
      (begin 
        (if (first res)
            (display (format "Success!\n"))
            (begin
              (display "Failed! Latest step:\n")
              (print (second res)) (display "\n"))))
      res)))
;run tests until youre done or something breaks
(define (my-tests expr-size value-size reps)
  (display reps)
  (display "\n")
  (if (= reps 0) 
      (covered-cases coverage)
      (let ((res (my-test expr-size value-size)))
        (if (not (first res))
            void
            (my-tests expr-size value-size (- reps 1))))))

(redex-test 1 100)