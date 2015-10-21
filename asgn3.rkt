#lang plai-typed

(require plai-typed/s-exp-match)


(define-type ExprC
  [numC (n : number)]
  [boolC (b : boolean)]
  [binopC (op : symbol) (l : ExprC) (r : ExprC)]
  [idC (s : symbol)]
  [appC (fun : ExprC) (arg : (listof ExprC))]
  [lamC (param : (listof symbol)) (body : ExprC)]
  [ifC (test : ExprC) (then : ExprC) (els : ExprC)]
  [withC (vardef : (listof ExprC)) (body : ExprC)])


(define-type Binding
  [bind (name : symbol) (val : Value)])

(define-type-alias Env (listof Binding))


(define-type Value
  [numV (n : number)]
  [boolV (b : boolean)]
  [closV  (param : (listof symbol)) (body : ExprC) (env : Env)])


;HELPER function that takes in a list of s-expressions and outputs as a list of symbols
(define (exp-to-sym-list [l : (listof s-expression)]) : (listof symbol)
  (cond
    [(empty? l) empty]
    [else (append (list (s-exp->symbol (first l))) (exp-to-sym-list (rest l)))]))

;PARSES an expression into an ExprC
(define (parse [s : s-expression]) : ExprC
  (cond
    [(s-exp-number? s) (numC (s-exp->number s))]
    [(s-exp-symbol? s) (idC (s-exp->symbol s))]
    [(s-exp-boolean? s) (boolC (s-exp->boolean s))]
    [(s-exp-match? '(+ ANY ANY) s)
     (let ([l (s-exp->list s)])
       (binopC '+ (parse (second l)) (parse (third l))))]
    [(s-exp-match? '(- ANY ANY) s)
     (let ([l (s-exp->list s)])
       (binopC '- (parse (second l)) (parse (third l))))]
    [(s-exp-match? '(* ANY ANY) s)
     (let ([l (s-exp->list s)])
       (binopC '* (parse (second l)) (parse (third l))))]
    [(s-exp-match? '(/ ANY ANY) s)
     (let ([l (s-exp->list s)])
       (binopC '/ (parse (second l)) (parse (third l))))]
    [(s-exp-match? '(eq? ANY ANY) s)
     (let ([l (s-exp->list s)])
       (binopC 'eq? (parse (second l)) (parse (third l))))]
    [(s-exp-match? '(<= ANY ANY) s)
     (let ([l (s-exp->list s)])
       (binopC '<= (parse (second l)) (parse (third l))))]
    [(s-exp-match? '(if ANY ANY ANY) s)
     (let ([l (s-exp->list s)])
       (ifC (parse (second l)) (parse (third l)) (parse (fourth l))))]

    [(s-exp-match? '(func ANY ... ANY) s)
     (let ([l (s-exp->list s)])
       (lamC
        (exp-to-sym-list (rest (reverse (rest (reverse (rest l))))))
        (parse (first (reverse l)))))]

    [(s-exp-match? '(ANY ANY ...) s)
     (let ([l (s-exp->list s)])
       (appC (parse (first l)) (map parse (rest l))))]
    
    ))

(test (parse '(+ 5 4)) (binopC '+ (numC 5) (numC 4)))
(test (parse '(- 10 2)) (binopC '- (numC 10) (numC 2)))
(test (parse '(* 1 7)) (binopC '* (numC 1) (numC 7)))
(test (parse '(/ 15 5)) (binopC '/ (numC 15) (numC 5)))
(test (parse '(eq? 10 10)) (binopC 'eq? (numC 10) (numC 10)))
(test (parse '(<= 5 10)) (binopC '<= (numC 5) (numC 10)))
(test (parse `a) (idC 'a))
(test (parse `#t) (boolC #t))
(test (parse '(if #t (+ 4 2) (- 2 1))) (ifC (boolC #t) (binopC '+ (numC 4) (numC 2)) (binopC '- (numC 2) (numC 1))))
(test (parse '(func x y (if (<= x 5) (+ y 5) (- x 5)))) (lamC (list 'x 'y) (ifC (binopC '<= (idC 'x) (numC 5)) (binopC '+ (idC 'y) (numC 5)) (binopC '- (idC 'x) (numC 5)))))

'((func seven (seven)) ((func minus (func minus (+ 3 10) (* 2 3)))) (func x y (+ x (* -1 y))))


(define (lookup [for : symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "name not found")]
    [else (cond
             [(symbol=? for (bind-name (first env)))
              (bind-val (first env))]
             [else (lookup for (rest env))])]))


(define (signal-runtime-error expected got)
  (error 'eval
         (foldr string-append ""
                (list "expected "expected", got "(to-string got)))))


(define (num+ [l : Value] [r : Value]) : Value
  (cond
    [(and (numV? l) (numV? r))
     (numV (+ (numV-n l) (numV-n r)))]
    [else
     (error 'num+ "one argument was not a number")]))

(test (num+ (numV 5) (numV 2)) (numV 7))

(define (num- [l : Value] [r : Value]) : Value
  (cond
    [(and (numV? l) (numV? r))
     (numV (- (numV-n l) (numV-n r)))]
    [else
     (error 'num- "one argument was not a number")]))

(define (num* [l : Value] [r : Value]) : Value
  (cond
    [(and (numV? l) (numV? r))
     (numV (* (numV-n l) (numV-n r)))]
    [else
     (error 'num* "one argument was not a number")]))

(define (num/ [l : Value] [r : Value]) : Value
  (cond
    [(and (numV? l) (numV? r))
     (cond
       [(= (numV-n r) 0) (error 'num/ "can't divide by zero")]
       [else (numV (/ (numV-n l) (numV-n r)))])]
    [else
     (error 'num/ "one argument was not a number")]))

(define (numbooleq? [l : Value] [r : Value]) : Value
  (cond
    [(and (numV? l) (numV? r))
     (boolV (eq? (numV-n l) (numV-n r)))]
    [(and (boolV? l) (boolV? r))
     (boolV (eq? (boolV-b l) (boolV-b r)))]
    [else
     (error 'numbooleq? "both arguments weren't a number or both weren't a boolean")]))

(test (numbooleq? (numV 5) (numV 4)) (boolV #f))

(define (num<= [l : Value] [r : Value]) : Value
  (cond
    [(and (numV? l) (numV? r))
     (boolV (<= (numV-n l) (numV-n r)))]
    [else
     (error 'num<= "one argument was not a number")]))

;HELPER function that binds a list of args from a function application to its param from
;the function definition and adds the bindings to the closure environment
(define (bind-args-to-params [params : (listof symbol)] [args : (listof ExprC)] [env : Env]) : Env
  (cond
    [(empty? params) env]
    [else (bind-args-to-params (rest params) (rest args) (cons (bind (first params) (interp (first args) env)) env))]))


;INTERPRETS an ExprC into a Value, using the environment for function lookups
(define (interp [e : ExprC] [env : Env]) : Value
  (type-case ExprC e
    [numC (n) (numV n)]
    [idC (s) (lookup s env)]
    [boolC (b) (boolV b)]
    [binopC (s l r)
            (case s
              [(+) (num+ (interp l env) (interp r env))]
              [(-) (num- (interp l env) (interp r env))]
              [(*) (num* (interp l env) (interp r env))]
              [(/) (num/ (interp l env) (interp r env))]
              [(eq?) (numbooleq? (interp l env) (interp r env))]
              [(<=) (num<= (interp l env) (interp r env))])]
    [lamC (a b) (closV a b env)]
    [appC (fun arg)
          (type-case Value (interp fun env)
            [numV (n) (signal-runtime-error "function value" n)]
            [closV (param body clo-env) (interp body (bind-args-to-params param arg clo-env))]
            [boolV (b) (signal-runtime-error "function value" b)])]
    [ifC (test then els) (cond
                            [(eq? #t (boolV-b (interp test env))) (interp then env)]
                            [else (interp els env)])]))

(test (interp (numC 5) (list)) (numV 5))
(test (interp (binopC '+ (numC 5) (numC 2)) (list)) (numV 7))
(test (interp (binopC '- (numC 10) (numC 2)) (list)) (numV 8))
(test (interp (binopC '* (numC 1) (numC 3)) (list)) (numV 3))
(test (interp (binopC '/ (numC 4) (numC 2)) (list)) (numV 2))
(test (interp (lamC (list 'x 'y) (binopC '+ (idC 'x) (idC 'y))) (list)) (closV (list 'x 'y) (binopC '+ (idC 'x) (idC 'y)) (list)))
(test (interp (boolC #t) (list)) (boolV #t))
(test (interp (ifC (boolC #t) (binopC '+ (numC 4) (numC 2)) (binopC '- (numC 2) (numC 1))) (list)) (numV 6))


(define fundef1 (parse '{func f x {+ x 3}}))

(test fundef1 (lamC (list 'x) (binopC '+ (idC 'x) (numC 3))))
(test (interp fundef1 (list)) (closV (list 'x) (binopC '+ (idC 'x) (numC 3)) (list)))


;('((func seven (seven)) ((func minus (func (minus (+ 3 10) (* 2 3)))) (func x y (+ x (* -1 y))))))


(define (serialize [v : Value]) : string
  (type-case Value v
    [numV (n) (to-string n)]
    [boolV (b) (to-string b)]
    [closV (a b env) "#<procedure>"]))


(define (top-eval [s : s-expression]) : string
  (serialize (interp (parse s) (list))))

(test (top-eval '(+ 5 4)) "9")


;(test (top-eval '(func x y (if (<= x 5) (+ y 5) (- x 5)))) (closV (list 'x 'y) (ifC (binopC '<= (idC 'x) (numC 5)) (binopC '+ (idC 'y) (numC 5)) (binopC '- (idC 'x) (numC 5))) (list)))
(test (top-eval '(func x y (if (<= x 5) (+ y 5) (- x 5)))) "#<procedure>")
