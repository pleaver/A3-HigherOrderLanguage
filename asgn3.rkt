#lang plai-typed

(require plai-typed/s-exp-match)



;;;;DEFINE TYPES;;;;
;------------------;


;EXPRESSIONS of the LOOI3 language
(define-type ExprC
  [numC (n : number)]
  [boolC (b : boolean)]
  [binopC (op : symbol) (l : ExprC) (r : ExprC)]
  [idC (s : symbol)]
  [appC (fun : ExprC) (arg : (listof ExprC))]
  [lamC (param : (listof symbol)) (body : ExprC)]
  [ifC (test : ExprC) (then : ExprC) (els : ExprC)])

;BINDING of a symbol to a Value
(define-type Binding
  [bind (name : symbol) (val : Value)])

(define-type-alias Env (listof Binding))
(define mt-env empty)
(define extend-env cons)

;VALUES of the LOOI3 language
(define-type Value
  [numV (n : number)]
  [boolV (b : boolean)]
  [closV  (param : (listof symbol)) (body : ExprC) (env : Env)])


;;;;DEFINE TYPES END;;;;
;----------------------;







;;;;PARSER BEGIN;;;;
;------------------;


;HELPER function that takes in a list of s-expressions and outputs as a list of symbols
(define (exp-to-sym-list [l : (listof s-expression)]) : (listof symbol)
  (cond
    [(empty? l) empty]
    [else (append (list (s-exp->symbol (first l))) (exp-to-sym-list (rest l)))]))

;HELPER function that takes in a list of s-expressions and outputs the symbols of the list
;used for parsing the (with...) expression
(define (parse-syms [s : (listof s-expression)]) : (listof symbol)
  (cond
   [(empty? s) empty]
   [else (let ([l (s-exp->list (first s))])
           (append (list (s-exp->symbol (first l))) (parse-syms (rest s))))]))

;HELPER function that takes in a list of s-expressions and outputs the ExprC arguements of the list
;used for parsing the (with...) expression
(define (parse-args [s : (listof s-expression)]) : (listof ExprC)
  (cond
   [(empty? s) empty]
   [else (let ([l (s-exp->list (first s))])
           (append (list (parse (first (reverse l)))) (parse-args (rest s))))]))

;HELPER function that checks to see if fst has a duplicate in rst
;returns true if there's a duplicate and false otherwise
(define (has-dup-param fst rst) : boolean
  (cond
    [(empty? rst) #f]
    [(eq? (member fst rst) #t) #t]
    [else (has-dup-param (first rst) (rest rst))]))

;HELPER function that checks to see if fst has a duplicate in rst
;returns true if there's a duplicate and false otherwise
(define (has-dup-sym fst rst) : boolean
  (cond
    [(empty? rst) #f]
    [(eq? (member fst rst) #t) #t]
    [else (has-dup-sym (first rst) (rest rst))]))


;PARSES an expression into an ExprC
(define (parse [s : s-expression]) : ExprC
  (cond
    [(s-exp-number? s) (numC (s-exp->number s))] 
    [(s-exp-symbol? s) (cond
                         [(eq? 'true (s-exp->symbol s)) (boolC #t)]
                         [(eq? 'false (s-exp->symbol s)) (boolC #f)]
                         [(eq? `+ s) (error 'parse "reserved symbols cannot be used as idC's")]
                         [(eq? `- s) (error 'parse "reserved symbols cannot be used as idC's")]
                         [(eq? `* s) (error 'parse "reserved symbols cannot be used as idC's")]
                         [(eq? `/ s) (error 'parse "reserved symbols cannot be used as idC's")]
                         [(eq? `eq? s) (error 'parse "reserved symbols cannot be used as idC's")]
                         [(eq? `<= s) (error 'parse "reserved symbols cannot be used as idC's")]
                         [(eq? `if s) (error 'parse "reserved symbols cannot be used as idC's")]
                         [(eq? `with s) (error 'parse "reserved symbols cannot be used as idC's")]
                         [(eq? `func s) (error 'parse "reserved symbols cannot be used as idC's")]
                         [else (idC (s-exp->symbol s))])]
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
    [(s-exp-match? '(with {SYMBOL = ANY} ... ANY) s)
     (let ([l (s-exp->list s)])
       (let ([sym-args (parse-syms (reverse (rest (reverse (rest l)))))])
       (let ([dup? (has-dup-sym (first sym-args) (rest sym-args))])
         (cond
           [(eq? dup? #t) (error 'parse "the given s-expression has duplicate symbols")]
           [else (appC
                  (lamC (parse-syms (reverse (rest (reverse (rest l))))) (parse (first (reverse l))))
                  (parse-args (reverse (rest (reverse (rest l))))))]))))]
    [(s-exp-match? '(func SYMBOL ... ANY) s)
     (let ([l (s-exp->list s)])
       (let ([params (reverse (rest (reverse (rest l))))])
         (cond
           [(> (length params) 0) (cond
                                    [(idC? (parse (first params))) (cond                                      
                                                                     [(eq? (has-dup-param (parse (first params)) (map parse (rest params))) #f) (lamC (exp-to-sym-list (reverse (rest (reverse (rest l))))) (parse (first (reverse l))))]
                                                                     [else (error 'parse "the given s-expression has duplicate parameters")])])]
           [else (lamC (exp-to-sym-list (reverse (rest (reverse (rest l))))) (parse (first (reverse l))))])))]
    [(s-exp-match? '(ANY ANY ...) s)
     (let ([l (s-exp->list s)])
       (appC (parse (first l)) (map parse (rest l))))]))


;;;;PARSER END;;;;
;----------------;






;;;;EVALUATOR BEGIN;;;;
;---------------------;


;HELPER function that looks for a symbol in the environment and returns the Values it's bound to if it exists
(define (lookup [for : symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "name not found")]
    [else (cond
             [(symbol=? for (bind-name (first env)))
              (bind-val (first env))]
             [else (lookup for (rest env))])]))

;HELPER function that signals a runtime error occured and prints the expected value vs the provided value
(define (signal-runtime-error expected got)
  (error 'interp
         (foldr string-append ""
                (list "expected "expected", got "(to-string got)))))

;HELPER function that adds 2 values into a new value
(define (num+ [l : Value] [r : Value]) : Value
  (cond
    [(and (numV? l) (numV? r))
     (numV (+ (numV-n l) (numV-n r)))]
    [else
     (error 'num+ "one argument was not a number")]))

;HELPER function that subtracts 2 values into a new value
(define (num- [l : Value] [r : Value]) : Value
  (cond
    [(and (numV? l) (numV? r))
     (numV (- (numV-n l) (numV-n r)))]
    [else
     (error 'num- "one argument was not a number")]))

;HELPER function that mulitplies 2 values into a new value
(define (num* [l : Value] [r : Value]) : Value
  (cond
    [(and (numV? l) (numV? r))
     (numV (* (numV-n l) (numV-n r)))]
    [else
     (error 'num* "one argument was not a number")]))

;HELPER function that divides 2 values into a new value
(define (num/ [l : Value] [r : Value]) : Value
  (cond
    [(and (numV? l) (numV? r))
     (cond
       [(= (numV-n r) 0) (error 'num/ "can't divide by zero")]
       [else (numV (/ (numV-n l) (numV-n r)))])]
    [else
     (error 'num/ "one argument was not a number")]))

;HELPER function that checks if 2 values are equal and returns the corresponding boolean value
(define (numbooleq? [l : Value] [r : Value]) : Value
  (cond
    [(and (numV? l) (numV? r))
     (boolV (eq? (numV-n l) (numV-n r)))]
    [(and (boolV? l) (boolV? r))
     (boolV (eq? (boolV-b l) (boolV-b r)))]
    [else
     (boolV (eq? 5 4))]))

;HELPER function that checks if the first value is less than or equal to the second value
(define (num<= [l : Value] [r : Value]) : Value
  (cond
    [(and (numV? l) (numV? r))
     (boolV (<= (numV-n l) (numV-n r)))]
    [else
     (error 'num<= "one argument was not a number")]))

;HELPER function that binds a list of args from a function application to its param from
;the function definition and adds the bindings to the closure environment
(define (bind-args-to-params [params : (listof symbol)] [args : (listof Value)] [env : Env]) : Env
  (cond
    [(= (length params) (length args)) (cond
                                         [(empty? params) env]
                                         [else (bind-args-to-params (rest params) (rest args) (append env (list (bind (first params) (first args)))))])]
    [else (error 'bind-args-to-params "parameter list does not match argument list")]))


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
          (let ([ f-value (interp fun env)])
          (type-case Value (interp fun env)
            [numV (n) (signal-runtime-error "function value" n)]
            [closV (param body clo-env) (interp body (bind-args-to-params param (map (lambda (x) (interp x env)) arg) clo-env))]
            [boolV (b) (signal-runtime-error "function value" b)]))]
    [ifC (test then els) (type-case Value (interp test env)
                           [boolV (b) (cond
                                        [b (interp then env)]
                                        [else (interp els env)])]
                           [else (error 'interp "the test expression of the if statement did not evaluate to a boolean")])]))


;;;;EVALUATOR END;;;;
;-------------------;






;;;;TOP-EVAL BEGIN;;;;
;--------------------;


;HELPER function that serializes a value into a string representation
(define (serialize [v : Value]) : string
  (type-case Value v
    [numV (n) (to-string n)]
    [boolV (b) (cond
                 [(eq? b #t) "true"]
                 [(eq? b #f) "false"])]
    [closV (a b env) "#<procedure>"]))


;Does a top-eval on an s-expression by parsing it into an ExprC, evaluating it into a Value, and serializing the value into a string
(define (top-eval [s : s-expression]) : string
  (serialize (interp (parse s) (list))))


;;;;TOP-EVAL END;;;;
;------------------;






;;;;TESTS;;;;
;-----------;


(test (exp-to-sym-list (list `x `y)) (list 'x 'y))

(test (parse-syms (list '(a = (binopC '+ (numC 5) (numC 2))))) (list 'a))

(test (has-dup-param 'x (list 'x 'x)) #t)

(test (has-dup-sym 'z (list 'z)) #t)
(test (has-dup-sym 'x (list 'z 'q)) #f)

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
(test (parse `true) (boolC #t))
(test (parse `false) (boolC #f))

(test/exn (parse '(+ + +)) "reserved symbols cannot be used as idC's")
(test/exn (parse '(- - -)) "reserved symbols cannot be used as idC's")
(test/exn (parse '(* * *)) "reserved symbols cannot be used as idC's")
(test/exn (parse '(/ / /)) "reserved symbols cannot be used as idC's")
(test/exn (parse '(eq? eq? eq?)) "reserved symbols cannot be used as idC's")
(test/exn (parse '(<= <= <=)) "reserved symbols cannot be used as idC's")
(test/exn (parse '(+ if with)) "reserved symbols cannot be used as idC's")
(test/exn (parse '(+ with if)) "reserved symbols cannot be used as idC's")
(test/exn (parse '(+ func if)) "reserved symbols cannot be used as idC's")
(test/exn (parse '(func x x 3)) "the given s-expression has duplicate parameters")
(test/exn (parse '(with (z = 8) (z = 9) (z))) "the given s-expression has duplicate symbols")

(test (parse '((func seven (seven)) ((func minus (func (minus (+ 3 10) (* 2 3))))) (func x y (+ x (* -1 y)))))
(appC (lamC (list 'seven) (appC (idC 'seven) (list))) (list (appC (lamC (list 'minus) (lamC (list) (appC (idC 'minus) (list (binopC '+ (numC 3) (numC 10)) (binopC '* (numC 2) (numC 3)))))) (list)) (lamC (list 'x 'y) (binopC '+ (idC 'x) (binopC '* (numC -1) (idC 'y)))))))

(test (parse-args (list '(a = (+ 5 4)))) (list (binopC '+ (numC 5) (numC 4))))

(test (parse '(with (x = (+ 5 4)) (+ x 1))) (appC (lamC (list 'x) (binopC '+ (idC 'x) (numC 1))) (list (binopC '+ (numC 5) (numC 4)))))

(test/exn (lookup 'x (list)) "name not found")
(test (lookup 'x (list (bind 'y (numV 2)) (bind 'x (numV 5)))) (numV 5))

(test/exn (signal-runtime-error (to-string 5) 3) "expected 5, got 3")

(test (num+ (numV 5) (numV 2)) (numV 7))
(test/exn (num+ (boolV #t) (numV 2)) "one argument was not a number")

(test (num- (numV 4) (numV 1)) (numV 3))
(test/exn (num- (boolV #t) (boolV #f)) "one argument was not a number")

(test (num* (numV 2) (numV 4)) (numV 8))
(test/exn (num* (numV 2) (boolV #f)) "one argument was not a number")

(test (num/ (numV 4) (numV 2)) (numV 2))
(test/exn (num/ (numV 1) (boolV #f)) "one argument was not a number")
(test/exn (num/ (numV 10) (numV 0)) "can't divide by zero")

(test (numbooleq? (numV 5) (numV 4)) (boolV #f))
(test (numbooleq? (boolV #t) (boolV #t)) (boolV #t))
(test (numbooleq? (boolV #t) (closV (list) (binopC '+ (numC 5) (numC 2)) (list))) (boolV #f))

(test (num<= (numV 2) (numV 5)) (boolV #t))
(test/exn (num<= (boolV #t) (boolV #f)) "one argument was not a number")

(test (interp (numC 5) (list)) (numV 5))
(test (interp (binopC '+ (numC 5) (numC 2)) (list)) (numV 7))
(test (interp (binopC '- (numC 10) (numC 2)) (list)) (numV 8))
(test (interp (binopC '* (numC 1) (numC 3)) (list)) (numV 3))
(test (interp (binopC '/ (numC 4) (numC 2)) (list)) (numV 2))
(test (interp (lamC (list 'x 'y) (binopC '+ (idC 'x) (idC 'y))) (list)) (closV (list 'x 'y) (binopC '+ (idC 'x) (idC 'y)) (list)))
(test (interp (boolC #t) (list)) (boolV #t))
(test (interp (ifC (boolC #t) (binopC '+ (numC 4) (numC 2)) (binopC '- (numC 2) (numC 1))) (list)) (numV 6))
(test (interp (idC 'x) (list (bind 'x (numV 2)))) (numV 2))
(test (interp (binopC 'eq? (numC 5) (numC 5)) (list)) (boolV #t))
(test (interp (binopC '<= (numC 10) (numC 1)) (list)) (boolV #f))
(test (interp (appC (lamC (list) (binopC '+ (numC 5) (numC 4))) (list)) (list)) (numV 9))
(test/exn (interp (appC (numC 5) (list)) (list)) "interp: expected function value, got 5")
(test/exn (interp (appC (boolC #t) (list)) (list)) "interp: expected function value, got #t")
(test (interp (ifC (boolC #f) (binopC '+ (numC 4) (numC 2)) (binopC '- (numC 4) (numC 2))) (list)) (numV 2))
(test (interp (binopC 'eq? (boolC #f) (boolC #t)) (list)) (boolV #f))
(test (interp (binopC 'eq? (lamC (list) (binopC '+ (numC 4) (numC 5))) (numC 1)) (list)) (boolV #f))
(test (interp (binopC 'eq? (numC 4) (numC 4)) (list)) (boolV #t))
(test/exn (interp (ifC (numC 5) (numC 4) (numC 3)) (list)) "the test expression of the if statement did not evaluate to a boolean")
(test (interp (ifC (boolC #t) (numC 4) (numC 3)) (list)) (numV 4))

(define fundef1 (parse '{func x {+ x 3}}))

(test fundef1 (lamC (list 'x) (binopC '+ (idC 'x) (numC 3))))
(test (interp fundef1 (list)) (closV (list 'x) (binopC '+ (idC 'x) (numC 3)) (list)))

(test (bind-args-to-params (list 'x 'y) (list (numV 4) (numV 1)) (list)) (list (bind 'x (numV 4)) (bind 'y (numV 1))))
(test/exn (bind-args-to-params (list 'x) (list) (list)) "parameter list does not match argument list")

(test (top-eval '(+ 5 4)) "9")
(test (top-eval `#t) "true")
(test (top-eval `#f) "false")
(test (top-eval '(func x (+ x 1))) "#<procedure>")

(test (top-eval '(func x y (if (<= x 5) (+ y 5) (- x 5)))) "#<procedure>")

(test (interp (appC (lamC (list 'x) (binopC '+ (idC 'x) (numC 5))) (list (numC 2))) (list)) (numV 7))



;;;;TESTS END;;;;
;---------------;