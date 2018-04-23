;; Name: Sachie (Tran) Tran
;; LET-interpreter
;; Starter file for HW5

(load "helpers.scm")


;; ================ Parser Definitions ==================================
;; This defines the translation from the concrete syntax to the abstract syntax
(define the-grammar
  '((program                        ;; <Program> ::= 
     (expression)                   ;;   Concrete    <Expression>
     a-prog)                        ;;   Abstract    (a-prog exp)
    
    (expression                     ;; <Expression> ::= 
     (number)                       ;;   Concrete       <Number> 
     const-exp)                     ;;   Abstract       (const-exp num)
    
    (expression                            ;; <Expression> ::= 
     ("-(" expression "," expression ")")  ;;   Concrete       -(<Expression>,<Expression>)
     diff-exp)                             ;;   Abstract       (diff-exp exp1 exp2)

    (expression                     ;; <Expression> ::= 
     ("zero?(" expression ")")      ;;   Concrete       zero?(<Expression>)
     zero?-exp)                     ;;   Abstract       (zero?-exp exp)
    
    (expression                                             ;; <Expression> ::= 
     ("if" expression "then" expression "else" expression)  ;;   Concrete       if <Expression> then <Expression> else <Expression>
     if-exp)                                                ;;   Abstract       (if-exp exp1 exp2 exp3)
        
    (expression                     ;; <Expression> ::= 
     (identifier)                   ;;   Concrete       <Identifier>
     var-exp)                       ;;   Abstract       (var-exp var)
    
    (expression                                          ;; <Expression> ::= 
     ("let" identifier "=" expression "in" expression)   ;;   Concrete       let <Identifier> = <Expression> in <Expression>
     let-exp)                                            ;;   Abstract       (let-exp var exp1 exp2)


    ;; ============== New definitions ========================

    (program                               ;; <Program> ::= 
     ("def!" identifier "=" expression)    ;;  Concrete     def! <Identifier> = <Expression>
     def-prog)                             ;;  Abstract     (def-prog var exp)
    
    (expression                            ;; <Expression> ::= 
     ("#true")                             ;;   Concrete       #true
     const-true)                           ;;   Abstract       (const-true)
    
    (expression                            ;; <Expression> ::=
     ("#false")                            ;;   Concrete       #false
     const-false)                          ;;   Abstract       (const-false)
     
    (expression                            ;; <Expression> ::= 
     ("*(" expression "," expression ")")  ;;   Concrete       *(<Expression>,<Expression>)
     times-exp)                            ;;   Abstract       (times-exp exp1 exp2)
    
    (expression                            ;; <Expression> ::= 
     ("/(" expression "," expression ")")  ;;   Concrete       /(<Expression>,<Expression>)
     div-exp)                              ;;   Abstract       (div-exp exp1 exp2)
    
    (expression                            ;; <Expression> ::= 
     ("+(" expression "," expression ")")  ;;   Concrete       +(<Expression>,<Expression>)
     plus-exp)                             ;;   Abstract       (plus-exp exp1 exp2)
    
    (expression                            ;; <Expression> ::= 
     ("=(" expression "," expression ")")  ;;   Concrete       =(<Expression>,<Expression>)
     equal-exp)                            ;;   Abstract       (equal-exp exp1 exp2)

    (expression                            ;; <Expression> ::= 
     ("<(" expression "," expression ")")  ;;   Concrete       <(<Expression>,<Expression>)
     less-than-exp)                        ;;   Abstract       (less-than-exp exp1 exp2)
    
    (expression                            ;; <Expression> ::= 
     ("&(" expression "," expression ")")  ;;   Concrete       &(<Expression>,<Expression>)
     and-exp)                              ;;   Abstract       (and-exp exp1 exp2)

    (expression                            ;; <Expression> ::= 
     ("|(" expression "," expression ")")  ;;   Concrete       |(<Expression>,<Expression>)
     or-exp)                               ;;   Abstract       (or-exp exp1 exp2)
    
    (expression                            ;; <Expression> ::= 
     ("!(" expression ")")                 ;;   Concrete       !(<Expression>)
     not-exp)                              ;;   Abstract       (not-exp exp)
))

(load "lex-scan-parse.scm")

;; =============== Environment Definition =============================

;; This is an implementation of the var-val pair list representation
;; of an environment that we've already seen.  The representation has been 
;; translated into a define-datatype so we get the constructors
;; and type checking predicate for free, and then can use cases to process.

(define-datatype environment environment?
  (empty-env)               ;; (empty-env) gives an empty environment
  (extend-env               ;; (extend-env var val env) extends the environment
   (var symbol?)
   (val expval?)
   (env environment?))
)

;; (apply-env env target-var) to figure out the mapping (value) of target-var
;; in the environment env.
(define apply-env ; Env x Var -> SType
  (lambda (env target-var)
    (cases environment env
      [empty-env () (raise-exception 'apply-env "No binding for ~s" target-var)]
      [extend-env (var val env*) 
         (cond
	  [(equal? var target-var) val]
	  [else (apply-env env* target-var)])])))


;; ==================== Expressed Values ==================================

;; Expressed values are Int + Bool 
(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (bool boolean?))
  (unit-val)
)

(define expval->num 
  (lambda (ev)
    (cases expval ev
      [num-val (num) num]
      [bool-val (bool) (if bool 1 0)]
      [else (raise-exception 'expval->num "Expressed value is not a number: ~s" ev)])))

(define expval->bool
  (lambda (ev)
    (cases expval ev
      [bool-val (bool) bool]
      [num-val (num) (if (equal? num 0) #f #t)]
      [else (raise-exception 'expval->bool "Expressed value is not a Boolean: ~s" ev)])))

(define expval->string
  (lambda (ev)
    (cases expval ev
      [bool-val (bool) (if bool "#true" "#false")]
      [unit-val () "#unit"]
      [num-val (num) (number->string num)]
)))

;; ==================== Parser ======================================
(define parse
  (lambda (str)
    (scan&parse str)))

;; ==================== Evaluator ====================================

(define value-of
  (lambda (prog env)
    (cases program prog
	   [a-prog (exp) (list (value-of-exp exp env) env)]
	   [def-prog (var exp) (list unit-val (extend-env var (value-of-exp exp env) env))]
	   [else (raise-exception 'value-of-prog "Abstract syntax case not implemented: ~s" (car prog))])))

(define value-of-exp
  (lambda (exp env)
    (cases expression exp
      ;; In class
      [const-exp (num) (num-val num)]
      [diff-exp (exp1 exp2) 
      (num-val (- (expval->num (value-of-exp exp1 env)) 
          (expval->num (value-of-exp exp2 env))))]
      [zero?-exp (exp1) (bool-val (= (expval->num (value-of-exp exp1 env)) 0))]
      [if-exp (exp1 exp2 exp3) 
        (if (expval->bool (value-of-exp exp1 env)) 
      (value-of-exp exp2 env) 
      (value-of-exp exp3 env))]
      [var-exp (var) (apply-env env var)]
      [let-exp (var exp1 exp2) 
         (value-of-exp exp2 (extend-env var (value-of-exp exp1 env) env))]
      [const-true () (bool-val #t)]
      [const-false () (bool-val #f)]

      [plus-exp (exp1 exp2)
      (num-val (+ (expval->num (value-of-exp exp1 env)) 
          (expval->num (value-of-exp exp2 env))))]

      [times-exp (exp1 exp2)
      (num-val (* (expval->num (value-of-exp exp1 env)) 
          (expval->num (value-of-exp exp2 env))))]

      [div-exp (exp1 exp2)
      (if (= (expval->num (value-of-exp exp2 env)) 0)
        (raise-exception 'value-of-exp "Cannot divide by 0: ~s" (exp2))
        (num-val (/ (expval->num (value-of-exp exp1 env)) 
          (expval->num (value-of-exp exp2 env)))))]

      [less-than-exp (exp1 exp2)
      (bool-val (< (expval->num (value-of-exp exp1 env)) 
          (expval->num (value-of-exp exp2 env))))]

      [equal-exp (exp1 exp2)
      (bool-val (= (expval->num (value-of-exp exp1 env)) 
          (expval->num (value-of-exp exp2 env))))]

      [and-exp (exp1 exp2) 
      (bool-val (and (expval->bool (value-of-exp exp1 env)) 
          (expval->bool (value-of-exp exp2 env))))]

      [or-exp (exp1 exp2)
      (bool-val (or (expval->bool (value-of-exp exp1 env)) 
          (expval->bool (value-of-exp exp2 env))))]

      [not-exp (exp)
      (bool-val (not (expval->bool (value-of-exp exp env))))]

      [else (raise-exception 'value-of-exp "Abstract syntax case not implemented: ~s" (car exp))])))



;; ==================== Interpreter ====================================

;; (start) -- Starts the interpreter.
(define start
  (lambda ()
    (begin
      (display "\n ><(((> === Welcome to Sachie's Interpreter === ---<{{@ \n \n")
      (let ((current-env (make-init-env)))
	(read-eval-print current-env)))))

;; make an invironment
(define make-init-env
  (lambda ()
    (begin 
      (let ((curr (extend-env 'pi (num-val 3.14159) (empty-env))))
	(extend-env 'e (num-val 2.71828) curr)))))

;; (get-input-string) -- Reads a line from the interactive input
;; port.  Ignores zero length strings.
(define get-input-string
  (lambda ()
    (let ([str (get-line (current-input-port))])
      (if (= (string-length str) 0) 
	  (get-input-string)
	  str))))

;; (read-eval-print) -- Main read, eval, and print loop.
(define read-eval-print
  (lambda (env)
    ;; Display an interpreter prompt
    (display "\n==> What's my assginment? \n") 
    (display "==> ")
    ;; Read a line user input
    (let ([code (get-input-string)])
      (cond 
       [(equal? code "!quit")
	(display "Goodbye!")  ;; Quit if '!quit entered.
	(newline)]
        [(equal? code "!debug1")
	(begin
	  (trace value-of)
	  (trace value-of-exp)
	;; "Loop".  Notice it is tail recursive.
	  (read-eval-print env))]
       [(equal? code "!debug2")
	(begin
	  (trace value-of)
	  (trace value-of-exp)
	  (trace expval->num)
	  (trace expval->bool)
	  (trace expval->proc)
	  (trace expval->string)
	;; "Loop".  Notice it is tail recursive.
	  (read-eval-print env))]
       [(equal? code "!debug0")
	(begin
	  (untrace value-of)
	  (untrace value-of-exp)
	  (untrace expval->num)
	  (untrace expval->bool)
	  (untrace expval->proc)
	  (untrace expval->string)
	  ;; "Loop".  Notice it is tail recursive.
	  (read-eval-print env))]
       
       [(equal? code "!env")
	(begin
	  (display "[")
	  (display  (str-builder env))
	  ;; "Loop".  Notice it is tail recursive.
	  (read-eval-print env))]
	  
   
       [(equal? code "!reset-env")
	(begin 
	  (set! env (make-init-env))
	  ;; "Loop".  Notice it is tail recursive.
	  (read-eval-print env))]

       [else   ;; Do something
	;; Parse code, eval expression, and print result.
	(guard  ;; Catches parse exceptions from sllgen
	 (parse-except 
    (parse-except
      (display "Runtime Error:\n")
      (display-exception parse-except))
	  [else   ;; With only an else case this catches every exception.
	   (display "Error:\n")
	   (display-exception parse-except)
	   ])
	 (let
	     ([abstract-code (parse code)])  ;; Try to parse the input line
	   (let*
	       ([val (car (value-of abstract-code env))])
	     (display (expval->string val))
	     (newline)
	     )))
	(read-eval-print env)]
       ))))

;; String builder - helper function for displaying environment
(define str-builder
  (lambda (env)
   (cases environment env
      [empty-env () "]"]
      [extend-env (var val env*)
		  (let ((vr (symbol->string var)) (vl (number->string (car (reverse val)))))
		  (cases environment env*
			 (empty-env () (string-append vr " = " vl (str-builder env*)))
			 (extend-env (var val sub-env) (string-append vr " = " vl  ", " (str-builder env*)))))])))


	   





