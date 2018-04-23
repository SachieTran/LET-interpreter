;; PROC-interp-starter.ss
;; Starter code for working on PROC language interpreter
;; This is basically the LET language interpreter with additions to
;; the grammar, but no other modifications

(load "helpers.scm")


;; ================ Parser Definitions ==================================
;; This defines the translation from the concrete syntax to the abstract syntax
(define the-grammar
  '((program                        ;; <Program> ::= 
     (expression)                   ;;   Concrete    <Expr>
     a-prog)                        ;;   Abstract    (a-prog exp)
    
    (expression                     ;; <Expr> ::= 
     (number)                       ;;   Concrete       <Number> 
     const-exp)                     ;;   Abstract       (const-exp num)
    
    (expression                            ;; <Expr> ::= 
     ("-(" expression "," expression ")")  ;;   Concrete     -(<Expr>,<Expr>)
     diff-exp)                         ;;   Abstract       (diff-exp exp1 exp2)

    (expression                     ;; <Expr> ::= 
     ("zero?(" expression ")")      ;;   Concrete       zero?(<Expr>)
     zero?-exp)                     ;;   Abstract       (zero?-exp exp)
    
    ;; <Expr> ::=
    ;;   Concrete   if <Expr> then <Expr> else <Expr>
    ;;   Abstract   (if-exp exp1 exp2 exp3)                
    (expression                                      
     ("if" expression "then" expression "else" expression) 
     if-exp)                                               
        
    (expression                     ;; <Expr> ::= 
     (identifier)                   ;;   Concrete       <ID>
     var-exp)                       ;;   Abstract       (var-exp var)

    ;; <Expr> ::=
      ;; Concrete    let <ID> = <Expr> in <Expr>         
      ;; Abstract    (let-exp var exp1 exp2)    
    (expression          
     ("let" identifier "=" expression "in" expression)
     let-exp) 
                                        
    ;; <Expr> ::=                       
    ;;   Concrete    proc (<ID>) <Expr>
    ;;   Abstract    (proc-exp var exp)                                       
    (expression
     ("proc" "(" identifier ")" expression)
     proc-exp)

    ;; <Expr> ::=  
    ;;    Concrete    (<Expr>  <Expr>) 
    ;;    Abstract    (call-exp exp1 exp2)
    (expression
     ("(" expression expression ")")
     call-exp)
))

;; Sets up the parser using the above concrete <-> abstract grammars.          
;; Defines a function call parse that takes a string in the concrete           
;; syntax and returns the corresponding abstract syntax tree. You must         
;; have defined the-grammar first, so must do this load after the-grammer
;; is defined. 
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
   (num real?))
  (bool-val
   (bool boolean?))
)

(define expval->num 
  (lambda (ev)
    (cases expval ev
      [num-val (num) num]
      [else (raise-exception 'expval->num "Expressed value is not a number: ~s" ev)])))

(define expval->bool
  (lambda (ev)
    (cases expval ev
      [bool-val (bool) bool]
      [else (raise-exception 'expval->bool "Expressed value is not a Boolean: ~s" ev)])))

(define expval->string
  (lambda (ev)
    (cases expval ev
      [bool-val (bool) (if bool "#t" "#f")]
      [num-val (num) (number->string num)]
)))

;; ==================== Evaluator ====================================
;; parse function is in lex-scan-parse.scm

(define value-of-prog
  (lambda (prog env)
    (cases program prog
      [a-prog (exp) (value-of-exp exp env)]
      [else (raise-exception 'value-of-prog "Abstract syntax case not implemented: ~s" (car prog))])))

(define value-of-exp
  (lambda (exp env)
    (cases expression exp
      [const-exp (num) (num-val num)]
      [diff-exp (rand1 rand2) 
		(num-val (- (expval->num (value-of-exp rand1 env)) 
			    (expval->num (value-of-exp rand2 env))))]
      [zero?-exp (exp1) (bool-val (= (expval->num (value-of-exp exp1 env)) 0))]
      [if-exp (exp1 exp2 exp3) 
	      (if (expval->bool (value-of-exp exp1 env)) 
		  (value-of-exp exp2 env) 
		  (value-of-exp exp3 env))]
      [var-exp (var) (apply-env env var)]
      [let-exp (var exp body) 
	       (let
		   ([val1 (value-of-exp exp env)])
		 (value-of-exp body (extend-env var val1 env)))]

      [else (raise-exception 'value-of-exp "Abstract syntax case not implemented: ~s" (car exp))])))


;; ==================== Interpreter ====================================

;; (start) -- Starts the interpreter.
(define start
  (lambda ()
    (begin
      (display "\n=== Welcome to the Soon-To-Be-PROC-Interpreter === \n\n")
      (read-eval-print))))

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
  (lambda ()
    ;; Display an interpreter prompt
    (display "==> ")
    ;; Read a line user input
    (let ([concrete-code (get-input-string)])
      (cond
       [(equal? concrete-code "!quit")  
	(display "Goodbye!")  ;; Quit if '!quit entered.
	(newline)]
       [else
	(guard
	 (ex
	  [else
	   (display "PARSE ERROR: \n")
	   (display-exception ex)])
	 ;; Parse code, eval expression, and print result.
	 (let
	     ([abstract-code (parse concrete-code)])
	   (guard
	    (ex
	     [else
	      (display "RUNTIME ERROR: \n")
	      (display-exception ex)])
	    (display (expval->string (value-of-prog abstract-code (empty-env))))
	 (newline))))
	;; "Loop".  Notice it is tail recursive.
	(read-eval-print)]
       ))))






