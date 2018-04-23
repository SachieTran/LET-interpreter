;; PROC-interp-final.ss
;; Has full installation of procedures (on top of initial LET language, not
;; on top of full LET language)

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
     ("-(" expression "," expression ")")  ;;   Concrete       -(<Expr>,<Expr>)
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
    ;; Concrete    proc (<ID>) <Expr>
    ;; Abstract    (proc-exp var exp)
    (expression                      
     ("proc" "(" identifier ")" expression)
     proc-exp)                             
    
    ;; <Expr> ::=
    ;; Concrete    (<Expr>  <Expr>)
    ;; Abstract    (call-exp exp1 exp2)
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
;; of an environment, we wrote earlier.  I translated the
;; representation into a define-datatype so we get the constructors
;; and type checking predicate for free, and can use cases to process.

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

(define-datatype expval expval?
  (num-val
   (num number?))
  (bool-val
   (b boolean?))
  (proc-val
   (p proc?))
)

(define-datatype proc proc?
  (procedure
   (param symbol?)
   (body expression?)
   (saved-env environment?)))

(define expval->num
  (lambda (ev)
    (cases expval ev
	   [num-val (num) num]
	   [else (raise-exception 'expval->num "Expressed value is not a number: ~s" ev)])))

(define expval->bool
  (lambda (ev)
    (cases expval ev
	   [bool-val (b) b]
	   [else (raise-exception 'expval->bool "Expressed value is not a Boolean: ~s" ev)])))

(define expval->proc
  (lambda (ev)
    (cases expval ev
	   [proc-val (p) p]
	   [else (raise-exception 'expval->proc "Expressed value is not a procedure: ~s" ev)])))

(define expval->string
  (lambda (ev)
    (cases expval ev
	   [bool-val (b) (if b "#true" "#false")]
	   [num-val (num) (number->string num)]
	   [proc-val (p) "#proc"]
	   )))
		

;; ==================== Evaluator =========================================
;; parse function is in lex-scan-parse.scm

(define value-of-prog
  (lambda (prog env)
    (cases program prog
      [a-prog (exp)  (value-of-exp exp env)]
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
	      (let
		  ([val1 (expval->bool (value-of-exp exp1 env))])
		(if val1 (value-of-exp exp2 env) (value-of-exp exp3 env)))]
      [var-exp (var) (apply-env env var)]
      [let-exp (var exp body)
	       (let 
		   ([val1 (value-of-exp exp env)])
		 (value-of-exp body (extend-env var val1 env)))]
      [proc-exp (var body) (proc-val (procedure var body env))]
      [call-exp (exp1 exp2)
		(let
		    ([p (value-of-exp exp1 env)]
		     [val (value-of-exp exp2 env)])
		  (cases proc (expval->proc p)
			 [procedure (param body saved-env)
				    (value-of-exp body (extend-env param val saved-env))]))]
      [else (raise-exception 'value-of-exp "Abstract syntax case not implemented: ~s" (car exp))])))


;; =================== Interpreter =========================================
;; (start) -- Starts the interpreter.
(define start
  (lambda ()
    (begin
      (display "\n ><(((> === Welcome to PROC Interpreter === ---<{{@ \n \n==> What's my assginment? \n")
      (let ((current-env (make-init-env)))
      (read-eval-print current-env)))))

;; make an invironment
(define make-init-env
  (lambda ()
    (begin
      (extend-env 'pi (num-val 3.14159) (empty-env))
      (extend-env 'e (num-val 2.71828) (empty-env)))))


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
    (display "==> ")
    ;; Read a line user input
    (let ([concrete-code (get-input-string)])
      (cond
       [(equal? concrete-code "!quit")  
	(display "Goodbye!")  ;; Quit if '!quit entered.
	(newline)]
       [(equal? concrete-code "!debug1")
	(begin
	  (trace value-of-prog)
	  (trace value-of-exp)
	;; "Loop".  Notice it is tail recursive.
	  (read-eval-print env))]
       [(equal? concrete-code "!debug2")
	(begin
	  (trace value-of-prog)
	  (trace value-of-exp)
	  (trace expval->num)
	  (trace expval->bool)
	  (trace expval->proc)
	  (trace expval->string)
	;; "Loop".  Notice it is tail recursive.
	  (read-eval-print env))]
       [(equal? concrete-code "!debug0")
	(begin
	  (untrace value-of-prog)
	  (untrace value-of-exp)
	  (untrace expval->num)
	  (untrace expval->bool)
	  (untrace expval->proc)
	  (untrace expval->string)
	  ;; "Loop".  Notice it is tail recursive.
	  (read-eval-print env))]
       [(equal? concrete-code "!env")
	(begin
	  (display "[")
	  (display (map (lambda (ls) (begin (display ls) (display"\n"))) env))
	  (display "]")
	  ;; "Loop".  Notice it is tail recursive.
	(read-eval-print env))]
       [(equal? concrete-code "!reset-env")
	(begin 
	  (set! env (make-init-env))
	  ;; "Loop".  Notice it is tail recursive.
	  (read-eval-print env))]
	
			
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
	    (display (expval->string (value-of-prog abstract-code (env))))
	 (newline))))
	;; "Loop".  Notice it is tail recursive.
	(read-eval-print env)]
       ))))

;; (begin (display (car ls)) (display " = ") (display (cadr ls)) (display ",")))
