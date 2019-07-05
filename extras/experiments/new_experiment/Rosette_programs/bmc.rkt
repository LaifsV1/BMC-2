#lang rosette
(provide k nil define-k bmc (rename-out [app-k #%app] [if-k if]))

(define k (make-parameter 1))

(define nil 'nil)

(define-syntax define-k ; unrolls recursive calls <= k times
 (syntax-rules ()
 [(_ (id arg ...) expr ...)
 (define (id arg ...)
 (if (>= (k) 0)
 (parameterize ([k (sub1 (k))])
 expr ...)
 nil))]
 [(_ id expr)
 (define id expr)]))

(define-syntax app-k
 (syntax-rules ()
 [(_ proc arg ...)
 (apply-or-nil proc arg ...)]))

(define-syntax if-k
 (syntax-rules ()
 [(_ cond then else)
 (let ([c cond])
 (if (equal? c nil) nil
 (if c then else)))]))

(define (apply-or-nil proc . arg)
 (if (or (equal? proc nil) (ormap (curry equal? nil) arg))
 nil
 (apply proc arg)))

(define (bmc proc [bound (k)])
 (define-symbolic* arg integer? [(procedure-arity proc)])
 (parameterize ([k bound])
 (define sol (verify (apply proc arg)))
 (printf "\n~a, k = ~a: ~a\n"
 (object-name proc) bound
 (if (sat? sol)
 `(cex ,@(evaluate arg sol))
 `(unsat)))))