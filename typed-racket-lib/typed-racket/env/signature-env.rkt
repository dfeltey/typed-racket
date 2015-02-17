#lang racket/base

;; Environment for signature definitions
;; to track bindings and type definitions inside of signatures

(provide register-signature!
         lookup-signature
         print-signature-env
         signature-env-map)

(require syntax/id-table
         (for-syntax syntax/parse racket/base)
         "../utils/utils.rkt"
         (utils tc-utils))

;; initial signature environment
(define signature-env (make-parameter (make-immutable-free-id-table)))

;; register-signature! : identifier? Signature? -> Void
;; adds a mapping from the given identifier to the given signature
;; in the signature environment
(define (register-signature! id sig)
  (when (lookup-signature id)
    (tc-error/fields "duplicate signature definition"
                     "identifier" (syntax-e id)))
  (signature-env (free-id-table-set (signature-env) id sig)))


(define-syntax-rule (with-signature-env/extend ids sigs . b)
  (let ([ids* ids]
        [sigs* sigs])
    (define new-env 
      (for/fold ([env (signature-env)])
                ([id (in-list ids*)]
                 [sig (in-list sigs*)])
        (free-id-table-set env id sig)))
    (parameterize ([siganture-env new-env]) . b)))

;; lookup-signature : identifier? -> (or/c #f Signature?)
;; look up the signature corresponding to the given identifier
;; in the signature environment
(define (lookup-signature id) 
  (free-id-table-ref (signature-env) id #f))

(define (signature-env-map f)  
  (free-id-table-map (signature-env) f))



;; For debugging
(define (print-signature-env)
  (printf "Start Print Signature Env\n")
  (free-id-table-for-each 
   (signature-env)
   (lambda (id sig)
     (printf "ID: ~a\n" id)
     (printf "Sig: ~a\n" sig)))
  (printf "End Print Signature Env\n"))

;; For testing units that import/export signatures
#;
(define-syntax (with-temporary-signatures stx)
  (syntax-parse stx
    [(_ ([x:id sig] ...) expr ...)
     #'(let ()
         (define temp-signature-env signature-env)
         (set! (signature-env (make-free-id-table)))
         (register-signature! #'x sig) ...
         (begin0 (begin expr ...) (set! signature-env temp-signature-env)))]))