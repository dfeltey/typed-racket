#lang racket/base

;; Unit tests for typed units

(require (submod "typecheck-tests.rkt" test-helpers)
         (except-in "test-utils.rkt" private)
         (for-syntax racket/base
                     typed-racket/tc-setup
                     typed-racket/utils/tc-utils))

(provide tests)
(gen-test-main)

(begin-for-syntax
  ;; for checking the printing of type aliases
  (current-type-names (init-current-type-names)))

;; see typecheck-tests.rkt for rationale on imports
(require rackunit
         typed/racket/unit
         (except-in typed-racket/utils/utils private)
         (except-in (base-env extra-procs prims class-prims
                              base-types base-types-extra)
                    define lambda λ case-lambda)
         (prefix-in tr: (only-in (base-env prims) define lambda λ case-lambda))
         (for-syntax (rep type-rep filter-rep object-rep)
                     (rename-in (types abbrev union numeric-tower filter-ops utils)
                                [Un t:Un]
                                [-> t:->])))

(define tests
  (test-suite
   "unit typechecking tests"
   
   #|
   This should typecheck, but doesn't because fact has no type annotation
   
   (define-signature fact^
     ([fact : (-> Integer Integer)]))



   (define-unit fact@
   (import (prefix i: fact^))
   (export fact^)
   (define (fact n) 
   (if (< n 1) 
   1
   (* n (i:fact (sub1 n)))))
   fact)
   |#
   
   [tc-err
    (let ()
      (unit (import)
            (export)
        (+ 1 "bad"))
      (error ""))]
   
   [tc-err
    (let ()
      (define-signature x^ ([x : String]))
      (unit (import x^) (export)
        (: y Integer)
        (define y x)
        y)
      (error ""))]
   ;; Type mismatch in unit body
   [tc-err
    (let ()  
      (unit (import) (export)
        (: x String)
        (define x 5))
      (error ""))]
   [tc-err
    (let ()
      (define-signature a^ ([a : String]))
      (unit (import) (export a^) (define a 5))
      (error ""))]
   [tc-err
    (let ()
      (define-signature a^ ([a : Integer]))
      (define a "foo")
      (invoke-unit (unit (import a^) (export) a) (import a^))
      (error ""))]
   [tc-err
    (let ()
      (define-signature a^ ([a : Integer]))
      (unit
        (import a^)
        (export)
        (: x String)
        (define x a))
      (error ""))]
   
   ;; This tests that the linking clauses in compound-unit forms
   ;; are correctly satisfied
   ;; This bug seems pretty subtle, and the type mismatch error
   ;; message doesn't make it obvious why it fails to typecheck
   [tc-err
    (let ()
      (define-signature a^ ())
       
      (define-unit a1
        (import)
        (export a^))
       
      (define-unit a2
        (import)
        (export a^))
       
      (define-unit u
        (import a^)
        (export)
        (init-depend a^))
       
      (define-compound-unit w
        (import)
        (export)
        (link
         (([A1 : a^]) a1)
         (() u A2)
         (([A2 : a^]) a2)))
      (error ""))]))

