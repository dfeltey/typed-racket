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
   
   
   ;; I want to write this, but this doesn't actually work
   [tc-err
    (module Test typed/racket/base
      (require typed/racket/unit)
      (define-signature x^ ([x : String]))
      (unit (import x^) (export)
        (: y Integer)
        (define y x)
        y))]
   
   [tc-err
    (unit (import) (export)
      (: x String)
      (define x 5))]))

