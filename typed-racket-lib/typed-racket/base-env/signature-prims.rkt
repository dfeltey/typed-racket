#lang racket/base

;; This file implements unit signatures for typed racket

(provide define-signature)

(require "../utils/utils.rkt"
         "colon.rkt"
         (for-syntax syntax/parse
                     racket/base
                     racket/list
                     racket/syntax
                     syntax/kerncase
                     "../private/syntax-properties.rkt"
                     syntax/id-table
                     racket/dict
                     racket/unit-exptime
                     (utils tc-utils))
         (only-in racket/unit
                  [define-signature untyped-define-signature]
                  extends)
         "../typecheck/internal-forms.rkt"
         (for-label "colon.rkt")
         (for-template (rep type-rep)))

(begin-for-syntax 
  (define-literal-set colon #:for-label (:))
  
  ;; TODO: there should be a more extensible way of handling signatures
  (define-syntax-class def-sig-form
    #:literal-sets (colon)
    (pattern [name:id : type]
             #:with internal-form #'(name type)
             #:with erased #'name))
  
  (define-splicing-syntax-class extends-form
    #:literals (extends)
    (pattern (~seq extends super:id)
             #:with internal-form #'super
             #:with extends-id #'super
             #:attr form #'(extends super))
    (pattern (~seq)
             #:with internal-form #'#f
             #:with extends-id '()
             #:attr form '())))

;; typed define-signature macro
(define-syntax (define-signature stx)
  (syntax-parse stx
    [(_ sig-name:id super-form:extends-form (form:def-sig-form ...)) 
       #`(begin
           #,(ignore (quasisyntax/loc stx
                       (untyped-define-signature sig-name #,@(attribute super-form.form)
                                                 (form.erased ...))))
           #,(internal (quasisyntax/loc stx
                         (define-signature-internal sig-name super-form.internal-form
                           (form.internal-form ...)))))]))
