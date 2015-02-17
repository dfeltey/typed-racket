#lang racket/base

;; Primitive forms for units/signatures

(provide ;define-signature
         unit 
         define-unit
         compound-unit 
         define-compound-unit
         compound-unit/infer
         define-compound-unit/infer
         invoke-unit
         define-values/invoke-unit)


(require  "../utils/utils.rkt"
          "colon.rkt"
          "../private/unit-literals.rkt"
          (for-syntax syntax/parse
                      racket/base
                      racket/list
                      racket/syntax
                      syntax/context
                      syntax/flatten-begin
                      syntax/kerncase
                      "../private/syntax-properties.rkt"
                     ; (private parse-type)
                     ;(rep type-rep)
                     ; (env signature-helper)
                      syntax/id-table
                      racket/dict
                      racket/unit-exptime
                      syntax/strip-context
                      (utils tc-utils)
                      syntax/id-table)
          (only-in racket/unit 
                   [define-signature untyped-define-signature] 
                   [unit untyped-unit]
                   [invoke-unit untyped-invoke-unit]
                   [compound-unit untyped-compound-unit]
                   [define-unit untyped-define-unit]
                   [define-compound-unit untyped-define-compound-unit]
                   [define-values/invoke-unit untyped-define-values/invoke-unit]
                   [compound-unit/infer untyped-compound-unit/infer]
                   [define-compound-unit/infer untyped-define-compound-unit/infer]
                   extends
                   import
                   export
                   init-depend
                   link
                   prefix)
          "../typecheck/internal-forms.rkt"
          "base-types.rkt"
          "base-types-extra.rkt"
          (for-label "colon.rkt")
          (for-template (rep type-rep)))

(begin-for-syntax
  (define-literal-set colon #:for-label (:))

  ;; TODO: extend for other sig forms
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
             #:attr form '()))

  (define-splicing-syntax-class init-depend-form
    #:literals (init-depend)
    (pattern (init-depend sig:id ...)
             #:attr form (list #'(init-depend sig ...))
             #:with names #'(sig ...))
    (pattern (~seq)
             #:attr form '()
             #:with names #'()))
  
  (define-syntax-class unit-expr
    (pattern e
             #:with val #'e))
  
  ;; More general handling of import/export signatures in units
  (define-syntax-class unit-imports
    #:literals (import)
    (pattern (import sig:sig-spec ...)
             #:with names #'(sig.sig-name ...)
             #:attr renamers (attribute sig.rename)))

  (define-syntax-class unit-exports
    #:literals (export)
    (pattern (export sig:sig-spec ...)
             #:with names #'(sig.sig-name ...)
             #:attr renamers (attribute sig.rename)))
  
  (define-syntax-class sig-spec
    #:literals (prefix)
    (pattern sig-id:id
             #:attr rename (lambda (id) id)
             #:with sig-name #'sig-id)
    (pattern (prefix p:id sig:sig-spec)
             #:attr rename (lambda (id) (format-id #'sig.sig-name
                                                 "~a~a"
                                                 #'p
                                                 ((attribute sig.rename) id)))
             #:with sig-name #'sig.sig-name))
  
  
  ;; need lexical signature vars to error with duplicate type annotations
  (define (signatures-vars stx)
    (define (signature-vars sig-id)
      (let-values ([(_0 vars _2 _3)
                    (signature-members sig-id sig-id)])
        vars))
    (apply append (map signature-vars (syntax->list stx))))
  
  ;; extract vars from a signature with the correct syntax marks
  ;; I have no idea why this works, or is necessary
  ;; TODO: this is probably not general enough and will need to be modified
  ;; to deal with prefix/rename when those are implemented for TR units
  (define (get-signature-vars sig-id)
    (define-values (_0 vars _2 _3)
      ;; TODO: give better argument for error-stx
      (signature-members sig-id sig-id))

    (map
     ;(unitify-id sig-id)
     syntax-local-introduce
     vars))
  
  ;; No idea what this does
  (define (unitify-id sig-id)
    (lambda (id)
      (syntax-local-introduce
       (syntax-local-get-shadower
        ((lambda (id-inner)
           (syntax-local-introduce
            ((syntax-local-make-delta-introducer sig-id) id-inner))) id)))))
  
  (define (get-signatures-vars stx)
    (define sig-ids (syntax->list stx))
    (apply append (map (lambda (sig-id) (get-signature-vars sig-id)) sig-ids)))

  ;; same trick as for classes to recover names
  (define (make-locals-table names)
    (with-syntax ([(name ...) names])
      (tr:unit:local-table-property
       #'(let-values ((()
                       (list (cons (quote-syntax name) (lambda () name)) ...)))
           (void))
       #t))
    
    #;
    (tr:unit:local-table-property
     #`(let-values ([(#,@names)
                     (values #,@(map (lambda (stx) #`(lambda () (#,stx)))
                                     names))])
         (void))
     #t))
 
  (define (make-annotated-table names)
    (with-syntax ([(name ...) 
                   (map
                    (lambda (id)
                      (syntax-property id 'sig-id id))
                    names)])
      #`(let-values ((()
                      (begin 
                        (list name ...)
                        (values))))
          (void))))
  
  
  (define (make-unit-signature-table imports
                                     exports
                                     init-depends)
    
    #`(unit-internal 
       (#:imports #,@imports)
       (#:exports #,@exports)
       (#:init-depends #,@init-depends))))


;; Abstraction for creating trampolining macros
(begin-for-syntax
  (define-syntax-class (begin-form name [arg #'()])
    #:literals (begin)
    (pattern (begin e ...)
             #:with trampoline-form
             #`(#,name #,@arg e ...)))
  (define-syntax-class (name-form name)
    (pattern (_ e ...)
             #:with trampoline-form
             #`(begin (#,name e) ...)))
  (define-splicing-syntax-class (rest-form name arg)
    (pattern (~seq) 
             #:with trampoline-form
             #`(begin))
    (pattern (~seq e1 e2 ...)
             #:with trampoline-form
             #`(begin (#,name #,@arg e1)
                      (#,name #,@arg e2) ...))))

(define-syntax (define-trampolining-macro stx)
  (syntax-parse stx
    [(_ name:id case ...)
     #`(define-syntax (name stx)
         (syntax-parse stx
           [(_) #'(begin)]
           [(name e) 
            (define exp-e 
              (local-expand #'e (syntax-local-context) (kernel-form-identifier-list)))
            (syntax-parse exp-e
              #:literal-sets (kernel-literals)
              [(~var b (begin-form #'name))
               #'b.trampoline-form]
              case ...
              [_ exp-e])]
           [(~var e (name-form #'name))
            #'e.trampoline-form]))]
    [(_ (name:id arg ...) case ...)
     #`(define-syntax (name stx)
         (syntax-parse stx
           [(_ arg ...) #'(begin)]
           [(name arg ... e) 
            (define exp-e 
              (local-expand #'e (syntax-local-context) (kernel-form-identifier-list)))
            (syntax-parse exp-e
              #:literal-sets (kernel-literals)
              [(~var b (begin-form #'name #`(arg ...)))
               #'b.trampoline-form]
              case ...
              [_ exp-e])]
           [(_ arg ... (~var exprs (rest-form #'name #`(arg ...))))
            #'exprs.trampoline-form]))]))

    
   




;; Typed macro for define-values/invoke-unit
;; This has to be handled specially because they types of
;; the defined values must be registered in the environment
;;
;; TODO: prefixes/etc on import/exports
(define-syntax (define-values/invoke-unit stx)
  (syntax-parse stx 
    #:literals (import export)
    [(_ unit-expr
        (import isig:id ...)
        (export esig:id ...))
     (with-syntax ([(temp) (generate-temporaries #'(temp))])
         #`(begin
             #,(internal (quasisyntax/loc stx
                           (define-values/invoke-unit-internal
                             (isig ...)
                             (esig ...))))
             (: temp (Unit (import isig ...)
                           (export esig ...)
                           ;; FIXME this needs to be AnyValues
                           Any))
             (define temp unit-expr)
             
             #,(ignore (quasisyntax/loc stx
                         (untyped-define-values/invoke-unit temp
                                                            (import isig ...)
                                                            (export esig ...))))))]))

;; Maybe the define-trampolining-macro should allow parameters
;; this would make handling a lot of forms much simpler
#;
(define-trampolining-macro process-define-values/invoke-unit
  [(define-values (name:id ...) rhs)
   #`(define-values (name ...)
       #,(ignore 
          (tr:unit:def-val/inv-unit
           (quasisyntax/loc #'rhs rhs))))])






;; helpful definitions for later typechecking
(define-values-for-syntax (access-table add-table)
  (let* ([key (gensym)]
         [get-table (lambda (stx) (syntax-property stx key))]
         [set-table (lambda (stx table) (syntax-property stx key table))])
    (values get-table set-table)))

(define-for-syntax (type-table-ref table id)
  (assoc id table free-identifier=?))



;; start of rewrite to use define-syntax/syntax-local-value as a 
;; better communication channel inside the unit macro
;;
;; Also moving away from syntax properties as places to store type information
;; 2 Feautures to help fix this
;;   1. Indexing unit imports
;;   2. inserting define-values names into the expression needed to type check
;;





;; This is the working version use this!!!
(define-trampolining-macro add-tags
  [(define-values (name:id ...) rhs)
   #`(define-values (name ...)
       #,(tr:unit:body-exp-def-type-property
          #'(#%expression
             (begin
               (void (lambda () name) ...)
               rhs))
          'def/type))]
  [e (tr:unit:body-exp-def-type-property #'e 'expr)])

#;
(define-syntax (add-tags stx)
  (syntax-parse stx
    [(_) #'(begin)]
    [(_ e)
     (define exp-e (local-expand #'e (syntax-local-context) (kernel-form-identifier-list)))
     (syntax-parse exp-e
       #:literals (begin define-values define-syntaxes)
       [(begin b ...)
        #'(add-tags b ...)]
       [(define-syntaxes (name:id ...) rhs:expr) 
        exp-e]
       [(define-values (name:id ...) rhs)
        #`(define-values (name ...)
            #,(tr:unit:body-exp-def-type-property
               #'(#%expression
                  (begin
                    (void (lambda () name) ...)
                    rhs))
               'def/type))]
       [_
        (tr:unit:body-exp-def-type-property exp-e 'expr)])]
    [(_ e ...)
     #'(begin (add-tags e) ...)]))


;; This table implementation is going to break when only/except are allowed in
;; typed units, the indexing strategy won't work in that case
(define-for-syntax (make-signature-local-table imports import-renamers 
                                               exports export-renamers 
                                               init-depends)
  (define (make-index-row sig-id renamer)
    (with-syntax ([(sig-var ...) (map renamer (get-signature-vars sig-id))]) 
      #`(list (quote-syntax #,sig-id) (cons (quote-syntax sig-var) (lambda () sig-var)) ...)))
  (tr:unit:index-table-property
   (with-syntax ([(init-depend ...) (syntax->list init-depends)])
     #`(let-values ([() (#%expression
                         (begin (void #,@(map make-index-row 
                                              (syntax->list imports)
                                              import-renamers))
                                (values)))]
                    [() (#%expression
                         (begin  (void #,@(map make-index-row 
                                               (syntax->list exports)
                                               export-renamers))
                                 (values)))]
                    [() (#%expression
                         (begin  (void (quote-syntax init-depend) ...)
                                 (values)))])
         (void)))
   #t))


(define-syntax (unit stx)
  (syntax-parse stx
    [(unit imports:unit-imports 
       exports:unit-exports
       init-depends:init-depend-form
       e:unit-expr ...)
     (ignore
      (tr:unit
       (quasisyntax/loc stx
         (untyped-unit  imports
                        exports
                        #,@(attribute init-depends.form)
                        #,(make-signature-local-table #'imports.names
                                                      (attribute imports.renamers)
                                                      #'exports.names
                                                      (attribute exports.renamers)
                                                      #'init-depends.names)
                        (add-tags e ...)))))]))

#;
(define-syntax (process-define-unit stx)
  (syntax-parse stx
    [(_) #'(begin)]
    [(_ e)
     (define exp-e (local-expand #'e (syntax-local-context) (kernel-form-identifier-list)))
     (printf "EXPANDED-OLD: ~a\n" exp-e)
     (syntax-parse exp-e
       #:literal-sets (kernel-literals)
       ;; #:literals (begin define-values define-syntaxes)
       [(begin b ...)
        #'(process-define-unit b ...)]
       [(define-syntaxes (name:id ...) rhs:expr)
        exp-e]
       [(define-values (name:id ...) rhs)
        #`(define-values (name ...)
            #,(ignore
               (tr:unit
                #`rhs)))]
       [_ exp-e])]
    [(_ e ...)
     #'(begin (process-define-unit e) ...)]))

(define-trampolining-macro process-define-unit
  [(define-values (name:id ...) rhs)
   #`(define-values (name ...)
       #,(ignore
          (tr:unit
           #'rhs)))])


;; define-unit macro
(define-syntax (define-unit stx)
  (syntax-parse stx
    [(define-unit uid:id
       imports:unit-imports
       exports:unit-exports
       init-depends:init-depend-form
       e:unit-expr ...)
     (quasisyntax/loc stx
       (process-define-unit 
        (untyped-define-unit uid
          imports
          exports
          #,@(attribute init-depends.form)
          #,(make-signature-local-table #'imports.names
                                        (attribute imports.renamers)
                                        #'exports.names
                                        (attribute exports.renamers)
                                        #'init-depends.names)
          (add-tags e ...))))]))


;; invoke-unit macro
(begin-for-syntax 
  (define-splicing-syntax-class invoke-imports
    #:literals (import)
    (pattern (~seq)
             #:attr untyped-import #'()
             #:with imports #'())
    (pattern (import sig:id ...)
             #:attr untyped-import #'((import sig ...))
             #:with imports #'((quote-syntax sig) ...))))

(define-syntax (invoke-unit stx)
  (syntax-parse stx
    [(invoke-unit unit-expr imports:invoke-imports)
     (ignore
      (tr:unit:invoke
       (quasisyntax/loc stx
         (untyped-invoke-unit
          #,(tr:unit:invoke:expr-property 
             #`(#%expression
                (begin
                  (void #,@#'imports.imports)
                  unit-expr)) 
             #t)
          #,@(attribute imports.untyped-import)))))]))

;; Syntax classes and macro for typed compound-unit
(begin-for-syntax
  (define-syntax-class compound-unit-form
    #:literals (compound-unit)
    (pattern
     (~and stx
           (compound-unit imports:compound-imports
                          exports:compound-exports
                          links:compound-links))
     #:attr untyped-stx
     (ignore
      (tr:unit:compound-property
       (quasisyntax/loc #'stx
         (#%expression
          (begin
            (void #,@#'imports.import-link-ids #,@(attribute links.bound-link-ids))
            (void #,@#'imports.import-sig-ids #,@(attribute links.bound-sig-ids))
            (void #,@#'imports.import-link-ids)
            exports.export-link-ids
            (void)
            (untyped-compound-unit imports
                                   exports
                                   links.untyped-links))))
       #t))))
  (define-syntax-class compound-imports
    #:literals (import)
    (pattern (import lb:link-binding ...)
             #:with import-link-ids
             #'(lb.link-qs ...)
             #:with import-sig-ids
             #'(lb.sig-qs ...)
             #:with import-link-map #'(lb.link-map-elem ...)))
  (define-syntax-class compound-exports
    #:literals (export)
    (pattern (export l:id ...)
             #:with export-link-ids 
             #'(void (quote-syntax l) ...)))
  (define-syntax-class compound-links
    #:literals (link)
    (pattern (link ld:linkage-decl ...)
             #:with untyped-links
             #'(link ld.untyped-link-decl ...)
             #:attr bound-link-ids (apply append (map syntax->list 
                                                   (syntax->list 
                                                    #'(ld.bound-link-ids ...))))
             #:attr bound-sig-ids (apply append (map syntax->list
                                                     (syntax->list
                                                      #'(ld.bound-sig-ids ...))))))
  (define-syntax-class linkage-decl
    (pattern ((lb:link-binding ...)
              unit-expr:expr
              link-id:id ...)
             #:with bound-link-ids #'(lb.link-qs ...)
             #:with bound-sig-ids #'(lb.sig-qs ...)
             #:with untyped-link-decl
             #`((lb ...)
                #,(tr:unit:compound:expr-property
                   #`(#%expression
                      (begin
                        (void (quote-syntax lb.sig-id) ...)
                        (void (quote-syntax lb.link-id) ...)
                        (void (quote-syntax link-id) ...)
                        unit-expr)) 
                   #t)
                link-id ...)))
  (define-syntax-class link-binding
    (pattern (link-id:id : sig-id:id)
             #:with link-qs #'(quote-syntax link-id)
             #:with sig-qs #'(quote-syntax sig-id)
             #:with link-map-elem #'(link-id sig-id))))


;; I think it would be better/make type checking easier
;; to pull all of the sig-name/link-name pairs to outside
;; of the compound form in ordet to construct the mapping
;; most easily at typecheck time
(define-syntax (compound-unit stx)
  (syntax-parse stx
    [cu:compound-unit-form
     (attribute cu.untyped-stx)]))

(define-trampolining-macro (process-define-compound-unit links sigs im ex infer)
  [(define-values (name:id ...) rhs)
   #`(define-values (name ...)
       #,(ignore
          (tr:unit:compound-property
           #`(#%expression
              (begin
                links
                sigs
                im
                ex
                infer
                rhs))
           #t)))])


(define-syntax (define-compound-unit stx)
  (syntax-parse stx
    [(_ uid 
        imports:compound-imports
        exports:compound-exports
        links:compound-links)
     (quasisyntax/loc stx
       (process-define-compound-unit
        (void #,@#'imports.import-link-ids #,@(attribute links.bound-link-ids))
        (void #,@#'imports.import-sig-ids #,@(attribute links.bound-sig-ids))
        (void #,@#'imports.import-link-ids)
        (void)
        exports.export-link-ids
        (untyped-define-compound-unit uid
                                      imports
                                      exports
                                      links.untyped-links)))]))

;; compound-unit/infer

(begin-for-syntax
  (define-syntax-class compound-infer-imports
    #:literals (import)
    (pattern (import im:infer-link-import ...)
             #:with import-link-ids
             #'(im.link-qs ...)
             #:with import-sig-ids
             #'(im.sig-qs ...)))
  
  (define-syntax-class compound-infer-exports
    #:literals (export)
    (pattern (export ex:infer-link-export ...)
             #:with export-links-or-sigs
             #'(void (quote-syntax ex.link-or-sig-id) ...)))
  
  (define-syntax-class compound-infer-links
    #:literals (link)
    (pattern (link lnk:infer-linkage-decl ...)
             ;; #:with untyped-links
             ;; #'(link lnk.untyped-link-decl ...)
             #:attr bound-link-ids (apply append (map syntax->list 
                                                      (syntax->list 
                                                       #'(lnk.bound-link-ids ...))))
             #:attr bound-sig-ids (apply append (map syntax->list
                                                     (syntax->list
                                                      #'(lnk.bound-sig-ids ...))))
             
             #:with links-untyped 
             #'(link lnk.linkage-stx ...)
             #:attr link-table
             #`(void lnk.linkage-information ...)))
  
  (define-syntax-class infer-link-import
    (pattern sig-id:id
             #:with sig-qs #'(quote-syntax sig-id)
             #:with link-qs #`(quote-syntax #,(generate-temporary)))
    (pattern (link-id:id : sig-id:id)
             #:with link-qs #'(quote-syntax link-id)
             #:with sig-qs #'(quote-syntax sig-id)))
  
  (define-syntax-class infer-link-export
    (pattern link-or-sig-id:id))
  
  ;; allowing the unit-id below to be exprs
  ;; so that the untyped macro can give better error
  ;; reporting
  (define-syntax-class infer-linkage-decl
    (pattern ((lb:link-binding ...)
              unit-id:expr
              link-id:id ...)
             #:with bound-link-ids #'(lb.link-qs ...)
             #:with bound-sig-ids #'(lb.sig-qs ...)
             #:with linkage-stx
             #`((lb ...)
                #,(tr:unit:compound:expr-property
                   #'unit-id
                   'infer)
                link-id ...)
             #:with linkage-information
             #`(#%expression
                (begin
                  (void (quote-syntax lb.sig-id) ...)
                  (void (quote-syntax lb.link-id) ...)
                  (void (quote-syntax link-id) ...)
                  (void (quote-syntax unit-id)
                        #;(lambda () unit-id)
                        ))))
    (pattern unit-id:expr
             #:with bound-link-ids #'()
             #:with bound-sig-ids #'()
             #:with linkage-stx
             (tr:unit:compound:expr-property #'unit-id 'infer)
             #:with linkage-information
             #`(#%expression
                (begin
                  (void)
                  (void)
                  (void)
                  (void (quote-syntax unit-id) 
                        #;(lambda () unit-id)
                        ))))))

;; NOTE/TODO:
;; - it seems that the docs for compound-unit/infer
;;   suggest that imports are filled in from the 
;;   static information bound to the unit-ids
;;   but simple tests don't seem to confirm this

(define-syntax (compound-unit/infer stx)
  (syntax-parse stx
    [(_ 
      imports:compound-infer-imports
      exports:compound-infer-exports
      links:compound-infer-links)
     (ignore
      (tr:unit:compound-property
       (quasisyntax/loc stx
         (#%expression
          (begin
            (void #,@#'imports.import-link-ids
                  #,@(attribute links.bound-link-ids))
            (void #,@#'imports.import-sig-ids
                  #,@(attribute links.bound-sig-ids))
            (void #,@#'imports.import-link-ids) 
            exports.export-links-or-sigs
            #,(attribute links.link-table)
            ;; NOTE:
            ;;  No reason to alter the syntax at all
            ;;  since nothing seems recoverable from the
            ;;  expansion
            (untyped-compound-unit/infer
             imports
             exports 
             links))))
       'infer))]))


;; This doesn't work because I can't figure out how to
;; get the identifiers to which the units are bound 
;; after expansion is finished

(define-syntax (define-compound-unit/infer stx)
  (syntax-parse stx
    [(_ unit-name:id
        imports:compound-infer-imports
        exports:compound-infer-exports
        links:compound-infer-links)
     (quasisyntax/loc stx
       (process-define-compound-unit
        
        (void #,@#'imports.import-link-ids
              #,@(attribute links.bound-link-ids))
        
        (void #,@#'imports.import-sig-ids
              #,@(attribute links.bound-sig-ids))
        (void #,@#'imports.import-link-ids) 
        exports.export-links-or-sigs
        
        #,(attribute links.link-table)
        
        
        (untyped-define-compound-unit/infer unit-name
                                            imports
                                            exports
                                            links)))]))



