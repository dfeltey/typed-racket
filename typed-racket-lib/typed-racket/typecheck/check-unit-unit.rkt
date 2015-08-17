#lang racket/unit

;; This module provides a unit for type-checking units

(require "../utils/utils.rkt"
         syntax/id-set
         racket/set
         racket/dict
         racket/format
         racket/list
         racket/match
         racket/syntax
         syntax/id-table
         syntax/parse
         syntax/stx
         syntax/strip-context
         racket/unit-exptime
         "signatures.rkt"
         (private parse-type syntax-properties type-annotation)
         (env lexical-env tvar-env global-env 
              signature-env signature-helper)
         (types utils abbrev union subtype resolve generalize signatures)
         (typecheck check-below internal-forms)
         (utils tc-utils)
         (rep type-rep)
         (for-syntax racket/base racket/unit-exptime syntax/parse)
         (for-template racket/base
                       racket/unsafe/undefined
                       (private unit-literals)
                       (submod "internal-forms.rkt" forms)))

(import tc-let^ tc-expr^)
(export check-unit^)

;; Helper Macro that traverses syntax and performs simple rewriting
;; FIXME: srclocs?
(define-syntax-rule (syntax-rewrite expr #:literals (lit ...)
                      [pattern body ...] ...)
  (let loop ([expr expr])
    (syntax-parse expr
      #:literal-sets (kernel-literals)
      #:literals (lit ...)
      [pattern body ...] ...
      [_
       (define list? (syntax->list expr))
       (cond
         [list?
          (quasisyntax/loc expr (#,@(map loop list?)))]
         [else expr])])))

;; Syntax class definitions
;; variable annotations expand slightly differently in the body of a unit
;; due to how the unit macro transforms internal definitions
(define-syntax-class unit-body-annotation
  #:literal-sets (kernel-literals)
  #:literals (void values :-internal cons)
  (pattern
   (~and orig-stx
         (#%expression
          (begin
            (#%plain-app void (#%plain-lambda () var-int))
            (begin
              (quote-syntax
               (:-internal var:id t) #:local)
              (#%plain-app values)))))
   #:attr fixed-form (quasisyntax/loc #'orig-stx
                         (begin
                           (quote-syntax (:-internal var-int t) #:local)
                           (#%plain-app values)))
   #:attr name #'var
   #:attr ref #'ver-int
   ;; Needed to substiture the internal renaming of exported definitions
   ;; in unit bodies in order to ensure that the annotation is applied
   ;; to the correct identifier
   #:attr letrec-form #`(begin
                          (quote-syntax (:-internal var t) #:local)
                          (#%plain-app values))
   #:attr subst-annotation (lambda (id)
                             #`(begin
                                 (quote-syntax (:-internal #,id t) #:local)
                                 (#%plain-app values)))))

(define-syntax-class unit-body-definition
  #:literal-sets (kernel-literals)
  #:literals (void)
  (pattern
   (#%expression
    (begin
      (#%plain-app void (#%plain-lambda () var:id) ...)
      e))
   #:with vars #'(var ...)
   #:with body #'e
   #:attr letrec-form #'e))


(define (process-ann/def-for-letrec ann/defs export-mapping import-mapping invoke?)
(cond
  [invoke?
   (define len (length invoke?))
   (define names #`(#,@(make-list len #'())))
   (raise-syntax-error 'tc-units "THIS IS BROKEN")]
  [else  
   (for/fold ([names #`()]
              [exprs #`()]
              [unannotated-exports (map car export-mapping)])
             ([a/d (in-list ann/defs)])
     (syntax-parse a/d
       [a:unit-body-annotation
        (define name (attribute a.name))
        ;; TODO:
        ;; Duplicate annotations from imports
        ;; are not currently detected due to a bug
        ;; in tc/letrec-values
        (define lookup-result (lookup-type name export-mapping))
        (define form ((attribute a.subst-annotation)
                      (or lookup-result name)))
        (define fixed (attribute a.fixed-form))
        ;; this should maybe remove the ref rather than the name
        ;; so that the correct internal names are removed
        (define new-unannotated-exports (remove name unannotated-exports))
        (values #`(#,@names ())
                #`(#,@exprs #,fixed)
                new-unannotated-exports)]
       [d:unit-body-definition
        (values #`(#,@names d.vars) #`(#,@exprs d.body) unannotated-exports)]))]))



(struct sig-info (name externals internals) #:transparent)
;; A Sig-Info is a (sig-info identifier? (listof identifier?) (listof identifier?))
;; name is the identifier corresponding to the signature this sig-info represents
;; externals is the list of external names for variables in the signature
;; internals is the list of internal names for variables in the signature

(define-syntax-class unit-int-rep
  #:literal-sets (kernel-literals)
  (pattern (#%plain-app int-var:id)
           #:with id #'int-var)
  (pattern int-var:id
           #:with id #'int-var))

(define-syntax-class index-row
  #:literal-sets (kernel-literals)
  #:literals (list cons)
  (pattern 
   (quote sig-id:id)
   #:with name #'sig-id))

(define-syntax-class signature-index-table
  #:literal-sets (kernel-literals)
  #:literals (void list cons values)
  (pattern
   (let-values ([() (#%expression
                     (begin (#%plain-app void export:index-row ...)
                            (#%plain-app values)))])
     (#%plain-app void))
   #:attr export-sigs (syntax->list #'(export.name ...))))

(define (parse-index-table import-sigs import-internal-ids import-tags
                           export-sigs export-temp-ids export-temp-internal-map
                           init-depend-tags)
  (define tag-map (map cons import-tags import-sigs))
  (define lookup-temp (λ (temp) (lookup-type temp export-temp-internal-map)))
  
  (values (for/list ([sig-id  (in-list import-sigs)]
                     [sig-internal-ids (in-list import-internal-ids)])
            (sig-info sig-id
                      (map car (Signature-mapping (lookup-signature sig-id)))
                      sig-internal-ids))
          (for/list ([sig (in-list export-sigs)]
                     [temp-ids (in-list export-temp-ids)])
            (sig-info sig
                      (map car (Signature-mapping (lookup-signature sig)))
                      (map lookup-temp temp-ids)))          
          (map (λ (x) (lookup-type x tag-map)) init-depend-tags)))

;; Needed to parse out signature names, and signature-tags from the unit syntax
;; the tags are used to lookup init-depend signatures
(define-syntax-class sig-vector
  #:literal-sets (kernel-literals)
  #:literals (vector-immutable cons)
  (pattern (#%plain-app 
            vector-immutable
            (#%plain-app cons 
                         (quote sig:id)
                         (#%plain-app vector-immutable sig-tag tag-rest ...))
            ...)
           #:with sigs #'(sig ...)
           #:with sig-tags #'(sig-tag ...)))

(define-syntax-class init-depend-list
  #:literal-sets (kernel-literals)
  #:literals (list cons)
  (pattern (#%plain-app list (#%plain-app cons _ sig-tag) ...)
           #:with init-depend-tags #'(sig-tag ...)))

(define-syntax-class export-table
  #:literal-sets (kernel-literals)
  #:literals (make-immutable-hash list cons vector-immutable check-not-unsafe-undefined unbox)
  (pattern (#%plain-app
            make-immutable-hash
            (#%plain-app
             list
             (#%plain-app
              cons
              signature-tag:id
              (#%plain-app
               vector-immutable
               (#%plain-lambda () 
                 (#%plain-app check-not-unsafe-undefined (#%plain-app unbox export-temp-id) external-id))
               ...))
             ...))
           #:attr export-temp-ids (map syntax->list (syntax->list #'((export-temp-id ...) ...)))))

(define-syntax-class unit-expansion
  #:literal-sets (kernel-literals)
  #:attributes (body-stx 
                import-internal-ids 
                import-sigs 
                import-sig-tags 
                export-sigs 
                export-temp-ids
                init-depend-tags)
  (pattern (#%plain-app
            make-unit:id
            name:expr 
            import-vector:sig-vector
            export-vector:sig-vector
            list-dep:init-depend-list
            (let-values (_ ...)
              (let-values (_ ...)
                (#%expression
                 (#%plain-lambda ()
                   (let-values (((export-temp-id:id) _) ...)
                     (#%plain-app
                      values
                      (#%plain-lambda (import-table:id)
                                      (let-values (((import:id ...) _) ...)
                                        unit-body:expr))
                      et:export-table
                      _ ...)))))))
           #:attr import-sigs (syntax->list #'import-vector.sigs)
           #:attr import-sig-tags (syntax->list #'import-vector.sig-tags)
           #:attr export-sigs (syntax->list #'export-vector.sigs)
           #:attr export-temp-ids (attribute et.export-temp-ids)
           #:attr init-depend-tags (syntax->list #'list-dep.init-depend-tags)
           #:attr import-internal-ids (map syntax->list (syntax->list #'((import ...) ...)))
           #:with body-stx #'unit-body))

(define-syntax-class export-temp-internal-map-elem
  #:literal-sets (kernel-literals)
  #:literals (set-box!)
  (pattern (#%plain-app set-box! temp-id:id internal-id:id)))

(define export-map-elem?
  (syntax-parser [e:export-temp-internal-map-elem #t]
                 [_ #f]))
(define extract-export-map-elem
  (syntax-parser [e:export-temp-internal-map-elem (cons #'e.temp-id #'e.internal-id)]))

;; Syntax class for the expansion of invoke-unit forms
(define-syntax-class invoke-unit-expansion
  #:literal-sets (kernel-literals)
  #:literals ()
  (pattern (#%plain-app invoke-unit/core:id unit-expr)
           #:attr units '()
           #:attr expr #'unit-expr
           #:attr imports '())
  (pattern
   (let-values ()
     body:invoke-unit-linkings)
   #:attr units (attribute body.units)
   #:attr expr (attribute body.expr)
   #:attr imports (attribute body.imports)))

(define-syntax-class invoke-unit-linkings
  #:literal-sets (kernel-literals)
  #:literals ()
  (pattern
   (let-values ([(u-temp:id)
                 (let-values ([(deps) _]
                              [(sig-provider) _] ...
                              [(temp) invoke-expr])
                   _ ...)])
     (#%plain-app invoke-unit/core:id (#%plain-app values _)))
   #:attr units '()
   #:attr expr #'invoke-expr
   #:attr imports '())
  (pattern
   (let-values ([(temp-id) u:unit-expansion])
     rest:invoke-unit-linkings)
   #:attr units (cons #'u (attribute rest.units))
   #:attr expr (attribute rest.expr)
   #:attr imports (append (attribute u.export-sigs) (attribute rest.imports))))


;; Compound Unit syntax classes
(define-syntax-class compound-unit-expansion
  #:literal-sets (kernel-literals)
  #:literals (vector-immutable cons)
  (pattern 
   (let-values ([(deps:id) _]
                [(local-unit-name) unit-expr] ...)
     (~seq (#%plain-app check-unit _ ...)
           (#%plain-app check-sigs _
                        (#%plain-app 
                         vector-immutable
                         (#%plain-app cons (quote import-sig:id) _) ...)
                        (#%plain-app
                         vector-immutable
                         (#%plain-app cons (quote export-sig:id) _) ...)
                        _)
           (let-values ([(fht) _]
                        [(rht) _])
             _ ...)) ...
     (#%plain-app
            make-unit:id
            name:expr 
            import-vector:sig-vector
            export-vector:sig-vector
            deps-ref
            internals))
   ;; Place holder attributes
   #:attr unit-exprs (syntax->list #'(unit-expr ...))
   #:attr unit-imports (map syntax->list (syntax->list #'((import-sig ...) ...)))
   #:attr unit-exports (map syntax->list (syntax->list #'((export-sig ...) ...)))
   ;; REMOVE THESE
   #:attr link-id-mapping '()
   #:attr import-link-ids '()
   #:attr export-link-ids '()
   #:attr compound-imports (syntax->list #'import-vector.sigs)
   #:attr compound-exports (syntax->list #'export-vector.sigs)
   #:with compound-unit #'5))

(define-syntax-class compound-unit-expr
  #:literal-sets (kernel-literals)
  #:literals (void)
  (pattern (#%expression
            (begin
              (#%plain-app void (quote-syntax export-sig:id) ...)
              (#%plain-app void (quote-syntax export-link:id) ...)
              (#%plain-app void (quote-syntax import-link:id) ...)
              unit-expr:expr))
           #:attr export-sigs (syntax->list #'(export-sig ...))
           #:attr export-links (syntax->list #'(export-link ...))
           #:attr import-links (syntax->list #'(import-link ...))
           #:with expr #'unit-expr))


;; infer-link
;; unit-id : the identifier corresponding to the unit being linked
;; export-links : the link ids being exported by the unit being linked
;; export-sigs : the identifiers corresponding to signatures exported by the unit
;; import-links : the identifiers of the links imported by the unit being linked
;; all-imports : all staticaly known imports of the unit being linked
;; all-exports : all statically known exports of the unit being linked
(struct infer-link (unit-id export-links export-sigs import-links all-imports all-exports) #:transparent)


(define (parse-infer-table-item stx)
  (syntax-parse stx
    #:literal-sets (kernel-literals)
    #:literals (void)
    [(#%expression
      (begin
        (#%plain-app void (quote-syntax sig-ex:id) ...)
        (#%plain-app void (quote-syntax link-ex:id) ...)
        (#%plain-app void (quote-syntax link-im:id) ...)
        (#%plain-app void (quote-syntax import-sig:id) ...)
        (#%plain-app void (quote-syntax export-sig:id) ...)
        (#%plain-app void (quote-syntax (#%plain-app values unit-runtime-id:id)))))
     (define type-of-id (lookup-type/lexical #'unit-runtime-id))
     (infer-link #'unit-runtime-id
                 (syntax->list #'(link-ex ...))
                 (syntax->list #'(sig-ex ...))
                 (syntax->list #'(link-im ...))
                 (syntax->list #'(import-sig ...))
                 (syntax->list #'(export-sig ...)))]))

;; process-infer-table : Infer-Table (Listof (Cons Id Id)) -> (Listof Syntax) (Listof (id . id))
;; Process a compound-unit/infer forms infer table to produce syntax expected
;; for typechecking a compound-unit, also update the link mapping
;;
;; We assume that the imports/exports to be inserted are uniquely determined
;; because otherwise the untyped macro should have failed at compile time
;;
;; Algorithm:
;; 1. Parse the representation of the infer-link
;; 2. Perform a first pass to insert exports and update the link mapping
;; 3. A second pass finishes by adding inferred imports looked up in the
;;    new link mapping
(define (process-infer-table infer-table init-link-map)
  ;; Pass 1: parse infer-table items into infer-link structs
  (define infer-links (map parse-infer-table-item infer-table))
  
  ;; Pass 2: Use static information associated with the unit-id
  ;; to fill out all the export information
  (define-values (infer-links/exports link-map/exports)
    (for/fold ([infer-links/exports null]
               [link-map/exports init-link-map])
              ([link infer-links])
      (match-define (infer-link unit-id export-links export-sigs import-links imports exports)
                    link)
      (define new-exports (filter-not 
                           (lambda (id) (member id export-sigs free-identifier=?))
                           exports))
      (define new-links (generate-temporaries new-exports))
      (define link-map-extension (map cons new-links new-exports))
      (values
       ;; create an extended infer-link
       (append infer-links/exports
               (list
                (infer-link unit-id 
                            (append new-links export-links) 
                            (append new-exports export-sigs)
                            import-links
                            imports
                            exports)))       
       ;; update the link-map
       (append link-map-extension link-map/exports))))
  
  ;; Pass 3: Use static information to fill in the import link-ids
  (define sig/link-map (map
                        (match-lambda 
                         [(cons k v) (cons v k)])
                        link-map/exports))
  (define infer-links/imports/exports
    (for/fold ([infer-links/imports/exports null])
              ([link infer-links/exports])
      (match-define (infer-link unit-id ex-links ex-sigs import-links import-sigs exports) link)
      (define new-links
        (filter-not
         (lambda (id) (member id import-links free-identifier=?))
         (map (lambda (id) (lookup-type id sig/link-map)) import-sigs)))
      
      (append infer-links/imports/exports
              (list (infer-link unit-id ex-links 
                                ex-sigs (append new-links import-links)
                                import-sigs exports)))))
  
  ;; Finally map over the list converting the structs into syntax expected for typechecking
  (define forms-to-check
    (map
    (match-lambda
     [(infer-link unit-id ex-links ex-sigs im-links _ _)
      (define (ids->row ids)
        #`(#%plain-app void 
                       #,@(map (lambda (id) #`(quote-syntax #,id)) ids)))
      #`(#%expression
         (begin
           #,(ids->row ex-sigs)
           #,(ids->row ex-links)
           #,(ids->row im-links)
           #,unit-id))])
    infer-links/imports/exports))
  (values forms-to-check
          link-map/exports))

(struct cu-expr-info (expr import-sigs import-links export-sigs export-links)
  #:transparent)
;; parse-compound-unit : Syntax -> (Values (Listof (Cons Symbol Id))
;;                                         (Listof Symbol)
;;                                         (Listof Signature)
;;                                         (Listof Signature)
;;                                         Infer-Table
;;                                         (Listof cu=expr-info))
;; Returns a mapping of link-ids to sig-ids, a list of imported sig ids
;; a list of exported link-ids
(define (parse-compound-unit stx)
  (define (list->sigs l) (map lookup-signature l))
  (syntax-parse stx
    [cu:compound-unit-expansion
     (define link-binding-info (tr:unit:compound-property stx))
     (match-define (list cu-import-syms unit-export-syms unit-import-syms)
       link-binding-info)
     (define compound-imports (attribute cu.compound-imports))
     (define compound-exports (attribute cu.compound-exports))
     (define unit-exprs (attribute cu.unit-exprs))
     (define unit-imports (attribute cu.unit-imports))
     (define unit-exports (attribute cu.unit-exports))
     ;; Map signature ids to link binding symbols
     (define mapping
       (let ()
         (define link-syms (append cu-import-syms (flatten unit-export-syms)))
         (define sig-ids (append compound-imports (flatten unit-exports)))
         (map cons link-syms (map lookup-signature sig-ids))))
     (define cu-exprs
       (for/list ([unit-expr (in-list unit-exprs)]
                  [import-sigs (in-list unit-imports)]
                  [import-links (in-list unit-import-syms)]
                  [export-sigs (in-list unit-exports)]
                  [export-links (in-list unit-export-syms)])
         (cu-expr-info unit-expr
                       (list->sigs import-sigs) import-links
                       (list->sigs export-sigs) export-links)))

     ;; NEED TO FIX compound-unit/infer issues
     (define infer-table #f
       #|
       (syntax-parse #'cu.infer-table
       #:literals (#%plain-app void)
       [(#%plain-app void) #f]
       [e #'e])
       |#)
     (values 
      mapping
      cu-import-syms
      (list->sigs compound-imports)
      (list->sigs compound-exports)
      infer-table
      cu-exprs)]))

;; parse-compound-unit-expr : Syntax -> (Values Syntax (Listof Id) (Listof Id))
;; Given a unit expression form from ompound unit
;; Returns an expression to typecheck, a list of imported link-ids
;; and a list of exported sig-ids
(define (parse-compound-unit-expr stx)
  (syntax-parse stx
    [cue:compound-unit-expr
     (values
      #'cue.expr
      (attribute cue.import-links)
      (attribute cue.export-links)
      (attribute cue.export-sigs))]))


;; Sig-Info -> (listof (pairof identifier? Type))
;; GIVEN: signature information
;; RETURNS: a mapping from internal names to types
(define (make-local-type-mapping si)
  (define sig (lookup-signature (sig-info-name si)))
  (define internal-names (sig-info-internals si))
  (define sig-types 
    (map cdr (Signature-mapping sig)))
  (map cons internal-names sig-types))

(define (arrowize-mapping mapping)
  (for/list ([(k v) (in-dict mapping)])
    (cons k (-> v))))

;; combine this and the above function later
(define (make-external-type-mapping si)
  (define sig (sig-info-name si))
  (define external-names (sig-info-externals si))
  (define sig-types 
    (map cdr (signature->bindings sig)))
  (map cons external-names sig-types))

(define (lookup-type name mapping)
  (let ([v (assoc name mapping free-identifier=?)])
    (and v (cdr v))))


;; Syntax Option<TCResults> -> TCResults
;; Type-check a unit form
(define (check-unit form [expected #f])
  (define expected-type
    (match expected
      [(tc-result1: type) (resolve type)]
      [_ #f]))
  (match expected-type
    [(? Unit? unit-type)
     (ret (parse-and-check form unit-type))]
    [_ (ret (parse-and-check form #f))]))

;; Syntax Option<TCResultss> -> TCResults

(define (check-invoke-unit form [expected #f])
  (define expected-type 
    (match expected
      ;; I think this is wrong, since invoke may return multiple values
      [(tc-result1: type) (resolve type)]
      [_ #f]))
  (define ret-val (ret (parse-and-check-invoke form expected-type)))
  ret-val)

;; Handle checking compound-unit and compound-unit/infer forms
;; the following invariant should hold
;; if the infer-table is #f then the form was compound-unit and
;; the list of forms-to-check will be non-empty
;; otherwise the expression was compound-unit/infer 
;; and the forms-to-check list will be empty but infer-table will
;; contain the relevant forms
;;
;; In either case a pass over both of these expressions
;; will produce the correct list of forms to typecheck
(define (check-compound-unit form [expected #f])
  (define expected-type
    (match expected
      [(tc-result1: type) (resolve type)]
      [_ #f]))
  (ret (parse-and-check-compound form expected-type)))

(define (check-unit-from-context form [expected #f])
  (define expected-type
    (match expected
      [(tc-result1: type) (resolve type)]
      [_ #f]))
  (ret (parse-and-check-unit-from-context form expected-type)))

(define (parse-and-check-unit-from-context form expected-type)
  (syntax-parse form
    #:literal-sets (kernel-literals)
    #:literals (void)
    [(#%expression
      (begin (#%plain-app void (quote-syntax sig-id:id)) unit))
     (define sig (lookup-signature #'sig-id))
     (define valid?
       (for/and ([(-id sig-type) (in-dict (Signature-mapping sig))])
         (define id (replace-context #'sig-id -id))
         (define lexical-type (lookup-type/lexical id))
         (if (subtype lexical-type sig-type)
             #t
             (begin (type-mismatch sig-type lexical-type) #f))))
     (if valid?
         (-unit null (list sig) null (-values (list -Void)))
         -Bottom)]))

(define (parse-and-check-compound form expected-type)
  (define-values (link-mapping
                  import-syms
                  import-sigs
                  export-sigs
                  infer-table
                  cu-exprs)
    (parse-compound-unit form))
  
  ;; Get forms to check, and extend the link mapping if bindings must be inferred
  ;; FIXME: compound-unit expansion no longer contains this, need to fix
  #|
  (define-values (forms-to-check link-mapping)
    (if infer-table
        (process-infer-table 
         (trawl-for-property infer-table tr:unit:compound:expr-property)
         init-link-mapping)
        (values
         (trawl-for-property compound-expr tr:unit:compound:expr-property)
         init-link-mapping)))
  |#
  
  (define (lookup-link-id id) (lookup-type id link-mapping))
  (define (lookup-sig-id id) 
    (lookup-type id (map (lambda (k/v) (cons (cdr k/v) (car k/v))) link-mapping)))
  
  (define-values (check _ init-depends)
    (for/fold ([check -Void]
               [seen-init-depends import-syms]
               [calculated-init-depends '()])
              ([form (in-list cu-exprs)])
      (match-define (cu-expr-info unit-expr-stx
                                  import-sigs
                                  import-links
                                  export-sigs
                                  export-links)
        form)
      (define unit-expected-type 
        (-unit import-sigs 
               export-sigs 
               (map lookup-signature
                    (map lookup-link-id (set-intersect seen-init-depends import-links)))
               ManyUniv))
      (define unit-expr-type (tc-expr/t unit-expr-stx))
      (check-below unit-expr-type unit-expected-type)
      (define-values (check new-init-depends)
        (match unit-expr-type
          [(Unit: _ _ ini-deps ty)
           ;; init-depends here are strictly subsets of the units imports
           ;; but these may not exactly match with the provided links
           ;; so all of the extended signatures mus be traversed to find the right
           ;; signatures for init-depends
           (define extended-imports
             (map cons import-links
                  (map (λ (l) (map Signature-name (flatten-sigs l))) import-sigs)))
           (define init-depend-links
             (for*/list ([sig-name (in-list (map Signature-name ini-deps))]
                         [(import-link import-family) (in-dict extended-imports)]
                         #:when (member sig-name import-family free-identifier=?))
               import-link))
           (values ty (set-intersect import-syms init-depend-links))]
          [_ (values #f (immutable-free-id-set))]))
      (values check 
              (set-union seen-init-depends export-links)
              (set-union calculated-init-depends new-init-depends))))
  (if check
      (-unit import-sigs
             export-sigs
             (map lookup-link-id init-depends)
             check)
      -Bottom))

;; syntax class for invoke-table
(define-syntax-class invoke-table
  #:literal-sets (kernel-literals)
  #:literals (void)
  (pattern (let-values ([()
                         (#%expression
                          (begin (#%plain-app void (quote-syntax sig-id:id) sig-var:id ...)
                                 (#%plain-app values)))]
                        ...)
             invoke-expr:expr)
           #:with sig-vars #'(sig-var ... ...)))

(define (parse-and-check-invoke form expected-type)
  (syntax-parse form 
    [iu:invoke-unit-expansion
     (define invoked-unit (attribute iu.expr))
     (define import-sigs (map lookup-signature (attribute iu.imports)))
     (define linking-units (attribute iu.units))
     (define unit-expr-type (tc-expr/t invoked-unit))
     (check-below unit-expr-type (-unit import-sigs null import-sigs ManyUniv))
     (for ([unit (in-list linking-units)]
           [sig (in-list import-sigs)])
       ;; TODO: error messages could be better by passing a message or
       ;; additional argument to parse-and-check
       (check-below (parse-and-check unit #f)
                    (-unit null (list sig) null ManyUniv)))
     (cond
       [(Unit? unit-expr-type)
        (define result-type (Unit-result unit-expr-type))
        (match result-type
          [(Values: (list (Result: t _ _) ...)) t]
          [(AnyValues: f) ManyUniv]
          ;; Should there be a ValuesDots case here?
         )]
       [else -Bottom])]))

;; Parse and check unit syntax
(define (parse-and-check form expected [insert-export-annotations? #f])
  (syntax-parse form
    [u:unit-expansion
     ;; extract the unit body syntax
     (define body-stx #'u.body-stx)
     (define import-sigs (attribute u.import-sigs))
     (define import-internal-ids (attribute u.import-internal-ids))
     (define import-tags (attribute u.import-sig-tags))
     (define export-sigs (attribute u.export-sigs))
     (define export-temp-ids (attribute u.export-temp-ids))
     (define init-depend-tags (attribute u.init-depend-tags))
     (define export-temp-internal-map
       (trawl-for-property body-stx export-map-elem? extract-export-map-elem))
     (define-values (imports-info exports-info init-depends)
       (parse-index-table import-sigs import-internal-ids import-tags
                          export-sigs export-temp-ids export-temp-internal-map
                          init-depend-tags))

     ;; Get Signatures to build Unit type
     (define import-signatures (map lookup-signature (map sig-info-name imports-info)))
     (define export-signatures (map lookup-signature (map sig-info-name exports-info)))
     (define init-depend-signatures (map lookup-signature init-depends))


     ;; TODO: CLEANUP this mess of stuff
     (define export-box-ids (apply append export-temp-ids))
     (define export-box-types
       (map -box (map cdr (apply append (map Signature-mapping export-signatures)))))
     (define export-box-type-map
       (map cons export-box-ids (apply append (map Signature-types-stx export-signatures))))

     (define body-rewrite
       (syntax-rewrite body-stx
         #:literals (set-box!)
         [(#%plain-app set-box! temp-id:id internal-id:id)
          (define ty-stx (lookup-type #'temp-id export-box-type-map))
          (define/with-syntax expr (type-inst-property #'#%expression ty-stx))
          (if ty-stx
              (syntax/loc body-stx (#%plain-app (expr set-box!) temp-id internal-id))
              (syntax/loc body-stx (#%plain-app set-box! temp-id internal-id)))]
         [uba:unit-body-annotation
          (attribute uba.fixed-form)]))

     (unless (valid-signatures? import-signatures)
       (tc-error/expr "unit expressions must import distinct signatures"))
     ;; this check for exports may be unnecessary
     ;; the unit macro seems to check it as well
     (unless (valid-signatures? export-signatures)
       (tc-error/expr "unit expresssions must export distinct signatures"))
     
     (define local-sig-type-map
       (apply append (map make-local-type-mapping imports-info)))
     ;; Need to pass on to tc/letrec to ensure variables defined with the correct types
     (define export-signature-type-map
       (map (lambda (si)
              (cons (sig-info-name si) (make-local-type-mapping si)))
            exports-info))


     ;; Thunk to pass to tc/letrec-values to check export subtyping
     (define (check-exports-thunk)
       (for* ([sig-mapping (in-list export-signature-type-map)]
              [sig (in-value (car sig-mapping))]
              [mapping (in-value (cdr sig-mapping))]
              [(id expected-type) (in-dict mapping)])
         (define id-lexical-type (lookup-type/lexical id))
         (unless (subtype id-lexical-type expected-type)
           (tc-error/fields "type mismatch in unit export"
                            "expected" expected-type
                            "given" id-lexical-type
                            "exported variable" (syntax-e id)
                            "exported signature" (syntax-e sig)
                            #:delayed? #t))))
     
     (define import-name-map
       (apply append (map
                      (lambda (si) (map cons (sig-info-externals si) (sig-info-internals si)))
                      imports-info)))
     (define export-name-map
       (apply append (map 
                      (lambda (si) (map cons (sig-info-externals si) (sig-info-internals si))) 
                      exports-info)))
     
     ;; extract unit body forms
     (define body-forms 
       (trawl-for-property body-stx tr:unit:body-exp-def-type-property))
     
     ;; get last expression in the body
     (define last-form 
       (or (and (not (empty? body-forms)) (last body-forms))))
     
     ;; get expression forms, if the body was empty or ended with
     ;; a definition insert a `(void)` expression to be typechecked
     (define expression-forms
       (let ([exprs 
              (filter
               (lambda (stx) (eq? (tr:unit:body-exp-def-type-property stx) 'expr))
               body-forms)])
         (cond
           [(not last-form) (append exprs (list #'(#%plain-app void)))]
           [(eq? (tr:unit:body-exp-def-type-property last-form) 'def/type)
            (append exprs (list #'(#%plain-app void)))]
           [else exprs])))
     
     ;; get the definitions/annotations in the body
     (define  annotation/definition-forms
       (filter
        (lambda (stx) (eq? (tr:unit:body-exp-def-type-property stx) 'def/type))
        body-forms))
     
     (define-values (ann/def-names ann/def-exprs unannotated-exports)
       (process-ann/def-for-letrec annotation/definition-forms 
                                   export-name-map
                                   import-name-map
                                   (if
                                    insert-export-annotations?
                                    (apply append (map make-local-type-mapping exports-info))
                                    #f)))

     ;; TODO: Export signature types should be introduced for typechecking
     ;;       the body of the unit if not already specified in the body
     ;;       This is more of a pragmatic feature than one required to typecheck
     ;;       but it would make porting programs somewhat simpler
     ;;       Currently adding these to the lexical scope doesn't seem to work, I think
     ;;       they need to be turned into real annotations that are inserted
     ;;       into the tc/letrec-values call
     
     (define signature-annotations (arrowize-mapping local-sig-type-map))
     (define unit-type
       (with-lexical-env/extend-types
         (append (map car signature-annotations) export-box-ids)
         (append (map cdr signature-annotations) export-box-types)
         (define res (tc-expr body-rewrite))
         #|
         (define res (tc/letrec-values ann/def-names
                                       ann/def-exprs
                                       #`(#,@expression-forms)
                                       #f
         check-exports-thunk))
         |#
     (define invoke-type
       (match res
         [(tc-results: tps) (-values tps)]))
     (-unit import-signatures
            export-signatures
            init-depend-signatures
            invoke-type)))
     unit-type]))

;; extended version of the function in check-class-unit.rkt
;; Syntax (Syntax -> Any) -> Listof<Syntax>
;; Look through the expansion of the unit macro in search for
;; syntax with some property (e.g., definition bodies and expressions)
(define (trawl-for-property form accessor [extractor values])
  (define (recur-on-all stx-list)
    (apply append (map (λ (stx) (trawl-for-property stx accessor extractor))
                       (syntax->list stx-list))))
  (syntax-parse form
    #:literal-sets (kernel-literals)
    [stx
     #:when (accessor #'stx)
     (list (extractor form))]
    [(let-values ([(x ...) rhs ...] ...) body ...)
     (recur-on-all #'(rhs ... ... body ...))]
    ;; for letrecs, traverse the RHSs too
    [(letrec-values ([(x ...) rhs ...] ...) body ...)
     (recur-on-all #'(rhs ... ... body ...))]
    [(letrec-syntaxes+values (sb ...) ([(x ...) rhs ...] ...) body ...)
     (recur-on-all #'(rhs ... ... body ...))]
    [(#%plain-app e ...)
     (recur-on-all #'(e ...))]
    [(#%plain-lambda (x ...) e ...)
     (recur-on-all #'(e ...))]
    [(begin e ...)
     (recur-on-all #'(e ...))]
    [(#%expression e)
     (recur-on-all (if (syntax->list #'e) #'e #'()))]
    [(() e)
     (recur-on-all #'(e))]
    [_ '()]))
