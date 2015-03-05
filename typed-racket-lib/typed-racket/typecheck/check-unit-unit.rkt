#lang racket/unit

;; This module provides a unit for type-checking units

(require "../utils/utils.rkt"
         racket/dict
         racket/format
         racket/list
         racket/match
         racket/set
         racket/syntax
         syntax/id-table
         syntax/parse
         syntax/stx
         racket/unit-exptime
         "signatures.rkt"
         (private parse-type syntax-properties type-annotation)
         (env lexical-env tvar-env global-env 
              signature-env signature-helper)
         (types utils abbrev union subtype resolve generalize)
         (typecheck check-below internal-forms)
         (utils tc-utils)
         (rep type-rep)
         (for-syntax racket/base racket/unit-exptime)
         (for-template racket/base
                       (private unit-literals)
                       (typecheck internal-forms)))

;;  REMOVE LATER
(require racket/format
         racket/pretty)

(import tc-if^ tc-lambda^ tc-app^ tc-let^ tc-expr^)
(export check-unit^)

;; Syntax class deifnitions
;; variable annotations expand slightly differently in the body of a unit
;; due to how the unit macro transforms internal definitions
(define-syntax-class unit-body-annotation
  #:literal-sets (kernel-literals)
  #:literals (void values :-internal cons)
  (pattern
   (#%expression
    (begin 
      (#%plain-app void)
      (begin
        (quote
         (:-internal var:id t))
        (#%plain-app values))))
   #:attr name #'var
   #:attr type (parse-type #'t)
   ;; Needed to substiture the internal renaming of exported definitions
   ;; in unit bodies in order to ensure that the annotation is applied
   ;; to the correct identifier
   #:attr letrec-form #`(begin
                          (quote-syntax
                           (:-internal var t))
                          (#%plain-app values))
   #:attr subst-annotation (lambda (id)
                             #`(begin
                                 (quote-syntax
                                  (:-internal #,id t))
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


(define (process-ann/def-for-letrec ann/defs export-mapping import-mapping)
  (define import-names (map car import-mapping))
  (for/fold ([names #`()]
             [exprs #`()])
            ([a/d (in-list ann/defs)])
    (syntax-parse a/d
      [a:unit-body-annotation
       (define name (attribute a.name))
       ;; TODO:
       ;; Duplicate annotations from imports
       ;; are not currently detected due to a bug
       ;; in tc/letrec-values
       #;
       (when (member name import-names free-identifier=?))
       (printf "ANN NAME: ~a\n" name)
       (printf "EXPORT MAPPING: ~a\n" export-mapping)
       (printf "mapped export ...: ~a\n"
               (map (lambda (id) (free-identifier=? name id))
                    (map car export-mapping)))
       (define form ((attribute a.subst-annotation) 
                     (or ;(lookup-type name export-mapping)
                      name
                         )))
       (values #`(#,@names ())
               ;; FIXME: ???
               #`(#,@exprs #,form))]
      [d:unit-body-definition
       (values #`(#,@names d.vars) #`(#,@exprs d.body))])))



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
   (#%plain-app list (quote-syntax sig-id:id) 
                (#%plain-app cons (quote-syntax var-ext:id)
                             (#%plain-lambda () var-int:unit-int-rep)) ...)
   
   #:with name #'sig-id
   #:attr info (sig-info #'sig-id 
                         (syntax->list #'(var-ext ...)) 
                         (syntax->list #'(var-int.id ...)))))

(define (get-info stx)
  (syntax-parse stx
    [ir:index-row
     (attribute ir.info)]))

(define-syntax-class signature-index-table
  #:literal-sets (kernel-literals)
  #:literals (void list cons values)
  (pattern
   (let-values ([() (#%expression
                     (begin (#%plain-app void import:index-row ...)
                            (#%plain-app values)))]
                [() (#%expression
                     (begin (#%plain-app void export:index-row ...)
                            (#%plain-app values)))]
                [() (#%expression
                     (begin (#%plain-app void (quote-syntax init-depend:id) ...)
                            (#%plain-app values)))])
     (#%plain-app void))
   #:attr imports (map get-info (syntax->list #'(import ...)))
   #:attr exports (map get-info (syntax->list #'(export ...)))
   #:attr init-depends (syntax->list #'(init-depend ...))))

(define (parse-index-table stx)
  (syntax-parse stx
    [t:signature-index-table
     (values (attribute t.imports)
             (attribute t.exports)
             (attribute t.init-depends))]))

(define-syntax-class unit-expansion
  #:literals (let-values letrec-syntaxes+values #%plain-app quote)
  #:attributes (;imports
                ;exports
                ;init-depends
                body-stx)
  (pattern (#%plain-app
            make-unit:id
            name:expr 
            import-vector:expr
            export-vector:expr
            list-dep:expr
            unit-body:expr)
           #:with body-stx #'unit-body))


;; Compound Unit syntax classes
(define-syntax-class compound-unit-expansion
  #:literals (#%expression #%plain-app void quote-syntax begin)
  (pattern (#%expression
            (begin
              (#%plain-app void (quote-syntax link-id) ...)
              (#%plain-app void (quote-syntax sig-id) ...)
              (#%plain-app void (quote-syntax import-link) ...)
              (#%plain-app void (quote-syntax export-link) ...)
              infer-table
              untyped-compound-unit-exp:expr))
           #:attr link-id-mapping (map cons 
                                    (syntax->list #'(link-id ...))
                                    (syntax->list #'(sig-id ...)))
           #:attr import-link-ids (syntax->list #'(import-link ...))
           #:attr export-link-ids (syntax->list #'(export-link ...))
           #:with compound-unit #'untyped-compound-unit-exp))

(define-syntax-class compound-unit-expr
  #:literals (#%expression #%plain-app void quote-syntax begin)
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

;; TODO: interp
(struct infer-link (unit-id export-links export-sigs import-links all-imports all-exports) #:transparent)


(define (parse-infer-table-item stx)
  (printf "\nPARSING infer item: ~a\n\n" stx)
  
  (syntax-parse stx
    #:literals (void quote-syntax #%plain-app begin #%expression #%plain-lambda)
    [(#%expression
      (begin
        (#%plain-app void (quote-syntax sig-ex:id) ...)
        (#%plain-app void (quote-syntax link-ex:id) ...)
        (#%plain-app void (quote-syntax link-im:id) ...)
        (#%plain-app void (quote-syntax import-sig:id) ...)
        (#%plain-app void (quote-syntax export-sig:id) ...)
        (#%plain-app void (quote-syntax (#%plain-app values unit-runtime-id:id)))))
     (define type-of-id (lookup-type/lexical #'unit-runtime-id))
     (printf "STATIC TYPE: ~a\n" type-of-id)
     (infer-link #'unit-runtime-id
                 (syntax->list #'(link-ex ...))
                 (syntax->list #'(sig-ex ...))
                 (syntax->list #'(link-im ...))
                 (syntax->list #'(import-sig ...))
                 (syntax->list #'(export-sig ...)))]
    ;; Debugging only
    [_ (printf "\nParse Failed: ~a\n\n" stx)]))

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
  
  (printf "\n\nPROCESSING-INFER-TABLE: ~a\n\n" infer-table)
  
  ;; Pass 1: parse infer-table items into infer-link structs
  (define infer-links (map parse-infer-table-item infer-table))
  
  (printf "\n\nINFER-LINK-STRUCTS: ~a\n\n" infer-links)
  
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
      (printf "In PASS1 of INFER-TABLE\n")
      (printf "EXPORTS: ~a\n" exports)
      (printf "NEW-EXPORTS: ~a\n" new-exports)
      (printf "ID: ~a\n" unit-id)
      (printf "link-map-extension: ~a\n" link-map-extension)
      
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
  (printf "PROCESSED-INFER-FORMS: ~a\n" forms-to-check)
  (printf "INFER-TABLE LINK-MAP: ~a\n" link-map/exports)
  (values forms-to-check
          link-map/exports))


;; parse-compound-unit : Syntax -> (Values (Listof (Cons Id Id))
;;                                         (Listof Id)
;;                                         (Listof Id)
;;                                         Syntax)
;; Returns a mapping of link-ids to sig-ids, a list of imported sig ids
;; a list of exported link-ids
(define (parse-compound-unit stx)
  (syntax-parse stx
    [cu:compound-unit-expansion
     (define mapping (attribute cu.link-id-mapping))
     (define link-ids (map car mapping))
     (define export-signatures 
       (map (lambda (id) 
              (if (member id link-ids free-identifier=?)
                  (lookup-type id mapping)
                  id)) 
            (attribute cu.export-link-ids)))
     (define infer-table
       (syntax-parse #'cu.infer-table
         #:literals (#%plain-app void)
         [(#%plain-app void) #f]
         [e #'e]))
     (values 
      mapping
      (attribute cu.import-link-ids)
      export-signatures
      infer-table
      #'cu.compound-unit)]))

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
  (printf "lt:name: ~a\n" name)
  (printf "lt:mapping: ~a\n" mapping)
  (let ([v (assoc name mapping free-identifier=?)])
    (printf "lt:v: ~a\n" v)
    (and v (cdr v))))


;; define-values/invoke-unit handling
(define (check-define-values/invoke-unit form [expected #f])
  (define expected-type
    (match expected
      [(tc-result1: type) (resolve type)]
      [_ #f]))
  (ret (parse-and-check-define-values/invoke-unit form expected-type)))

(define (parse-and-check-define-values/invoke-unit form expected)
  (printf "CHECKING define-values/invoke-unit\n")
  (define forms
    (trawl-for-property form tr:unit:def-val/inv-unit-expr-property))
  (printf "Forms: ~a\n" forms)
  -Void)


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
  #;
  (ret (parse-and-check-invoke form expected-type))
  (define ret-val (ret (parse-and-check-invoke form expected-type)))
  (printf "made it out of parse-and-check\n")
  (printf "ret: ~a\n" ret-val)
  ret-val
  )

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

(define (parse-and-check-compound form expected-type)
  (define-values (init-link-mapping compound-import-links compound-export-sigs 
                               infer-table compound-expr)
    (parse-compound-unit form))
  
  (printf "INFER-TABLE-IN-CHECK-COMPUND: ~a\n" infer-table)
  ;; Get forms to check, and extend the link mapping if bindings must be inferred
  (define-values (forms-to-check link-mapping)
    (if infer-table
        (process-infer-table 
         (trawl-for-property infer-table tr:unit:compound:expr-property)
         init-link-mapping)
        (values
         (trawl-for-property compound-expr tr:unit:compound:expr-property)
         init-link-mapping)))
  
  ;(printf "INFER-TABLE: ~a\n" infer-table)
  ;(printf "COMPOUND-IMPORT-LINKS: ~a\n" compound-import-links)
  (printf "FORMS-TO-CHECK: ~a\n" forms-to-check)
  
  (define (lookup-link-id id) (lookup-type id link-mapping))
  (define (lookup-sig-id id) 
    (lookup-type id (map (lambda (k/v) (cons (cdr k/v) (car k/v))) link-mapping)))
  
  (define (set-union lst1 lst2)
    (remove-duplicates (append lst1 lst2) free-identifier=?))
  (define (set-intersect lst1 lst2)
    (filter 
     (lambda (e) (member e lst2 free-identifier=?))
     lst1))
  
  (define import-signatures (map lookup-signature (map lookup-link-id compound-import-links)))
  (define export-signatures (map lookup-signature compound-export-sigs))
  
  
  
  (define-values (check _ init-depends)
    (for/fold ([check -Void]
               [seen-init-depends compound-import-links]
               [calculated-init-depends '()])
              ([form (in-list forms-to-check)])
      (define-values (unit-expr-stx import-link-ids export-link-ids export-sig-ids)
        (parse-compound-unit-expr form))
      
      (define import-sigs (map lookup-signature (map lookup-link-id import-link-ids)))
      (define export-sigs (map lookup-signature export-sig-ids))
            
      (define unit-expected-type 
        (-unit import-sigs 
               export-sigs 
               (map lookup-signature
                    (map lookup-link-id (set-intersect seen-init-depends import-link-ids))) 
               ManyUniv))
      (define unit-expr-type (tc-expr/t unit-expr-stx))
      (check-below unit-expr-type unit-expected-type)
      (define-values (check new-init-depends)
        (match unit-expr-type
          [(Unit: _ _ ini-deps ty) 
           (values ty (set-intersect (map Signature-name ini-deps) compound-import-links))]
          [_ (values #f null)]))
      (values check 
              (set-union seen-init-depends export-link-ids) 
              (set-union calculated-init-depends new-init-depends))))
  
  (printf "Compound forms to check: ~a\n" forms-to-check)
  (if check
      ;; is this true? Does a compound always have no init-depends?
      (-unit import-signatures export-signatures init-depends check)
      -Bottom))

;; syntax class for invoke-table
(define-syntax-class invoke-table
  #:literals (let-values void #%plain-app #%expression begin quote-syntax)
  (pattern (let-values ([()
                         (#%expression
                          (begin (#%plain-app void (quote-syntax sig-id:id) sig-var:id ...)
                                 (#%plain-app values)))]
                        ...)
             invoke-expr:expr)
           #:with sig-vars #'(sig-var ... ...)))

(define (parse-and-check-invoke form expected-type)
  (printf "syntax transforming: ~a\n" (syntax-transforming?))
  (print-signature-env)
  (printf "invoke form: ~a\n" form)
 
  (define-values (sig-ids unit-expr-stx)
    (syntax-parse form
      #:literal-sets (kernel-literals)
      #:literals (void values)
      [(#%expression 
        (begin
          (#%plain-app void (~optional (quote-syntax (#%plain-app values infer-id:id)) 
                                       #:defaults ([infer-id #f])))
          (#%plain-app void (quote-syntax sig-id:id) ...)
          expr))
       (printf "INFER: ~a\n" (attribute infer-id))
       (define unit-expr-stx
         (or (attribute infer-id)
             (first (trawl-for-property #'expr tr:unit:invoke:expr-property))))
       (values (syntax->list #'(sig-id ...)) unit-expr-stx)]))
  
  (printf "sigs: ~a\n" sig-ids)
  (printf "unit-expr-stx: ~a\n" unit-expr-stx)
  (define import-signatures (map lookup-signature sig-ids))
  (define imports-sig-stx (map cons import-signatures sig-ids))
  
  (define expected-unit-type
    ;; is null the correct value for the init-depend signatures???
    (-unit import-signatures null null ManyUniv))
  (define unit-expr-type
    (tc-expr/t unit-expr-stx))
  (printf "unit-expr-type: ~a\n" unit-expr-type)
  (printf "before check-below is ok?\n")
  (check-below unit-expr-type expected-unit-type)
  (printf "Just before cond is ok\n")
  (printf "imports-sig-mpas: ~a\n" (map Signature-mapping import-signatures))
  
  (cond 
    ;; not a unit then tc-error/expr
    [(Unit? unit-expr-type)
     (for* ([(sig stx) (in-dict imports-sig-stx)]
            ;; This is wrong need to flatten the mapping to get members from 
            ;; parent signatures as well
            [(-id sig-type) (in-dict (Signature-mapping sig))])
       (printf "inside for*\n")
       ;; FIXME: so that replacing this context is unnecessary
       ;(define id ((make-syntax-delta-introducer stx -id) -id))
       (define id (format-id stx "~a" -id))
       ;(define id (syntax-local-introduce (syntax-local-get-shadower -id)))
       (define lexical-type (lookup-type/lexical id))
       (printf "id: ~a\n lexical-type: ~a\n" id lexical-type)
       ;; type mismatch 
       (unless (subtype lexical-type sig-type)
         (type-mismatch sig-type lexical-type "TODO: message about signature")))
     (define result-type (Unit-result unit-expr-type))
     (match result-type
       [(Values: (list (Result: t _ _) ...))
        t]
       [(AnyValues: f) ManyUniv]
       ;; Should there be a ValuesDots case here?
       )]
    [else 
     (tc-error/expr #:stx unit-expr-stx
                    #:return -Bottom
                    "TODO: Didn't get a unit")]))


;; NEW 

(define (parse-and-check form expected)
  (print-signature-env)
  (syntax-parse form
    [u:unit-expansion
     (define body-stx #'u.body-stx)
     ;; handle signature table information
     (define unit-index-table 
       (first (trawl-for-property body-stx tr:unit:index-table-property)))
     (define-values (imports-info exports-info init-depends)
       (parse-index-table unit-index-table))
     
     ;; Get Signatures to build Unit type
     (define import-signatures (map lookup-signature (map sig-info-name imports-info)))
     (define export-signatures (map lookup-signature (map sig-info-name exports-info)))
     (define init-depend-signatures (map lookup-signature init-depends))
     
     (printf "import-signatures: ~a\nexport-signatures: ~a\ninit-depends-signatures: ~a\n"
             import-signatures
             export-signatures
             init-depend-signatures)
     
     
     (define local-sig-type-map
       (apply append (map make-local-type-mapping imports-info)))
     
     ;; Need to pass on to tc/letrec to ensure variables defined with the correct types
     (define export-signature-type-map
       (apply append (map make-local-type-mapping exports-info)))
     (printf "EXPORT TYPE MAPPING: ~a\n" export-signature-type-map)
     
     ;; Thunk to pass to tc/letrec-values to check export subtyping
     ;; Error messages can be improved
     (define (check-exports-thunk)
       (for ([(id expected-type) (in-dict export-signature-type-map)])
         (define id-lexical-type (lookup-type/lexical id))
         (unless (subtype id-lexical-type expected-type)
           (type-mismatch expected-type id-lexical-type
                          "TODO: error message about export signature"))))
     
     
     
     (define signature-annotations
       (arrowize-mapping local-sig-type-map))
     
     (printf "signature-annotations: ~a\n" signature-annotations)
     
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
     
     (define-values (ann/def-names ann/def-exprs)
       (process-ann/def-for-letrec annotation/definition-forms 
                                   export-name-map 
                                   import-name-map))

     (printf "ann/def-names: ~a\n" ann/def-names)
     (printf "ann/def-exprs: ~a\n" ann/def-exprs)
     (printf "body-forms: ~a\n" body-forms)
      
      
                                             
     ;; FIXME
      
     (printf "expression forms: ~a\n" expression-forms)
     (define unit-type
       (with-lexical-env/extend-types 
         (map car signature-annotations)
         (map cdr signature-annotations)
         (define res (tc/letrec-values ann/def-names 
                                       ann/def-exprs 
                                       #`(#,@expression-forms)
                                       #f
                                       check-exports-thunk))
         
         (printf "res: ~a\n" res)
          
          
          (printf "annotation/definition-forms: ~a\n" annotation/definition-forms)
          (define annotations (filter unit-type-annotation? annotation/definition-forms))
          (define definitions 
            (map process-unit-body-definition
                 (filter-not unit-type-annotation? annotation/definition-forms)))
          (printf "annotations: ~a\n" annotations)
          (printf "definitions: ~a\n" definitions)
          ;(define defined-vars (apply append (map car definitions)))
              
          
          ;; TODO:
          ;; 1. add types from `import` signatures to the environment
          ;; 2. process annotations/add to lexical environment
          ;; 3. infer types from definitions 
          ;; 4. type check definitions
          ;; 5. type check expressions
          ;; 6. determine `invoke` type
          ;; 7. correctly handle subtyping with exports
          
          (define invoke-type
            (match res
              [(tc-results: tps) (-values tps)]))
          
          
          (-unit import-signatures 
                     export-signatures
                     init-depend-signatures 
                     invoke-type
                     ;(-values (tc-results-ts res))
                     #;
                     (match res
                       [(tc-result1: t) t]))))
     (printf "UNIT FINAL TYPE: ~a\n" unit-type)
      unit-type]))

#;
(define (parse-and-check.Old form expected)
  (syntax-parse form
    [u:unit-expansion
     (define body-stx #'u.body-stx)
     (define unit-index-table 
       (first (trawl-for-property body-stx tr:unit:index-table-property)))
     (define-values (imports-info exports-info init-depends)
       (parse-index-table unit-index-table))
     (printf "imports-info: ~a\n" imports-info)
     (printf "exports-info: ~a\n" exports-info)
     (printf "init-depends: ~a\n" init-depends)
     (define local-sig-type-map
       (apply append (map make-local-type-mapping imports-info)))
     (define signature-annotations
       (arrowize-mapping local-sig-type-map))
     (printf "signature-annotations: ~a\n" signature-annotations)
     
     (define external-sig-type-map
       (apply append (map make-external-type-mapping imports-info)))
     
     (define export-internal-type-map
       (apply append (map make-local-type-mapping exports-info)))
     
     (define export-external-type-map
       (apply append (map make-external-type-mapping exports-info)))
     
     (printf "export-external anotations: ~a\n" export-external-type-map)
     
     (printf "export-annotations: ~a\n" export-internal-type-map)
     
     (printf "local-sig-type-map: ~a\n" local-sig-type-map)
     (define forms (trawl-for-property body-stx tr:unit:body-exp-def-type-property))
     (printf "forms: ~a\n" forms)
     
     (define annotations (filter unit-type-annotation? forms))
     (define forms-to-check (filter-not unit-type-annotation? forms))
     (printf "annotations: ~a\n" annotations)
     (define import-signature-names (apply append (map sig-info-externals imports-info)))
     (define export-signature-names (apply append (map sig-info-externals exports-info)))
     
     ;; map external export name to internal export names
     (define export-name-map
       (apply append (map 
                      (lambda (si) (map cons (sig-info-externals si) (sig-info-internals si))) 
                      exports-info)))
     
     (define annotation-map
       (for/fold ([mapping '()])
                 ([form (in-list annotations)])
         (syntax-parse form
           [ann:unit-body-annotation
            (define name (attribute ann.name))
            (define type (attribute ann.type))
            (printf "name: ~a\n" name)
            (printf "type: ~a\n" type)
            (cond
             
             [(member name export-signature-names free-identifier=?)
              =>
              (lambda (external-name-list)
                (define name (car external-name-list))
                ;; need to recover the export internal name
                ;; TODO: lookup-type is a bad name
                (cons (cons (lookup-type name export-name-map) type)
                      mapping))]
             [(or (member name (map car mapping) free-identifier=?)
                  (member name import-signature-names free-identifier=?)
                  ;; This check is wrong
                  ;; It should not be a type error for there to be an 
                  ;; annotation that is also present in an exported
                  ;; signature, but the name needs to be remapped to
                  ;; the correct name in order to give the correct
                  ;; annotation in the unit body
                  #;
                  (member name export-signature-names free-identifier=?))
              (printf "made it here\n")
              (tc-error/delayed #:stx name 
                                "Duplicate type annotation of ~a for ~a, previous was ~a"
                                type 
                                (syntax-e name) 
                                ;; FIXME: need to get the type from the mapping
                                ;; or from the signature depening on where the id
                                ;; came from
                                (or (lookup-type name mapping)
                                    (lookup-type name export-external-type-map)
                                    (lookup-type name external-sig-type-map)))
              mapping]
             [else (cons (cons name type) mapping)])])))
     
     (define all-annotations (append annotation-map signature-annotations))
     (printf "all annotations: ~a\n" all-annotations)
     (printf "Univ: ~a\n" Univ)
     (define body-type
       (with-lexical-env/extend-types 
           (map car all-annotations) (map cdr all-annotations)
           (for/last ([stx (in-list forms)])
             (define prop-val (tr:unit:body-exp-def-type-property stx))
             (cond
              [(equal? prop-val 'def/type)
               (cond 
                [(unit-type-annotation? stx) #f]
                [else
                 (define-values (vars body) (process-definition stx))
                 (define body-result (tc-expr body))
                 (define body-types (tc-results-ts body-result))
                 (printf "vars: ~a\n" vars)
                 
                 ;; --------
                 #|
                 (define x (first vars))
                 (printf "x: ~a\n" x)
                 (define x-ann (car (first all-annotations)))
                 (printf "x-ann: ~a\n" x-ann)
                 (printf " x =?= x-ann??: ~a\n"
                         (free-identifier=? x x-ann))
                 |#
                 ;; --------
                 
                 
                 (printf "body-types: ~a\n" (-values body-types))
                 
                 ;; map identifiers to types using local and exported signature bindings
                 (printf "vars: ~a\n" vars)
                 
                 (define var-types
                   (map (lambda (id) (or (lookup-type id all-annotations)
                                    #;(lookup-type id export-internal-type-map)
                                    Univ))
                        vars))
                 (printf "var-types: ~a\n" var-types)
                 ;(printf "(ret var-types) : ~a\n" (ret var-types))
                 
                 ;; check subtyping here ?
                 
                 #;
                 (check-below body-result 
                              (ret var-types))
                 
                 #f
                 ])
               ;; TODO: handle annotations/definitions
               #f]
              [else 
               (define results (tc-expr stx))
               (define types (tc-results-ts results))
               (define invoke-type (-values types))
               (printf "types: ~a\n" invoke-type)]))))
     
     
     (printf "parsing ok!\n")
     
     (void)
     ])
  (-unit null null null -Void)
  )

(define (unit-type-annotation? stx)
  (syntax-parse stx
    [s:unit-body-annotation #t]
    [_ #f]))

;; Syntax -> (values (listof identifier?) Syntax)
;; GIVEN: syntax representing a unit body definition
;; RETURNS: the variables defined by the definition
;;          and the syntax of the definition's body
(define (process-definition stx)
  (syntax-parse stx
    [d:unit-body-definition
     (values (attribute d.vars) #'d.body)]))

;; process-unit-body-definition :: Syntax -> (Pairof (Listof Identifier) Syntax)
;; GIVEN: the tagged syntax for a unit body definition
;; RETURNS: a list of pairs of the variables being defined
;;          and the syntax of the body expression
(define (process-unit-body-definition stx)
  (syntax-parse stx
    [d:unit-body-definition
     (cons (attribute d.vars) #'d.body)]))


;; Syntax Option<Type> -> Type
#|
(define (parse-and-check form expected)
  (syntax-parse form
    [u:unit-expansion
     (define body-stx #'u.body-stx)
     (define imports-stx (syntax->list #'u.imports))
     (define imports (map lookup-signature imports-stx))
     (define exports-stx (syntax->list #'u.exports))
     (define exports (map lookup-signature exports-stx))
     (define init-depends (map lookup-signature (syntax->list #'u.init-depends)))
     (define import-mapping (signatures->bindings imports-stx))
     (define export-mapping (signatures->bindings exports-stx))
          
     (define exprs+defns 
       (trawl-for-property body-stx tr:unit:body-expr-or-defn-property))
     
     (define defns (filter list?
                           (map tr:unit:body-expr-or-defn-property exprs+defns)))
     
     (printf "defns: ~a\n" defns)
     #;
     (define-values (bad-anns exprs+defns)
       (split-annotations exprs+annotations))
     
     (define local-table-stx
       (first (trawl-for-property body-stx tr:unit:local-table-property)))
     (define local-names-stxs
       (trawl-for-property body-stx (lambda (stx) (syntax-property stx 'sig-id))))
     (define local-name-mapping (parse-local-names local-names-stxs))
     
     (define anns
       (map tr:unit:annotation-property
            (trawl-for-property body-stx tr:unit:annotation-property)))
     
     (define body-annotations (if (empty? anns) empty (last anns)))
     
     (define b-type (car (first body-annotations)))
     (define b-def (first (first defns)))
     (printf "b-type: ~a\nb-def: ~a\n" b-type b-type)
     (printf "(free-identifier=? b-type b-def) => ~a\n" (free-identifier=? b-type b-def))
     
     
     
     
     (printf "anns: ~a\n" anns)
     
     ;; check that no annotation for unit variables are defined
     (define import-names (map (lambda (stx) (syntax-property stx 'sig-id)) local-names-stxs))
     (printf "local-names: ~a\n" import-names)
     ;; 
     
     (printf "body-annotations ~a\n" body-annotations)
     ;(define a-body (car (first body-annotations)))
     ;(define a-sig (first import-names))
     ;(printf "a-body: ~a\n" a-body)
     ;(printf "a-sig: ~a\n" a-sig)
     
     #;
     (for ([name import-names])
       (define ref (assoc name body-annotations free-identifier=?))
       (when ref
         (tc-error/delayed #:stx (car ref)
                           "Duplicate type annotation of ~a for ~a, previous was ~a"
                           (syntax-e (cdr ref))
                           (syntax-e (car ref))
                           'PLACEHOLDER)))
     
     
 
     (define-values (local-names local-types)
       (let ([local-dict (compose-mappings local-name-mapping import-mapping)])
         (for/fold ([names '()]
                    [types '()])
                   ([(k v) (in-dict local-dict)])
           (values (cons k names) (cons (-> (parse-type v)) types)))))
     
     (define body-type #f)
     #;
     (define body-type
       (with-lexical-env/extend-types 
           (append local-names (map car anns)) (append local-types (map cdr anns)) 
           (for/last ([stx (in-list (reverse exprs+defns))])
             (define prop-val (tr:unit:body-expr-or-defn-property stx))
             (define results (tc-expr stx))
             (define types (tc-results-ts results))
             
             (cond
              ;; syntax came from a definition need to check subtyping here
              ;; be careful about defs for exported sigs
              [(list? prop-val) 
               (cond [(empty? prop-val) -Void]
                     [else
                      (define var-types (map
                                         (lambda (id)
                                           (or (ref anns id)
                                               (let ([ty (ref export-mapping id)])
                                                 (or (and ty (parse-type ty)) Univ))))
                                         prop-val))
                      
                      
                      (printf "anns: ~a\n" anns)
                      
                      (printf "(bound-identifier=? (car prop-val) (car (car anns))): ~a\n"
                              (bound-identifier=? (car prop-val) (car (car anns)) #f))
                      #|
                      ;(printf "prop-val: ~a\n" prop-val)
                      ;(printf "anns: ~a\n" anns)
                      ;(printf "(car prop-val): ~a\n" (car prop-val))
                      ;(printf "(ref anns (car prop-val)): ~a\n" (ref anns (car prop-val)))
                      ;(printf "var-types: ~a\n" var-types)
                      (printf "Inspect Syntax prop-val\n")
                      (for ([id prop-val])
                        (inspect-syntax id))
                      (printf "Inspect Syntax anns\n")
                      (for ([(id type) (in-dict anns)])
                        (inspect-syntax id))
                      
                      
                      
                      (printf "anns c -> ~a\n" (identifier-binding-symbol (car (car anns))))
                      (printf "prop-val c -> ~a\n" (identifier-binding-symbol (car prop-val)))
                      (printf "werid=?: ~a\n" (weird=? (car prop-val) (car (car anns))))
                      (define ac (car (car anns)))
                      (define pvc (car prop-val))
                      (printf "id-bind ac ~a\n" (identifier-binding ac))
                      (printf "id-bind pvc ~a\n" (identifier-binding pvc))
                      |#
                      
                      
                      (check-below results (ret var-types))
                      -Void])]
              [else (first types)])
             
             )))
     (define unit-type (or body-type -Void))
     (make-Unit imports exports init-depends unit-type)
     ]))
|#

(define (ann->dict stxs)
  (for/list ([stx stxs])
    (syntax-parse stx
      [:unit-body-annotation
       (cons #'name (parse-type #'type))])))

(define (parse-local-names stxs)
  (for/list ([stx stxs])
    (syntax-parse stx
      #:literals (#%plain-app)
      [(#%plain-app name:id)
       (cons #'name (syntax-property stx 'sig-id))])))

;; (Listof Syntax) -> (Values (Listof (Pairof Identifier Type) (Listof Syntax))
;; GIVEN: a list of syntax representing definition expressions and
;;        annotation expressions found within a unit
;; WHERE: each element in the list of syntax has the 
;;        tr:unit:body-expr-or-defn syntax-property
;; RETURNS: two lists, the first contains all the annotations from 
;;          the unit body, and the second only the expressions
;;          the returned lists are in reverse order of their position
;;          from the unit body
#;
(define (split-annotations stxs)
  (for/fold ([anns '()]
             [exprs '()])
            ([stx (in-list stxs)])
    (define prop-val (tr:unit:body-expr-or-defn-property stx))
    (if (list? prop-val)
        (syntax-parse stx
          [e:unit-body-annotation
           (define ann (cons #'e.name (parse-type #'e.type)))
           (values (cons ann anns) exprs)]
          [_ 
           (values anns (cons stx exprs))])
        (values anns (cons stx exprs)))))


(define (ref dict id)
  (let ([val (assoc id dict free-identifier=?)])
    (if val (cdr val) #f)))

;; AList AList -> AList
;; GIVEN: two association lists
;; RETURNS: their composition
(define (compose-mappings m1 m2)
  (for/list ([kv (in-list m1)])
    (define key (car kv))
    (define val (cdr kv))
    (cons key
          ;; would be nice to make this an arrow type
          ;; and parse it here instead of above ...
          (cdr (assoc val m2 free-identifier=?)))))



;; copied from check-class-unit.rkt
;; Syntax (Syntax -> Any) -> Listof<Syntax>
;; Look through the expansion of the unit macro in search for
;; syntax with some property (e.g., definition bodies and expressions)
(define (trawl-for-property form accessor)
  (define (recur-on-all stx-list)
    (apply append (map (λ (stx) (trawl-for-property stx accessor))
                       (syntax->list stx-list))))
  (syntax-parse form
    #:literals (let-values letrec-values #%plain-app
                #%plain-lambda letrec-syntaxes+values
                #%expression begin)
    [stx
     #:when (accessor #'stx)
     (list form)]
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
     (recur-on-all #'e)]
    [(() e)
     (recur-on-all #'(e))]
    [_ '()]))



;;;;;;;;; REMOVE THIS LATER

(define (weird=? id1 id2)
  (equal?
   (identifier-binding-symbol id1)
   (identifier-binding-symbol id2)))



;; This module provides utility functions for examining syntax objects
(define rule (make-string 50 #\;))
(define (prule) (displayln rule))
(define (inspect-syntax stx)
  (define datum (syntax->datum stx))
  (define keys (syntax-property-symbol-keys stx))
  (prule)
  (displayln (~a ";; Inspecting syntax object: " (~a stx #:max-width 20)))
  (newline)
  (displayln "Pretty-printed syntax:")
  (pretty-print datum)
  (newline)
  (displayln (~a "Source: " (~a #:width 20 #:align 'right (syntax-source stx))))
  (displayln (~a "Line: " (~a #:width 22 #:align 'right (syntax-line stx))))
  (displayln (~a "Column: " (~a #:width 20 #:align 'right (syntax-column stx))))
  (displayln (~a "Position: " (~a #:width 18 #:align 'right (syntax-position stx))))
  (displayln (~a "Span: " (~a #:width 22 #:align 'right (syntax-span stx))))
  (newline)
  (displayln "Properties:")
  (for ([key (in-list keys)])
    (displayln (~a " " key ": " (syntax-property stx key))))
  (newline)
  (newline)
  (displayln (~a "Tainted: " (~a #:width 19 #:align 'right (syntax-tainted? stx))))
  (newline)
  (prule))
