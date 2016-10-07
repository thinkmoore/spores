#lang racket/base

(require (for-syntax racket/base
                     racket/list
                     racket/match
                     racket/stxparam
                     syntax/parse
                     syntax/kerncase
                     syntax/id-table
                     racket/stxparam)
         racket/stxparam
         racket/contract
         racket/list
         racket/unsafe/ops
         syntax/parse)

(provide spore define-spore spore?
         (contract-out [spore/c (->i ([static-contract contract?]
                                      [get-contract    contract?]
                                      [put-contract    contract?])
                                     (#:opaque-ok? [opaque-ok boolean?])
                                     [result contract?])]))

(define-syntax-parameter current-spore #f)

(define-for-syntax (do-expand-closed stx)
  (syntax-case stx ()
    [(expand-closed stx)
     (let ([expanded (local-expand #'stx (syntax-local-context) (list #'define-values #'ok-id #'ok-id-mut #'ok-id-mut-ext #'ok-set! #'spore))])
       (closed expanded))]))

(define-syntax (expand-closed stx)
  (do-expand-closed stx))

(define-for-syntax (make-mut-transformer current id)
  #`(lambda (stx)
      (syntax-case stx ()
        [(ref rest (... ...)) #'((ok-id-mut #,current ref #,id) rest (... ...))]
        [ref #'(ok-id-mut #,current ref #,id)])))

(define-for-syntax (make-nonmut-transformer current id)
  #`(lambda (stx)
      (syntax-case stx ()
        [(ref rest (... ...)) #'((ok-id #,current ref #,id) rest (... ...))]
        [ref #'(ok-id #,current ref #,id)])))

(define-for-syntax (make-nonmut-ctc-transformer current id)
  #`(lambda (stx)
      (syntax-case stx ()
        [(ref rest (... ...))  #'((ok-id-ctc #,current ref #,id) rest (... ...))]
        [ref #'(ok-id-ctc #,current ref #,id)])))

(define-for-syntax (make-ext-mut-transformer current get put)
  #`(lambda (stx)
      (syntax-case stx ()
        [(ref rest (... ...)) #'((ok-id-mut-ext #,current ref #,get #,put) rest (... ...))]
        [ref #'(ok-id-mut-ext #,current ref #,get #,put)])))

(define-for-syntax (closed stx)
  (define code-insp 
    (variable-reference->module-declaration-inspector (#%variable-reference)))
  (kernel-syntax-case* (syntax-disarm stx code-insp) #f (spore ok-id ok-id-ctc ok-id-mut ok-id-mut-ext)
                       [(define-values (id ...) expr)
                        (quasisyntax/loc stx
                          (define-values (id ...)
                            (let-syntax (#,@(map (lambda (id) #`(#,id #,(make-mut-transformer (syntax-parameter-value #'current-spore) id)))
                                                 (syntax->list #'(id ...))))
                              (expand-closed expr))))]
                       [(define-syntaxes (id ...) expr)
                        (quasisyntax/loc stx
                          (define-syntaxes (id ...)
                            (expand-closed expr)))]
                       [(let-values ([(id ...) expr] ...) body0 body ...)
                        (quasisyntax/loc stx
                          (let-values
                              (#,@(map (λ (stx)
                                         (syntax-case stx ()
                                           [[(id ...) expr] #`[(id ...) (expand-closed expr)]]))
                                       (syntax->list #'([(id ...) expr] ...))))
                            #,@(cons #`(let-syntax (#,@(map (lambda (id) #`(#,id #,(make-mut-transformer (syntax-parameter-value #'current-spore) id)))
                                                            (syntax->list #'(id ... ...))))
                                         (expand-closed body0))
                                     (map (λ (e) #`(let-syntax (#,@(map (lambda (id) #`(#,id #,(make-mut-transformer (syntax-parameter-value #'current-spore) id)))
                                                                        (syntax->list #'(id ... ...))))
                                                     (expand-closed #,e)))
                                          (syntax->list  #'(body ...))))))]
                       [(#%plain-lambda (id ...) body0 body ...)
                        (quasisyntax/loc stx
                          (#%plain-lambda
                           (id ...)
                           #,@(cons #`(let-syntax (#,@(map (lambda (id) #`(#,id #,(make-mut-transformer (syntax-parameter-value #'current-spore) id)))
                                                           (syntax->list #'(id ...))))
                                        (expand-closed body0))
                                    (map (λ (e) #`(let-syntax (#,@(map (lambda (id) #`(#,id #,(make-mut-transformer (syntax-parameter-value #'current-spore) id)))
                                                                       (syntax->list #'(id ...))))
                                                    (expand-closed #,e)))
                                         (syntax->list  #'(body ...))))))]
                       [(if expr0 expr1 expr2)
                        (quasisyntax/loc stx
                          (if (expand-closed #'expr0)
                              (expand-closed #'expr1 sc)
                              (expand-closed #'expr2 sc)))]
                       [(begin expr0 expr ...)
                        (quasisyntax/loc stx
                          (begin (expand-closed expr0)
                                 #,@(map (λ (e) #'(expand-closed e)) (syntax->list #'(expr ...)))))]
                       [(begin0 expr0 expr ...)
                        (quasisyntax/loc stx
                          (begin0 (expand-closed expr0)
                                  #,@(map (λ (e) #'(expand-closed e)) (syntax->list #'(expr ...)))))]
                       [(case-lambda (formals expr0 expr ...) ...)
                        (quasisyntax/loc stx 
                          (case-lambda
                            #,@(map (λ (stx)
                                      (syntax-case stx ()
                                        [(formals expr0 expr ...)
                                         #`(formals
                                            (let-syntax (#,@(map (lambda (id) #`(#,id #,(make-mut-transformer (syntax-parameter-value #'current-spore) id)))
                                                                 (syntax->list #'formals)))
                                              (expand-closed expr0))
                                            #,@(map (λ (e)
                                                      #`(let-syntax (#,@(map (lambda (id) #`(#,id #,(make-mut-transformer (syntax-parameter-value #'current-spore) id)))
                                                                             (syntax->list #'formals)))
                                                          (expand-closed e)))
                                                    (syntax->list #'(expr ...))))]))
                                    (syntax->list #'((formals expr0 expr ...) ...)))))]
                       [(letrec-values ([(id ...) expr] ...) body0 body ...)
                        (quasisyntax/loc stx 
                          (letrec-values
                              #,@(map (λ (stx)
                                        (syntax-case stx ()
                                          [[(idinner ...) exprinner]
                                           #`[(idinner ...) (let-syntax (#,@(map (lambda (id) #`(#,id #,(make-mut-transformer (syntax-parameter-value #'current-spore) id)))
                                                                                 (syntax->list #'(id ... ...))))
                                                              (expand-closed exprinner))]]))
                                      (syntax->list #'([(id ...) expr] ...)))
                            #,@(cons #`(let-syntax (#,@(map (lambda (id) #`(#,id #,(make-mut-transformer (syntax-parameter-value #'current-spore) id)))
                                                            (syntax->list #'(id ... ...))))
                                         (expand-closed body0))
                                     (map (λ (e) #`(let-syntax (#,@(map (lambda (id) #`(#,id #,(make-mut-transformer (syntax-parameter-value #'current-spore) id)))
                                                                        (syntax->list #'(id ... ...))))
                                                     (expand-closed #,e)))
                                          (syntax->list  #'(body ...))))))]
                       [(set! id expr) (quasisyntax/loc stx (ok-set! (expand-closed id) (expand-closed expr)))]
                       [(quote datum)
                        (syntax/loc stx (quote datum))]
                       [(quote-syntax datum)
                        (syntax/loc stx (quote-syntax datum))]
                       [(with-continuation-mark expr0 expr1 expr2)
                        (quasisyntax/loc stx
                          (with-continuation-mark
                              (expand-closed expr0)
                            (expand-closed expr1)
                            (expand-closed expr2)))]
                       [(#%plain-app expr0 expr ...)
                        (quasisyntax/loc stx
                          (#%plain-app (expand-closed expr0)
                                       #,@(map (λ (e) #`(expand-closed #,e)) (syntax->list #'(expr ...)))))]
                       [(#%top . (ok-id id)) (quasisyntax/loc stx (#%top . id))]
                       [(#%top . (ok-id-mut id)) (quasisyntax/loc stx (#%top . id))]
                       [(#%top . id) (raise-syntax-error #f "1 spore closes over undeclared binding" #'id)]
                       [(#%expression expr)
                        (quasisyntax/loc stx
                          (#%expression (expand-closed expr)))]
                       [(#%variable-reference id)
                        (raise-syntax-error #f "Unexpected form" stx)]
                       [(#%variable-reference (#%top . id))
                        (raise-syntax-error #f "Unexpected form" stx)]
                       [(#%variable-reference)
                        (raise-syntax-error #f "Unexpected form" stx)]
                       [(spore decls vars results body0 body ...)
                        (quasisyntax/loc stx
                            (spore (#,@(map (lambda (decl)
                                              (syntax-case decl ()
                                                [(id expr #:mutable)
                                                 #'(id (expand-closed expr) #:mutable)]
                                                [(id expr)
                                                 #'(id (expand-closed expr))]))
                                            (syntax->list #'decls)))
                                   (#,@(map (lambda (vardecl)
                                              (syntax-case vardecl ()
                                                [(id expr)
                                                 #'(id (expand-closed expr))]))
                                            (syntax->list #'vars)))
                                   (#,@(map (lambda (result)
                                              (syntax-case result ()
                                                [result #'(expand-closed result)]))
                                            (syntax->list #'results)))
                                   body0 body ...))]
                       [(ok-id current err id)
                        (quasisyntax/loc stx (ok-id current err id))]
                       [(ok-id-ctc current err id)
                        (quasisyntax/loc stx (ok-id current err id))]
                       [(ok-id-mut current err id)
                        (quasisyntax/loc stx (ok-id-mut current err id))]
                       [(ok-id-mut-ext current err get put)
                        (quasisyntax/loc stx (ok-id-mut-ext current err get put))]
                       [id (identifier? #'id)
                           (raise-syntax-error #f "2 spore closes over undeclared binding" #'id)]
                       [other (raise-syntax-error #f "Unexpected form" stx)]))

(define-syntax (ok-id stx)
  (syntax-parse stx
    [(ok-id current err:id i:id)
     (if (eq? (syntax->datum #'current) (syntax-parameter-value #'current-spore))
         #'i
         (raise-syntax-error #f "3 spore closes over undeclared binding" #'err))]))

(define-syntax (ok-id-ctc stx)
  (syntax-parse stx
    [(ok-id-ctc current err:id i:id)
     (if (eq? (syntax->datum #'current) (syntax-parameter-value #'current-spore))
         #'((ok-id current err i))
         (raise-syntax-error #f "4 spore closes over undeclared binding" #'err))]))

(define-syntax (ok-id-mut stx)
  (syntax-parse stx
    [(ok-id-mut current err:id i:id)
     (if (eq? (syntax->datum #'current) (syntax-parameter-value #'current-spore))
         #'i
         (raise-syntax-error #f "5 spore closes over undeclared binding" #'err))]))

(define-syntax (ok-id-mut-ext stx)
  (syntax-parse stx
    [(ok-id-mut-ext current err:id get:id put:id)
     (if (eq? (syntax->datum #'current) (syntax-parameter-value #'current-spore))
         #'((ok-id current err get))
         (raise-syntax-error #f "6 spore closes over undeclared binding" #'err))]))

(define-syntax (ok-set! stx)
  (syntax-parse stx
    [(ok-set! idspec vspec)
     (with-syntax ([id (do-expand-closed #'idspec)]
                   [v  (do-expand-closed #'vspec)])
       (syntax-case #'id (ok-id ok-id-mut)
         [(ok-id-mut current err id)
          (if (eq? (syntax->datum #'current) (syntax-parameter-value #'current-spore))
              #'(set! id v)
              (raise-syntax-error #f "7 spore closes over undeclared binding" #'id))]
         [(ok-id-mut-ext current err get put)
          (if (eq? (syntax->datum #'current) (syntax-parameter-value #'current-spore))
              #'(put v)
              (raise-syntax-error #f "8 spore closes over undeclared binding" #'id))]
         [(ok-id current err id) (raise-syntax-error #f "spore mutates undeclared mutable binding" #'err)]))]))

(begin-for-syntax 
  (define-syntax-class spore-declaration
    (pattern (name:id contract:expr (~optional #:mutable) (~optional #:opaque)))))

(define-for-syntax (mutable? decl)
  (syntax-case decl ()
    [(cv cc #:mutable) #t]
    [(cv cc #:mutable #:opaque) #t]
    [_ #f]))

(define-for-syntax (opaque? decl)
  (syntax-case decl ()
    [(cv cc #:mutable #:opaque) #t]
    [(cv cc #:opaque) #t]
    [_ #f]))

(define-for-syntax (decl-name decl)
  (syntax-parse decl
    [sd:spore-declaration #'sd.name]))

(define-for-syntax (decl-ctc decl)
  (syntax-parse decl
    [sd:spore-declaration #'sd.contract]))

(define-syntax (spore stx)
  (syntax-parse stx
    [(_ (cv:spore-declaration ...)
        ([v:id c:expr] ...)
        (rc:expr ...)
        body:expr ...+)
       (with-syntax ([(static ...)        (filter (lambda (decl) (and (not (mutable? decl)) (not (opaque? decl)))) (syntax->list #'(cv ...)))]
                     [(mut ...)           (filter (lambda (decl) (and (mutable? decl)       (not (opaque? decl)))) (syntax->list #'(cv ...)))]
                     [(static-opaque ...) (filter (lambda (decl) (and (not (mutable? decl)) (opaque? decl)))       (syntax->list #'(cv ...)))]
                     [(mut-opaque ...)    (filter (lambda (decl) (and (mutable? decl)       (opaque? decl)))       (syntax->list #'(cv ...)))])
         (with-syntax ([(cvc-in ...) (generate-temporaries #'(static ...))]
                       [(cvc-get ...) (generate-temporaries #'(static ...))]
                       [(cvc-opaque ...) (generate-temporaries #'(static-opaque ...))]
                       [(get ...) (generate-temporaries #'(mut ...))]
                       [(put ...) (generate-temporaries #'(mut ...))]
                       [(get-opaque ...) (generate-temporaries #'(mut-opaque ...))]
                       [(put-opaque ...) (generate-temporaries #'(mut-opaque ...))]
                       [current (datum->syntax stx (gensym 'spore))])
           #`(let (#,@(map (lambda (temp decl) #`[#,temp (contract #,(decl-ctc decl) #,(decl-name decl) current-contract-region 'spore)])
                             (syntax->list #'(cvc-opaque ... cvc-in ...))
                             (syntax->list #'(static-opaque ... static ...)))
                   #,@(flatten (map (lambda (get put decl)
                                      (list #`[#,get (lambda () (contract #,(decl-ctc decl) #,(decl-name decl) current-contract-region 'spore))]
                                            #`[#,put (lambda (val) (set! #,(decl-name decl) (contract #,(decl-ctc decl) val 'spore current-contract-region)))]))
                                    (syntax->list #'(get-opaque ...))
                                    (syntax->list #'(put-opaque ...))
                                    (syntax->list #'(mut-opaque ...)))))
               (let-syntax (#,@(map (lambda (decl repid) #`(#,(decl-name decl) #,(make-nonmut-transformer #'current repid)))
                                    (syntax->list #'(static-opaque ...))
                                    (syntax->list #'(cvc-opaque ...)))
                            #,@(map (lambda (mut-decl get put) #`(#,(decl-name mut-decl) #,(make-ext-mut-transformer #'current get put)))
                                    (syntax->list #'(mut-opaque ...))
                                    (syntax->list #'(get-opaque ...))
                                    (syntax->list #'(put-opaque ...))))
                 (spore-proc (contract (-> (listof contract?) (listof contract?) (listof contract?) c ... (values rc ...))
                                       (lambda (static-ctcs get-ctcs put-ctcs v ...)
                                         (let (#,@(flatten
                                                   (map (lambda (get put decl)
                                                          (list #`[#,get (lambda ()
                                                                           (for/fold ([value #,(decl-name decl)])
                                                                                     ([ctc (cons #,(decl-ctc decl) get-ctcs)])
                                                                             (contract ctc value current-contract-region 'spore)))]
                                                                #`[#,put (lambda (val)
                                                                           (set! #,(decl-name decl)
                                                                                 (for/fold ([value val])
                                                                                           ([ctc (cons #,(decl-ctc decl) put-ctcs)])
                                                                                   (contract ctc value 'spore current-contract-region))))]))
                                                        (syntax->list #'(get ...))
                                                        (syntax->list #'(put ...))
                                                        (syntax->list #'(mut ...))))
                                               #,@(map (lambda (get in)
                                                         #`[#,get (lambda ()
                                                                    (for/fold ([value #,in])
                                                                              ([ctc static-ctcs])
                                                                      (contract ctc value current-contract-region 'spore)))])
                                                       (syntax->list #'(cvc-get ...))
                                                       (syntax->list #'(cvc-in ...))))
                                           #,@(map (lambda (body)
                                                     #`(let-syntax (#,@(map (lambda (arg) #`(#,arg #,(make-mut-transformer #'current arg)))
                                                                            (syntax->list #'(v ...)))
                                                                    #,@(map (lambda (decl get) #`(#,(decl-name decl) #,(make-nonmut-ctc-transformer #'current get)))
                                                                            (syntax->list #'(static ...))
                                                                            (syntax->list #'(cvc-get ...)))
                                                                    #,@(map (lambda (decl get put) #`(#,(decl-name decl) #,(make-ext-mut-transformer #'current get put)))
                                                                            (syntax->list #'(mut ...))
                                                                            (syntax->list #'(get ...))
                                                                            (syntax->list #'(put ...))))
                                                         (syntax-parameterize ([current-spore (syntax->datum #'current)])
                                                           (expand-closed #,body))))
                                                   (syntax->list #'(body ...)))))
                                       'spore current-contract-region)
                             (list cvc-in ...)
                             #,(if (and (empty? (syntax->list #'(static-opaque ...)))
                                        (empty? (syntax->list #'(mut-opaque ...))))
                                   #'#f
                                   #'#t))))))]))

(define-syntax (define-spore stx)
  (syntax-parse stx
    [(_ name:id
        (cv:spore-declaration ...)
        ([v:id c:expr] ...)
        (rc:expr ...)
        body:expr ...+)
     #'(define name (spore (cv ...) ([v c] ...) (rc ...) body ...))]))

(define-values (prop:spore spore? prop:spore-accessor) (make-impersonator-property 'prop:spore))
(define-values (prop:opaque prop:opaque-check prop:opaque-accessor) (make-impersonator-property 'prop:opaque))
(define-values (prop:static-contracts prop:static-contracts-check prop:static-contracts-accessor) (make-impersonator-property 'prop:static-contracts))
(define-values (prop:get-contracts prop:get-contracts-check prop:get-contracts-accessor) (make-impersonator-property 'prop:get-contracts))
(define-values (prop:put-contracts prop:put-contracts-check prop:put-contracts-accessor) (make-impersonator-property 'prop:put-contracts))
(define-values (prop:statics prop:statics-check prop:statics-accessor) (make-impersonator-property 'prop:statics))

(define (spore-proc procedure statics opaque)
  (impersonate-procedure
   (lambda args
     (apply procedure empty empty empty args))
   #f
   prop:spore procedure
   prop:opaque opaque
   prop:statics statics
   prop:static-contracts empty
   prop:get-contracts empty
   prop:put-contracts empty))

(define (spore/c #:opaque-ok? [opaque #t] static-contract get-contract put-contract)
  (make-contract
   #:name (format "(spore/c #:opaque ~a ~a ~a ~a)"
                  opaque
                  (contract-name static-contract)
                  (contract-name get-contract)
                  (contract-name put-contract))
   #:first-order (lambda (v) (spore? v))
   #:late-neg-projection
   (lambda (partial-blame)
     (lambda (value negative)
       (let ([blame (blame-replace-negative partial-blame negative)])
         (cond
           [(not (spore? value))
            (raise-blame-error blame value (list 'given: "~a" 'expected: "~a") value 'spore)]
           [(and (not opaque) (prop:opaque-accessor value))
            (raise-blame-error blame value (list 'given: "~a" 'expected: "~a") value "a non-opaque spore")]
           [(not (andmap (contract-first-order static-contract) (prop:statics-accessor value)))
            (raise-blame-error blame value (list 'given: "~a" 'expected: "spore with static imports satisfying ~a")
                               value (contract-name static-contract))]
           [else
            (let ([static-contracts (cons static-contract (prop:static-contracts-accessor value))]
                  [get-contracts    (cons get-contract (prop:get-contracts-accessor value))]
                  [put-contracts    (cons put-contract (prop:put-contracts-accessor value))]
                  [procedure        (prop:spore-accessor value)])
              (unsafe-impersonate-procedure
               value
               (lambda args
                 (apply procedure static-contracts get-contracts put-contracts args))
               prop:static-contracts static-contracts
               prop:get-contracts get-contracts
               prop:put-contracts put-contracts))]))))))