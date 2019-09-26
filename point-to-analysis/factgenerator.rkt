;; Yihao Sun  (ysun67@syr.edu)
;; Syracsue 2019

;; this is a mini compiler will trun a lite java(js) based toy lang
;; into an predicate facts, to simplify this, I will assume I already
;; get the declarative s-expr IR of this lite lang(actually for here
;; just some racket list).

#lang racket

;; Token
;; here all identifier are racket symbol
;; "." in toy lang will be tokenized to DOT
;; ";" and "," will be discard
;; in racket's pattern match {} and () will be treated as same

;; Grammar
;; instruction
;; the type is erased, using a "var" instead
(define (instr? e)
  ;; (displayln e)
  (match e
    ;; *alloc*:  var x = new clazz();
    [`(var ,(? symbol?) = new ,(? symbol?)()) #t]
    ;; *assign*:  a = b;
    [`(,(? symbol?) = ,(? symbol?)) #t]
    ;; *load*  a = b.f;
    [`(,(? symbol?) = ,(? symbol?) DOT ,(? symbol?)) #t]
    ;; *store*  a.f = b;
    [`(,(? symbol?) DOT ,(? symbol?) = ,(? symbol?)) #t]
    ;; *vcall* with return    a = b.m(args);
    [`(,(? symbol?) = ,(? symbol?) DOT ,(? symbol?)(,(? symbol?) ...)) #t]
    ;; *vcall* without return    b.m(args);
    [`(,(? symbol?) DOT ,(? symbol?)(,(? symbol?) ...)) #t]
    ;; *this call* without return f(args);
    [`(,(? symbol?)(,(? symbol?) ...)) #t]
    ;; *this call* with return a = f(args)
    [`((? symbol?) = ,(? symbol?)(,(? symbol?) ...)) #t]
    [(? symbol?) #t]
    [else #f]))

;; return must be a value or nothing
(define (return? e)
  ;; (displayln e)
  (match e
    [`(return ,(? symbol? var)) #t]
    [`(return) #t]
    [else #f]))

;; function definition
;; here, I ignore the type infomation just using keyword "fun"
(define (fun? e)
  ;;(displayln e)
  (match e
    [`(fun ,(? symbol?) (,(? symbol?) ...) (,(? instr?)... ,(? return?))) #t]
    [`(fun ,(? symbol?) (,(? symbol?) ...) (,(? instr?)... )) #t]
    [else #f]))


;; member definition
(define (member? e)
  ;; (displayln e)
  (match e
    [`(var ,(? symbol?)) #t]
    [else #f]))

;; class definition
;; in class, var can't be initialized as soon as it defined
;; assume all definition of varible member is ahead of all
;; function definition
(define (class? e)
  (match e
    [`(class ,(? symbol?) (,(? member?)... ,(? fun?) ...)) #t]
    [else #f]))

;; program
;; and other global definition is not allowed
(define (prog? e)
  (match e
    [`(,(? class?)...) #t]
    [else #f]))


;; fact generator

;; datalog rule
;; .decl Alloc(v: Var, o: Obj, in:Method)  // v = new O(); and in is in where it calls this ∈ Var v
;; .decl Assign(to: Var, from: Var)            // to = from;  v1 ⊇ v2
;; .decl Load(to: Var, target: Var, f: Field)  // to = target.f
;; .decl Store(target: Var, f: Field, from: Var)   // target.f = from
;; .decl Vcall(target: Var, fun: Method, ins: Instr, inM:Method)    // inside some Method "in", target.fun()
;;                                                                 // ins is the full call line code
;; .decl ThisCall(fun: Method, ins: Instr, inM:Method)   // some direct call like foo(); or this.foo(); 

;; // some info relate to name
;; .decl FormalArg(m: Method, pos: Position, arg: Var) // formal arg inside a Method m, pos is a mark 
;;                                                     // to identify which arg it is
;; .decl RealArg(i: Instr, pos: Position, arg: Var)    // i is from where a function is called
;; .decl FormalRet(m: Method, ret: Var)                // the formal return of a function
;; .decl RealRet(i: Instr, ret: Var)                   // in which Instr the value is returned to
;; .decl ClassOf(o: Obj, c: Class)                  // we need to denote the Class of a o is c 
;; .decl MethodOf(c: Class, m: Method)       // the signature of a Method is c and it's Class is c
;; .decl MemberOf(v: Var, c: Class)                    // denote the memeber varible in class

;; grammar of predicate IR
(define (fact? e)
  ;;(displayln e)
  (match e
    [`(Alloc ,(? symbol?) ,(? number?) ,(? symbol?)) #t]
    [`(Assign ,(? symbol?) ,(? symbol?)) #t]
    [`(Load ,(? symbol?) ,(? symbol?) ,(? symbol?)) #t]
    [`(Store ,(? symbol?) ,(? symbol?) ,(? symbol?)) #t]
    [`(Vcall ,(? symbol?) ,(? symbol?) ,(? list?) ,(? symbol?)) #t]
    [`(ThisCall ,(? symbol?) ,(? list?) ,(? symbol?)) #t]
    [`(FormalArg ,(? symbol?) ,(? number?) ,(? symbol?)) #t]
    [`(RealArg ,(? list?) ,(? number?) ,(? symbol?)) #t]
    [`(FormalRet ,(? symbol?) ,(? symbol?)) #t]
    [`(RealRet ,(? list?) ,(? symbol?)) #t]
    [`(ClassOf ,(? number?) ,(? symbol?)) #t]
    [`(MethodOf ,(? symbol?) ,(? symbol?)) #t]
    [`(MemberOf ,(? symbol?) ,(? symbol?)) #t]
    [else #f]
    ))

;; here I use a generate function to gen some uique number to
;; represent the addr of object in heap
(define counter 0)
(define (gen-num)
  (set! counter (+ counter 1))
  counter)

;(define (factgen-func-arg i args ))

(define (factgen-instr e inMeth)
  (match e
    [`(var ,(? symbol? vname) = new ,(? symbol? cname)())
     (define obj (gen-num))
     (list
      `(Alloc ,vname ,obj ,inMeth)
      `(ClassOf ,obj ,cname))]
    [`(,(? symbol? to) = ,(? symbol? from))
     (list `(Assign ,to ,from))]
    [`(,(? symbol? to) = ,(? symbol? target) DOT ,(? symbol? f))
     (list `(Load ,to ,target ,f))]
    [`(,(? symbol? target) DOT ,(? symbol? f) = ,(? symbol? from))
     (list `(Store ,target ,f ,from))]
    [`(,(? symbol? v) = ,(? symbol? target) DOT ,(? symbol? meth)(,(? symbol? args) ...))
     (cons
      `(RealRet ,e ,v)
      (cons
        `(Vcall ,target ,meth ,e ,inMeth)
        (foldl
         (λ (x res) (cons `(RealArg ,e ,(length res) ,x) res))
         '() args)))]
    [`(,(? symbol? target) DOT ,(? symbol? meth)(,(? symbol? args) ...))
     (cons
      `(Vcall ,target ,meth ,e ,inMeth)
      (foldl
       (λ (x res) (cons `(RealArg ,e ,(length res) ,x) res))
       '() args))]
    [`(,(? symbol? meth)(,(? symbol? args) ...))
     (cons
      `(ThisCall ,meth ,e ,inMeth)
      (foldl
       (λ (x res) (cons `(RealArg ,e ,(length res) ,x) res))
       '() args))]
    [`(,(? symbol? v) = ,(? symbol? meth)(,(? symbol? args) ...))
      (cons
       `(ThisCall ,meth ,e ,inMeth)
       (foldl
        (λ (x res) (cons `(RealArg ,e ,(length res) ,x) res))
        '() args))]
    [(? symbol?) '()]
    ))

(define (factgen-return e meth)
  (match e
    [`(return ,(? symbol? v))
     `(FormalRet ,meth ,v)]))

(define (factgen-fun e className)
  (match e
    [`(fun ,(? symbol? meth) (,(? symbol? args) ...)
           (,(? instr? ins) ... ,(? return? ret)))
     (list*
      `(MethodOf ,className ,meth)
      (factgen-return ret meth)
      (foldl
       (λ (x res) (cons `(FormalArg ,meth ,(length res) ,x) res))
       '() args)
      (map (λ (i) (factgen-instr i meth)) ins))
     ]
    [`(fun ,(? symbol? meth) (,(? symbol? args) ...)
           (,(? instr? ins)... ))
     (cons
      `(MethodOf ,className ,meth)
      (append
       (foldl
        (λ (x res) (cons `(FormalArg ,meth ,(length res) ,x) res))
        '() args)
       (map (λ (i) (factgen-instr i meth)) ins)))
     ]
    ))

(define (factgen-member e className)
  (match e
    [`(var ,(? symbol? v))
     `(MemberOf ,v ,className)]))

(define (factgen-class e)
  (match e
    [`(class ,(? symbol? className)
        (,(? member? mbs)... ,(? fun? funs)...))
     ;; flatten way
     (append
      (map (λ (m) (factgen-member m className)) mbs)
      (map (λ (f) (factgen-fun f className)) funs))]))

;; generate strutural facts
(define (factgen e)
  (match e
    [`(,(? class? clazzs)...)
     ;; structural way
     ;; (map factgen-class clazzs)]))
     ;; flatten way
     (append* (map factgen-class clazzs))]))

;; flatten the fact tree
;; define predicate expr
(define (fact-flatten f)
  (if (fact? f)
      (list f)
      (append* (map (λ (x) (fact-flatten x)) f))))


;; test

;; test grammar
;; our target program
;; class A1 {
;;   var some;
;;   var other;
;;   fun setSome(s) { some = s; }
;;   fun getSome() { return some; }
;; }
;; class B1 {}
;; class Main {
;;   fun Main () {
;;     func1();
;;   }
;;   fun func1() {
;;     var a1 = new A1();
;;     var b1 = new B1();
;;     var c1 = new B1();
;;     a1.setSome(b1);
;;     a1.other = b1;
;;     c1 = a1.getSome();
;;     c1 = a1.other;
;;   }
;;   fun print(Object m){ /*some io here*/ }
;; }

;; equivlent s-expr
(define prog-test
  `((class A1 {(var some)
               (var other)
               (fun setSome(s)((some = s)))
               (fun getSome()((return some)))
               })
    (class B1 {})
    (class Main {(fun Main(){(func1())})
                 (fun func1(){
                              (var a1 = new A1())
                              (var b1 = new B1())
                              (var c1 = new B1())
                              (a1 DOT setSome (b1))
                              (a1 DOT other = b1)
                              (c1 = a1 DOT getSome ())
                              (c1 = a1 DOT other)
                              })
                 })
     ))

(define func1 `(fun getSome(){(some = other)(return some)}))
(define classA `(class A1 {(var some)
                          (var other)
                          (fun getSome(){(return some)})
                          }) )

(fun? `(fun getSome(){(return some)}))
(class? `(class A1 {(var some)
                    (var other)
                    (fun getSome(){(return some)})
                    }))

(prog? prog-test)

;; (factgen-instr `(var a1 = new A1()) 'func1)
;; (factgen-instr `(c1 = a1 DOT getSome ()) 'func1)
;; (factgen-fun func1 'A1)
(factgen prog-test)
(fact-flatten (factgen prog-test))
