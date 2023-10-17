#lang algebraic/racket/base

(require
  algebraic/data
  algebraic/racket/base/forms
  algebraic/function
  algebraic/prelude)

(require (only-in seq cut-where starts-with?))

(require (only-in racket/contract/base not/c))

(require (only-in racket/symbol symbol->immutable-string))

; type Name = String

(data Expr
      (Var   ; Name -> Expr
       Ctr   ; Name -> [Expr] -> Expr              constructors
       FCall ; Name -> [Expr] -> Expr              "indifferent" function
       GCall ; Name -> [Expr] -> Expr              "curious" function
       Let)) ; (Name, Expr) -> Expr -> Expr

(data Pat (Pat)) ; Name -> [Name] -> Pat

(data GDef (GDef)) ; Name -> Pat -> [Name] -> Expr -> GDef

(data FDef (FDef)) ; Name -> [Name] -> Expr -> FDef

(data Program (Program)) ; [FDef] -> [GDef] -> Program

(define isValue
  (function
   [(Ctr _ args) (andmap isValue args)]
   [_            #f]))

(define isCall
  (function
   [(FCall _ _) #t]
   [(GCall _ _) #t]
   [_           #f]))

(define isVar
  (function
   [(Var _) #t]
   [_       #f]))


(define fDef ; :: Program -> Name -> FDef
  (function*
   [((Program fs _) fname) (findf (function [(FDef x _ _) (equal? x fname)]) fs)]))

(define gDefs ; :: Program -> Name -> [GDef]
  (function*
   [((Program _ gs) gname) (filter (function [(GDef x _ _ _) (equal? x gname)]) gs)]))

(define gDef ; :: Program -> Name -> Name -> GDef
  (function*
   [(p gname cname) (findf (function [(GDef _ (Pat c _) _ _) (equal? c cname)]) (gDefs p gname))]))

; type Subst = [(Name, Expr)]
; type Subst = hash Name -> Expr

(define lookup
  (function*
   [(() key def) def]
   [(((x v) . xs) key def)
    (if (equal? x key) v (lookup xs key def))]))

(define // ; :: Expr -> Subst -> Expr
  (function*
   [((Var x) sub) (lookup sub x (Var x))]
   [((Ctr name args) sub) (Ctr name (map (lambda (x) (// x sub)) args))]
   [((FCall name args) sub) (FCall name (map (lambda (x) (// x sub)) args))]
   [((GCall name args) sub) (GCall name (map (lambda (x) (// x sub)) args))]
   [((Let (x e1) e2) sub) (Let (list x (// e1 sub)) (// e2 sub))]))

(define intStep ; :: Program -> Expr -> Expr
  (function*
   [(p (Ctr name args))
      (let ([(values (x . xs)) (cut-where (not/c isValue) args)])
        (Ctr name (++ values (cons (intStep p x) xs))))]
   [(p (FCall name args)) (let ([(FDef _ vs body) (fDef p name)]) (// body (map list vs args)))]
   [(p (GCall gname ((Ctr cname cargs) . args)))
      (let ([(GDef _ (Pat _ cvs) vs body) (gDef p gname cname)])
        (// body (map list (++ cvs vs) (++ cargs args))))]
   [(p (GCall gname (e . es))) (GCall gname (cons (intStep p e) es))]
   [(p (Let (x e1) e2)) (// e2 (list (list x e1)))]))

(define (int p e)
  (if (isValue e)
      e
      (int p (intStep p e))))


(define fCall?
  (lambda (x) (starts-with? "f" x)))

(define gCall?
  (lambda (x) (starts-with? "g" x)))



(define expression
  (function [(symb . params) (let* [(name (symbol->immutable-string symb))
                                    (args (map expression params))]
                               (cond
                                 ((fCall? name) (FCall name args))
                                 ((gCall? name) (GCall name args))
                                 (else          (Ctr name args))))] ;; slight difference, any call that doesnt start with f or g is treated as a constructor call
            [symb (Var (symbol->immutable-string symb))]))

(define definition
  (function [('define (symb (ctr . cparams) . params) expr)
             (GDef (symbol->immutable-string symb) (Pat (symbol->immutable-string ctr) (map symbol->immutable-string cparams)) (map symbol->immutable-string params) (expression expr))]
            [('define (symb . params) expr)
             (FDef (symbol->immutable-string symb) (map symbol->immutable-string params) (expression expr))]
            ))
             
(define program
  (function
   [defns (let ([(fs gs) (foldl
                          (function* [(defn (fs gs))
                                      (let ([res (definition defn)])
                                        (case res
                                          [(FDef . _) (list (cons res fs) gs)]
                                          [(GDef . _) (list fs (cons res gs))]))])
                          '(() ())
                          defns)])
            (Program (reverse fs) (reverse gs)))]))

;(define prog1
;  (Program
;    (list (FDef "fSqr" (list "x") (GCall "gMult" (list (Var "x") (Var "x")))))
;    (list (GDef "gAdd" (Pat "Z" '()) '("y") (Var "y"))
;          (GDef "gAdd" (Pat "S" '("x")) '("y") (Ctr "S" (list (GCall "gAdd" (list (Var "x") (Var "y"))))))
;          (GDef "gMult" (Pat "Z" '()) '("y") (Ctr "Z" '()))
;          (GDef "gMult" (Pat "S" '("x")) '("y") (GCall "gAdd" (list (Var "y") (GCall "gMult" (list (Var "x") (Var "y"))))))
;          (GDef "gEven" (Pat "Z" '()) '() (Ctr "True" '()))
;          (GDef "gEven" (Pat "S" '("x")) '() (GCall "gOdd" (list (Var "x"))))
;          (GDef "gOdd" (Pat "Z" '()) '() (Ctr "False" '()))
;          (GDef "gOdd" (Pat "S" '("x")) '() (GCall "gEven" (list (Var "x"))))
;          (GDef "gAdd1" (Pat "Z" '()) '("y") (Var "y"))
;          (GDef "gAdd1" (Pat "S" '("x")) '("y") (GCall "gAdd1" (list (Var "x") (Ctr "S" (list (Var "y")))))))))

(define prog1 (program
               '((define (fSqr x) (gMult x x))
                 (define (gAdd (Z) y) y)
                 (define (gAdd (S x) y) (S (gAdd x y)))
                 (define (gMult (Z) y) (Z))
                 (define (gMult (S x) y) (gAdd y (gMult x y)))
                 (define (gEven (Z)) (True))
                 (define (gEven (S x)) (gOdd x))
                 (define (gOdd (Z)) (False))
                 (define (gOdd (S x)) (gEven x))
                 (define (gAdd1 (Z) y) y)
                 (define (gAdd1 (S x) y) (gAdd1 x (S y))))))

(define expr1
  (expression '(gEven (fSqr (S (S (S (Z))))))))

(define prog2
  (program
    '((define (gEqSymb (A) y) (gEqA y))
      (define (gEqSymb (B) y) (gEqB y))
      (define (gEqA (A)) (True)) (define (gEqA (B)) (False))
      (define (gEqB (B)) (True)) (define (gEqB (A)) (False))
      (define (gIf (True) x y) x)
      (define (gIf (False) x y) y)
      (define (fMatch p s) (gM p s p s))
      (define (gM (Nil) ss op os) (True))
      (define (gM (Cons p pp) ss op os) (gX ss p pp op os))
      (define (gX (Nil) p pp op os) (False))
      (define (gX (Cons s ss) p pp op os) (gIf (gEqSymb p s) (gM pp ss op os) (gN os op)))
      (define (gN (Nil) op) (False))
      (define (gN (Cons s ss) op) (gM op ss op ss)))))

(define expr2
  (expression '(fMatch (Cons (A) (Cons (B) (Nil))) (Cons (A) (Cons (A) (Cons (A) (Nil)))))))


(define prog4
  (program '((define (fInf) (S (fInf)))
             (define (fB x) (fB (S x))))))

;(define expr4
;  (expression '(fInf)))

;(intStep prog4 (intStep prog4 expr4))

