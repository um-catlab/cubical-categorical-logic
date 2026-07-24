{-# OPTIONS --type-in-type #-}
module HyperDoc.Operational.Effects.eval where 

open import Cubical.Data.FinData
open import Cubical.Data.Maybe renaming (rec to mrec)
open import Cubical.Data.Nat 
open import Cubical.Data.Bool

open import Cubical.Foundations.Prelude 
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure


open import HyperDoc.Algebra.Algebra hiding (eval)

open Signature

record Poly : Type where 
  constructor _◂_ 
  field 
    S : Type 
    P : S → Type

den : Poly → Set → Set 
den (S ◂ P) X = Σ[ s ∈ S ] (P s → X)

pmap : {X Y : Type}{p : Poly} → (X → Y) → den p X → den p Y 
pmap f (s , p) = s , (λ z → f (p z))

module Syntax (Sig : Signature) where 
  mutual 
    data VTy : Type where 
      𝟙 : VTy
      U : CTy → VTy 

    data CTy : Type where 
      F : VTy → CTy

  data _⊢v_ : (A A' : VTy) → Type 
  data _⊢c_ : (A : VTy)(B : CTy) → Type 
  data _⊢k_ : (B B' : CTy) → Type 


  data _⊢v_  where
    -- category 
    var : ∀ {A} → A ⊢v A
    -- type structure
    tt : ∀{A} → A ⊢v 𝟙

    thunk : ∀{A B} → A ⊢c B → A ⊢v U B

  data _⊢k_ where
    -- category 
    hole : ∀ {B} → B ⊢k B
    bind : {A : VTy}{B : CTy} → A ⊢c B → F A ⊢k B

  data _⊢c_ where 
    -- Effects
    ops : ∀{A : VTy}{B : CTy}(op : Sig .Op) →  
      (Fin (Sig .arity op) → A ⊢c B) → A ⊢c B
  
    -- type structure
    ret : ∀{A B} → F A ⊢k B → A ⊢c B
    force : ∀{A B} →  A ⊢v U B → A ⊢c B   



  mutual 
    subV : {A A' A'' : VTy} → A ⊢v A' → A' ⊢v A'' → A ⊢v A'' 
    subV V var = V
    subV V tt = tt
    subV V (thunk M) = thunk (subC V M)

    subC : ∀ {A A' B} → A ⊢v A' → A' ⊢c B → A ⊢c B 
    subC V (ops op args) = ops op λ i → subC V (args i)
    subC V (ret S) = ret {!   !}
    subC V (force W) = force (subV V W)

  ret' : ∀ {A A'} → A ⊢v A' → A ⊢c F A' 
  ret' V = subC V (ret hole)
    --plug : ∀ {A B B'} → B ⊢k B' → A ⊢c B → A ⊢c B' 
    --plug hole M = M
    --plug (bind N) M = {!  !}

module OpSem (Sig : Signature) where 
  open Syntax Sig

  findFirst :
    ∀ {ℓ} {X : Set ℓ} {n : ℕ} →
    (X → Bool) →
    (Fin n → X) →
    Maybe (Fin n)
  findFirst {n = zero} p f = nothing
  findFirst {n = suc n} p f with p (f zero)
  ... | true  = just zero
  ... | false =
    mapMaybe suc (findFirst p (λ i → f (suc i)))
    where
      mapMaybe : ∀ {A B} → (A → B) → Maybe A → Maybe B
      mapMaybe g nothing  = nothing
      mapMaybe g (just x) = just (g x)

  _>>=m_ : {A B : Type} → Maybe A → (A → Maybe B) → Maybe B 
  nothing >>=m f = nothing
  just a >>=m f = f a
  
  {-# TERMINATING #-}
  purestep : ∀ {A B} → A ⊢c B → Maybe (A ⊢c B)
  purestep {A} {B} (ops op args) = map-Maybe (ops op) args' where 
    i? : Maybe (Fin (arity Sig op)) 
    i? = findFirst (λ M → caseMaybe false true (purestep M)) args

    args' : Maybe (Fin (arity Sig op) → A ⊢c B)
    args' = i? >>=m λ i → purestep (args i) >>=m λ M → just λ j → if j == i then M else args j
    
  purestep {A} {B} (ret (bind M)) = just M
  purestep {A} {B} (force (thunk M)) = just M
  purestep {A} {B} _ = nothing

  reduce : ∀ {A B} → ℕ → A ⊢c B → A ⊢c B 
  reduce zero M = M
  reduce (suc n) M = mrec M (reduce n) (purestep M)

  reify : ∀ {A} → FreeOn Sig (𝟙 ⊢v A) → 𝟙 ⊢c F A
  reify (inc x) = subC x (ret hole)
  reify (ops o args) = ops o λ i → reify (args i)

  open import Cubical.Foundations.Isomorphism
  open import Cubical.Data.List
  module SemOp 
    (p : Poly)
    (isFinite : ∀ (s : Poly.S p) → Σ[ n ∈ ℕ ] Iso (Fin n) (Poly.P p s)) where
    open Poly p 

    T : Set → Set 
    T = den p
    module Monad
      (η : ∀ {X : Set} → X → T X)
      (μ : ∀ {X : Set} → T (T X) → T X)
      (TAlg : {X : Set} → IsAlg Sig ((T X) , {!   !})) where 

      leaves : {X : Set} → T X → List X 
      leaves (s , f) = foldrFin _∷_ [] λ i → f (Iso.fun (isFinite s .snd) i)

      bf : {X : Set} → T X → ℕ 
      bf (s , p) = isFinite s .fst

      asFin : {X : Set}{(s , p) : T X} → P s → Fin (bf (s , p)) 
      asFin {X}{t}p = Iso.inv (isFinite (t .fst) .snd) p

      Trm : Set → Set 
      Trm = FreeOn Sig

      isOp : {X : Set} → Trm X → Bool 
      isOp (inc x) = false
      isOp (ops o x) = true
      open import Cubical.Data.Sigma
      firstOp : {X : Set} → (t : T(Trm X)) → Maybe (Fin (bf t) × Trm X)
      firstOp {X} t = map-Maybe (λ i → i , t .snd (Iso.fun (isFinite (t .fst) .snd) i)) 
        (findFirst isOp λ i → t .snd (Iso.fun (isFinite (t .fst) .snd) i))
        --  {! map-Maybe ? (findFirst (λ {(inc x) → false
                                 --  ; (ops o x) → true}) λ i → t .snd (Iso.fun (isFinite (t .fst) .snd) i))

      sem : {X : Set} → 
        (t : T (Trm X))(i : Fin (bf t))
        (op : Op Sig)(args : Fin (arity Sig op) → Trm X) → 
        T (Trm X)
      sem t i op args = 
        let (s , f) = pmap η t in 
        μ (s , λ j → if asFin {_}{s , f} j == i then TAlg op (λ x → η (args x)) else f j)

  
      eval : {X : Set} → Trm X → T X 
      eval (inc x) = η x
      eval (ops o x) = TAlg o λ i → eval (x i)

      evalT : {X : Set} → T(Trm X) → T X
      evalT t = μ (pmap eval t)

      step : {X : Set} → T(Trm X) → T(Trm X)
      step t with (firstOp t)
      ... | nothing = t
      ... | just (i , inc x) = t
      ... | just (i , ops o x) = sem t i o x

      sound : Type 
      sound = {X : Set} → (t : T(Trm X)) → evalT t ≡ evalT (step t)
    

{-}
      data _↦T_ {X : Set} : T(Trm X) → T(Trm X) → Set where
        rule : {t : T(Trm X)} (i : Fin (bf t)) → 
          firstOp t ≡ just i → {!   !}  
-}
      update : {X : Set} → (t : T X) → Fin (bf t) → X → T X
      update (s , f) i M = s , λ j → if asFin {_}{s , f} j == i then M else f j 

      -- affine in subterms
      test : Type
      test  = 
        ∀ {X : Set} → 
        (t : T (Trm X))(i : Fin (bf t))
        (op : Op Sig)(args : Fin (arity Sig op) → Trm X) → 
        leaves (update (pmap just t) i nothing) 
        ++ foldrFin (λ x xs → just x ∷ xs) [] args
        ≡ leaves (pmap just (sem t i op args))
       


      stepE : {X : Set} → T (Trm X) → Maybe (T (Trm X)) 
      stepE (s , f) = {!   !}

      evalE : {!   !} 
      evalE = {!   !}


  mutual 
    V[_] : (A : VTy) → 𝟙 ⊢v A → Set 
    V[ 𝟙 ] V = V ≡ tt
    V[ U B ] V = C[ B ] (force V)

    data Free {A : VTy}: 𝟙 ⊢c F A → Type where 
      base : ∀ {M}{V} → M ≡ ret' V → V[ A ] V → Free M 
      opcong : ∀ {op}{args : Fin (Sig .arity op) → 𝟙 ⊢c F A} → 
        ((i : Fin (Sig .arity op)) → Free (args i)) → 
        Free (ops op args)
      anti : ∀ {M M'} → purestep M ≡ just M' → Free M' → Free M 

    C[_] : (B : CTy) → 𝟙 ⊢c B → Set 
    C[ F A ] M = Free M 

  mutual 
    FLv : ∀ {A} → (V : 𝟙 ⊢v A) → V[ A ] V 
    FLv var = {!   !}
    FLv tt = refl
    FLv (thunk M) = {! FLc M  !} 

    FLc : ∀ {B} → (M : 𝟙 ⊢c B) → C[ B ] M 
    FLc (ops op x) = {!   !}
    FLc (ret S) = {!   !}
    FLc (force V) = FLv V

  -- use eliminator
  conv : ∀ {A} → (M : 𝟙 ⊢c F A) → Free M → Σ[ n ∈ ℕ ] Σ[ t ∈ FreeOn Sig (𝟙 ⊢v A) ] reduce n M ≡ reify t 
  conv M (base {M}{V} x x₁) = 0 , inc V , x 
  conv M (opcong {op} dargs) = {!   !} , (ops op (λ i → {! dargs i   !}) , {!   !})
  conv M (anti {_}{M'} MtoM' PrfM') = 
    let (n , t , prf) = conv M' PrfM' in (suc n) , t , (cong (λ h → mrec M (reduce n) h) MtoM' ) ∙ prf

  LR : ∀ {A} → (M : 𝟙 ⊢c F A) → Σ[ n ∈ ℕ ] Σ[ t ∈ FreeOn Sig (𝟙 ⊢v A) ] reduce n M ≡ reify t 
  LR M = {!   !}



module testing where
  open import Cubical.Data.List
  open import Cubical.Foundations.Isomorphism


  module State where 
    data Ops : Type where 
      get set0 set1 : Ops 

    Sig : Signature
    Sig .Op = Ops
    Sig .arity get = 2
    Sig .arity set0 = 1
    Sig .arity set1 = 1

    open OpSem Sig 
    open Syntax Sig

    Statep : Poly
    Statep .Poly.S = Bool → Bool
    Statep .Poly.P = λ _ → Bool

    sfin : (s : Bool → Bool) → Σ-syntax ℕ (λ n → Iso (Fin n) Bool)
    sfin _ .fst = 2
    sfin _ .snd .Iso.fun zero = false
    sfin _ .snd .Iso.fun one = true
    sfin _ .snd .Iso.inv false = zero
    sfin _ .snd .Iso.inv true = one
    sfin _ .snd .Iso.sec = {!   !}
    sfin _ .snd .Iso.ret = {!   !}

    open SemOp Statep sfin 

    η : {X : Type} → X → T X
    η x = (λ b → b) , λ _ → x

    μ : {X : Type} → T (T X) → T X 
    μ (s , r) = (λ b → r b .fst (s b)) , λ b → r b .snd (s b)

    s-get : {X : Type} → T X → T X → T X 
    s-get (s , r) (s' , r') .fst false = s false 
    s-get (s , r) (s' , r') .fst true = s' true
    s-get (s , r) (s' , r') .snd false = r false
    s-get (s , r) (s' , r') .snd true = r' true

    s-set0 : {X : Type} → T X → T X 
    s-set0 (s , r) .fst x = s false
    s-set0 (s , r) .snd x = r false

    s-set1 : {X : Type} → T X → T X 
    s-set1 (s , r) .fst x = s true
    s-set1 (s , r) .snd x = r true

    stalg : {X : Type} → IsAlg Sig (T X , {!   !}) 
    stalg get args = s-get (args zero) (args one)
    stalg set0 args = s-set0 (args zero)
    stalg set1 args = s-set1 (args zero)

    open Monad η μ stalg

    foo : test 
    foo t zero get args with t .fst false 
    ... | false = {!   !}
    ... | true = {!   !}
    foo t one get args with t .fst true
    ... | false = {!   !}
    ... | true = {!   !}
    foo t zero set0 args = {!   !}
    foo t one set0 args = {!   !}
    foo t zero set1 args = {!   !}
    foo t one set1 args = {!   !} 

    term : T (Trm ℕ) 
    term = (λ _ → false) , λ { false → {!  !}
                             ; true → {!   !}}

    open import Cubical.Data.Sigma 
    bar : sound 
    bar = {!   !}

  module Write where 
    data Ops : Type where 
      tella tellb tellc : Ops  

    Sig : Signature
    Sig .Op = Ops
    Sig .arity _ = 1

    open OpSem Sig 
    open Syntax Sig

    data Str : Type where
      a b c : Str 

    WriteP : Poly 
    WriteP .Poly.S = List Str
    WriteP .Poly.P = λ _ → Unit

    prf : (s : List Str) → Σ-syntax ℕ (λ n → Iso (Fin n) Unit)
    prf _ .fst = 1
    prf _ .snd .Iso.fun = λ _ → tt
    prf _ .snd .Iso.inv = λ z → zero
    prf _ .snd .Iso.sec tt = refl
    prf _ .snd .Iso.ret zero = refl

    open SemOp WriteP prf 

    η : {X : Set} → X → T X
    η x = [] , λ _ → x

    μ : {X : Type} → T (T X) → T X
    μ (xs , r) = (xs ++ r tt .fst) , λ _ → r tt .snd tt

    walg : {X : Type} → IsAlg Sig (T X , {!   !})
    walg tella args = ([ a ] ++ args zero .fst) , (λ z → args zero .snd tt)
    walg tellb args = ([ b ] ++ args zero .fst) , (λ z → args zero .snd tt)
    walg tellc args = ([ c ] ++ args zero .fst) , (λ z → args zero .snd tt)

    open Monad η μ walg 
    foo : test 
    foo t zero tella args = {!   !}
    foo t zero tellb args = {!   !}
    foo t zero tellc args = {!   !}


module Ex where 
  Sig : Signature
  Sig .Op = Bool
  Sig .arity false = 1
  Sig .arity true = 2

  open OpSem Sig 
  open Syntax Sig
  M : 𝟙 ⊢c F 𝟙
  M = force (thunk (ops true λ { zero → force (thunk (ops false λ _ → ret hole))
                               ; one → ret hole}))

  _ = {! reduce 99  M  !}
