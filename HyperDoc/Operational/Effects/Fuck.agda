{-# OPTIONS --type-in-type #-}

module HyperDoc.Operational.Effects.Fuck where 

open import Cubical.Data.FinData
open import Cubical.Data.Nat 
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to ⊎rec)

open import Cubical.Foundations.Prelude 
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Adjoint 
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monad.ExtensionSystem hiding (F)

open import Cubical.Categories.NaturalTransformation 
open NatTrans 

open import Cubical.Categories.Constructions.FullSubcategory
open import HyperDoc.Algebra.Algebra hiding (eval)
--open Signature
--open Theory

open Category
open Functor
open Alg
open AlgHom
open NaturalBijection

data Sig (X : Type) : Type where
  get : X → X → Sig X
  set0 set1 : X → Sig X

SigMap : {X Y : Type} → (X → Y) → Sig X → Sig Y 
SigMap f (get x x₁) = get (f x) (f x₁) 
SigMap f (set0 x) = set0 (f x)
SigMap f (set1 x) = set1 (f x)

data Sig* (X : Type) : Type where 
  var : X  → Sig* X
  get : X → X → Sig* X
  set0 set1 : X → Sig* X

State : Type → Type 
State X = Bool → X × Bool



data B (X : Type) : Type where 
  done : State X → B X  
  step : X → B X


smap : {X Y : Type} → (X → Y) → State X → State Y 
smap f s = λ z → f (s z .fst) , z

sget : {X : Type} → State X → State X → State X 
sget s t false = s false
sget s t true = t true

sset0 : {X : Type} → State X → State X 
sset0 {X} s _ = s false

sset1 : {X : Type} → State X → State X 
sset1 {X} s _ = s true

--left to right eval strategy?
lam : {X : Type} → Sig (X × B X) → B (Sig* X)
lam {X} (get (x , done s) (x' , done s')) = done (sget (smap var s) (smap var s'))
lam {X} (get (x , done s) (_ , step x')) = step (get x x')
lam {X} (get (_ , step x) (x' , _)) = step (get x x')
lam {X} (set0 (x , done s)) = done (sset0 (smap var s))
lam {X} (set0 (x , step x')) = step (set0 x')
lam {X} (set1 (x , done s)) = done (sset1 (smap var s))
lam {X} (set1 (x , step x')) = step (set1 x')

-- fold like 
fld : {X : Type} → Sig (State X) → State (Sig* X) 
fld {X} (get s s') = sget (smap var s) (smap var s')
fld {X} (set0 s) = sset0 (smap var s)
fld {X} (set1 s) = sset1 (smap var s)

{-# NO_POSITIVITY_CHECK #-}
data mu (F : Type → Type)(X : Type) : Type where 
  inn : F (mu F X) → mu F X

FreeStAlg : Type → Type  
FreeStAlg = mu Sig

out : {X : Type} → FreeStAlg X → Sig (FreeStAlg X) 
out (inn x) = x

_∘s_ : {X Y Z : Type} → (Y → Z) → (X → Y) → X → Z 
_∘s_ = λ z z₁ z₂ → z (z₁ z₂)

last : {X : Type} → Sig* (FreeStAlg X) → FreeStAlg X
last (var x) = x
last (get x x₁) = inn (get x x₁)
last (set0 x) = inn (set0 x)
last (set1 x) = inn (set1 x)

{-# TERMINATING #-}
co : {X : Type} → FreeStAlg X → State (FreeStAlg X) 
co = ((smap last ∘s fld) ∘s SigMap co) ∘s out


--B X = Unit ⊎ State X

{-}
step' : {X : Type} → Sig (State X) → State (Sig X) 
step' {X} (get x x₁) = {!   !}
step' {X} (set0 x) = {!   !}
step' {X} (set1 x) = {!   !}

step : {X : Type} → Sig (X × B X) → B (Sig X)  
step {X} (get (x , inl tt) (x' , inl tt)) = inr {!   !}
step {X} (get (fst₁ , inl tt) (fst₂ , inr x)) = {!   !}
step {X} (get (fst₁ , inr x) t') = {!   !}
step {X} (set0 t) = {!   !}
step {X} (set1 t) = {!   !}


  -}

{-}
open import Cubical.Foundations.Powerset
open import Cubical.Data.List renaming (map to lmap)

module raw where 
  -- is this even a profunctor
  mutual 
    data VTy : Type where 
      𝟙 : VTy
      U : CTy → VTy 
    data CTy : Type where 
      F : VTy → CTy 
  open Signature
  mutual 
    data _⊢v_ : VTy → VTy → Type where 
      subV : ∀ {A A' A''} → A ⊢v A' → A' ⊢v A'' → A ⊢v A''
      var : ∀ {A} → A ⊢v A
      subVIdl : ∀ {A A'} → (V : A ⊢v A') → subV (var {A}) V ≡ V
      subVIdr : ∀ {A A'} → (V : A ⊢v A') → subV V (var {A'}) ≡ V
      subVAssoc : ∀ {A₁ A₂ A₃ A₄}(V : A₁ ⊢v A₂)(W : A₂ ⊢v A₃)(Y : A₃ ⊢v A₄) → 
        subV (subV V W) Y ≡ subV V (subV W Y)
      isSet⊢v : ∀{A A'} → isSet (A ⊢v A')

      thunk : ∀ {A B} → A ⊢c B → A ⊢v U B

    data _⊢k_ : CTy → CTy → Type where
      -- category 
      kcomp : ∀ {B B' B''} → B ⊢k B' → B' ⊢k B'' → B ⊢k B''
      hole : ∀ {B} → B ⊢k B
      kcompIdl : ∀ {B B'} → (M : B ⊢k B') → kcomp (hole {B}) M ≡ M
      kcompIdr : ∀ {B B'} → (M : B ⊢k B') → kcomp M (hole {B'}) ≡ M
      kcompAssoc : ∀ {B₁ B₂ B₃ B₄}(M : B₁ ⊢k B₂)(N : B₂ ⊢k B₃)(P : B₃ ⊢k B₄) → 
        kcomp(kcomp M N) P ≡  kcomp M (kcomp N P)
      isSet⊢k : ∀{B B'} → isSet (B ⊢k B')


    data _⊢c_ : VTy → CTy → Type where 
      -- profunctor      
      subC : ∀ {A A' B} → A ⊢v A' → A' ⊢c B → A ⊢c B
      plug : ∀ {A B B'} → B ⊢k B' → A ⊢c B → A ⊢c B'
      plugId : ∀ {A B}{M : A ⊢c B} → plug (hole {B}) M ≡ M
      subCId : ∀ {A B}{M : A ⊢c B} → subC (var {A}) M ≡ M
      plugDist : ∀ {A B B' B''}{S : B ⊢k B'}{S' : B' ⊢k B''}{M : A ⊢c B} → --rcomp
        plug S' (plug S M) ≡ plug (kcomp S S') M
      subDist : ∀ {A A' A'' B}{V : A ⊢v A'}{V' : A' ⊢v A''}{M : A'' ⊢c B} → --lcomp
        subC V (subC V' M) ≡ subC (subV V V') M
      plugSub : ∀ {A A' B B'}{V : A ⊢v A'}{M : A' ⊢c B}{S : B ⊢k B'} → 
        subC V (plug S M) ≡ plug S (subC V M)
      isSet⊢c : ∀{A B} → isSet (A ⊢c B)

      force : ∀ {A B} → A ⊢v U B → A ⊢c B
      -- ops
      ops : ∀{Sig : Signature} {A : VTy}{B : CTy}(op : Sig .Op) →  
        (Fin (Sig .arity op) → A ⊢c B) → A ⊢c B
      -- monoid
      e : ∀ {A B} → A ⊢c B 
      _⊕_ : ∀ {A B} → A ⊢c B → A ⊢c B → A ⊢c B

      -- state
      get : ∀ {A B} →  A ⊢c B → A ⊢c B → A ⊢c B
      set0 set1 : ∀ {A B} → A ⊢c B → A ⊢c B 

      opsSub : ∀{A A' : VTy}{B : CTy}(V : A ⊢v A')(M N : A' ⊢c B) → 
        subC V (M ⊕ N) ≡ (subC V M ⊕ subC V N)

      opsPlug : ∀ {A : VTy}{B B' : CTy}(S : B ⊢k B')(M N : A ⊢c B) → 
        plug S (M ⊕ N) ≡ (plug S M ⊕ plug S N)  

  data _↦_ {A : VTy}{B : CTy} : A ⊢c B → A ⊢c B → Type where 
    βU : ∀ {M : A ⊢c B} → force (thunk M) ↦ M

  data _↦T_ {A : VTy}{B : CTy} : List (A ⊢c B) → List (A ⊢c B) → Type where 
    e-rule : ∀ {xs ys : List (A ⊢c B)} →  
      (xs ++ [ e ] ++ ys) ↦T (xs ++ ys) 
    ⊕-rule : ∀ {xs ys : List (A ⊢c B)}{M N : A ⊢c B} → 
      (xs ++ [ M ⊕ N ] ++ ys) ↦T (xs ++ (M ∷ N ∷ []) ++ ys)
    pure-rule : ∀ {xs ys : List (A ⊢c B)}{M M' : A ⊢c B} → 
        (xs ++ [ M ] ++ ys) ↦T (xs ++ [ M' ] ++ ys) 


  State : Type → Type
  State X = Bool → X × Bool

  s-get : {X : Type} → State X → State X → State X 
  s-get s s' false = s false
  s-get s s' true = s' true

  s-set0 : {X : Type} → State X → State X 
  s-set0 s _ = s false
  
  s-set1 : {X : Type} → State X → State X 
  s-set1 s _ = s true
 

  nf : {X : Type} → (s : State X) → s ≡ 
    s-get 
      (let (x , b') = s false in if b' then (λ s → x , true) else (λ s → x , false)) 
      (let (x , b') = s true in if b' then (λ s → x , true) else (λ s → x , false)) 
  nf s = funExt sub where 
    sub : 
      (x : Bool) →
      s x ≡
      s-get
      (if s false .snd then (λ s₁ → s false .fst , true) else
      (λ s₁ → s false .fst , false))
      (if s true .snd then (λ s₁ → s true .fst , true) else
      (λ s₁ → s true .fst , false))
      x
    sub false  with (s false .snd)
    ... | false = ΣPathP (refl , {!   !})
    ... | true = ΣPathP (refl , {!   !})
    sub true with (s true .snd)
    ... | false = ΣPathP (refl , {!   !})
    ... | true = ΣPathP (refl , {!   !})

  -- not correct, the input "s" is always ignored.. except for get ?
  data _↦S_ {A : VTy}{B : CTy} : State (A ⊢c B) → State (A ⊢c B) → Type where 
    get-rule :  {M N : A ⊢c B}{b : Bool} → 
      (λ s → get M N , b) ↦S λ s → (if s then N else M) , b 
    set0-rule : {M : A ⊢c B}{b : Bool} → 
      (λ s → set0 M , b) ↦S λ s → M , false
    set1-rule : {M : A ⊢c B}{b : Bool} → 
      (λ s → set1 M , b) ↦S λ s → M , true
    pure-rule : {M M' : A ⊢c B}{b : Bool} → 
      M ↦ M' → 
      (λ s → M , b) ↦S λ s → M' , b


  module hrm 
    (Sig : Signature)
    (T : Type → Type)
    (Talg : (X : Type) → IsAlg  Sig (T X , {!   !}))
    (η : {X : Type} → X → T X)
    (mmap : {X Y : Type} → (X → Y) → T X → T Y) where 

    data _↦E_ {A : VTy}{B : CTy} : T (A ⊢c B) → T (A ⊢c B) → Type  where 
      pure-rule : {M M' : A ⊢c B} → 
        M ↦ M' → 
        η M ↦E η M'

      -- wrong
      op-rule : {op : Sig .Op}{args : Fin (Sig .arity op) → A ⊢c B} →  
        η (ops {Sig} op args) ↦E Talg (A ⊢c B) op λ x → η (args x)

      cong-rule :  {op : Sig .Op}{args args' : Fin (Sig .arity op) → T (A ⊢c B)}  → 
        ((x : Fin (Sig .arity op)) → args x ↦E args' x) → 
        Talg (A ⊢c B) op args ↦E Talg (A ⊢c B) op args'


    data _↦E*_ {A : VTy}{B : CTy} : T (A ⊢c B) → T (A ⊢c B) → Type  where
      ref : ∀ {M} → M ↦E* M
      tran : ∀ {M N P} → M ↦E* N → N ↦E P → M ↦E* P


    open import Cubical.Foundations.Powerset
    Pred : VTy → CTy → Type 
    Pred A B = ℙ (T (A ⊢c B))

    isAntiClo : ∀{A}{B} → Pred A B → Type
    isAntiClo {A}{B} P = (M N : T ( A ⊢c B)) → M ↦E* N → N ∈ P → M ∈ P

    AntiClPred : VTy → CTy → Type 
    AntiClPred A B = Σ[ P ∈ Pred A B ] isAntiClo P

    data FreePred {A : VTy}: T(𝟙 ⊢c F A) → Type where 
      base :  (V : T(𝟙 ⊢v A))(M : T(𝟙 ⊢c F A)) → 
        M ≡ mmap {!   !} V  → FreePred {A} M


  data MonOps : Type where 
    e ⊕ : MonOps 

  open Signature

  MonoidSig : Signature 
  MonoidSig .Op = MonOps
  MonoidSig .arity e = 0
  MonoidSig .arity ⊕ = 2
  -- observe 

  module foo where 
    open hrm MonoidSig List (λ {X e args → []
                                ; X ⊕ args → args zero ++ args one}) [_] lmap

    _ : [ ops e (λ ()) ] ↦E []
    _ = op-rule {_}{_}{e}{λ()} 

    _ = {! cong-rule {_}{_}{⊕} ?  !}


    duh : {A : VTy}{B : CTy}(M N : A ⊢c B) → {!   !}
      -- [ ops ⊕ (λ { zero → M ; one → N ; (suc (suc ())) }) ] ↦E (M ∷ [ N ]) 
    duh {A}{B} M N = op-rule {A}{B}{⊕}{λ {zero → M; one → N}}

  module bar where 
    
    data StOps : Type where 
      get set0 set1 : StOps
    
    StateSig : Signature
    StateSig .Op = StOps
    StateSig .arity get = 2
    StateSig .arity set0 = 1
    StateSig .arity set1 = 1

    stGet : ∀ {X} → State X → State X → State X
    stGet t t' false = t false
    stGet t t' true = t' true

    StateAlg : (X : Type ) → IsAlg StateSig ((State X) , {!   !}) 
    StateAlg X get args = stGet (args zero) (args one)
    StateAlg X set0 args b = args zero false
    StateAlg X set1 args b = args zero true


    open hrm StateSig State StateAlg (λ {X} x b → x , b)  {! d !}

    module _ (A : VTy)(B : CTy)(M N : A ⊢c B) where 
      t' :  A ⊢c B 
      t' = ops {StateSig} get λ {zero → M ; one → N}
      t : A ⊢c B 
      t = ops {StateSig} set0 λ _ → t'

      {- 
        (λ b → get(M , N) , false) ↦E
        vs 
        (λ b → get(M , N) , b) ↦E
      -}
      deriv : (λ b → t , b) ↦E* (λ b → M , b) 
      deriv = tran (tran ref (op-rule {A}{B}{set0}{λ _ → t'})) 
        {! op-rule {A}{B}{get}{?}  !}

    h : (A : VTy)(B : CTy)(args : Fin 2 → A ⊢c B) → 
      (λ b → ops get args , b) ↦E stGet (λ b → args zero , b) (λ b → args one , b)
    h A B args = op-rule {A}{B}{get}{args}

    g : (A : VTy)(B : CTy)(args args' : Fin 2 → State (A ⊢c B)) → 
      (((x : Fin 2) → args x ↦E args' x)) → 
      stGet (args zero) (args one) ↦E stGet (args' zero) (args' one) 
    g A B args args' = cong-rule {A}{B}{get}{args}{args'}

  V : Category _ _ 
  V .ob = VTy
  V .Hom[_,_] = _⊢v_
  V .id = var
  V ._⋆_ = subV
  V .⋆IdL = subVIdl
  V .⋆IdR = subVIdr
  V .⋆Assoc = subVAssoc
  V .isSetHom = isSet⊢v

  C : Category _ _ 
  C .ob = CTy
  C .Hom[_,_] = _⊢k_
  C .id = hole
  C ._⋆_ = kcomp
  C .⋆IdL = kcompIdl
  C .⋆IdR = kcompIdr
  C .⋆Assoc = kcompAssoc
  C .isSetHom = isSet⊢k



  alg : VTy → CTy → Alg MonoidSig
  alg A B .Carrier = List (A ⊢c B) , {!   !}
  alg A B .interp e args = []
  alg A B .interp ⊕ args = args zero ++ args one

  open import HyperDoc.Operational.Effects.BiAlgebra
  open BiAlg

  bialg : VTy → CTy → BiAlg MonoidSig 
  bialg A B .car = List (A ⊢c B), {!   !}
  bialg A B .isAlg e args = []
  bialg A B .isAlg ⊕ args = args zero ++ args one
  bialg A B .isRGraph .fst M N = M ↦T N , {!   !}
  bialg A B .isRGraph .snd = {!   !}
  bialg A B .congruence e args = {!   !}
  bialg A B .congruence ⊕ args = {!   !}

  open import Cubical.Categories.Bifunctor
  open BifunctorSep
  
  O : BifunctorSep (V ^op) C (BIALG MonoidSig) 
  O .Bif-ob = bialg
  O .Bif-homL V B .BiAlgHom.map = lmap (subC V)
  O .Bif-homL V B .BiAlgHom.isAlgHom e args = refl
  O .Bif-homL V B .BiAlgHom.isAlgHom ⊕ args = {!   !} -- yeah
  O .Bif-homL V B .BiAlgHom.isRelator = {!   !}
  O .Bif-L-id = BiAlgHom≡ (funExt λ {[] → refl
                                   ; (x ∷ xs) → {!   !}})
  O .Bif-L-seq V V' = BiAlgHom≡ {!   !}
  O .Bif-homR = {!   !}
  O .Bif-R-id = {!   !}
  O .Bif-R-seq = {!   !}
  O .SepBif-RL-commute = {!   !}

  -}