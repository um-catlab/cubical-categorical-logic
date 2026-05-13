{-# OPTIONS --type-in-type #-}
module HyperDoc.Operational.Effects.NormalForm where 

-- split epimorphism 

open import Cubical.Data.FinData
open import Cubical.Data.Nat 
open import Cubical.Data.Bool 
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to ⊎rec)

open import Cubical.Foundations.Prelude 
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monad.ExtensionSystem hiding (F)

open import Cubical.Categories.Constructions.FullSubcategory
open import HyperDoc.Algebra.Algebra hiding (eval)
open Signature
open Theory

open Category
open Functor
open Alg
open AlgHom


-- StSig : hSet _  → hSet _ 
-- StSig (X , isSetX) = (X × X) ⊎ (X ⊎ X) , {!   !} 

-- a monad supporting the operations (and equations) of state
module hmm 
  (St : ExtensionSystem (SET _ ))
  (Tget : {X : hSet _} → ⟨ St .fst X ⟩ → ⟨ St .fst X ⟩ → ⟨ St .fst X ⟩)
  (Tset0 Tset1 : {X : hSet _} →  ⟨ St .fst X ⟩ → ⟨ St .fst X ⟩)  where

  open ExtensionSystemFor (St .snd)
  
  T = St .fst

  mutual 
    data VTy : Type where 
      𝟙 : VTy 
    data CTy : Type where  
      F : VTy → CTy 
  data _⊢c_ : VTy → CTy → Type where 
    dummy : ∀{A B} → A ⊢c B
    get : ∀ {A B} → A ⊢c B → A ⊢c B → A ⊢c B
    set0 set1 : ∀ {A B} → A ⊢c B → A ⊢c B 

  data _↦_  {A : VTy}{B : CTy} : A ⊢c B → A ⊢c B → Type where  

  _⟨_⟩e : {X : Type } → ⟨ T ((X ⊎ Unit) , {!   !}) ⟩ → ⟨ T (X , {!   !}) ⟩ → ⟨ T (X , {!   !}) ⟩
  _⟨_⟩e t e = bind (⊎rec η (λ _ → e)) t

  _⟨_⟩m : {X : Type } → ⟨ T ((X ⊎ Unit) , {!   !}) ⟩ → X → ⟨ T (X , {!   !}) ⟩
  _⟨_⟩m t x = t ⟨ η x ⟩e

  data _↦alt_ {A : VTy} : ⟨ T (𝟙 ⊢c F A , {!   !}) ⟩ → ⟨ T (𝟙 ⊢c F A , {!   !}) ⟩ → Type  where 
    set0-cong : {M N : ⟨ T (𝟙 ⊢c F A , {!   !}) ⟩} → 
      M ↦alt N → 
      Tset0 M ↦alt Tset0 N 

  data _↦sem_ {A : VTy} : ⟨ T (𝟙 ⊢c F A , {!   !}) ⟩ → ⟨ T (𝟙 ⊢c F A , {!   !}) ⟩ → Type  where 
    pure : {M N : 𝟙 ⊢c F A}{t : ⟨ T ((𝟙 ⊢c F A) ⊎ Unit ,  {!   !}) ⟩ } → 
      M ↦ N → 
      (t ⟨ M ⟩m) ↦sem (t ⟨ N ⟩m)
    -- all this is.. syntactic operation is replaced by semantic operation
    get-step : {M N : 𝟙 ⊢c F A}{t : ⟨ T ((𝟙 ⊢c F A) ⊎ Unit , {!   !}) ⟩ } → 
      (t ⟨ get M N ⟩m) ↦sem (t ⟨ Tget (η M) (η N) ⟩e )
    set0-step : {M : 𝟙 ⊢c F A}{t : ⟨ T ((𝟙 ⊢c F A) ⊎ Unit , {!   !}) ⟩ } → 
      (t ⟨ set0 M ⟩m) ↦sem (t ⟨ Tset0 (η M)⟩e )
    set1-step : {M : 𝟙 ⊢c F A}{t : ⟨ T ((𝟙 ⊢c F A) ⊎ Unit , {!   !}) ⟩ } → 
      (t ⟨ set1 M ⟩m) ↦sem (t ⟨ Tset1 (η M)⟩e )

  {-
    if we assume all pure reductions have been completed beforehand
      think, we normalized to the free algebra first
    then 
      pure should never fire 
      at that point, how is any derivation using  _↦sem_ 
      any different from simply denoting the free algebra into a model?

      simple effects like state 
        may directly give you a normal form when you denote them into a nice model 
        ex) State monad as the free model 

      but what about effects like commutative monoid?
      seemingly there is no normal form


  -}

  data _↦*sem_ {A : VTy} : ⟨ T (𝟙 ⊢c F A , {!   !}) ⟩ → ⟨ T (𝟙 ⊢c F A , {!   !}) ⟩ → Type  where 
    ref : ∀ (M : ⟨ T (𝟙 ⊢c F A , {!   !}) ⟩) → M ↦*sem M
    tran : ∀ {M  N P  : ⟨ T (𝟙 ⊢c F A , {!   !}) ⟩} → 
       M ↦*sem N → N ↦sem P → M ↦*sem P

State : Type → Type 
State X = Bool → Bool × X

stget : {X : Type} → State X → State X → State X 
stget f g false = f false
stget f g true = g true

stset0 : {X : Type} → State X → State X 
stset0 f _ = f false

stset1 : {X : Type} → State X → State X 
stset1 f _ = f true

return : {X : Type} → X → State X 
return x s = s , x

sext : ExtensionSystem (SET _ ) 
sext .fst (X , isSetX) = State X , {!   open import Cubical.HITs.PropositionalTruncation
  !}
sext .snd .ExtensionSystemFor.η = return 
sext .snd .ExtensionSystemFor.bind f s b = let (b' , a) = s b in f a b'
sext .snd .ExtensionSystemFor.bind-r = refl
sext .snd .ExtensionSystemFor.bind-l = refl
sext .snd .ExtensionSystemFor.bind-comp = refl

module Example where 
  open hmm sext stget stset0 stset1
  open ExtensionSystemFor (sext .snd)

  t : {A : VTy} → State ((𝟙 ⊢c F A) ⊎ Unit)
  t {A} b = b , (inr tt)

  M : {A : VTy} → 𝟙 ⊢c F A 
  M = {!   !}

  N : {A : VTy} → 𝟙 ⊢c F A 
  N = {!   !}

  test : (t ⟨ set0 M ⟩m) ↦sem (t ⟨ stset0 (η M)⟩e)
  test = set0-step {𝟙}{M}{t}

  _ : (λ b → b , set0 M) ↦sem λ b → false , M
  _ = set0-step {𝟙}{M}{t}

  test' : (t ⟨ get M N ⟩m) ↦sem (t ⟨ stget (η M) (η N) ⟩e ) 
  test' = get-step {𝟙}{M}{N}{t}

  _ : (λ b → b , get M N) ↦sem λ b → stget (λ s → s , M) (λ s → s , N) b
  _ = get-step {𝟙}{M}{N}{t}

  test'' : (t ⟨ set0 (get M N) ⟩m) ↦*sem λ b → false , M 
  test'' = tran (tran (ref _) set0-step) get-step



module CBBB where 
  open import HyperDoc.Operational.Effects.Model 
  open import HyperDoc.Operational.Effects.Syntax
  open import HyperDoc.Operational.Effects.BiAlgebra
  open import HyperDoc.Operational.Graph
  open import Cubical.Categories.Bifunctor
  open BifunctorSep

  data Ops : Type where 
    get set0 set1 : Ops 

  St : Signature
  St .Op = Ops
  St .arity get = 2
  St .arity set0 = 1
  St .arity set1 = 1

  open SynModel St
  open Syntax St
  open BiAlg
  open BiAlgHom
  open import Cubical.Functions.Logic
  open import Cubical.HITs.PropositionalTruncation renaming (rec to hrec)

  data _↦sem_ {B : CTy} : State (𝟙 ⊢c B) → State (𝟙 ⊢c B) → Type where 
    -- needs to be prop valued relation
    -- needs to be reflexive
    -- needs to be a congruence w.r.t. operations
    -- stget (args zero) (args one) ↦sem stget (args' zero) (args' one)
    -- n ↦ n' → yuck n ↦sem yuck n'


  -- discrete bialgebra
  -- the reduction relation is just equality
  freeSt :  Type → BiAlg St
  freeSt X .car = (State X) , {!   !}
  freeSt X .isAlg get args = stget (args zero) (args one)
  freeSt X .isAlg set0 args = stset0 (args zero)
  freeSt X .isAlg set1 args = stset1 (args zero)
  freeSt X .isRGraph .fst s s' = s ≡ₚ s'
  freeSt X .isRGraph .snd s = ∣ refl ∣₁
  freeSt X .congruence get args args' steps = {!   !}
  freeSt X .congruence set0 args args' steps = 
    hrec squash₁ (λ p → ∣ (cong stset0 p) ∣₁) (steps zero)
  freeSt X .congruence set1 args args' steps = 
    hrec squash₁ (λ p → ∣ (cong stset1 p) ∣₁) (steps zero)

  module _ (Sig : Signature) where 
    data _↦free_ {X : Type}: FreeOn Sig X → FreeOn Sig X → Type  where
      ref : (x : FreeOn Sig X) → x ↦free x
      alg-cong : ∀ 
        {op}
        {args args'  : Fin (Sig .arity op) → FreeOn Sig X} → 
        (∀ (i : Fin (Sig .arity op)) → args i ↦free args' i) → 
        ---------------------
        ops op args ↦free ops op args'
      isProp↦free : ∀ {x y} → isProp (x ↦free y)

    freeBi : Type → BiAlg Sig
    freeBi X .car = (FreeOn Sig X) , {!   !}
    freeBi X .isAlg = ops
    freeBi X .isRGraph .fst x y = (x ↦free y) , isProp↦free
    freeBi X .isRGraph .snd = ref
    freeBi X .congruence op args args' = alg-cong {op = op}{args}{args'}

    freeBimap : (X : Type)(B : BiAlg Sig)→ (X → ⟨ B .car ⟩ ) → BIALG Sig [ freeBi X , B ]
    freeBimap X B f .BiAlgHom.map = FreeAlgMorphism {Sig}{X}{alg B} f .carmap
    freeBimap X B f .isAlgHom = FreeAlgMorphism {Sig}{X}{alg B} f .pres
    freeBimap X B f .isRelator .fst {n} {n'} (ref x) = 
      isRGraph B .snd (freeBimap X B f .BiAlgHom.map n)
    freeBimap X B f .isRelator .fst {n} {n'} (alg-cong {op}{args}{args'} steps) = 
      congruence B op 
        (λ i → FreeAlgMorphism {Sig}{X}{alg B} f .carmap (args i)) 
        (λ i → FreeAlgMorphism {Sig}{X}{alg B} f .carmap (args' i)) 
        λ i → {! steps  i  !}
    freeBimap X B f .isRelator .fst {n} {n'} (isProp↦free d d₁ i) = {!   !}
    freeBimap X B f .isRelator .snd = refl


  -- the NBE approach , an algebra hom 
  -- should be the map out of the free (bi) algebra
  Omap : BIALG St [ freeBi St (𝟙 ⊢v 𝟚) , freeSt (𝟙 ⊢v 𝟚) ]
  Omap = freeBimap St (𝟙 ⊢v 𝟚) (freeSt (𝟙 ⊢v 𝟚)) return

  t : FreeOn St (𝟙 ⊢v 𝟚) 
  t = ops set0 λ _ → ops get λ {zero → ops set1 λ _ → inc σ₁
                              ; one → inc σ₂}

  _ : Omap  .BiAlgHom.map t  ≡ λ _ → Bool.true , σ₁
  _ = refl

  -- the coalgebraic approach , graph hom into graph with more reduction rules
  -- take the equations of the theory as directed rewrites
  data _↦T_ {X : Type }: FreeOn St X → FreeOn St X → Type where 
    ref : (x : FreeOn St X) → x ↦T x
    alg-cong : ∀ 
      {op}
      {args args'  : Fin (St .arity op) → FreeOn St X} → 
      (∀ (i : Fin (St .arity op)) → args i ↦T args' i) → 
      ---------------------
      ops op args ↦T ops op args'

    getMM : (x : FreeOn St X) → 
      ops get (λ {zero → x ; one → x}) ↦T x
    {- 
      s0g : {M N : FreeStAlg X} → set0 (get M N)  ↦ set0 M  
      s1g : {M N : FreeStAlg X} → set1 (get M N)  ↦ set1 N  
      s0s0 : {M : FreeStAlg X} → set0 (set0 M)  ↦ set0 M 
      s0s1 : {M : FreeStAlg X} → set0 (set1 M)  ↦ set1 M 
      s1s0 : {M : FreeStAlg X} → set1 (set0 M)  ↦ set0 M 
      s1s1 : {M : FreeStAlg X} → set1 (set1 M)  ↦  set1 M 
      -- gg : {M N L P : FreeStAlg X} → get (get M N) (get L P)  ↦  get M P
      ggl : {M N P : FreeStAlg X} → get (get M N) P  ↦  get M P
      ggr : {M N P : FreeStAlg X} → get M (get N P)  ↦  get M P
      gs : {M N : FreeStAlg X} → get (set0 M) (set1 N)  ↦  get M N
      gid : {M : FreeStAlg X} → get M M ↦ M 
    -}
    isProp↦T : ∀ {x y} → isProp (x ↦T y)

  co : Type → BiAlg St
  co X .car = (FreeOn St X) , {!   !}
  co X .isAlg = ops
  co X .isRGraph .fst M N = (M ↦T N) , isProp↦T
  co X .isRGraph .snd = ref
  co X .congruence op args args' = alg-cong {op = op}{args}{args'}

  expandGraph : (X : Type) → BIALG St [ freeBi St X , co X ]
  expandGraph X = freeBimap St X (co X) inc

  eval' : {X : Type} → FreeOn St X → State X 
  eval' {X} = FreeAlgMorphism {St}{X} {alg (freeSt X)} return .carmap

  triangle : (X : Type) → BIALG St [ co X , freeSt  X ]
  triangle X .BiAlgHom.map = eval'
  triangle X .isAlgHom = FreeAlgMorphism {St}{X} {alg (freeSt X)} return .pres
  triangle X .isRelator .fst = {!   !} -- yes, this is soundness
  {-
    n ↦T n' ⇒ eval' n ≡ₚ eval' n'

    see below

    sound' : {X : Type}{M M' : FreeStAlg X} → M ↦ M' → eval M ≡ eval M'
    sound' ref = refl
    sound' (cong-get prf prf') i false = sound' prf i false
    sound' (cong-get prf prf') i true = sound' prf' i true
    sound' (cong-set0 prf) i b = sound' prf i false
    sound' (cong-set1 prf) i b = sound' prf i true
    sound' s0g = refl
    sound' s1g = refl
    sound' s0s0 = refl
    sound' s0s1 = refl
    sound' s1s0 = refl
    sound' s1s1 = refl
    sound' ggl = {!   !}
    sound' ggr = {!   !}
    -- sound' (gg {M}) i false = eval M false
    -- sound' (gg {M}{N}{L}{P}) i true = eval P true
    sound' (gs {M}{N}) i false = eval M false
    sound' (gs {M}{N}) i true = eval N true
    sound' (gid {M}) i false = eval M false
    sound' (gid {M}) i true = eval M true
  -}
  triangle X .isRelator .snd = {!   !}

  nbe :  {X : Type } → BIALG St [ freeBi St X , freeSt X ]
  nbe {X} = freeBimap St X (freeSt X) return

  -- yes these do commute
  -- wait.. of course they should.. they are both maps out of the free bialgebra! 
  -- as long as they agree on the carrier X
  test : {X : Type} → expandGraph X ⋆⟨ BIALG St ⟩ triangle X ≡ nbe {X}
  test {X} = BiAlgHom≡ (funExt λ {(inc x) → refl
                                ; (ops o x) → {!   !}})
  -- λ i x → FreeAlgMorphism! {St}{X}{alg (freeSt X)}{{!   !}}{{!   !}} {!   !} i .carmap x
    -- BiAlgHom≡ {! FreeAlgMorphism! {St}{X}{alg (freeSt X)}{?}{?} ? !}


  -- no, needs to be a model
  freeStBimap : (X : Type)(B : BiAlg St)→ (X → ⟨ B .car ⟩ ) → BIALG St [ freeSt X , B ]
  freeStBimap X B f .BiAlgHom.map s = 
    alg B .interp get 
      λ {zero → let (b , x) = s Bool.false in 
          (if b then 
            alg B .interp set1 (λ _ → f x) else 
            alg B .interp set0 (λ _ → f x)) ; 
         one → let (b , x) = s Bool.true in 
          (if b then 
            alg B .interp set1 (λ _ → f x) else 
            alg B .interp set0 (λ _ → f x))}
  freeStBimap X B f .isAlgHom get args = {!  !}
  freeStBimap X B f .isAlgHom set0 args = {!   !}
  freeStBimap X B f .isAlgHom set1 args = {!   !}
  freeStBimap X B f .isRelator = {!   !}

  -- no, remember this is a set map
  norm : BIALG St [ freeBi St (𝟙 ⊢v 𝟚) , freeBi St (𝟙 ⊢v 𝟚) ]
  norm = Omap ⋆⟨ BIALG St ⟩ {!   !}

data FreeStAlg (X : Type) : Type where 
  inc : X → FreeStAlg X 
  get : FreeStAlg X → FreeStAlg X → FreeStAlg X  
  set0 set1 : FreeStAlg X → FreeStAlg X 


nf : {X : Type} → State X → FreeStAlg X 
nf {X} s = 
  get 
    (let (b , x) = s false in (if b then set1 (inc x) else set0 (inc x))) 
    (let (b , x) = s true in (if b then set1 (inc x) else set0 (inc x))) 

_ = {! nf (λ b → false , _)  !}

eval : {X : Type} → FreeStAlg X → State X 
eval {X} (inc x) = return x
eval {X} (get x x') = stget (eval x) (eval x')
eval {X} (set0 x) = stset0 (eval x)
eval {X} (set1 x) = stset1 (eval x)

isId : {X : Type} → (s : State X) → eval (nf s) ≡ s 
isId {X} s i false with (s false) 
... | false , x = false , x
... | true , x = true , x
isId {X} s i true with (s true) 
... | false , x = false , x
... | true , x = true , x

norm : {X : Type} → FreeStAlg X → FreeStAlg X 
norm {X} x = nf (eval x)

-- can't prove w/o equations
statement : {X : Type} → (M : FreeStAlg X) → 
  Σ[ s ∈ State X ] M ≡ nf s
statement (inc x) = return x , {!   !}
statement (get m m₁) = (stget (statement m .fst) (statement m₁ .fst)) , (cong₂ get {!   !} {!   !})
statement (set0 m) = (stset0 (statement m .fst)) , (cong set0 (statement m .snd) ∙ {!   !})
statement (set1 m) = {!   !}
_ = {! nf (eval (inc 7))  !}

exp : FreeStAlg ℕ
exp = get (set0 (get (get (set1 (set0 (get (inc 1) (inc 2)))) (get (inc 3) (inc 4))) (set1 (set0 (set1 (get (inc 5) (inc 6))))))) (inc 7)

_ : norm exp ≡ get (set0 (inc 1)) (set1 (inc 7))
_ = refl

eta : {X : Type} → FreeStAlg X → FreeStAlg X 
eta {X} M = get (set0 M) (set1 M)

eta≡' : {X : Type} → (M : FreeStAlg X) → eval (eta M) ≡ eval M 
eta≡' {X} M = funExt λ {false → refl
                     ; true → refl}
                     
eta≡ : {X : Type} → (M : FreeStAlg X) → norm (eta M) ≡ norm M
eta≡ {X} M = cong nf ((eta≡' {X} M))

-- + congruences
data _↦_ {X : Type} : FreeStAlg X → FreeStAlg X → Type where 
  -- The bialgebra part
  ref : { M : FreeStAlg X} → M ↦ M 
  cong-get : {M M' N N' : FreeStAlg X} → 
    M ↦ M' → 
    N ↦ N' → 
    get M N ↦ get M' N' 

  cong-set0 : {M M' : FreeStAlg X} → 
    M ↦ M' → 
    set0 M ↦ set0 M' 

  cong-set1 : {M M' : FreeStAlg X} → 
    M ↦ M' → 
    set1 M ↦ set1 M' 
  -- equations as reductions (check lax bialgebra rule)
  s0g : {M N : FreeStAlg X} → set0 (get M N)  ↦ set0 M  
  s1g : {M N : FreeStAlg X} → set1 (get M N)  ↦ set1 N  
  s0s0 : {M : FreeStAlg X} → set0 (set0 M)  ↦ set0 M 
  s0s1 : {M : FreeStAlg X} → set0 (set1 M)  ↦ set1 M 
  s1s0 : {M : FreeStAlg X} → set1 (set0 M)  ↦ set0 M 
  s1s1 : {M : FreeStAlg X} → set1 (set1 M)  ↦  set1 M 
  -- gg : {M N L P : FreeStAlg X} → get (get M N) (get L P)  ↦  get M P
  ggl : {M N P : FreeStAlg X} → get (get M N) P  ↦  get M P
  ggr : {M N P : FreeStAlg X} → get M (get N P)  ↦  get M P
  gs : {M N : FreeStAlg X} → get (set0 M) (set1 N)  ↦  get M N
  gid : {M : FreeStAlg X} → get M M ↦ M 

sound' : {X : Type}{M M' : FreeStAlg X} → M ↦ M' → eval M ≡ eval M'
sound' ref = refl
sound' (cong-get prf prf') i false = sound' prf i false
sound' (cong-get prf prf') i true = sound' prf' i true
sound' (cong-set0 prf) i b = sound' prf i false
sound' (cong-set1 prf) i b = sound' prf i true
sound' s0g = refl
sound' s1g = refl
sound' s0s0 = refl
sound' s0s1 = refl
sound' s1s0 = refl
sound' s1s1 = refl
sound' ggl = {!   !}
sound' ggr = {!   !}
-- sound' (gg {M}) i false = eval M false
-- sound' (gg {M}{N}{L}{P}) i true = eval P true
sound' (gs {M}{N}) i false = eval M false
sound' (gs {M}{N}) i true = eval N true
sound' (gid {M}) i false = eval M false
sound' (gid {M}) i true = eval M true

sound : {X : Type}{M M' : FreeStAlg X} → M ↦ M' → norm M ≡ norm M' 
sound prf = cong nf (sound' prf)

data _↦*_ {X : Type} : FreeStAlg X → FreeStAlg X → Type where 
  mref : {M : FreeStAlg X} → M ↦* M
  tran : {M N P : FreeStAlg X} → P ↦* M → M ↦ N → P ↦* N  

soundness' : {X : Type}{M M' : FreeStAlg X} → M ↦* M' → eval M ≡ eval M'
soundness' mref = refl
soundness' (tran {M}{N}{P} prf x) = soundness' prf ∙ sound' x

soundness : {X : Type}{M M' : FreeStAlg X} → M ↦* M' → norm M ≡ norm M'
soundness prf = cong nf (soundness' prf)

complete : {X : Type} → (M N : FreeStAlg X) → eval M ≡ eval N → (M ↦* N) × (N ↦* M) 
complete {X} (inc x) (inc x₁) prf .fst = {!   !}
complete {X} (inc x) (get N N₁) prf .fst = {!   !}
complete {X} (inc x) (set0 N) prf .fst = {!   !}
complete {X} (inc x) (set1 N) prf .fst = {!   !}
complete {X} (get M M₁) N prf .fst = {!   !}
complete {X} (set0 M) N prf .fst = {!   !}
complete {X} (set1 M) N prf .fst = {!   !}
complete {X} M N prf .snd = {!   !} 

-- no, they have different normal forms
-- inc x vs get (set0 inc x)(set1 inc x)
cannonicity' : {X : Type}(M : FreeStAlg X) → Σ[ N ∈ FreeStAlg X ] (M ↦* N) × (eta N ≡ norm M)
cannonicity' (inc x) = (inc x) , (mref , refl)
cannonicity' (get M M') = {!   !}
cannonicity' (set0 M) = {!   !}
cannonicity' (set1 M) = {!   !}

data NF {X : Type} : FreeStAlg X  → Type where 
  incNF : ∀ (x : X) → NF (inc x)
  getNF1 : ∀ (x y : X) → NF (get (inc x) (inc y)) 
  getNF2 : ∀ (x y : X) → NF (get (inc x) (set0 (inc y))) 
  getNF3 : ∀ (x y : X) → NF (get (set1 (inc x)) (inc y)) 
  getNF4 : ∀ (x y : X) → NF (get (set1 (inc x)) (set0 (inc y))) 
  set0NF : ∀ (x : X) → NF (set0 (inc x)) 
  set1NF : ∀ (x : X) → NF (set1 (inc x)) 
  -- others


jfc : {X : Type}(M : FreeStAlg X) →  Σ[ N ∈ FreeStAlg X ] NF N × (M ↦* N)
jfc (inc x) = inc x , incNF x , mref
jfc (get M M₁) = {!   !}
jfc (set0 M) with (jfc M) 
... | fst₁ , incNF x , snd₁ = set0 (inc x) , {!   !} , {!   !}
... | fst₁ , getNF1 x y , snd₁ = {!   !}
... | fst₁ , getNF2 x y , snd₁ = {!   !}
... | fst₁ , getNF3 x y , snd₁ = {!   !}
... | fst₁ , getNF4 x y , snd₁ = {!   !}
... | fst₁ , set0NF x , snd₁ = {!   !}
... | fst₁ , set1NF x , snd₁ = {!   !}
jfc (set1 M) with (jfc M) 
... | N , incNF x , M↦*N = (set1 (inc x)) , ((set1NF x) , tran {!  cong-set1 ? !} ref)
... | N , getNF1 x y , M↦*N = (set1 (inc y)) , ((set1NF y) , {!   !})
... | N , getNF2 x y , M↦*N = {!   !}
... | N , getNF3 x y , M↦*N = {!   !}
... | N , getNF4 x y , M↦*N = {!   !}
... | N , set0NF x , M↦*N = {!   !}
... | N , set1NF x , M↦*N = {!   !}

open import Cubical.Data.Sum 
-- RHS trivially inhabited by ref
progress : {X : Type}(M : FreeStAlg X) → NF M ⊎ (Σ[ N ∈ FreeStAlg X ] (M ↦ N)) 
progress (inc x) = inl (incNF x)
progress (get M M₁) = {!   !}
progress (set0 M) with (progress M) 
... | inl (incNF x) = inl (set0NF x)
... | inl (getNF1 x y) = {!   !}
... | inl (getNF2 x y) = {!   !}
... | inl (getNF3 x y) = {!   !}
... | inl (getNF4 x y) = {!   !}
... | inl (set0NF x) = {!   !}
... | inl (set1NF x) = {!   !}
... | inr x = {!   !}
progress (set1 M) = {!   !}

{-
progress (inc x) = inl (incNF x)
progress (get M N) with (progress M , progress N)
... | inl (incNF x) , inl (incNF x₁) = inl (getNF x x₁)
... | inl (incNF x) , inl (getNF x₁ y) = inr ((get (inc x) (inc y)) , ggr)
... | inl (incNF x) , inl (set0NF x₁) = {!   !}
... | inl (incNF x) , inl (set1NF x₁) = {!   !}
... | inl (getNF x y) , inl x₁ = {!   !}
... | inl (set0NF x) , inl x₁ = {!   !}
... | inl (set1NF x) , inl x₁ = {!   !}
... | inl x , inr x₁ = {!   !}
... | inr x , snd₁ = {!   !}
progress (set0 M) with (progress M) 
... | inl (incNF x) = inl (set0NF x)
... | inl (getNF x y) = inr (set0 (inc x) , s0g)
... | inl (set0NF x) = inr (set0 (inc x) , s0s0)
... | inl (set1NF x) = inr (set1 (inc x) , s0s1)
... | inr (N , M↦N) = inr ((set0 N) , (cong-set0 M↦N))
progress (set1 M) = {!   !}

-}
cannonicity : {X : Type}(M : FreeStAlg X) → Σ[ N ∈ FreeStAlg X ] (M ↦* N) × NF {X} N 
cannonicity (inc x) = (inc x) , (mref , incNF x)
cannonicity (get M M₁) = {!   !}
cannonicity (set0 M) = {!   !}
cannonicity (set1 M) = {!   !}

{-
    tran : {X Y Z : Node B} →  
      Edge[_,_] B X Y →  
      B ◂ Z ↦* X  → 
      B ◂ Z ↦* Y  
  -}
evalfun : {X : Type} → FreeStAlg X → FreeStAlg X
evalfun {X} (set0 (get M N)) = set0 M
evalfun {X} (set1 (get M N)) = set1 N
evalfun {X} (set0 (set0 M)) = set0 M
evalfun {X} (set0 (set1 M)) = set1 M
evalfun {X} (set1 (set0 M)) = set0 M
evalfun {X} (set1 (set1 M)) = set1 M
evalfun {X} (get (get M N) (get L P)) = get M P
evalfun {X} (get (set0 M) (set1 N)) = get M N
-- evalfun {X} (get M .M) = ?
evalfun {X} (inc x) = inc x
evalfun {X} (get x x₁) = get (evalfun x) (evalfun x₁)
evalfun {X} (set0 x) = set0 (evalfun x)
evalfun {X} (set1 x) = set1 (evalfun x)


hmm : {X : Type} → (M : FreeStAlg X) → NF (evalfun M) 
hmm (inc x) = incNF x
hmm (get M M') with (hmm M , hmm M') 
... | fst₁ , snd₁ = {! fst₁  !}
hmm (set0 M) = {!   !}
hmm (set1 M) = {!   !}

run : {X : Type} → ℕ → FreeStAlg X → FreeStAlg X 
run {X} zero x = x
run {X} (suc n) x = evalfun (run n x)



adjust : {X : Type} → FreeStAlg X → FreeStAlg X 
adjust {X} (inc x) = get (set0 (inc x)) (set1 (inc x))
adjust {X} (get (inc x) (inc y)) = get (set0 (inc x)) (set1 (inc y))
adjust {X} (get (inc x) y) = get (set0 (inc x)) y
adjust {X} (get x (inc y)) = get x (set1 (inc y))
adjust {X} (set0 x) = {!   !}
adjust {X} (set1 x) = {!   !}
{-}
{-}
try : {X : Type} → (x : FreeStAlg X) → Σ[ n ∈ ℕ ] (adjust (run n x)) ≡ norm x 
try {X} (inc x) = 0 , refl
try {X} (get x x') = {!   !}{{{{{!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}!   !}! {!   !} !}! {!   !} !}! {!   !} !}! {!   !} !}! {!   !}!   !} !}! {!   !}!   !} !}! {!   !}!  {!   !}!} !}! {!   !}!  {!   !}!} !}! {!   !}!{!   !} {!   !}!} !}! {!   !}!{!   !} {!   !}!} !}! {!   !}!{!   !} {!   !}!} !}{!{!   !}!{!   !} {!   !}!}  !}{{!   !}!{!   !} {!   !}!}!   !{!   !}!{!   !} {!   !}!}!   !{!   !}!{!   !} {!   !}!}!   !{!   !}!{!   !} {!   !}!}!   !{!   !}!{!   !} {!   !}!}!   !{!   !}!{!   !} {!   !}!}!   !{!   !}!{!   !} {!   !}!}!   !{!   !}!{!   !} {!   !}!}!   !{!   !}!{!   !} {!   !}!}!   !{!   !}!{!   !} {!   !}!}!   !{!   !}!{!   !} {!   !}!}!   !{!   !}!{!   !} {!   !}!}!   !{!   !}!{!   !} {!   !}!}!   !{!   !}!{!   !} {!   !}!{!   !{!   !}!{!   !} {!   !}!}!   !{!   !}!{!   !} {!   !}!}!   !{!   !}!{!   !} {!   !}!}!   !}!   !{!{!   !} {!   !}!}!   !}!   !{!{!   !} {!   !}!   !}!}!   !{!{!   !}  !}!  {!   !}!}!   !{!{!   !}  !}!{!   !}  !}!   !{!   !}!{!   !} {!   !}!}!   !{!   !}!  {!   !}!}!   !{!   !}!{!   !} {!   !}!{!   !{!   !}!{!   !} {!   !}!}!   !{!   !}!{!   !} {!   !}!}!   !{!   !}!{!   !} {!   !}!}!   !}!   !{!{!   !} {!   !}!}!   !}!   !{!{!   !} {!   !}!   !}!}!   !{!{!   !}  !}!  {!   !}!}!   !{!{!   !}  !}!{!   !}  {!   !}}!   !{!   !}!{!  {!   !}!} {!   !}{!   !}}!   !{!   !}!  {!{!   !}  !}!{!   {!   !}{!   !}!{!   !} {!{!   !}  !}!{!   {!   !}{!   !}!{!   !} {!{!   !}  !}!}{!  {!   !}{!   !}!{!   !} {!{!   !}  !}!}}   {!   !}}! {! {!{!   !} {!{!   !}  !}!} !} {!   !}}!   !{!{!   !} {!{!   !}  !}!   !}{!   !}}! {!   {!   !}} !{!   !}{! {!   !}{!   !}!} {!   {!   !}!  {!   !}!}} !}! {{{!   !}   !}   !}!   {!  {!   !}!}} !}! {!{!   !}!   !}  !} !}!{!  {!   !}!}{!   !}!{!   !} {!   !}!} !}! {! {!   !} !}!   !}!{!   !}  !} !}! {!   !}!{{!   !}   !} {!  {!   !}!}!} !}! {!   !}! {!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}!   !}}! {!   !}!{{!   !}   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} !}! {!   !}!{!   !} {!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}!   !}}! {!   !}!{{!   !}   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} !}! {!   !}!{!   !} {!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}!   !}}! {!   !}!{{!   !}   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} {!   !}}! {!   !}!{!   !}{!   !}{!   !}!} !{!   !}! {!   !}!{!   !} {!   !}!   !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}! {!   !}!{!   !} {!   !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} {! {!   !}{!   !}!{!   !} {!{!   !}  !}!}!}} {!   !}{!   !}!{!   !} {!{!   !}  !}!}!}{!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !} {!   !}{!   !}!{!   !} {!{!   !}  !}!}!}! {!   !}{!   !}!{!   !} {!{!   !}  !}!}!}! {!   !}{!   !}!{!   !} {!{!   !}  !}!}!}! {!   !}{!   !}!{!   !} {!{!   !}  !}!}!}! {!   !}{!   !}!{!   !} {!{!   !}  !}!}!}! {!   !}{!   !}!{!   !} {!{!   !}  !}!}{!  {!   !}{!   !}!{!   !} {!{!   !}  !}!}}}  {!   !}{!   !}!{!   !} {!{!   !}  !}!}}{! {!   !}{!   !}!{!   !} {!{!   !}  !}!}!}  {!   !}{!   !}!{!   !} {!{!   !}  !}!}}!  {!   !}{!   !}!{!   !} {!{!   !}  !}!}}!  {!   !}{!   !}!{!   !} {!{!   !}  !}!}}!  {!   !}{!   !}!{!   !} {!{!   !}  !}!}}!  {!   !}{!   !}!{!   !} {!{!   !}  !}!}}!  {!   !}{!   !}!{!   !} {!{!   !}  !}!}!   {!   !}{!   !}!{!   !} {!{!   !}  !}!}}!  {!   !}{!   !}!{!   !} {!{!   !}  !}!}}   {!   !}{!   !}!{!   !} {!{!   !}  !}!}{!  {!   !}{!   !}!{!   !} {!{!   !}  !}!}}!  {!   !}{!   !}!{!   !} {!{!   !}  !}!}}   {!   !}{!   !}!{!   !} {!{!   !}  !}!}!   {!   !}{!   !}!{!   !} {!{!   !}  !}!}!   {!   !}{!   !}!{!   !} {!{!   !}  !}!}!   {!   !}{!   !}!{!   !} {!{!   !}  !}!}!   {!   !}{!   !}!{!   !} {!{!   !}  !}!}   !{!   !}{!   !}!{!   !} {!{!   !}  !}!}   !{!   !}{!   !}!{!   !} {!{!   !}  !}!}!   {!   !}{!   !}!{!   !} {!{!   !}  !}!}   !{!   !}{!   !}!{!   !} {!{!   !}  !}!}   !{!   !}{!   !}!{!   !} {!{!   !}  !}!}   !{!   !}{!   !}!{!   !} {!{!   !}  !}!}   !{!   !}{!   !}!{!   !} {!{!   !}  !}!}   !{!   !}{!   !}!{!   !} {!{!   !}  !}!}   !{!   !}{!   !}!{!   !} {!{!   !}  !}!}   !{!   !}{!   !} {!   !} {!{!   !}  !}}{!   {!   !}{!   !} {!   !} {!{!   !}  !}}!   !{!   !}{!   !} {!   !} {!{!   !}  !}}!   !{!   !}{!   !} {!   !} {!{!   !}  !}}!   !{!   !}!   !}{!{!   !} {!{!   !}  !}!}   !{!   !}!   !{! {!   !} {!{!   !}  !}}!   !{!   !}!   !}! {!   !}{! {!   !} !}{!   !}{!   !}!   !{! {!   !} !}{!   !}   !}!   !{!   !}!   !}!{!   !}{!  {!   !}!}{!   !}!{!   !}!   !{!   !}!  {! {!   !} !}!}!   {{!   !}!   !} {!   !} {! {!   !} !}}}!   {{!   !}!   !} {!   !} {! {!   !} !}}}!   {{!   !}!   !} {!   !} {! {!   !} !}}}!   {{!   !}!   !} {!   !} {! {!   !} !}}}!   {{!   !}   !}! {!   !} {! {!   !} !}}}!   {{!   !}   !}! {!   !} {! {!   !} !}}}!   {{!   !}   !}! {!   !}{!  {!   !}!}!}}!   {{!   !}   !}! {!   !}{!  {!   !}!}!}}!   {{!   !}   !}!{!   !} {!  {!   !}!}!}}!   {{!   !}   !}}{!   !} {!  {!   !}!}{{!   !{{!   !}   !}!{!   !} {!  {!   !}!}!}   !}{{!   !}   !}}{!   !} {!  {!   !}!} !}!  {{{!   !}   !} {!   !} {!  {!   !}!}}!}!  {!{!   !}  !}{!{!   !} {!  {!   !}!}!}}!  {{{!   !}   !} {!   !} {!  {!   !}!}}!   !}!{!   !}!  {! {!   !} !}!}{!   !} {!   !}{!{!   !}  !}! {!   !}{{!  {!   !}!}   !}!}!{!   !}!  {!   !}! {!   !{!   !} !}!}! {{!{!   !}  !} {{!   !}   !}{!   !}{!   !}}{!{!   !}  !{!   !}!}!{!   {!   !}}  !}! {{!{!   !}  !} {!   !} {!   {!   !}}} !}! {{!{!   !}  !} {!   !} {!   {!   !}}} !}! {! {!   !} !}{!{!   !} {!   {!   !}}!}   !} !{!   !}! {! {!   !} {!   {!   !}}} !}! {! {!   !} !}! {!   !}{!   !{!   !}{!   !}} !{!   !}! {! {!   !} !}!  {!   !}!} !}! {! {!   !} !}!{!   !}{!   !}{!   !}!   !}!} !{!   !}! {!   !}!  {!   !{!   !}!} !}! {! {!   !} !}!{!   !} {!   !{!   !}!} !}! {! {!   !} !}!{!   !} {!   !{!   !}!} !}! {! {!   !} !}!{!   !} {!   !{!   !}!} !}! {! {!   !} !}!{!   !} {!   !{!   !}!} !}! {! {!   !} !}!{!   !} {!   !{!   !}!} !}! {!{!   !}{!   !} !}!{!   !} {!   {!   !}{!   !}!} !}! {!   !}!{!   !} {!   !}!} !}! {!{!   !}  !}!{!   !} {!   {!   !}}!} !}! {!{!   !}  !}!{!   !} {!   {!   !}}!} !}! {!{!   !}  !}!{!   !} {!   {!   !}}!} !}! {!{!   !}  !}!{!   !} {!   {!   !}}!} !}! {!{!   !}  !}!{!   !} {!   {!   !}}!} !}! {!{!   !}  !}!{!   !} {!   {!   !}}!} !}! {!{!   !}  !}!{!   !} {!   {!   !}}!} !}! {!{!   !}  !}!{!   !} {!   {!   !}}!} !}! {{!   !}   !}!{!   !} {!  {!   !}!}!} !}! {{!   !}   !}!{!   !} {!  {!   !}!}!} !}! {{!   !}   !}!{!   !} {!  {!   !}!}!} !}! {{!   !}   !}!{!   !} {!  {!   !}!}!} !}! {{!   !}   !}!{!   !} {!  {!   !}!}!} !}! {{!   !}   !}!{!   !} {!  {!   !}!}!} !}! {{!   !}   !}!{!   !} {!  {!   !}!}!} !}! {{!   !}   !}!{!   !} {!  {!   !}!}!} !}! {{!   !}   !}!{!   !} {!  {!   !}!}!} !}! {!   !}{!   !}{!   !} {!   !}!} !}! {{{!   !}   !}   !}!   !}!{!   !{!   !} {! {!   !} !}!} !}! {!   !}!{!   !} {!   !}!} !}! {!   !}!   !}!{!   !} {! {!   !} !}!} !}! {!   !}!   !}!{!   !} {! {!   !} !}!} !}! {!   !}!   !}!{!   !} {! {!   !} !}!} !}! {!   !}!   !}!{!   !} {! {!   !} !}!} !}! {!   !}!   !}!{!   !} {! {!   !} !}!} !}! {!   !}!   !}!{!   !} {! {!   !} !}!} !}!{!   !}{!   !}!   !}!{!   !} {!{!   !}{!   !} !}!} !}! {!   !}!{!   !} {!   !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} {! {!   !}{!   !}!{!   !} {!{!   !}  !}!}!}}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !} {!   !}{!   !}!{!   !} {!{!   !}  !}!}!}{!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !} {!   !}{!   !}!{!   !} {!{!   !}  !}!}!}! {!   !}{!   !}!{!   !} {!{!   !}  !}!}{!  {!   !}{!   !}!{!   !} {!{!   !}  !}!}}}! {!   !}{!   !}!{!   !} {!{!   !}  !}!}!}  {!   !}{!   !}!{!   !} {!{!   !}  !}!}}{! {!   !}{!   !}!{!   !} {!{!   !}  !}!}!}! {!   !}{!   !}!{!   !} {!{!   !}  !}!}!}  {!   !}{!   !}!{!   !} {!{!   !}  !}!}}!  {!   !}{!   !}!{!   !} {!{!   !}  !}!}}!  {!   !}{!   !}!{!   !} {!{!   !}  !}!}}!  {!   !}{!   !}!{!   !} {!{!   !}  !}!}}!  {!   !}{!   !}!{!   !} {!{!   !}  !}!}}!  {!   !}{!   !}!{!   !} {!{!   !}  !}!}}!  {!   !}{!   !}!{!   !} {!{!   !}  !}!}}!  {!   !}{!   !}!{!   !} {!{!   !}  !}!}}!  {!   !}{!   !}!{!   !} {!{!   !}  !}!}!   {!   !}{!   !}!{!   !} {!{!   !}  !}!}}   {!   !}{!   !}!{!   !} {!{!   !}  !}!}{!  {!   !}{!   !}!{!   !} {!{!   !}  !}!}}   {!   !}{!   !}!{!   !} {!{!   !}  !}!}!   {!   !}{!   !}!{!   !} {!{!   !}  !}!}!   {!   !}{!   !}!{!   !} {!{!   !}  !}!}!   {!   !}{!   !}!{!   !} {!{!   !}  !}!}!   {!   !}{!   !}!{!   !} {!{!   !}  !}!}!   {!   !}{!   !}!{!   !} {!{!   !}  !}!}!   {!   !}{!   !}!{!   !} {!{!   !}  !}!}!   {!   !}{!   !}!{!   !} {!{!   !}  !}!}!   {!   !}{!   !}!{!   !} {!{!   !}  !}!}!   {!   !}{!   !}!{!   !} {!{!   !}  !}!}!   {!   !}{!   !}!{!   !} {!{!   !}  !}!}!   {!   !}{!   !}!{!   !} {!{!   !}  !}!}!   {!   !}{!   !}!{!   !} {!{!   !}  !}!}!   {!   !}{!   !}!{!   !} {!{!   !}  !}!}!   {!   !}{!   !}!{!   !} {!{!   !}  !}{{!   {!   !}{!   !}!{!   !} {!{!   !}  !}!}   !{!   !}{!   !}!{!   !} {!{!   !}  !}!}!   {!   !}{!   !} {!   !} {!{!   !}  !}}}!   {!   !}!   !}{!{!   !} {!{!   !}  !}!}!   {!   !}{!   !} {!   !} {!{!   !}  !}}!   !{!   !}}!   {! {!   !} !}{!   !}!  {!   !}{!   !}!   !}}!{!   !}{{!{!   !}  !}   !}{{!   !}!   !{!   !}! {!  {!   !}!} !}   !}{!   !}!   !}}{{!   !}   {!   !}} {!   !} {!   !}}!  {{!   !}   {! {!   !} !}}!}!  {{!   !}   !}{!{!   !} {! {!   !} !}!}}!  {{!   !}!   !} {!   !} {! {!   !} !}}!   !}{!   !}}!  {! {!   !} !}!{!   !}! {!   !}{{!   !}   !}! {!   !}{{! {!   !} !}   !}!}{!   !}}!  {!   !}! {!   {!   !}} !}!}!  {{!   !}   !}!{{!   !}   !{!   !} {!   !}!}{!   !}}!  {!   !}!  {!  {!   !}!}!}!}!  {{!   !}   !}!{!   !} {!  {!   !}!}!}!}!  {{!   !}   !}!{!   !} {!  {!   !}!}!}!}! {{{!   !}   !} {!   !} {!  {!   !}!}}{!   !{{!   !}   !}!{!   !}!{!  {!   !}!}  !}! {{{!   !}   !} {!   !} {!  {!   !}!}} !}! {{{!   !}   !} {!   !} {!  {!   !}!}} !}! {!{!   !}  !}{!{!   !} {!  {!   !}!}!}   !} {!   !}}! {! {!   !} {!  {!   !}!}} !}! {!{!   !}  !}! {!   !}{!   {!   !}}{!   !}} {!   !}}! {! {!   !} !}! {!   !} !} !}! {!{!   !}  !}!{!   !}{!   !{!   !}{!   !}!} {!   !}}! {!   !}!  {!   {!   !}}!} !}! {!{!   !}  !}!{!   !} {!   {!   !}}!} !}! {!{!   !}  !}!{!   !} {!   {!   !}}!} !}! {!{!   !}  !}!{!   !} {!   {!   !}}!} !}! {!{!   !}  !}!{!   !} {!   {!   !}}!} !}! {!{!   !}  !}!{!   !} {!   {!   !}}!} !}! {!{!   !}  !}!{!   !} {!   {!   !}}!} !}! {!{!   !}  !}!{!   !} {!   {!   !}}!} !}! {!{!   !}  !}!{!   !} {!   {!   !}}!} !}! {!{!   !}  !}!{!   !} {!   {!   !}}!} !}! {!{!   !}  !}!{!   !} {!   {!   !}}!} !}! {!{!   !}  !}!{!   !} {!   {!   !}}!} !}! {!{!   !}  !}!{!   !} {!   {!   !}}!} !}! {!{!   !}  !}!{!   !} {!   {!   !}}!} !}! {!   !}!{!   !}!   !} {!   !}!} !}! {{{{!   !}   !}   !}   !}!{!   !}{!   !}{!  {!   !}!}!} !}! {!   !}!{!   !} {!   !}!} !}! {{!   !}   !}!{!   !} {!  {!   !}!}!} !}! {{!   !}   !}!{!   !} {!  {!   !}!}!} !}! {{!   !}   !}!{!   !} {!  {!   !}!}!} !}! {{!   !}   !}!{!   !} {!  {!   !}!}!} !}! {!   !}{!   !}{!   !} {!   !}!} !}! {{{!   !}   !}   !}!   !}!{!   !{!   !} {! {!   !} !}!} !}! {!   !}!{!   !} {!   !}!} !}! {!   !}!   !}!{!   !} {! {!   !} !}!} !}! {!   !}!   !}!{!   !} {! {!   !} !}!} !}! {!   !}!   !}!{!   !} {! {!   !} !}!} !}! {!   !}!   !}!{!   !} {! {!   !} !}!} !}! {!   !}!   !}!{!   !} {! {!   !} !}!} !}! {!   !}!   !}!{!   !} {! {!   !} !}!} !}! {!   !}!   !}!{!   !} {! {!   !} !}!} !}! {!   !}!   !}!{!   !} {! {!   !} !}!} !}! {!   !}!   !}!{!   !} {! {!   !} !}!} !}! {!   !}!   !}!{!   !} {! {!   !} !}!} !}!{!   !}{!   !}!   !}!{!   !} {!{!   !}{!   !} !}!} !}! {!   !}!{!   !} {!   !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!}!   {!   !}{!   !}!{!   !} {!{!   !}  !}!} !}{{!   !}{!   !}!{!   !} {!{!   !}  !}!}  !}{!   !}{!   !}!{!   !} {!{!   !}  !}!}re 
{!   !}{!   !}!{!   !} {!{!   !}  !}!}have{!   !}{!   !}!{!   !} {!{!   !}  !}!} Σ[ {!   !}{!   !}!{!   !} {!{!   !}  !}!}∈ ℕ {!   !}{!   !}!{!   !} {!{!   !}  !}!}(adj{!   !}{!   !}!{!   !} {!{!   !}  !}!}t (r{!   !}{!   !}!{!   !} {!{!   !}  !}!} n x{!   !}{!   !}!{!   !} {!{!   !}  !}!} ≡ n{!   !}{!   !}!{!   !} {!{!   !}  !}!}m x {!   !}{!   !}!{!   !} {!{!   !}  !}!} hav{!   !}{!   !}!{!   !} {!{!   !}  !}!}= tr{!   !}{!   !}!{!   !} {!{!   !}  !}!}{X} {!   !}{!   !}!{!   !} {!{!   !}  !}!}
  h{!   !}{!   !}!{!   !} {!{!   !}  !}!}e' :{!   !}{!   !}!{!   !} {!{!   !}  !}!}[ n {!   !}{!   !}!{!   !} {!{!   !}  !}!}ℕ ] {!   !}{!   !}!{!   !} {!{!   !}  !}!}djus{!   !}{!   !}!{!   !} {!{!   !}  !}!}(run{!   !}{!   !}!{!   !} {!{!   !}  !}!} x'){!   !}{!   !}!{!   !} {!{!   !}  !}!}≡ no{!   !}{!   !}!{!   !} {!{!   !}  !}!} x' {!   !}{!   !}!{!   !} {!{!   !}  !}!} hav{!   !}{!   !}!{!   !} {!{!   !}  !}!} =  {!   !}{!   !}!{!   !} {!{!   !}  !}!}  {! {!   {!   !}}!{!   !} {!   !}!{!   !} !}!{!   !}{!   !}!{!   !} {!{!   !}  !}!}tr{!{!   !}{!   !}!{!   !} {!{!   !}  !}!} !} {!   !}{!   !}!{!   !} {!{!   !}  !}!}} {!{!   !}{!   !} {!   !}}{!{!   !}  !}e{!   {!   !}{!   !}0{!   !}{{!{!   !}  !}   !}){!   !}{!   !}!{!   !} {!{!   !}  !}!} {{!{!   !}{!   !} {!   !}}{!{!   !}  !} {!   {!   !}}!}{! {!{!   !} {!{!   !}  !}!} !}{{!   !}{!   !} {!   !}!{!{!   !}  !}r{!   {!   !}} {X} {!{!   !}  !{!   !}set{!   !}{!   !}{!   !}i{!   !}c x{!   !}!   !}) ={{!   !}   !}{{!   !} {!  {!   !}!} !}{!   {!   !}}{! {!   !} {!   !{!   !}}{!   !}y {!   !}X} (set1 ({!   !}e{!   !}!   !} {! {!   !} !} x₁)) = {!   {!{!   !}  !}}{!   {!   !}}{{!   !}   !}ry {{!   !}} ({!   !}{!   !}t1 (set0{!   !}x)){!   !}= {!   !}{{!   !}   !}{!   !}ry{!  {!   !}!}{X} (set{!   !} (set1 x)) = {!   {!   !}}{!   !}{!{!   !}  !}--init :  {X :{!   !}Type} → ℕ {!   !} FreeStAlg X →  Fr{!   !}eStAlg X 
{!   !}-init {X} n t = ru{!   !} {X} n (ge{!   !} (set0 t) (set1 t){!   !}
-}
_ : run {!   !}00 exp ≡ get (set0{!   !}(inc 1)) ({!   !}nc 7) 
_ = refl

r{!   !}cord Split{!   !}dem {C : Category {!   !} _ }(A B :{!   !}ob C) : Type where{!   !} 
  field {!   !}    e : C [ A , A {!   !} 
    sec {!   !} C [ A , B ] 
    {!   !}et : C [ B{!   !}, A ] 
    rs≡id :{!   !}ret ⋆⟨ C ⟩{!   !}sec ≡ C .id {B}
  {!   !} e≡sr : se{!   !} ⋆⟨ C ⟩ ret ≡ e

o{!   !}en SplitId{!   !}m

module _ 
  {C {!   !} Category {!   !} _ }
  {A B B' : o{!   !} C}
  (s :{!   !}SplitIdem {C} A B){!   !}
  (iso : {!   !}atIso C B B' ) whe{!   !}e

  new :{!   !}SplitIdem {C} A B'{!   !}  new .e ={!   !}e s
  new .sec = s{!   !}c s ⋆⟨ C ⟩{!   !}iso .fst
  new .re{!   !} = isIso.i{!   !}v (iso .snd) ⋆⟨ C {!   !} ret s
  n{!   !}w .rs≡id = C .⋆Ass{!   !}c _ _ _  ∙{!   !}cong (λ h → (C ⋆ i{!   !}Iso.inv (i{!   !}o .snd)) h) (sym ({!   !} .⋆Assoc _{!   !}_ _) ∙ cong (λ h →{!   !} (C ⋆ h) ({!   !}so .fst)) (rs≡id s{!   !} ∙ C .⋆IdL{!   !}_) ∙ isIso.sec (is{!   !} .snd)
  new .e≡{!   !}r = (C .⋆Assoc _ _{!   !}_ ∙ cong (λ h → {!   !}C ⋆ sec s) h)  (sy{!   !} (C .⋆Assoc _ _ {!   !}) ∙ cong (λ h → (C{!   !}⋆ h) (ret s)) (i{!   !}Iso.ret (iso .snd){!   !} ∙ C .⋆IdL _)) ∙{!   !}e≡sr s

example : {!   !}X : Type) → Spli{!   !}Idem {SET _} (Free{!   !}tAlg X , {!   !}{!   !}{!   !}State X , {!   !}{!   !}{!   !}example X .e = norm {X}
example X .sec = eval
example X .ret = nf
example X .rs≡id = funExt isId
example X .e≡sr = refl


data FreeStMod (X : Type) : Type where 
  inc : X → FreeStMod X 
  get : FreeStMod X → FreeStMod X → FreeStMod X  
  set0 set1 : FreeStMod X → FreeStMod X 
  -- look like reduction rules
  s0g : {M N : FreeStMod X} → set0 (get M N) ≡ set0 M  
  s1g : {M N : FreeStMod X} → set1 (get M N) ≡ set1 N  
  s0s0 : {M : FreeStMod X} → set0 (set0 M) ≡ set0 M 
  s0s1 : {M : FreeStMod X} → set0 (set1 M) ≡ set1 M 
  s1s0 : {M : FreeStMod X} → set1 (set0 M) ≡ set0 M 
  s1s1 : {M : FreeStMod X} → set1 (set1 M) ≡ set1 M 
  gg : {M N L P : FreeStMod X} → get (get M N) (get L P) ≡ get M P
  gs : {M N : FreeStMod X} → get (set0 M) (set1 N) ≡ get M N
  gid : {M : FreeStMod X} → get M M ≡ M 



-- this exists by initiality, manual definition for easy goals 
eval' : {X : Type} → FreeStMod X → State X 
eval' {X} (inc x) = return x
eval' {X} (get x x') = stget (eval' x) (eval' x')
eval' {X} (set0 x) = stset0 (eval' x)
eval' {X} (set1 x) = stset1 (eval' x)
eval' {X} (s0g {M} i) b = eval' M false
eval' {X} (s1g {_}{N} i) b = eval' N true
eval' {X} (s0s0 {M} i) b = eval' M false
eval' {X} (s0s1 {M} i) b = eval' M true
eval' {X} (s1s0 {M} i) b = eval' M false
eval' {X} (s1s1 {M} i) b = eval' M true
eval' {X} (gg {M} {N} {L} {P} i) false = eval' M false
eval' {X} (gg {M} {N} {L} {P} i) true = eval' P true
eval' {X} (gs {M} {N} i) false = eval' M false
eval' {X} (gs {M} {N} i) true = eval' N true
eval' {X} (gid {M} i) false = eval' M false
eval' {X} (gid {M} i) true = eval' M true

-- also the initial map
nf' : {X : Type} → State X → FreeStMod X  
nf' {X} s = 
  get 
    (let (b , x) = s false in (if b then set1 (inc x) else set0 (inc x))) 
    (let (b , x) = s true in (if b then set1 (inc x) else set0 (inc x)))

-- these are iso in the category of models 
initIso : {X : Type} → CatIso (SET ℓ-zero) (State X , {!   !}) (FreeStMod X , {!   !})
initIso .fst = nf'
initIso .snd .isIso.inv = eval'
initIso .snd .isIso.sec = {!   !}
initIso .snd .isIso.ret = {!   !}

si :  {X : Type} →  SplitIdem {SET _} (FreeStAlg X , {!   !}) (FreeStMod X , {!   !}) 
si {X} = new {SET _}{B = State X , {!  !}} (example X) (initIso {X})

-}

{-
data Ops : Type where 
  get set0 set1 : Ops 

data Eqns : Type where 
  -- set set - overwrites 
  s0s0 s0s1 s1s0 s1s1 : Eqns
  -- set get
  s0g s1g : Eqns
  -- get get 
  gg : Eqns
  -- get set 
  gs : Eqns
  -- needless branch
  gmm : Eqns

ΣSt : Signature 
ΣSt .Op = Ops
ΣSt .arity get = 2
ΣSt .arity set0 = 1
ΣSt .arity set1 = 1

getTerm : {n : ℕ} → Term ΣSt n → Term ΣSt n → Term ΣSt n
getTerm M N = app get (λ {zero → M
                        ; one → N })

set0Term : {n : ℕ} → Term ΣSt n → Term ΣSt n 
set0Term M = app set0 (λ {zero → M })        

set1Term : {n : ℕ} → Term ΣSt n → Term ΣSt n 
set1Term M = app set1 (λ {zero → M })     

TSt : Theory 
TSt .Sig = ΣSt
TSt .Eq = Eqns
TSt .ax s0s0 = record { ctx = 1 ; lhs = set0Term (set0Term (var zero)) ; rhs = set0Term (var zero) }
TSt .ax s0s1 = record { ctx = 1 ; lhs = set0Term (set1Term (var zero)) ; rhs = set1Term (var zero) }
TSt .ax s1s0 = record { ctx = 1 ; lhs = set1Term (set0Term (var zero)) ; rhs = set0Term (var zero) }
TSt .ax s1s1 = record { ctx = 1 ; lhs = set1Term (set1Term (var zero)) ; rhs = set1Term (var zero) }
TSt .ax s0g = record { ctx = 2 ; lhs = set0Term (getTerm (var zero) (var one)) ; rhs = set0Term (var zero) }
TSt .ax s1g = record { ctx = 2 ; lhs = set1Term (getTerm (var zero) (var one)) ; rhs = set1Term (var one) }
TSt .ax gg = record { ctx = 4 ; lhs = getTerm (getTerm (var zero) (var one)) (getTerm (var two) (var three)) ; rhs = getTerm (var zero) (var three) }
TSt .ax gs = record { ctx = 2 ; lhs = getTerm (set0Term (var zero)) (set1Term (var one)) ; rhs = getTerm (var zero) (var one) }
TSt .ax gmm = record { ctx = 1 ; lhs = getTerm (var zero) (var zero) ; rhs = var zero }


mget : {M : ob (MOD TSt)} → ⟨ M .fst .Carrier ⟩ → ⟨ M .fst .Carrier ⟩ → ⟨ M .fst .Carrier ⟩
mget {M} t1 t2 = M .fst .interp get λ {zero → t1
                                     ; one → t2}

mset0 : {M : ob (MOD TSt)} → ⟨ M .fst .Carrier ⟩ → ⟨ M .fst .Carrier ⟩ 
mset0 {M} t = M .fst .interp set0 λ {zero → t}      

mset1 : {M : ob (MOD TSt)} → ⟨ M .fst .Carrier ⟩ → ⟨ M .fst .Carrier ⟩ 
mset1 {M} t = M .fst .interp set1 λ {zero → t}    

-- some lambda bullshit
mset0set0 : {M : ob (MOD TSt)} → (t : ⟨ M .fst .Carrier ⟩) → mset0 {M} (mset0 {M} t) ≡ mset0 {M} t 
mset0set0 {M} t = 
  subst2 (λ h h' → h ≡ h') 
    (cong (λ h → interp (M .fst) set0 h) (funExt (λ {zero → cong (λ h → interp (M .fst) set0 h) (funExt λ {zero → refl})}))) 
    ((cong (λ h → interp (M .fst) set0 h)) (funExt (λ {zero → refl})))  
    (M .snd s0s0 λ {zero → t})

mget2 : {M : ob (MOD TSt)} → (t : ⟨ M .fst .Carrier ⟩) → mget {M} t t ≡ t 
mget2 {M} t = {!   !}

mset1get : {M : ob (MOD TSt)} → (t t' : ⟨ M .fst .Carrier ⟩) → mset1 {M} (mget {M} t t') ≡ mset1 {M} t' 
mset1get {M} t t' = {!   !}

data FreeSt (X : Type) : Type where 
  inc : X → FreeSt X 
  get : FreeSt X → FreeSt X → FreeSt X  
  set0 set1 : FreeSt X → FreeSt X 
  -- look like reduction rules
  eq₁ : {M N : FreeSt X} → set0 (get M N) ≡ set0 M  
  eq₂ : {M N : FreeSt X} → set1 (get M N) ≡ set1 N  
  eq₃ : {M : FreeSt X} → set0 (set0 M) ≡ set0 M 
  eq₄ : {M : FreeSt X} → set0 (set1 M) ≡ set1 M 
  eq₅ : {M : FreeSt X} → set1 (set0 M) ≡ set0 M 
  eq₆ : {M : FreeSt X} → set1 (set1 M) ≡ set1 M 
  eq₇ : {M N L P : FreeSt X} → get (get M N) (get L P) ≡ get M P
  eq₈ : {M N : FreeSt X} → get (set0 M) (set1 N) ≡ get M N
  eq₉ : {M : FreeSt X} → get M M ≡ M 

freeHIT : Type → ob (MOD TSt) 
freeHIT X .fst .Carrier = FreeSt X , {!   !}
freeHIT X .fst .interp get args = get (args zero) (args one)
freeHIT X .fst .interp set0 args = set0 (args zero)
freeHIT X .fst .interp set1 args = set1 (args zero)
freeHIT X .snd s0s0 args = eq₃
freeHIT X .snd s0s1 args = eq₄
freeHIT X .snd s1s0 args = eq₅
freeHIT X .snd s1s1 args = eq₆
freeHIT X .snd s0g args = eq₁
freeHIT X .snd s1g args = eq₂
freeHIT X .snd gg args = eq₇
freeHIT X .snd gs args = eq₈
freeHIT X .snd gmm args = eq₉


hitInitial' : {X : Type}{M : ob (MOD TSt)} → (X → ⟨ M .fst .Carrier ⟩) → FreeSt X → fst (M .fst .Carrier) 
hitInitial' {X} {M} f (inc x) = f x
hitInitial' {X} {M} f (get x x₁) = mget {M} (hitInitial' {X}{M} f x) (hitInitial' {X}{M} f x₁) 
hitInitial' {X} {M} f (set0 x) = mset0 {M} (hitInitial' {X}{M} f x)
hitInitial' {X} {M} f (set1 x) = mset1 {M} (hitInitial' {X}{M} f x)
hitInitial' {X} {M} f (eq₁ i) = {! (M .snd s0g ?  ∙ ?) i  !}
hitInitial' {X} {M} f (eq₂ i) = {!   !}
hitInitial' {X} {M} f (eq₃ {N} i) = goal i where 
  goal : mset0 {M} (mset0 {M} (hitInitial' {X}{M} f N)) ≡ mset0 {M} (hitInitial' {X}{M} f N)
  goal = mset0set0 {M} (hitInitial' f N)

hitInitial' {X} {M} f (eq₄ i) = {!   !}
hitInitial' {X} {M} f (eq₅ i) = {!   !}
hitInitial' {X} {M} f (eq₆ i) = {!   !}
hitInitial' {X} {M} f (eq₇ i) = {!   !}
hitInitial' {X} {M} f (eq₈ i) = {!   !}
hitInitial' {X} {M} f (eq₉ i) = {!   !}

hitInitial : {X : Type}{M : ob (MOD TSt)} → (X → ⟨ M .fst .Carrier ⟩) → MOD TSt [ freeHIT X , M ] 
hitInitial {X} {M} f .carmap = hitInitial' {X}{M} f
hitInitial {X} {M} f .pres get args = cong (λ h → interp (M .fst) get h) (funExt λ {zero → refl
                                                                                  ; one → refl})
hitInitial {X} {M} f .pres set0 args = cong (λ h → interp (M .fst) set0 h) (funExt λ {zero → refl})
hitInitial {X} {M} f .pres set1 args = cong (λ h → interp (M .fst) set1 h) (funExt λ {zero → refl})


hitInitialEq : {X : Type}{M : ob (MOD TSt)}{f g : MOD TSt [ freeHIT X , M ]} → 
  ((x : X) → f .carmap (inc x) ≡ g .carmap (inc x)) → 
  f ≡ g
hitInitialEq {X}{M}{f}{g} prf = AlgHom≡ (funExt go) where 
  go : (x : FreeSt X) → f .carmap x ≡ g .carmap x 
  go (inc x) = prf x
  go (get x x₁) = f .pres get (λ {zero → x
                                ; one → x₁}) ∙ cong (λ h → interp (M .fst) get h) (funExt (λ {zero → go x
                                                                                            ; one → go x₁})) ∙ sym (g .pres get λ {zero → x
                                                                           ; one → x₁ } )
  go (set0 x) = f .pres set0  (λ {zero → x}) ∙ cong (λ h → interp (M .fst) set0 h)  (funExt (λ {zero → go x})) ∙ sym (g .pres set0 λ {zero → x} )
  go (set1 x) = f .pres set1  (λ {zero → x}) ∙ cong (λ h → interp (M .fst) set1 h)  (funExt (λ {zero → go x})) ∙ sym (g .pres set1 λ {zero → x} )
  go (eq₁ {M'}{N} i) = M .fst .Carrier .snd  (f .carmap (eq₁ i)) (g .carmap (eq₁ i)) _ _  i
  go (eq₂ i) = M .fst .Carrier .snd  (f .carmap (eq₂ i)) (g .carmap (eq₂ i)) _ _  i
  go (eq₃ i) = {!   !}
  go (eq₄ i) = {!   !}
  go (eq₅ i) = {!   !}
  go (eq₆ i) = {!   !}
  go (eq₇ i) = {!   !}
  go (eq₈ i) = {!   !}
  go (eq₉ {N} i) = {!   !}

State : Type → Type 
State X = Bool → Bool × X

stget : {X : Type} → State X → State X → State X 
stget f g false = f false
stget f g true = g true

stset0 : {X : Type} → State X → State X 
stset0 f _ = f false

stset1 : {X : Type} → State X → State X 
stset1 f _ = f true

return : {X : Type} → X → State X 
return x s = s , x

freeST : Type → ob (MOD TSt ) 
freeST x .fst .Carrier = (State x) , {!   !}
freeST x .fst .interp get args = stget (args zero) (args one)
freeST x .fst .interp set0 args = stset0 (args zero)
freeST x .fst .interp set1 args = stset1 (args zero)
freeST x .snd s0s0 args = refl
freeST x .snd s0s1 args = refl
freeST x .snd s1s0 args = refl
freeST x .snd s1s1 args = refl
freeST x .snd s0g args = refl
freeST x .snd s1g args = refl
freeST x .snd gg args i false = args zero false
freeST x .snd gg args i true = args three true
freeST x .snd gs args i false = args zero false
freeST x .snd gs args i true = args one true
freeST x .snd gmm args i false = args zero false
freeST x .snd gmm args i true = args zero true


{- 
  tabulate the results 



-}

cf : {X : Type}{M : ob (MOD TSt)} →  (X → ⟨ M .fst .Carrier ⟩)  → State X → ⟨ M .fst .Carrier ⟩ 
cf {X}{M} f s = 
    mget{M} 
      (let (b , x) = s false in (if b then mset1 {M} (f x) else mset0 {M} (f x) )) 
      (let (b , x) = s true  in (if b then mset1 {M} (f x) else mset0 {M} (f x) ))


nf : {X : Type} → State X → FreeSt X
nf {X} s = 
  get 
    (let (b , x) = s false in (if b then set1 (inc x) else set0 (inc x))) 
    (let (b , x) = s true  in (if b then set1 (inc x) else set0 (inc x)))

stToHit : {X : Type} → MOD TSt [ freeST X , freeHIT X ] 
stToHit {X} .carmap = nf
stToHit {X} .pres get args = sym eq₇
stToHit {X} .pres set0 args with (args zero false .fst) 
... | false = (eq₉ ∙ sym eq₃) ∙ sym eq₁
... | true = (eq₉ ∙ sym eq₄) ∙ sym eq₁
stToHit {X} .pres set1 args with (args zero true .fst) 
... | false = eq₉ ∙ sym eq₅ ∙ sym eq₂
... | true = eq₉ ∙ sym eq₆ ∙ sym eq₂

initIso : (X : Type) → CatIso (MOD TSt) (freeHIT X) (freeST X) 
initIso X .fst = hitInitial {X}{freeST X} return
initIso X .snd .isIso.inv = stToHit {X}
initIso X .snd .isIso.sec = {!   !}
initIso X .snd .isIso.ret = hitInitialEq {X}{freeHIT X} λ x → eq₈ ∙ eq₉

get' : {X : Type} → FreeOn ΣSt X → FreeOn ΣSt X → FreeOn ΣSt X
get' M N = ops get λ {zero → M
                    ; one → N}

set0' : {X : Type} → FreeOn ΣSt X → FreeOn ΣSt X
set0' M = ops set0 λ{zero → M}

set1' : {X : Type} → FreeOn ΣSt X → FreeOn ΣSt X
set1' M = ops set1 λ{zero → M}

nf' : {X : Type} → State X → FreeOn ΣSt X
nf' {X} s = get' 
    (let (b , x) = s false in (if b then set1' (inc x) else set0' (inc x))) 
    (let (b , x) = s true  in (if b then set1' (inc x) else set0' (inc x)))

eval' : {X : Type} → FreeOn ΣSt X → State X 
eval' {X} (inc x) = return x
eval' {X} (ops get args) = stget (eval' (args zero)) (eval' (args one))
eval' {X} (ops set0 args) = stset0 (eval' (args zero))
eval' {X} (ops set1 args) = stset1 (eval' (args zero))

isId : {X : Type} → (s : State X) → eval' {X} (nf' {X} s) ≡ s 
isId {X} s = funExt λ {false → {!   !}
                     ; true → {!   !}}



-}
























































{-

-- no , cant do this b/c we don't have equations
hmm : {X : Type} → ALG ΣSt [ freeST X .fst , FreeAlg ΣSt X ] 
hmm {X} .carmap = nf' {X}
hmm {X} .pres get args = {!   !}
hmm {X} .pres set0 args = {!   !}
hmm {X} .pres set1 args = {!   !}


eval : {X : Type} → FreeSt X → State X 
eval {X} x = {!   !}
ex : {X : Type} → SplitEpi {SET _} ((FreeOn ΣSt X) , {!   !}) ((FreeSt X) , {!   !}) 
ex {X} .fst = FreeAlgMorphism {ΣSt}{X}{freeHIT X .fst} inc .carmap
ex {X} .snd .fst hit = nf' (hitInitial {X}{freeST X} return .carmap hit)
ex {X} .snd .snd = funExt {!   !}

{-
-- no, can't define this in alg, the map back into algebras can't be shown to preserve operations
ex : {X : Type} → SplitEpi {ALG ΣSt} (FreeAlg ΣSt X) (freeHIT X .fst) 
ex {X} .fst = FreeAlgMorphism {ΣSt}{X}{freeST X .fst} return ⋆⟨ ALG ΣSt ⟩ stToHit
ex {X} .snd .fst = hitInitial {X}{freeST X} return ⋆⟨ ALG ΣSt ⟩ hmm
ex .snd .snd = {!   !}
-}

{-

data FreeStMod (X : Type) : Type where 
  inc : X → FreeStMod X 
  get : FreeStMod X → FreeStMod X → FreeStMod X  
  set0 set1 : FreeStMod X → FreeStMod X 
  -- look like reduction rules
  eq₁ : {M N : FreeStMod X} → set0 (get M N) ≡ set0 M  
  eq₂ : {M N : FreeStMod X} → set1 (get M N) ≡ set1 N  
  eq₃ : {M : FreeStMod X} → set0 (set0 M) ≡ set0 M 
  eq₄ : {M : FreeStMod X} → set0 (set1 M) ≡ set1 M 
  eq₅ : {M : FreeStMod X} → set1 (set0 M) ≡ set0 M 
  eq₆ : {M : FreeStMod X} → set1 (set1 M) ≡ set1 M 
  eq₇ : {M N L P : FreeStMod X} → get (get M N) (get L P) ≡ get M P
  eq₈ : {M N : FreeStMod X} → get (set0 M) (set1 N) ≡ get M N
  eq₉ : {M : FreeStMod X} → get M M ≡ M 


ModAlg : Type → Alg ΣSt
ModAlg X .Carrier = FreeStMod X , {!   !}
ModAlg X .interp get args = get (args zero) (args one)
ModAlg X .interp set0 args = set0 (args zero)
ModAlg X .interp set1 args = set1 (args zero)

get' : {X : Type} → FreeOn ΣSt X → FreeOn ΣSt X → FreeOn ΣSt X
get' M N = ops get λ {zero → M
                    ; one → N}

set0' : {X : Type} → FreeOn ΣSt X → FreeOn ΣSt X
set0' M = ops set0 λ{zero → M}

set1' : {X : Type} → FreeOn ΣSt X → FreeOn ΣSt X
set1' M = ops set1 λ{zero → M}

State : Type → Type 
State X = Bool → Bool × X

stget : {X : Type} → State X → State X → State X 
stget f g false = f false
stget f g true = g true

stset0 : {X : Type} → State X → State X 
stset0 f _ = f false

stset1 : {X : Type} → State X → State X 
stset1 f _ = f true

return : {X : Type} → X → State X 
return x s = s , x

StAlg : Type → Alg ΣSt 
StAlg X .Carrier = State X , {!   !}
StAlg X .interp get args = stget (args zero) (args one)
StAlg X .interp set0 args = stset0 (args zero)
StAlg X .interp set1 args = stset1 (args zero)

SplitEpi : {C : Category _ _ } → ob C → ob C → Type 
SplitEpi {C} A B = 
  Σ[ sec ∈ C [ A , B ] ] 
  Σ[ ret ∈ C [ B , A ] ] 
    ret ⋆⟨ C ⟩ sec ≡ C .id {B} 


eval : {X : Type} → FreeStMod X → State X 
eval (inc x) = return x
eval (get M N) = stget (eval M) (eval N)
eval (set0 M) = stset0 (eval M)
eval (set1 M) = stset1 (eval M)
eval (eq₁ {M}{N} i) b = eval M false
eval (eq₂ {M}{N} i) b = eval N true
eval (eq₃ {M} i) b = eval M false
eval (eq₄ {M} i) b = eval M true
eval (eq₅ {M} i) b = eval M false
eval (eq₆ {M} i) b = eval M true
eval (eq₇ {M} {N} {L} {P} i) false = eval M false
eval (eq₇ {M} {N} {L} {P} i) true = eval P true
eval (eq₈ {M} {N} i) false = eval M false
eval (eq₈ {M} {N} i) true = eval N true
eval (eq₉ {M} i) false = eval M false
eval (eq₉ {M} i) true = eval M true

hmm : {X : Type} → (M N P : FreeStMod X) → FreeStMod X 
hmm M N P = set0 (get (set1 (get M N)) (set1 (set0 P)))

compd : {X : Type} → (M N P : FreeStMod X)(b : Bool) → 
  eval (set0 (get (set1 (get M N)) (set1 (set0 P)))) b ≡ eval N true 
compd M N P b = refl

reify : {X : Type} → State X  → FreeStMod X 
reify f = 
  get 
    (
      let (b , x) = f false 
      in (
        if b 
        then set1 (inc x) 
        else set0 (inc x))
    )( 
      let (b , x) = f true
      in (
        if b 
        then set1 (inc x) 
        else set0 (inc x))
    )

reify' : {X : Type} → State X  → FreeOn ΣSt X
reify' f = get' 
    (
      let (b , x) = f false 
      in (
        if b 
        then set1' (inc x) 
        else set0' (inc x))
    )( 
      let (b , x) = f true
      in (
        if b 
        then set1' (inc x) 
        else set0' (inc x))
    )

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl

proof : {X : Type} → (s : State X) → eval (reify s) ≡ s
proof s = funExt sub where 
  sub : (x : Bool) →
    stget
    (eval
    (if s false .fst then set1 (inc (s false .snd)) else
      set0 (inc (s false .snd))))
    (eval
    (if s true .fst then set1 (inc (s true .snd)) else
      set0 (inc (s true .snd))))
    x
    ≡ s x
  sub false with (s false .fst)
  ... | false = ΣPathP ({!   !} , refl) -- yes, but need to inspect to get path
  ... | true = ΣPathP ({!   !} , refl)
  sub true with (s true .fst)
  ... | false = ΣPathP ({!   !} , refl)
  ... | true = ΣPathP ({!   !} , refl)

ex : {X : Type} → SplitEpi {SET _ } (FreeStMod X , {!   !}) (State X , {!   !}) 
ex .fst = eval
ex .snd .fst = reify
ex {X} .snd .snd = funExt proof

reduce :  {X : Type} → FreeStMod X → FreeStMod X
reduce {X} M = reify (eval M)

idem :  {X : Type} → (M : FreeStMod X) → reduce (reduce M) ≡ reduce M 
idem M = goal where 
  goal : reify (eval (reify (eval M))) ≡ reify (eval M) 
  goal = cong reify (proof (eval M))
  

inc' :  {X : Type} → FreeOn ΣSt X → FreeStMod X 
inc' {X} = FreeAlgMorphism {ΣSt} {X} {ModAlg X} inc .carmap

proof' : {X : Type} → (m : FreeStMod X ) → inc' (reify' (eval m)) ≡ m 
-- get (set0 (inc x)) (set1 (inc x)) ≡ inc x
proof' (inc x) = eq₈ ∙ eq₉
proof' (get m m₁) = cong₂ (λ h h' → get h h') ({!   !} ∙ proof' m) {!   !}
  --  cong₂ get (proof' m) (proof' m₁) ∙ ?
proof' (set0 m) with (eval m false .fst) 
... | false = eq₉ ∙ {!   !}
-- cong set0 (proof' m)
... | true =  {!   !} -- this is false
proof' (set1 m) = {!   !}
proof' (eq₁ i) = {!   !}
proof' (eq₂ i) = {!   !}
proof' (eq₃ i) = {!   !}
proof' (eq₄ i) = {!   !}
proof' (eq₅ i) = {!   !}
proof' (eq₆ i) = {!   !}
proof' (eq₇ i) = {!   !}
proof' (eq₈ i) = {!   !}
proof' (eq₉ i) = {!   !}

ex' :  {X : Type} → SplitEpi {SET _ } (FreeOn ΣSt X , {!   !}) (FreeStMod X , {!   !}) 
ex' {X} .fst = inc'
ex' .snd .fst m = reify' (eval m)
ex' .snd .snd = funExt proof'


  {-funExt goal where 
  goal : (s : State X) →  stget
    (eval
    (if s false .fst then set1 (inc (s true .snd)) else
      set0 (inc (s false .snd))))
    (λ s₁ → s₁ , s true .snd)
    ≡ s
  goal s = funExt sub where 
    sub : (x : Bool) →
      stget
      (eval
      (if s false .fst then set1 (inc (s true .snd)) else
        set0 (inc (s false .snd))))
      (λ s₁ → s₁ , s true .snd) x
      ≡ s x 
    sub false with inspect (s false .fst) 
    ... | false with≡ x = ΣPathP ({!   !} , {!   !})
    ... | true with≡ x = {!   !}
    sub true = {!   !}

-}


example' : {X : Type} → SplitEpi {SET _ } ((FreeOn  ΣSt X) , {!   !}) ((State X) , {!   !}) 
example' {X} .fst = FreeAlgMorphism {ΣSt} {X} {StAlg X} return .carmap
example' .snd .fst f = {!   !}
  --get' (set0' (inc (f false .snd))) (set1' (inc (f true .snd)))
example' .snd .snd = funExt λ f → funExt λ {false → ΣPathP ({! refl  !} , refl)
                                          ; true → ΣPathP ({!   !} , refl)}









example : {X : Type} → SplitEpi {ALG ΣSt} (FreeAlg ΣSt X) (StAlg X) 
example .fst = FreeAlgMorphism return
example .snd .fst .carmap f = get' (set0' (inc (f false .snd))) (set1' (inc (f true .snd)))
example .snd .fst .pres get args = cong₂ ops refl (funExt λ {zero → {!   !}
                                                           ; one → {!   !}})
example .snd .fst .pres set0 args = {!   !}
example .snd .fst .pres set1 args = {!   !}
example .snd .snd = {!   !}



-}

{-

get' : {n : ℕ} →  Term ΣSt n → Term ΣSt n → Term ΣSt n 
get' m n = app get λ {zero → m
                    ; one → n}

set0' : {n : ℕ} →  Term ΣSt n → Term ΣSt n 
set0' m = app set0 λ {zero → m}

set1' : {n : ℕ} →  Term ΣSt n → Term ΣSt n 
set1' m = app set1 λ {zero → m}

TSt : Theory 
TSt .Sig = ΣSt
TSt .Eq = Eqns
TSt .ax β₁ = record { ctx = 2 ; lhs = get' (set0' (var zero)) (set0' (var one)) ; rhs = set0' (var zero) }
TSt .ax β₂ = record { ctx = 2 ; lhs = get' (set1' (var zero)) (set1' (var one)) ; rhs = set1' (var one) }
TSt .ax ss₁ = record { ctx = 1 ; lhs = set0' (set1' (var zero)) ; rhs = set0' (var zero) }
TSt .ax ss₂ = record { ctx = 1 ; lhs = set1' (set0' (var zero)) ; rhs = set1' (var zero) }
TSt .ax gg = record { ctx = 4 ; lhs = get' (get' (var zero) (var one)) (get' (var two) (var three)) ; rhs = get' (get' (var zero) (var two)) (get' (var one) (var three)) }

FreeStAlg : Type → Type 
FreeStAlg = FreeOn ΣSt

data FreeStMod' (X : Type) : Type where 
  inc : X → FreeStMod' X 
  get : FreeStMod' X → FreeStMod' X → FreeStMod' X  
  set0 set1 : FreeStMod' X → FreeStMod' X 
  β₁' : {M N : FreeStMod' X} → get (set0 M) (set0 N) ≡ set0 M
  β₂' : {M N : FreeStMod' X} → get (set1 M) (set1 N) ≡ set1 N
  ss₁' : {M : FreeStMod' X} → set0 (set1 M) ≡ set0 M
  ss₂' : {M : FreeStMod' X} → set1 (set0 M) ≡ set1 M
  gg' : {M M' N N' : FreeStMod' X} → get (get M N) (get M' N') ≡ get (get M M') (get N N')

FreeStMod : Type → ob (MOD TSt) 
FreeStMod X .fst .Alg.Carrier = FreeStMod' X , {!   !}
FreeStMod X .fst .Alg.interp get args = get (args zero) (args one)
FreeStMod X .fst .Alg.interp set0 args = set0 (args zero)
FreeStMod X .fst .Alg.interp set1 args = set1 (args zero)
FreeStMod X .snd β₁ args = β₁'
FreeStMod X .snd β₂ args = β₂'
FreeStMod X .snd ss₁ args = ss₁'
FreeStMod X .snd ss₂ args = ss₂'
FreeStMod X .snd gg args = gg'


FreeModMorphism : {X : Type}{M : ob (MOD TSt)} → 
  (X →  ⟨ M .fst .Carrier ⟩ ) → 
  FreeStMod' X  → ⟨ M .fst .Carrier ⟩
FreeModMorphism {X} {M} f (inc x) = f x
FreeModMorphism {X} {M} f (get x x₁) = M .fst .interp get λ {zero → FreeModMorphism f x
                                                           ; one → FreeModMorphism f x₁}
FreeModMorphism {X} {M} f (set0 x) = M .fst .interp set0 λ {zero → FreeModMorphism f x}
FreeModMorphism {X} {M} f (set1 x) = M .fst .interp set1 λ {zero → FreeModMorphism f x}
FreeModMorphism {X} {M} f (β₁' i) = M .snd {! β₁  !} {!   !} i
FreeModMorphism {X} {M} f (β₂' i) = {!   !}
FreeModMorphism {X} {M} f (ss₁' i) = {!   !}
FreeModMorphism {X} {M} f (ss₂' i) = {!   !}
FreeModMorphism {X} {M} f (gg' i) = {!   !}

FreeModMorphism! : {X : Type}{M : ob (MOD TSt)}{f g : (MOD TSt) [ FreeStMod X , M ]} → 
  (∀ x → f .carmap (inc x) ≡ g .carmap (inc x)) → 
  f ≡ g 
FreeModMorphism! {X}{M}{f}{g} prf = AlgHom≡ (funExt go) where 
  go : (x : FreeStMod' X ) → f .carmap x ≡ g .carmap x
  go (inc x) = prf x
  go (get x x₁) = f .pres get (λ {zero → x
                                ; one → x₁}) ∙ ((λ i → M .fst .interp get (λ a → go {!   !} i))) ∙ sym (g .pres get (λ {zero → x ; one → x₁}))
  go (set0 x) = {!   !}
  go (set1 x) = {!   !}
  go (β₁' i) = {!   !}
  go (β₂' i) = {!   !}
  go (ss₁' i) = {!   !}
  go (ss₂' i) = {!   !}
  go (gg' i) = {!   !}


State : Type → Type 
State X = Bool → Bool × X

stget : {X : Type} → State X → State X → State X 
stget f g false = f false
stget f g true = g true

stset0 : {X : Type} → State X → State X 
stset0 f b = false , (f b .snd)

stset1 : {X : Type} → State X → State X 
stset1 f b = true , (f b .snd)

return : {X : Type} → X → State X 
return x s = s , x

include : {X : Type} → FreeStAlg X → FreeStMod' X 
include (inc x) = inc x
include (ops get args) = get (include (args zero)) (include (args one))
include (ops set0 args) = set0 (include (args zero))
include (ops set1 args) = set1 (include (args zero))


StAlg : Type → Alg ΣSt 
StAlg X .Carrier = State X , {!   !}
StAlg X .interp get args = stget (args zero) (args one)
StAlg X .interp set0 args = stset0 (args zero)
StAlg X .interp set1 args = stset1 (args zero)

StMod : Type → ob (MOD TSt) 
StMod X .fst = StAlg X
StMod X .snd β₁ args = {!   !}
StMod X .snd β₂ args = {!   !}
StMod X .snd ss₁ args = {!   !}
StMod X .snd ss₂ args = {!   !}
StMod X .snd gg args = {!   !}

eval : {X : Type} → (MOD TSt) [ FreeStMod X , StMod X ] 
eval = {!   !}

reify : {X : Type} → State X → FreeStAlg X 
reify f = {!   !}
  -- get (set0 (inc (f false .snd))) (set1 (inc (f true .snd)))

SplitEpi' : {C : Category _ _ } → ob C → ob C → Type 
SplitEpi' {C} A B = 
  Σ[ sec ∈ C [ A , B ] ] 
  Σ[ ret ∈ C [ B , A ] ] 
    ret ⋆⟨ C ⟩ sec ≡ C .id {B} 

foo : {X : Type} → SplitEpi' {ALG ΣSt} (FreeAlg ΣSt X) (StAlg X)
foo {X} .fst = FreeAlgMorphism return
foo {X} .snd .fst .carmap f = {!   !}
foo {X} .snd .fst .pres = {!   !}
foo {X} .snd .snd = {!   !}

StEx : {X : Type} → SplitEpi' {ALG ΣSt} (FreeAlg ΣSt X) (MOD→ALG  TSt .F-ob (FreeStMod  X)) 
StEx .fst = FreeAlgMorphism inc
StEx {X} .snd .fst .carmap = goal where 

  ev : FreeStMod' X → State X 
  ev = FreeModMorphism return

  ref : State X  →  FreeOn ΣSt X 
  ref f = ops get λ {zero → ops set0 λ {zero → inc (f false .snd)}
                   ; one → ops set1 λ {zero → inc (f true .snd)}}

  goal : FreeStMod' X → FreeOn ΣSt X
  goal m = ref (ev m)
StEx .snd .fst .pres = {!   !}
StEx .snd .snd = FreeModMorphism! {!   !} 
-- no.. 
  -- (x : X) → get (set0 (inc x)) (set1 (inc x)) ≡ inc x 
{- 
  we have a normalization procedure that we can factor into s and r 
-} 
record SplitIdem {C : Category _ _ }(A : ob C) : Type where 
  field 
    -- A : Syntax 
    {B} : ob C -- normal forms 
    e : C [ A , A ] -- normalization endomap
    r : C [ A , B ] -- compute normal form
    s : C [ B , A ] -- reconstruct syntax
    rs≡e : r ⋆⟨ C ⟩ s ≡ e
    sr≡id : s ⋆⟨ C ⟩ r ≡ C .id {B}

record SplitEpi {C : Category _ _ }{A B : ob C}(sec : C [ A , B ]) : Type where 
  field 
    ret : C [ B , A ]
    idem : ret ⋆⟨ C ⟩ sec ≡ C .id {B} 

-- eval ; reify should be idempotent
what : {X : Type} → SplitEpi {SET _} (include {X}) 
what .SplitEpi.ret m = {!   !}
what .SplitEpi.idem = {!   !}

record Fork (C : Category _ _ ) : Type where 
  field 
    {X Y Z} : ob C
    f g : C [ X , Y ]
    e : C [ Y , Z ]
    cond : f ⋆⟨ C ⟩ e ≡ g ⋆⟨ C ⟩ e

record SplitCoeq {C : Category _ _ } (fork : Fork C): Type where 
  open Fork fork
  field 
    s : C [ Z , Y ]
    t : C [ Y , X ]
    eq1 : s ⋆⟨ C ⟩ e ≡ C .id {Z}
    eq2 : e ⋆⟨ C ⟩ s ≡ t ⋆⟨ C ⟩ g 
    eq3 : t ⋆⟨ C ⟩ f ≡ C .id {Y}

module EpiToCoeq {C : Category _ _ } {A B : ob C}(sec : C [ A , B ]){splitEpi : SplitEpi {C}{A}{B}sec} where 
  open Fork
  open SplitCoeq 
  open SplitEpi

  fork : Fork C 
  fork .X = B
  fork .Y = B
  fork .Z = A
  fork .f = splitEpi .ret ⋆⟨ C ⟩ sec
  fork .g = C .id {B}
  fork .e = splitEpi .ret
  fork .cond = cong (λ h → seq' C h (splitEpi .ret)) (splitEpi .idem)

  splitCoeq : SplitCoeq {C} fork 
  splitCoeq .s = sec
  splitCoeq .t = C .id {B}
  splitCoeq .eq1 = {!   !} ∙ {! splitEpi .idem  !}
  splitCoeq .eq2 = splitEpi .idem ∙ sym (C .⋆IdL _)
  splitCoeq .eq3 = cong (λ h → (C ⋆ C .id) h) (splitEpi. idem) ∙ C .⋆IdL _
  -}
  -}