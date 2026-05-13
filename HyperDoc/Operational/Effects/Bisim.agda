{-# OPTIONS --type-in-type #-}
module HyperDoc.Operational.Effects.Bisim where 

open import Cubical.Data.Sigma
open import Cubical.Data.Sum 
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Bool 
open import Cubical.Data.Nat

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Functions.Logic hiding (inl ; inr ; ⊥)

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets

open import HyperDoc.Operational.Effects.BiAlgebra
open import HyperDoc.Operational.Graph hiding (FORGET ; FORGETᴰ)

open Category 
open Functor

module D where 
  -- behavior functor of a deterministic automata
  Det : hSet _  → hSet _
  Det X = (Unit* ⊎ ⟨ X ⟩) , isSet⊎ isSetUnit* (X .snd)

  -- Relational Lifting of Det Functor 
  DetRel : {X Y : hSet _} → 
    (R : ⟨ X ⟩ → ⟨ Y ⟩ → hSet _) → ⟨ Det X ⟩ → ⟨ Det Y ⟩ → hSet _
  DetRel {X} {Y} R (inl tt*) (inl tt*) = Unit* , isSetUnit*
  DetRel {X} {Y} R (inl _) (inr _) = ⊥ , λ()
  DetRel {X} {Y} R (inr _) (inl _) = ⊥ , (λ ())
  DetRel {X} {Y} R (inr x) (inr y) = R x y

  Coalg : (hSet _  → hSet _) → Type
  Coalg F = Σ[ X ∈ hSet _ ] (⟨ X ⟩ → ⟨ F X ⟩)

  DetAut : Type 
  DetAut = Coalg Det

  -- Bisimulation 
  -- for any related states, they either terminate, or step to related states
  Bisimulation : DetAut → DetAut → Type 
  Bisimulation α β = 
    Σ[ R ∈ (⟨ α .fst ⟩ → ⟨ β .fst ⟩ → hSet _) ]
    ((x : ⟨ α .fst ⟩)(y : ⟨ β .fst ⟩ ) → ⟨ R x y ⟩  → ⟨ DetRel {α .fst}{β .fst}R  (α .snd x) (β .snd y) ⟩)


  Bisimilarity : {α β : DetAut} → ⟨ α .fst ⟩ → ⟨ β .fst ⟩ → Type 
  Bisimilarity {α} {β} x y  = 
    Σ[ B ∈ Bisimulation α β ] 
      ⟨ B .fst x y ⟩


  -- terminates at true
  M1 : DetAut
  M1 .fst = Bool , isSetBool
  M1 .snd false = inr true
  M1 .snd true = inl tt*

  -- terminates at even odd numbers
  M2 : DetAut 
  M2 .fst = ℕ , isSetℕ
  M2 .snd n  with evenOrOdd n 
  ... | inl x = inr (suc n)
  ... | inr x = inl tt*

  -- relate false and odd numbers. true and even  
  R : Bool → ℕ → hSet _ 
  R true n with (evenOrOdd n)
  ... | inl x = ⊥ , λ ()
  ... | inr x = Unit , isSetUnit
  R false n with (evenOrOdd n)
  ... | inl x = Unit , isSetUnit
  ... | inr x = ⊥ , (λ())

  M1M2Bisim : Bisimulation M1 M2 
  M1M2Bisim .fst = R
  M1M2Bisim .snd false n with (evenOrOdd n) 
  ... | inl x = λ tt → {!   !}
  ... | inr x = λ ()
  M1M2Bisim .snd true n with (evenOrOdd n) 
  ... | inl x = λ ()
  ... | inr x = λ _ → tt*


module ND where 
  -- our behavior functor 
  NDet : hSet _ → hSet _ 
  NDet X = (ℙ ⟨ X ⟩) , isSetℙ

  NDetRel : {X Y : hSet _} → 
    (R : ⟨ X ⟩ → ⟨ Y ⟩ → hSet _) → ⟨ NDet X ⟩ → ⟨ NDet Y ⟩ → hSet _
  NDetRel {X} {Y} R U V .fst = 
    ((u : ⟨ X ⟩) → u ∈ U → Σ[ v ∈ ⟨ Y ⟩ ] (v ∈ V) × ⟨ R u v ⟩) 
    × ((v : ⟨ Y ⟩) → v ∈ V → Σ[ u ∈ ⟨ X ⟩ ] (u ∈ U) × ⟨ R u v ⟩)
  NDetRel {X} {Y} R U V .snd = isSet× (isSetΠ λ _ → isSet→ (isSetΣ (Y .snd) λ _ → 
    isSet× {!   !} {!   !})) {!   !}


  Coalg : (hSet _  → hSet _) → Type
  Coalg F = Σ[ X ∈ hSet _ ] (⟨ X ⟩ → ⟨ F X ⟩)

  NDetAut : Type 
  NDetAut = Coalg NDet

  Bisimulation : NDetAut → NDetAut → Type 
  Bisimulation α β = 
    Σ[ R ∈ (⟨ α .fst ⟩ → ⟨ β .fst ⟩ → hSet _) ]
    ((x : ⟨ α .fst ⟩)(y : ⟨ β .fst ⟩ ) → ⟨ R x y ⟩  → ⟨ NDetRel {α .fst}{β .fst}R  (α .snd x) (β .snd y) ⟩)

  Bisimilarity : {α β : NDetAut} → ⟨ α .fst ⟩ → ⟨ β .fst ⟩ → Type 
  Bisimilarity {α} {β} x y  = 
    Σ[ B ∈ Bisimulation α β ] 
      ⟨ B .fst x y ⟩

  open import HyperDoc.Operational.Effects.Syntax
  open import HyperDoc.Algebra.Algebra 
  emp : Signature 
  emp .Signature.Op = ⊥
  emp .Signature.arity ()

  open Syntax emp

  Comp : VTy → CTy → NDetAut 
  Comp A B .fst = A ⊢c B , isSet⊢c
  Comp A B .snd M M' = (M ↦ M') , isProp↦

  hmm : {A : VTy}{B : CTy}{M : A ⊢c B} → 
    Bisimilarity {Comp A B}{Comp A B} (force (thunk M)) M 
  hmm {A} {B} {M} .fst .fst x y = (x ↦ y) , {!   !}
  hmm {A} {B} {M} .fst .snd x y x↦y .fst x' x↦x' = y , {!   !}
  hmm {A} {B} {M} .fst .snd x y x↦y .snd = {!   !}
  hmm {A} {B} {M} .snd = Uβ



{-


-- Pow, Exp
data Shape : Type where 
  var pow : Shape
  const : hSet _ → Shape
  _⊗_ _⊕_ : Shape → Shape → Shape

Const : hSet _ → Functor (SET _) (SET _) 
Const X .F-ob _ = X
Const X .F-hom = λ z z₁ → z₁
Const X .F-id = refl
Const X .F-seq _ _ = refl

ToFunctor : Shape → Functor (SET _) (SET _) 
ToFunctor var = Id
ToFunctor (const X) = Const X
ToFunctor pow .F-ob X = ℙ ⟨ X ⟩  , {!   !}
ToFunctor pow .F-hom {X}{Y} f P y = ∃[ x ∶ ⟨ X ⟩ ] f x ≡ₚ y ⊓ P x
ToFunctor pow .F-id = {!   !}
ToFunctor pow  .F-seq = {!   !}
ToFunctor (s ⊗ s') .F-ob X .fst = ToFunctor s .F-ob X .fst × ToFunctor s' .F-ob X .fst
ToFunctor (s ⊗ s') .F-ob X .snd = isSet× (ToFunctor s .F-ob X .snd) (ToFunctor s' .F-ob X .snd)
ToFunctor (s ⊗ s') .F-hom f (x , y) = (ToFunctor s .F-hom f x) , ToFunctor s' .F-hom f y
ToFunctor (s ⊗ s') .F-id i (x , y) = (ToFunctor s .F-id  i x) , (ToFunctor s' .F-id i y)
ToFunctor (s ⊗ s') .F-seq f g i (x , y)= (ToFunctor s .F-seq f g i x) , (ToFunctor s' .F-seq f g i y)
ToFunctor (s ⊕ s') .F-ob X .fst = ToFunctor s .F-ob X .fst ⊎ ToFunctor s' .F-ob X .fst
ToFunctor (s ⊕ s') .F-ob X .snd = isSet⊎ (ToFunctor s .F-ob X .snd) (ToFunctor s' .F-ob X .snd)
ToFunctor (s ⊕ s') .F-hom f (inl x) = inl (ToFunctor s .F-hom f x)
ToFunctor (s ⊕ s') .F-hom f (inr x) = inr (ToFunctor s' .F-hom f x)
ToFunctor (s ⊕ s') .F-id i (inl x) = inl (ToFunctor s .F-id i x)
ToFunctor (s ⊕ s') .F-id i (inr x) = inr (ToFunctor s' .F-id i x)
ToFunctor (s ⊕ s') .F-seq f g i (inl x) = inl (ToFunctor s .F-seq f g i x)
ToFunctor (s ⊕ s') .F-seq f g i (inr x) = inr (ToFunctor s' .F-seq f g i x)


Rel : Type 
Rel = Σ[ X ∈ Type ] Σ[ Y ∈ Type ] (X → Y → Type)

RelHom : Rel → Rel → Type    
RelHom (X , Y , R) (X' , Y' , R') = 
  Σ[ f ∈ (X → X') ] Σ[ g ∈ (Y → Y') ] 
  ((x : X)(y : Y) → R x y → R' (f x) (g y))

REL : Category _ _ 
REL .ob = Rel
REL .Hom[_,_] = RelHom
REL .id = (λ z → z) , (λ z → z) , (λ x₁ y z → z)
REL ._⋆_ = λ f g →
    (λ z₁ → g .fst (f .fst z₁)) ,
    (λ z₁ → g .snd .fst (f .snd .fst z₁)) ,
    (λ x₁ y₁ z₁ →
        g .snd .snd (f .fst x₁) (f .snd .fst y₁) (f .snd .snd x₁ y₁ z₁))
REL .⋆IdL _ = refl
REL .⋆IdR _ = refl
REL .⋆Assoc _ _ _ = refl
REL .isSetHom = {!   !}

RelLift : Shape → Functor REL REL 
RelLift var = Id
RelLift (const X) .F-ob _ = ⟨ X ⟩ , (⟨ X ⟩ , _≡_)
RelLift (const X) .F-hom = λ z → (λ z₁ → z₁) , (λ z₁ → z₁) , (λ x₁ y₁ z₁ → z₁)
RelLift (const X) .F-id = refl
RelLift (const X) .F-seq _ _ = refl
RelLift (X ⊗ Y) .F-ob R = 
  RelLift X .F-ob R .fst × RelLift Y .F-ob R .fst , 
  (RelLift X .F-ob R .snd .fst × RelLift Y .F-ob R .snd .fst , 
  λ (x , y)(x' , y') → 
    RelLift X .F-ob R .snd .snd x x' × 
    RelLift Y .F-ob R .snd .snd y y')
RelLift pow .F-ob R = 
  (ℙ (R .fst)) , 
  ((ℙ (R .snd .fst)) , 
  λ U V → 
    ((u : R .fst)→ u ∈ U → Σ[ v ∈ R .snd .fst ] (v ∈ V) × R .snd .snd u v) × 
  ((v : R .snd .fst) → v ∈ V → Σ[ u ∈ R .fst ] (u ∈ U) × R .snd .snd u v))
RelLift pow .F-hom = {!   !}
RelLift pow .F-id = {!   !}
RelLift pow .F-seq = {!   !}
RelLift (X ⊗ Y) .F-hom = {!   !}
RelLift (X ⊗ Y) .F-id = {!   !}
RelLift (X ⊗ Y) .F-seq = {!   !}
RelLift (X ⊕ Y) .F-ob R =
  (RelLift X .F-ob R .fst ⊎ RelLift Y .F-ob R .fst) , 
  ((RelLift X .F-ob R .snd .fst ⊎ RelLift Y .F-ob R .snd .fst) , 
  λ { (inl x) (inl x') → RelLift X .F-ob R .snd .snd x x'
    ; (inl x) (inr y) → ⊥
    ; (inr y) (inl x) → ⊥
    ; (inr y) (inr y') → RelLift Y .F-ob R .snd .snd y y'})
RelLift (X ⊕ Y) .F-hom = {!   !}
RelLift (X ⊕ Y) .F-id = {!   !}
RelLift (X ⊕ Y) .F-seq = {!   !}

FORGETR : Functor REL (SET _ ×C SET _) 
FORGETR .F-ob R = (R .fst , {!   !}) , (R .snd .fst , {!   !}) 
FORGETR .F-hom = λ z → z .fst , z .snd .fst
FORGETR .F-id = refl
FORGETR .F-seq _ _ = refl

test : (s : Shape) → FORGETR ∘F RelLift s ≡ (ToFunctor s ×F ToFunctor s) ∘F FORGETR 
test var = Functor≡ (λ _ → refl) {!   !}
test pow = Functor≡ (λ _ → {!   !}) {!   !}
test (const x) = Functor≡ (λ _ → {!   !}) {!   !}
test (s ⊗ s₁) = {!   !}
test (s ⊕ s₁) = {!   !}

DetBeh' : Shape 
DetBeh' = const (Unit , isSetUnit) ⊕ var

DetBeh : Functor (SET _)(SET _) 
DetBeh = ToFunctor DetBeh'




{-}
module _ (base : Type)(interp : base → Type) where 
  data Shape : Type where 
    var : base → Shape
    𝟙 : Shape
    _⊗_ _⊕_ : Shape → Shape → Shape


  DenShape : Shape → Type 
  DenShape (var X) = interp X
  DenShape 𝟙 = Unit
  DenShape (X ⊗ Y) = DenShape X × DenShape Y
  DenShape (X ⊕ Y) = DenShape X ⊎ DenShape Y

  Sets : Category _ _ 
  Sets .ob = Shape
  Sets .Hom[_,_] X Y = DenShape X → DenShape Y
  Sets .id = λ z → z
  Sets ._⋆_ = λ f g z₁ → g (f z₁)
  Sets .⋆IdL _ = refl
  Sets .⋆IdR _ = refl
  Sets .⋆Assoc _ _ _ = refl
  Sets .isSetHom = {!   !} 


  Rel : Type 
  Rel = Σ[ X ∈ Type ] Σ[ Y ∈ Type ] (X → Y → Type)

  RelHom : Rel → Rel → Type    
  RelHom (X , Y , R) (X' , Y' , R') = 
    Σ[ f ∈ (X → X') ] Σ[ g ∈ (Y → Y') ] 
    ((x : X)(y : Y) → R x y → R' (f x) (g y))

  REL : Category _ _ 
  REL .ob = Rel
  REL .Hom[_,_] = RelHom
  REL .id = (λ z → z) , (λ z → z) , (λ x₁ y z → z)
  REL ._⋆_ = λ f g →
      (λ z₁ → g .fst (f .fst z₁)) ,
      (λ z₁ → g .snd .fst (f .snd .fst z₁)) ,
      (λ x₁ y₁ z₁ →
         g .snd .snd (f .fst x₁) (f .snd .fst y₁) (f .snd .snd x₁ y₁ z₁))
  REL .⋆IdL _ = refl
  REL .⋆IdR _ = refl
  REL .⋆Assoc _ _ _ = refl
  REL .isSetHom = {!   !}

  RelLift : Functor 


{-}
-}
-}
-}