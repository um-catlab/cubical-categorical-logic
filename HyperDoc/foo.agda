{-# OPTIONS --type-in-type #-}
--lazy 
module HyperDoc.foo where  

open import Cubical.Data.Nat  hiding ( _^_ )
open import Cubical.Data.Nat.Order 
open import Cubical.Data.FinData
open import Cubical.Data.Sigma

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

open Category
open Functor

-- : Ref : ℕ → Type
data Ty : Type where
  𝟙 Ref : Ty 
  _⊕_ : Ty → Ty → Ty

𝟚 = 𝟙 ⊕ 𝟙

data _◂_⊢_ : ℕ → Ty → Ty → Type where 
    -- category 
  sub : ∀ {n A A' A''} → n ◂ A ⊢ A' → n ◂ A' ⊢ A'' → n ◂ A ⊢ A''
  var : ∀ {n A} → n ◂ A ⊢ A
  subIdl : ∀ {n A A'} → (V : n ◂ A ⊢ A') → sub (var {n}{A}) V ≡ V
  subIdr : ∀ {n A A'} → (V : n ◂ A ⊢ A') → sub V (var {n}{A'}) ≡ V
  subAssoc : ∀ {n A₁ A₂ A₃ A₄}(V : n ◂ A₁ ⊢  A₂)(W : n ◂ A₂ ⊢ A₃)(Y : n ◂ A₃ ⊢  A₄) → 
    sub (sub V W) Y ≡ sub V (sub W Y)
  isSet⊢ : ∀{n A A'} → isSet (n ◂ A ⊢ A')

  -- type structure 
  tt : ∀{n A} → n ◂ A ⊢ 𝟙
  η𝟙 : ∀{n A} → (V : n ◂ A ⊢ 𝟙) → tt ≡ V

  --π₁ : ∀{B B'} → (B & B') ⊢k B
  --π₂ : ∀{B B'} → (B & B') ⊢k B'
  -- ⟨_,_⟩k : ∀{B B' B''} → B'' ⊢k B → B'' ⊢k B' → B'' ⊢k (B & B')

  σ₁ : ∀ {n A A'} → n ◂  A ⊢ (A ⊕ A')
  σ₂ : ∀ {n A A'} → n ◂  A' ⊢ (A ⊕ A') 
  case : ∀ {n A A' A''} → (n ◂  A ⊢ A'') → (n ◂  A' ⊢ A'') → n ◂ (A ⊕ A') ⊢ A''
  ⊕β₁ : ∀{n A A' A''}{V : n ◂  A ⊢ A''}{W : n ◂  A' ⊢ A''} → sub σ₁ (case V W) ≡ V  
  ⊕β₂ : ∀{n A A' A''}{V : n ◂ A ⊢ A''}{W : n ◂  A' ⊢ A''} → sub σ₂ (case V W) ≡ W 

  ref : ∀ {n Γ} → 
    Fin n → 
    ---------------
    n ◂ Γ ⊢ Ref
  read :  ∀ {n Γ} → 
    (M : n ◂ Γ ⊢ Ref) → 
    -------------------
    n ◂ Γ ⊢ 𝟚

  alloc : ∀ {n Γ} → 
    (M : n ◂ Γ ⊢ 𝟚) → 
    ------------------ 
    suc n ◂ Γ ⊢ Ref

  promote : {A A' : Ty}{n m : ℕ} → 
    n ≤ m → 
    n ◂ A ⊢ A' → 
    ---------------
    m ◂ A ⊢ A' 

  promote-var :
    {A : Ty}{n m : ℕ} → 
    (n≤m : n ≤ m) → 
    var {A = A}≡ promote n≤m var


W : Category ℓ-zero ℓ-zero 
W .ob = ℕ
W .Hom[_,_] = _≤_
W .id = ≤-refl
W ._⋆_ = ≤-trans
W .⋆IdL _ = isProp≤ _ _ 
W .⋆IdR _ = isProp≤ _ _ 
W .⋆Assoc _ _ _ = isProp≤ _ _
W .isSetHom = isProp→isSet isProp≤

open import Cubical.Categories.Presheaf
open import Cubical.Categories.Monoidal.Instances.Presheaf 
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open import HyperDoc.Lib
open EnrichedCategory
open NatTrans

-- open import Cubical.Categories.Monoidal.EnrichedFunctor
open PshMon (W ^op) _

Model : Type 
Model = EnrichedCategory 𝓟Mon _

module _ {ℓV ℓV'  : Level} (V : MonoidalCategory ℓV ℓV') where 
  open MonoidalCategory V
    renaming (ob to obV; Hom[_,_] to V[_,_]; id to idV; _⋆_ to _⋆V_; ⋆Assoc to VAssoc)

  record EnrichedFunctor {ℓE ℓD : Level}(E : EnrichedCategory V ℓE)(D : EnrichedCategory V ℓD) : Type (ℓ-max (ℓ-max (ℓ-max ℓV ℓV') (ℓ-suc ℓE)) (ℓ-suc ℓD)) where 
    private module E = EnrichedCategory E 
    private module D = EnrichedCategory D 
    field 
      F₀ : E.ob → D.ob
      F₁ : {X Y : E.ob} → V[ E.Hom[ X , Y ] , D.Hom[ F₀ X , F₀ Y ] ]
      Fid : {X : E.ob} → (E.id {X} ⋆V F₁ {X} {X}) ≡ D.id {F₀ X}
      Fseq : {X Y Z : E.ob} → (F₁ {X} {Y} ⊗ₕ F₁ {Y} {Z}) ⋆V D.seq (F₀ X) (F₀ Y) (F₀ Z) ≡ E.seq X Y Z ⋆V F₁ {X} {Z} 


ModelMorphism : Model → Model → Type 
ModelMorphism = EnrichedFunctor 𝓟Mon


-- Kleisli Model
SetModel : Model 
SetModel .ob = Presheaf (W ^op) _
SetModel .Hom[_,_] = _^_
SetModel .id = {!   !}
SetModel .seq = {!   !}
SetModel .⋆IdL = {!   !}
SetModel .⋆IdR = {!   !}
SetModel .⋆Assoc = {!   !}

RefF : Presheaf W _  
RefF .F-ob n = (Fin n) , {!   !}
RefF .F-hom {n}{m} n≤m = {!   !}
RefF .F-id = {!   !}
RefF .F-seq = {!   !}

Bool : Presheaf W _
Bool =  {!   !}


synHom : Ty → Ty → Functor W (SET _) 
synHom A A' .F-ob n = n ◂ A ⊢ A' , {!   !}
synHom A A' .F-hom n≤m t = promote n≤m t
synHom A A' .F-id {n} = funExt λ V → {!   !} -- promote ≤-refl V ≡ V
synHom A A' .F-seq V V' = funExt λ V'' → {!   !} -- promote (≤-trans V V') V'' ≡ promote V' (promote V V'')

Syn : Model 
Syn .ob = Ty
Syn .Hom[_,_] A A' = synHom A A' ∘F from^op^op
Syn .id .N-ob n tt* = var
Syn .id .N-hom n≤m = funExt λ tt* → promote-var n≤m
Syn .seq A A' A'' .N-ob n (V , V') = sub V V'
Syn .seq A A' A'' .N-hom _ = funExt λ (V , V') → {!   !}
Syn .⋆IdL A A' = makeNatTransPath (funExt λ n → funExt λ (tt* , V) → {!   !})
Syn .⋆IdR = {!   !}
Syn .⋆Assoc = {!   !}

open import Cubical.Categories.Presheaf.Morphism.Alt
open PshHom
Sem : ModelMorphism Syn SetModel 
Sem .EnrichedFunctor.F₀ Ty.𝟙 = {!   !}
Sem .EnrichedFunctor.F₀ Ref = {!   !}
Sem .EnrichedFunctor.F₀ (A ⊕ A₁) = {!   !}
Sem .EnrichedFunctor.F₁ .N-ob n V .N-ob m n≤m = {!   !}
Sem .EnrichedFunctor.F₁ .N-ob n V .N-hom = {!   !}
Sem .EnrichedFunctor.F₁ .N-hom = {!   !}
Sem .EnrichedFunctor.Fid = {!   !}
Sem .EnrichedFunctor.Fseq = {!   !}