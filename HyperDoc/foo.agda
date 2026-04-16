{-# OPTIONS --type-in-type #-}
--lazy 
module HyperDoc.foo where  

open import Cubical.Data.Nat 
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
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open import HyperDoc.Lib
open EnrichedCategory
open NatTrans

open PshMon (W ^op) _

Model : Type 
Model = EnrichedCategory 𝓟Mon _

promote : {A A' : Ty}{n m : ℕ} → n ≤ m → n ◂ A ⊢ A' → m ◂ A ⊢ A' 
-- the interesting cases
promote {A} {A'} {n} {m} n≤m (ref x) = ref {! x  !} -- convert x : Fin n → x : Fin m , inclusion
promote {A} {A'} {n} {m} n≤m (read V) = read (promote n≤m V)
promote {A} {A'} {suc n} {zero} sucn≤zero (alloc {n} V) = {! V!} -- this case is false by assumption, dispatch
promote {A} {A'} {suc n} {suc m} sucn'≤sucm (alloc {n} V) = goal where 

  goal : suc m ◂ A ⊢ Ref 
  goal = alloc {m} (promote (pred-≤-pred  sucn'≤sucm) V)

-- boring cases
promote {A} {A'} {n} {m} n≤m (sub V V') = sub (promote n≤m  V) (promote n≤m V')
promote {A} {A'} {n} {m} n≤m var = var
promote {A} {A'} {n} {m} n≤m (subIdl V i) = subIdl (promote n≤m V) i
promote {A} {A'} {n} {m} n≤m (subIdr V i) = subIdr (promote n≤m V) i
promote {A} {A'} {n} {m} n≤m (subAssoc V V₁ V₂ i) = subAssoc (promote n≤m V) (promote n≤m V₁) (promote n≤m V₂) i
promote {A} {A'} {n} {m} n≤m (isSet⊢ V V₁ x y i i₁) = isSet⊢ (promote n≤m V) (promote n≤m V₁) (cong₂ promote refl x) (cong₂ promote refl y) i i₁
promote {A} {A'} {n} {m} n≤m tt = tt
promote {A} {A'} {n} {m} n≤m (η𝟙 V i) = η𝟙  (promote n≤m V) i
promote {A} {A'} {n} {m} n≤m σ₁ = σ₁
promote {A} {A'} {n} {m} n≤m σ₂ = σ₂
promote {A} {A'} {n} {m} n≤m (case V V₁) = case (promote n≤m V) (promote n≤m V₁)
promote {A} {A'} {n} {m} n≤m (⊕β₁ {V = V}{V'} i) = ⊕β₁ {V = promote n≤m V }{promote n≤m V'} i
promote {A} {A'} {n} {m} n≤m (⊕β₂ {V = V}{V'}i) = ⊕β₂ {V = promote n≤m V }{promote n≤m V'} i

synHom : Ty → Ty → Functor W (SET _) 
synHom A A' .F-ob n = n ◂ A ⊢ A' , {!   !}
synHom A A' .F-hom n≤m t = promote n≤m t
synHom A A' .F-id {n} = funExt λ V → {!   !} -- promote ≤-refl V ≡ V
synHom A A' .F-seq V V' = funExt λ V'' → {!   !} -- promote (≤-trans V V') V'' ≡ promote V' (promote V V'')

Syn : Model 
Syn .ob = Ty
Syn .Hom[_,_] A A' = synHom A A' ∘F from^op^op
Syn .id .N-ob n tt* = var
Syn .id .N-hom n≤m = refl
Syn .seq A A' A'' .N-ob n (V , V') = sub V V'
Syn .seq A A' A'' .N-hom _ = refl
Syn .⋆IdL A A' = makeNatTransPath (funExt λ n → funExt λ (tt* , V) → {!   !})
Syn .⋆IdR = {!   !}
Syn .⋆Assoc = {!   !}