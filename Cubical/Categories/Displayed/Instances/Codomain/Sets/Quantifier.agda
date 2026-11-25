{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Codomain.Sets.Quantifier where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
  hiding (_[-][-,_])
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import
  Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.UniversalQuantifier
open import Cubical.Categories.Displayed.Instances.Codomain.Base
open import Cubical.Categories.Displayed.Instances.Codomain.Sets.Base
open import Cubical.Categories.Displayed.Instances.Codomain.Sets.Closed
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Limits.BiCartesianClosedV

open PshHom
open PshIso
open UniversalElementⱽ'
open UniversalElement

module _ {ℓ : Level} {Γ A : hSet ℓ}
  (Aᴰ : Categoryᴰ.ob[_] (SETᴰ ℓ ℓ) (BinProductsSET (Γ , A) .vertex)) where
  private
    module SETᴰ = Categoryᴰ (SETᴰ ℓ ℓ)
    module SETCod = Categoryᴰ (SETCod ℓ)
    ΓA = BinProductsSET (Γ , A) .vertex
    ∀Spec = ∀Pshⱽ (SETCod ℓ) A (λ c → BinProductsSET (c , A))
      (λ Δ yᴰ → isFibrationSETCod yᴰ (BinProductsSET (Δ , A) .vertex) fst) Aᴰ

  ∀Cod : SETᴰ.ob[ Γ ]
  ∀Cod γ = (∀ (x : ⟨ A ⟩) → Fib ℓ Aᴰ (γ , x))
    , isSetΠ λ x → isSetFib ℓ Aᴰ (γ , x)

  instCod : SETCod.Hom[ (λ z → z) ][ Pull {X = ΓA} {Y = Γ} fst ∀Cod , Aᴰ ]
  instCod = mk ℓ λ z →
    z .snd .fst .snd (z .fst .snd) .fst
    , z .snd .fst .snd (z .fst .snd) .snd
      ∙ (λ i → z .snd .snd i , z .fst .snd)

  module _ {Δ : hSet ℓ} {γ : ⟨ Δ ⟩ → ⟨ Γ ⟩} {c : SETᴰ.ob[ Δ ]} where
    private
      ΔA = BinProductsSET (Δ , A) .vertex
      γA : ⟨ ΔA ⟩ → ⟨ ΓA ⟩
      γA z = γ (z .fst) , z .snd

    genCod : SETCod.Hom[ γA ][ Pull {X = ΔA} {Y = Δ} fst c , Aᴰ ]
      → SETCod.Hom[ γ ][ c , ∀Cod ]
    genCod g = mk ℓ λ z →
      (γ (z .fst) , λ x → pt ℓ g ((z .fst , x) , z , refl)) , refl

    instCod⟨_⟩ : SETCod.Hom[ γ ][ c , ∀Cod ]
      → SETCod.Hom[ γA ][ Pull {X = ΔA} {Y = Δ} fst c , Aᴰ ]
    instCod⟨ h ⟩ = mk ℓ λ w →
      h .fst (w .snd .fst) .snd (w .fst .snd) .fst
      , h .fst (w .snd .fst) .snd (w .fst .snd) .snd
        ∙ (λ i → h .snd i (w .snd .fst) , w .fst .snd)
        ∙ (λ i → γ (w .snd .snd i) , w .fst .snd)

    inst-gen : (g : SETCod.Hom[ γA ][ Pull {X = ΔA} {Y = Δ} fst c , Aᴰ ])
      → instCod⟨ genCod g ⟩ ≡ g
    inst-gen g = Codomain≡ (SET ℓ) refl (funExt λ w → cong (g .fst) λ i →
      (w .snd .snd i , w .fst .snd) , w .snd .fst
      , λ j → w .snd .snd (i ∧ j))

    gen-inst : (h : SETCod.Hom[ γ ][ c , ∀Cod ]) → genCod instCod⟨ h ⟩ ≡ h
    gen-inst h = Codomain≡ (SET ℓ) refl (funExt λ z →
      ΣPathP (b z , λ i x → FibPathP ℓ {X = ΓA} (λ j → b z j , x)
        {u = pt ℓ instCod⟨ h ⟩ ((z .fst , x) , z , refl)}
        {u' = h .fst z .snd x} refl i))
      where
      b : ∀ z → γ (z .fst) ≡ h .fst z .fst
      b z i = h .snd (~ i) z

    inst≡ : (h : SETCod.Hom[ γ ][ c , ∀Cod ])
      → yoRecⱽ ∀Spec instCod .N-ob (Δ , c , γ) h ≡ instCod⟨ h ⟩
    inst≡ h = Codomain≡ (SET ℓ) refl
      ( reind-fst {P = Pull {X = ΔA} {Y = Δ} fst c} {Q = Aᴰ} _ _
      ∙ funExt λ w → cong (λ t → t w .snd (w .fst .snd) .fst)
          (reind-fst {P = Pull {X = ΔA} {Y = Δ} fst c} {Q = ∀Cod} _ _))

  ∀UE : UniversalElementⱽ' (SETCod ℓ) Γ ∀Spec
  ∀UE .vertexⱽ = ∀Cod
  ∀UE .elementⱽ = instCod
  ∀UE .universalⱽ (Δ , c , γ) .fst = genCod
  ∀UE .universalⱽ (Δ , c , γ) .snd .fst g = inst≡ (genCod g) ∙ inst-gen g
  ∀UE .universalⱽ (Δ , c , γ) .snd .snd h = cong genCod (inst≡ h) ∙ gen-inst h

  ∀SETCod : UniversalQuantifier (SETCod ℓ) A (λ c → BinProductsSET (c , A))
    (λ Δ yᴰ → isFibrationSETCod yᴰ (BinProductsSET (Δ , A) .vertex) fst) Aᴰ
  ∀SETCod .fst = ∀Cod
  ∀SETCod .snd = improvePshIso (REPRⱽ ∀UE .snd)
    ((λ _ h → instCod⟨ h ⟩) , funExt λ _ → funExt λ h → inst≡ h)
    ((λ _ → genCod) , refl)

UniversalQuantifiersSETCod : ∀ {ℓ}
  → UniversalQuantifiers (SETCod ℓ) BinProductsSET isFibrationSETCod
UniversalQuantifiersSETCod Aᴰ = ∀SETCod Aᴰ

module _ {ℓ : Level} {Γ A Δ : hSet ℓ}
  {Aᴰ : Categoryᴰ.ob[_] (SETᴰ ℓ ℓ) (BinProductsSET (Γ , A) .vertex)}
  {γ : ⟨ Δ ⟩ → ⟨ Γ ⟩} {c : Categoryᴰ.ob[_] (SETᴰ ℓ ℓ) Δ} where
  _ : (h : Categoryᴰ.Hom[_][_,_] (SETCod ℓ) γ c (∀Cod Aᴰ))
    (w : ⟨ ∫El ℓ (Pull {X = BinProductsSET (Δ , A) .vertex} {Y = Δ} fst c) ⟩)
    → UniversalQuantifiersSETCod Aᴰ .snd .trans .N-ob (Δ , c , γ) h .fst w
      ≡ h .fst (w .snd .fst) .snd (w .fst .snd) .fst
  _ = λ h w → refl

  _ : (g : Categoryᴰ.Hom[_][_,_] (SETCod ℓ) (λ z → γ (z .fst) , z .snd)
         (Pull {X = BinProductsSET (Δ , A) .vertex} {Y = Δ} fst c) Aᴰ)
      (z : ⟨ ∫El ℓ c ⟩) (x : ⟨ A ⟩)
    → invPshIso (UniversalQuantifiersSETCod Aᴰ .snd) .trans .N-ob (Δ , c , γ) g
      .fst z .snd x .fst
      ≡ g .fst ((z .fst , x) , z , refl)
  _ = λ g z x → refl

SETCodCCCⱽ : ∀ {ℓ} → CartesianClosedCategoryⱽ (SETCC {ℓ}) (ℓ-suc ℓ) ℓ
SETCodCCCⱽ .CartesianClosedCategoryⱽ.CCⱽ = SETCodCCⱽ
SETCodCCCⱽ .CartesianClosedCategoryⱽ.lrⱽ = AllLRⱽSETCod
SETCodCCCⱽ .CartesianClosedCategoryⱽ.expⱽ = ExponentialsⱽSETCod
SETCodCCCⱽ .CartesianClosedCategoryⱽ.forallⱽ = UniversalQuantifiersSETCod

SETCodBCCCⱽ : ∀ {ℓ} → BiCartesianClosedCategoryⱽ (SETCC {ℓ}) (ℓ-suc ℓ) ℓ
SETCodBCCCⱽ .BiCartesianClosedCategoryⱽ.CCCⱽ = SETCodCCCⱽ
SETCodBCCCⱽ .BiCartesianClosedCategoryⱽ.initⱽ = InitialsⱽSETCod
SETCodBCCCⱽ .BiCartesianClosedCategoryⱽ.bcpⱽ = BinCoProductsⱽSETCod
SETCodBCCCⱽ .BiCartesianClosedCategoryⱽ.opcartesianLifts = isOpfibrationSETCod
