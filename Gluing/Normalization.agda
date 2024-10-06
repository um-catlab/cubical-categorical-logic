{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Gluing.Normalization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Relation.Nullary hiding (⟪_⟫)
open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.HITs.GroupoidTruncation
open import Cubical.HITs.SetTruncation
open import Cubical.Data.Unit.Properties

open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Instances.Discrete
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct.More
open import
  Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
  hiding (_×_)
open import Cubical.Categories.Constructions.Free.CartesianCategory.Base
  hiding (rec)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Presheaf.Base
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Presheaf using (UniversalElementᴰ)
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.Displayed.Instances.Presheaf.Properties

private variable
  ℓq ℓq' : Level

open Category
open Functor
--open ProductQuiver

module _ (Q : ×Quiver ℓq ℓq') where
  private module Q = ×QuiverNotation Q
  module _ (isGroupoidQ : isGroupoid Q.Ob) where
    Cl : CartesianCategory _ _
    Cl = FreeCartesianCategory Q
    private
      module Cl = CartesianCategoryNotation Cl
    data NormalForm : (τ : Cl .fst .ob) (Γ : Cl .fst .ob) → Type (ℓ-max ℓq ℓq')
    data NeutralTerm : (τ : Cl .fst .ob) (Γ : Cl .fst .ob) → Type (ℓ-max ℓq ℓq')
    data NeutralTerm where
      var : ∀{τ : Cl .fst .ob} → NeutralTerm τ τ
      proj₁ : ∀{τ₁ τ₂} → NeutralTerm τ₁ (τ₁ Cl.×bp τ₂)
      proj₂ : ∀{τ₁ τ₂} → NeutralTerm τ₂ (τ₁ Cl.×bp τ₂)
      symb : ∀(f : Q.mor){Γ}(M : NormalForm (Q.dom f) Γ) → NeutralTerm (↑ (Q.cod f)) Γ
      --isSetNe : ∀{τ Γ} → isSet (NeutralTerm τ Γ)
    data NormalForm where
      shift : ∀{τ : Q .fst} {Γ} → NeutralTerm (↑ τ) Γ → NormalForm (↑ τ) Γ
      pair : ∀{τ₁ τ₂ Γ} → NormalForm τ₁ Γ → NormalForm τ₂ Γ → NormalForm (τ₁ Cl.×bp τ₂) Γ
      uniq : ∀{Γ} → NormalForm Cl.𝟙 Γ
      --isSetNf : ∀{τ Γ} → isSet (NormalForm τ Γ)
    Ren : Category _ _
    Ren = DiscreteCategory (Cl .fst .ob , isGroupoidQ)
    ⊆ : Functor Ren (Cl .fst)
    ⊆ = DiscFunc (idfun _)
    --test : {x y : ob Ren} → Ren [ x , y ] → Cl .fst [ ⊆ .F-ob x , ⊆ .F-ob y ]
    --test = ⊆ .F-hom
    𝒫Ren : Category _ _
    𝒫Ren = PresheafCategory Ren (ℓ-max ℓq ℓq')
    nerve : Functor (Cl .fst) 𝒫Ren
    nerve = CurryBifunctor (Sym (HomBif (Cl .fst) ∘Fl (⊆ ^opF)))
    𝒫Renᴰ : Categoryᴰ 𝒫Ren _ _
    𝒫Renᴰ = PRESHEAFᴰ Ren _ (ℓ-max ℓq ℓq')
    private
      module 𝒫Renᴰ = Categoryᴰ 𝒫Renᴰ
    S : Section nerve 𝒫Renᴰ
    S = elimLocal' Q
      (LiftedTerminalReindex (PRESHEAFᴰ-VerticalTerminals Ren _ _ _))
      (LiftedBinProductsReindex'
        (BinProductsToBinProducts' _ (Cl .snd .snd))
        (PRESHEAFᴰ-isFibration _ _ _) (PRESHEAFᴰ-VerticalProducts _ _ _))
      OB {!HOM!}
      where
      OB : (τ : Q .fst) → 𝒫Renᴰ.ob[ nerve ⟅ ⊆ ⟅ ↑ τ ⟆ ⟆ ]
      OB τ .F-ob (Γ , e) = NormalForm (↑ τ) Γ , {!!} --isSetNf
      OB τ .F-hom {-{x = Δ,e'} {Δ',e''}-} (p , q) = subst (NormalForm (↑ τ)) (sym p)
      OB τ .F-id {x = (Γ , e)} = funExt λ nf → goal nf
        where
        -- It doesn't type check if I inline this?
        goal : ∀ nf → subst (NormalForm (↑ τ)) refl nf ≡ nf
        goal nf = substRefl nf
        --foo : Σ[ p ∈ Γ ≡ Γ ] ⊆ ⟪ p ⟫ ⋆⟨ Cl .fst ⟩ e ≡ e
        --foo = (Cubical.Categories.Constructions.Elements.Contravariant.∫ᴾ (nerve ⟅ ⊆ ⟅ ↑ τ ⟆ ⟆)) .id
        --test : Γ ≡ Γ
        --test = foo .fst
        --test2 : test ≡ refl
        --test2 = refl
      OB τ .F-seq = {!!}
      HOM : {!!}
      HOM = {!!}
