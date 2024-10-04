{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Gluing.Normalization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.HITs.GroupoidTruncation
open import Cubical.HITs.SetTruncation
open import Cubical.Data.Unit.Properties

open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
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
      module CC = CartesianCategoryNotation Cl
      module CCProd = Notation _ (Cl .snd .snd)
    data NormalForm : (τ : Cl .fst .ob) (Γ : Cl .fst .ob) → Type (ℓ-max ℓq ℓq')
    data NeutralTerm : (τ : Cl .fst .ob) (Γ : Cl .fst .ob) → Type (ℓ-max ℓq ℓq')
    data NeutralTerm where
      var : ∀{τ : Cl .fst .ob} → NeutralTerm τ τ
      proj₁ : ∀{τ₁ τ₂} → NeutralTerm τ₁ (τ₁ CCProd.× τ₂)
      proj₂ : ∀{τ₁ τ₂} → NeutralTerm τ₂ (τ₁ CCProd.× τ₂)
      symb : ∀(f : Q.mor){Γ}(M : NormalForm (Q.dom f) Γ) → NeutralTerm (Q.cod f) Γ
      isSetNe : ∀{τ Γ} → isSet (NeutralTerm τ Γ)
    data NormalForm where
      shift : ∀{τ : Q .fst} {Γ} → NeutralTerm (↑ τ) Γ → NormalForm (↑ τ) Γ
      pair : ∀{τ₁ τ₂ Γ} → NormalForm τ₁ Γ → NormalForm τ₂ Γ → NormalForm (τ₁ CCProd.× τ₂) Γ
      uniq : ∀{Γ} → NormalForm CC.𝟙 Γ
      isSetNf : ∀{τ Γ} → isSet (NormalForm τ Γ)
    DiscreteCl : Category _ _
    DiscreteCl = DiscreteCategory (Cl .fst .ob , isGroupoidQ)
    ⊆ : Functor DiscreteCl (Cl .fst)
    ⊆ = DiscFunc λ x → x
    PreRen : Category _ _
    PreRen = PresheafCategory DiscreteCl _
    nerve : Functor (Cl .fst) PreRen
    nerve = CurryBifunctor (Sym (HomBif (Cl .fst) ∘Fl (⊆ ^opF))) 
    S : Section nerve (PRESHEAFᴰ DiscreteCl _ _)
    S = elimLocal' Q
      (LiftedTerminalReindex (PRESHEAFᴰ-VerticalTerminals DiscreteCl _ _ _))
      (LiftedBinProductsReindex'
        (BinProductsToBinProducts' _ (Cl .snd .snd))
        (PRESHEAFᴰ-isFibration _ _ _) (PRESHEAFᴰ-VerticalProducts _ _ _))
      {!!} {!!}
