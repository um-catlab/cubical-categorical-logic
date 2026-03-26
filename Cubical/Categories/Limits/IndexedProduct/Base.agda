-- Product of a family of objects X → C .ob indexed by a type X
module Cubical.Categories.Limits.IndexedProduct.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma as Ty hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functor
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.Cartesian
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Bifunctor as R hiding (Fst; Snd)

open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.IndexedProduct
open import Cubical.Categories.Yoneda

private
  variable
    ℓC ℓC' ℓ ℓ' : Level

open Category

module _ (C : Category ℓC ℓC') where
  ΠTy : {X : Type ℓ} → (X → C .ob) → Type _
  ΠTy c⟨x⟩ = UniversalElement C (ΠTyPsh (λ x → C [-, c⟨x⟩ x ]))

  IndexedProducts : (ℓ : Level) → Type _
  IndexedProducts ℓ = ∀ (X : Type ℓ) (c⟨x⟩ : X → C .ob) → ΠTy c⟨x⟩

module ΠTyNotation {C : Category ℓC ℓC'} {X : Type ℓ} c⟨x⟩ (Π : ΠTy C {X = X} c⟨x⟩) where
  private
    module C = Category C
  module Π = UniversalElementNotation Π
  open Π public
  lda : ∀ {Γ} → (∀ x → C [ Γ , c⟨x⟩ x ]) → C [ Γ , Π.vertex ]
  lda = intro

  app : (∀ x → C [ Π.vertex , c⟨x⟩ x ])
  app = element

  Πβ : ∀ {Γ} (f : ∀ x → C [ Γ , c⟨x⟩ x ]) → ∀ x → (lda f C.⋆ app x) ≡ f x
  Πβ f = funExt⁻ β

  Πη : ∀ {Γ} (f : C [ Γ , Π.vertex ]) → f ≡ lda (λ x → f C.⋆ app x)
  Πη f = η

module IndexedProductsNotation {C : Category ℓC ℓC'} {ℓ} (Πs : IndexedProducts C ℓ) where
  private
    module Π {X : Type ℓ} c⟨x⟩ = ΠTyNotation {X = X} c⟨x⟩ (Πs X c⟨x⟩)

  open Π public
  Π : {X : Type ℓ} → (X → C .ob) → C .ob
  Π = λ z → UniversalElement.vertex (Πs _ z)
