{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Presheaf.Constructions.BinProduct.LocalRepresentability where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.BinProduct.Base
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Bifunctor

private
  variable
    ℓ ℓ' ℓA ℓB ℓA' ℓB' ℓC ℓC' ℓD ℓD' ℓP ℓQ ℓS : Level

open Functor
open PshHom
open PshIso

module _ {C : Category ℓ ℓ'} where
  private
    module C = Category C

  -- This should be possible to do compositionally if PshProd were
  -- universe polymorphic
  LRProf : (P : Presheaf C ℓP) → Profunctor C C (ℓ-max ℓ' ℓP)
  LRProf P .F-ob x = (C [-, x ]) ×Psh P
  LRProf P .F-hom f = PshHom→NatTrans (×PshIntro (π₁ _ _ ⋆PshHom yoRec _ f) (π₂ _ _))
  LRProf P .F-id = makeNatTransPath $ funExt λ y → funExt λ f → ΣPathP (C.⋆IdR _ , refl)
  LRProf P .F-seq f g = makeNatTransPath $ funExt λ y → funExt λ h →
    ΣPathP ((sym $ C.⋆Assoc (π₁ (C [-, _ ]) P .N-ob y h) f g) , refl)

  LocallyRepresentable : Presheaf C ℓP → Type _
  LocallyRepresentable P = UniversalElements $ LRProf P

LRPresheaf : ∀ (C : Category ℓ ℓ') (ℓP : Level) → Type _
LRPresheaf C ℓP = Σ (Presheaf C ℓP) LocallyRepresentable

LRPsh→Functor : ∀ {C : Category ℓ ℓ'}
  ((P , _×P) : LRPresheaf C ℓP)
  → Functor C C
LRPsh→Functor (P , _×P) = FunctorComprehension (LRProf P) _×P
