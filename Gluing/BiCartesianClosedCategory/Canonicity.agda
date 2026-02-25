{-# OPTIONS --lossy-unification #-}
module Gluing.BiCartesianClosedCategory.Canonicity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit
open import Cubical.Data.Quiver.Base
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Limits.BiCartesianClosed.Base
open import Cubical.Categories.Limits.Cartesian.Base

open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Sets.Properties
open import Cubical.Categories.Displayed.Constructions.Weaken.UncurriedProperties
open import Cubical.Categories.Displayed.Limits.BiCartesianClosedV

open import Cubical.Categories.Constructions.Free.BiCartesianClosedCategory.Forded as FreeBiCCC
  renaming ([_,_] to [_,+_])
open import Cubical.Categories.Constructions.Free.BiCartesianClosedCategory.Quiver
open import Cubical.Categories.Displayed.Limits.BiCartesianClosedSection

private
  variable ℓQ ℓQ' : Level

open Category
open Functor
open Section

module _ (+×⇒Q : +×⇒Quiver ℓQ ℓQ') where
  private
    module +×⇒Q = +×⇒Quiver +×⇒Q

  FREE : BiCartesianClosedCategory _ _
  FREE = FreeBiCartesianClosedCategory +×⇒Q

  private
    module FREE = BiCartesianClosedCategory FREE

  wkSET : {ℓ : Level} → BiCartesianClosedCategoryᴰ _ _ _
  wkSET {ℓ} = weakenBCCC (FreeBiCartesianClosedCategory +×⇒Q) (SETBiCCC {ℓ})

  Pts : Functor FREE.C (SET (ℓ-max ℓQ ℓQ'))
  Pts = FREE.C [ ⊤ ,-]

  PtsCartesian : CartesianFunctor FREE.CC (SET (ℓ-max ℓQ ℓQ'))
  PtsCartesian .fst = Pts
  PtsCartesian .snd x y z =
    isIsoToIsEquiv
      ((λ (f , g) u → ⟨ f u , g u ⟩ Eq.refl) ,
      (λ _ → ΣPathP ((funExt λ _ → ×β₁) , (funExt λ _ → ×β₂))) ,
      λ _ → funExt λ _ → sym (×η Eq.refl _))

  CanonicalFormMotive : BiCartesianClosedCategoryᴰ _ _ _
  CanonicalFormMotive =
    FreeBiCCC.elimLocalMotive +×⇒Q PtsCartesian EqSETᴰBCCCⱽ

  module _
    (cf : FreeBiCCC.ElimInterpᴰ +×⇒Q CanonicalFormMotive)
    where

    canonicalizeSection : Section Pts (SETᴰ (ℓ-max ℓQ ℓQ') (ℓ-max ℓQ ℓQ'))
    canonicalizeSection = FreeBiCCC.elimLocal +×⇒Q PtsCartesian EqSETᴰBCCCⱽ cf

    canonicalize :
      ∀ {o} → (e : FREE.C [ ⊤ , ↑ o ]) →
      (ElimInterpᴰ.ı-ob cf o ((Pts ⟪ e ⟫) (idₑ Eq.refl))) .fst
    canonicalize e = canonicalizeSection .F-homᴰ e _ _
