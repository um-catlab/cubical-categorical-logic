{-# OPTIONS --lossy-unification #-}
{-
  The category `STRICT-FUNCTOR C D` of strict functors and strict
  natural transformations between two categories. Mirrors `FUNCTOR C D`
  but with objects in `StrictFunctor` and morphisms in `StrictNatTrans`.

  Because `_S∘_` is strictly unital and associative, this is what we use
  as the hom-category in the strict CAT bicategory.
-}
module Cubical.Categories.Functors.Strict.FUNCTOR where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functors.Strict.Base
open import Cubical.Categories.Functors.Strict.Presheaf

private
  variable
    ℓc ℓc' ℓd ℓd' : Level

open StrictFunctor
open StrictNatTrans
open Category

module _ {C : Category ℓc ℓc'} {D : Category ℓd ℓd'} where
  private
    module C = Category C
    module D = Category D

  isPropStrict-N-hom : (F G : StrictFunctor C D) (ϕ : Strict-N-ob-Type F G)
    → isProp (Strict-N-hom-Type F G ϕ)
  isPropStrict-N-hom F G ϕ =
    isPropImplicitΠ λ _ →
    isPropImplicitΠ λ _ →
    isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → D.isSetHom _ _

  StrictNatTransΣ : (F G : StrictFunctor C D) → Type _
  StrictNatTransΣ F G =
    Σ (Strict-N-ob-Type F G) (Strict-N-hom-Type F G)

  StrictNatTransΣIso : (F G : StrictFunctor C D)
    → Iso (StrictNatTrans F G) (StrictNatTransΣ F G)
  StrictNatTransΣIso F G .Iso.fun α = α .N-ob , α .N-hom
  StrictNatTransΣIso F G .Iso.inv (ϕ , h) .N-ob = ϕ
  StrictNatTransΣIso F G .Iso.inv (ϕ , h) .N-hom = h
  StrictNatTransΣIso F G .Iso.sec _ = refl
  StrictNatTransΣIso F G .Iso.ret _ = refl

  isSetStrictNatTrans : (F G : StrictFunctor C D) → isSet (StrictNatTrans F G)
  isSetStrictNatTrans F G =
    isOfHLevelRetractFromIso 2 (StrictNatTransΣIso F G)
      (isSetΣ (isSetΠ λ _ → D.isSetHom)
              (λ _ → isProp→isSet (isPropStrict-N-hom F G _)))

module _ (C : Category ℓc ℓc') (D : Category ℓd ℓd') where
  private
    module D = Category D

  STRICT-FUNCTOR : Category (ℓ-max (ℓ-max ℓc ℓc') (ℓ-max ℓd ℓd'))
                            (ℓ-max (ℓ-max ℓc ℓc') ℓd')
  STRICT-FUNCTOR .ob = StrictFunctor C D
  STRICT-FUNCTOR .Hom[_,_] = StrictNatTrans
  STRICT-FUNCTOR .id = idStrictTrans _
  STRICT-FUNCTOR ._⋆_ = seqStrictTrans
  STRICT-FUNCTOR .⋆IdL α =
    makeStrictNatTransPath (funExt λ _ → D.⋆IdL _)
  STRICT-FUNCTOR .⋆IdR α =
    makeStrictNatTransPath (funExt λ _ → D.⋆IdR _)
  STRICT-FUNCTOR .⋆Assoc α β γ =
    makeStrictNatTransPath (funExt λ _ → D.⋆Assoc _ _ _)
  STRICT-FUNCTOR .isSetHom = isSetStrictNatTrans _ _
