{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Monoidal.Base hiding (MonoidalStr)
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.Monoidal.NaturalTransformation.Base
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Presheaf.StrictHom.Base

module Cubical.Categories.Monoidal.NaturalTransformation.Instances.Presheaf.Next
  {ℓ ℓ' ℓO : Level} {A : Category ℓ ℓ'} {Wo : WFOrder ℓO ℓ'} (dir : DirectStr A Wo)
  where

open import Cubical.Categories.Direct.StrictDownset dir
open import Cubical.Categories.Monoidal.Functor.Instances.Presheaf.Later dir

open PshMon A ℓ
open LaxMonoidalFunctor
open StrongMonoidalFunctor
open StrongMonoidalStr

-- The identity, packaged as a lax monoidal endofunctor of 𝓟Mon.
Id-lax : LaxMonoidalFunctor 𝓟Mon 𝓟Mon
Id-lax .F = Id
Id-lax .laxmonstr = IdLaxStr

-- ▷ as a lax monoidal endofunctor of 𝓟Mon (projecting from ▷-strong).
▷-lax : LaxMonoidalFunctor 𝓟Mon 𝓟Mon
▷-lax .F = ▷
▷-lax .laxmonstr = ▷-strong .strmonstr .laxmonstr


-- `nextNT : Id ⇒ ▷` as a monoidal natural transformation.
-- For the cartesian target 𝓟Mon, both laws collapse to `refl` at the deepest
-- N-ob layer: both sides of the μ-law compute pointwise to
-- `(x .F-hom g px , y .F-hom g py)`; both sides of the ε-law compute to the
-- unique map into the terminal 𝟙.
-- TODO: The fact that it is monoidal follows that Id and ▷ are both product preserving
-- functors x Cartesian Monoidal Cats (𝓟Mon). However, some equalities are no longer strict
-- if using that construction.
open MonoidalNatTrans

nextNT-monoidal : MonoidalNatTrans 𝓟Mon 𝓟Mon Id-lax ▷-lax
nextNT-monoidal .φ = nextNT
nextNT-monoidal .monstr .MonoidalStr.ε-law =
  makePshHomStrictPath
    (funExt λ _ → funExt λ _ →
      makePshHomStrictPath (funExt λ _ → funExt λ _ → refl))
nextNT-monoidal .monstr .MonoidalStr.μ-law x y =
  makePshHomStrictPath
    (funExt λ _ → funExt λ _ →
      makePshHomStrictPath (funExt λ _ → funExt λ _ → refl))
