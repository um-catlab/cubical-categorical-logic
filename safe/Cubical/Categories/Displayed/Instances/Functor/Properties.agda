module Cubical.Categories.Displayed.Instances.Functor.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation.Base
import Cubical.Categories.Instances.TotalCategory as ∫

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Instances.Functor.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')(Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ') where
  open Functor
  open Functorᴰ
  open NatTrans
  open NatTransᴰ
  -- This probably belongs in TotalCategory.Properties but currently
  -- that's a circular dependency and also upstream.
  ∫F-Functor : Functor (∫.∫C (FUNCTORᴰ Cᴰ Dᴰ)) (FUNCTOR (∫.∫C Cᴰ) (∫.∫C Dᴰ))
  ∫F-Functor .F-ob (F , Fᴰ) = ∫.∫F Fᴰ
  ∫F-Functor .F-hom (α , αᴰ) .N-ob (x , xᴰ) = (α .N-ob x , αᴰ .N-obᴰ xᴰ)
  ∫F-Functor .F-hom (α , αᴰ) .NatTrans.N-hom (f , fᴰ) =
    ΣPathP (α .N-hom f , αᴰ .N-homᴰ fᴰ)
  ∫F-Functor .F-id = makeNatTransPath refl
  ∫F-Functor .F-seq f g = makeNatTransPath refl
  -- this should be definable like this but we'll just do it manually
  -- bc typechecking v slow that way
  --
  -- ∫F-Functor = CurryBifunctor
  --   (ParFunctorToBifunctor (∫.intro (appF _ _ ∘F (∫.Fst ×F ∫.Fst)) {!!}))
