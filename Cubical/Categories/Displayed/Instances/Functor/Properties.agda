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
open import Cubical.Categories.Displayed.HLevels
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

-- When the target has propositional displayed homs, displayed natural
-- transformations are determined by their components and the
-- displayed functor category again has propositional homs.
module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (propHoms : hasPropHoms Dᴰ) where
  open NatTrans
  open NatTransᴰ
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  mkPropHomsNatTransᴰ : {F G : Functor C D} {α : NatTrans F G}
    {Fᴰ : Functorᴰ F Cᴰ Dᴰ} {Gᴰ : Functorᴰ G Cᴰ Dᴰ}
    → (∀ {x} (xᴰ : Cᴰ.ob[ x ])
      → Dᴰ.Hom[ α .N-ob x ][ Fᴰ .Functorᴰ.F-obᴰ xᴰ , Gᴰ .Functorᴰ.F-obᴰ xᴰ ])
    → NatTransᴰ α Fᴰ Gᴰ
  mkPropHomsNatTransᴰ αᴰ .N-obᴰ = αᴰ
  mkPropHomsNatTransᴰ αᴰ .N-homᴰ _ =
    isProp→PathP (λ i → propHoms _ _ _) _ _

  hasPropHomsFUNCTORᴰ : hasPropHoms (FUNCTORᴰ Cᴰ Dᴰ)
  hasPropHomsFUNCTORᴰ α Fᴰ Gᴰ αᴰ βᴰ =
    makeNatTransPathᴰ Cᴰ Dᴰ refl
      (λ i xᴰ → propHoms _ _ _ (αᴰ .N-obᴰ xᴰ) (βᴰ .N-obᴰ xᴰ) i)
