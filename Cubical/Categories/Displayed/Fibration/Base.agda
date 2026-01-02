{-# OPTIONS --lossy-unification #-}
{- This file takes a long time to type check -}
module Cubical.Categories.Displayed.Fibration.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Profunctor.General

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Profunctor
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.Displayed.FunctorComprehension
import Cubical.Categories.Displayed.Constructions.Reindex.Base as Reindex
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex
open import Cubical.Categories.Displayed.Presheaf.CartesianLift
  using () renaming (
    CartesianLift to PshᴰCartesianLift
  ; isFibration to PshᴰisFibration) public

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level


module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module Cᴰ = Fibers Cᴰ
    module C = Category C

  -- Definition #1:
  -- The Cartesian lifting of a displayed object yᴰ along f
  -- is precisely the data that Presheafᴰ reindexing of Cᴰ [-][-, yᴰ ]
  -- by f is representable
  CartesianLift :
    {x y : C.ob}(yᴰ : Cᴰ.ob[ y ]) (f : C [ x , y ]) → Type _
  CartesianLift {x} yᴰ f = PshᴰCartesianLift f (Cᴰ [-][-, yᴰ ])

  isFibration : Type _
  isFibration =
    ∀ {c : C.ob} (cᴰ : Cᴰ.ob[ c ]) → PshᴰisFibration (Cᴰ [-][-, cᴰ ])

  -- TODO port to the this version of cartesian lift
  module _ (isFib : isFibration) where
    private
      module Cⱽ = Fibers Cᴰ
    module _ {x}{y}(f : C [ x , y ]) (yᴰ : Cᴰ.ob[ y ]) where
      private
        module f*yᴰ = UniversalElementⱽ (isFib yᴰ f)
      fibration→HomᴰRepr :
        UniversalElement Cⱽ.v[ x ] (Cⱽ.HomᴰProf f ⟅ yᴰ ⟆)
      fibration→HomᴰRepr .UniversalElement.vertex = f*yᴰ.vertexⱽ
      fibration→HomᴰRepr .UniversalElement.element =
        Cⱽ.reind (C.⋆IdL f) f*yᴰ.elementⱽ
      fibration→HomᴰRepr .UniversalElement.universal xᴰ = isIsoToIsEquiv ((λ fᴰ → f*yᴰ.introᴰ (Cⱽ.idᴰ Cⱽ.⋆ᴰ fᴰ))
        , (λ fᴰ → Cᴰ.rectify $ Cᴰ.≡out $ (sym (Cᴰ.reind-filler _ _) ∙ Cᴰ.⟨⟩⋆⟨ sym $ Cᴰ.reind-filler _ _  ⟩)
          ∙ Cᴰ.reind-filler _ _ ∙ Cᴰ.reind-filler _ _ ∙ Cᴰ.≡in f*yᴰ.βⱽ
          ∙ Cᴰ.⋆IdL _)
        , λ fⱽ → Cᴰ.rectify $ Cᴰ.≡out $ f*yᴰ.∫ue.intro≡ $ change-base {C = Cᴰ [_][ xᴰ , yᴰ ]} (C._⋆ f)
          C.isSetHom ((sym $ C.⋆IdL (f*yᴰ.∫ue.element .fst)))
          (Cⱽ.⋆IdL _ ∙ sym (Cᴰ.reind-filler _ _) ∙ Cⱽ.⟨⟩⋆⟨ sym $ Cⱽ.reind-filler _ _ ⟩ ∙ Cᴰ.reind-filler _ _)
        )

    CartesianLiftF-fiber :
      ∀ {x}{y} (f : C [ x , y ]) → Functor Cⱽ.v[ y ] Cⱽ.v[ x ]
    CartesianLiftF-fiber f =
      FunctorComprehension (Cⱽ.HomᴰProf f) (fibration→HomᴰRepr f)

  -- -- Definition #2: This is the "textbook" compositional
  -- -- definition. It suffers from very slow performance
  -- CartesianLift' : {x y : C.ob}(yᴰ : Cᴰ.ob[ y ]) (f : C [ x , y ]) → Type _
  -- CartesianLift' yᴰ f = RightAdjointAtⱽ (Δ/C C Cᴰ) (_ , yᴰ , f)
