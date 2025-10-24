{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Fibration.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.More
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
open import Cubical.Categories.Displayed.Fibration.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module Cᴰ = Fibers Cᴰ
    module C = Category C

  module CartesianLiftNotation {x y}{f : C [ x , y ]}{yᴰ : Cᴰ.ob[ y ]}
    (f*yᴰ : CartesianLift Cᴰ yᴰ f) where
    private
      module f*yᴰ = UniversalElementⱽ f*yᴰ

    π : Cᴰ [ f ][ f*yᴰ.vertexⱽ , yᴰ ]
    π = Cᴰ.reind (C.⋆IdL f) f*yᴰ.elementⱽ

    introⱽ : ∀ {xᴰ}
      → Cᴰ [ f ][ xᴰ , yᴰ ]
      → Cᴰ.v[ x ] [ xᴰ , f*yᴰ.vertexⱽ ]
    introⱽ fᴰ = f*yᴰ.introⱽ (Cᴰ.reind (sym $ C.⋆IdL f) fᴰ)

    module _ {w wᴰ}{g : C [ w , x ]} where
      opaque
        βᴰ : (gᴰ : Cᴰ [ g C.⋆ f ][ wᴰ , yᴰ ])
          → (f*yᴰ.introᴰ gᴰ Cᴰ.⋆ᴰ π) ≡ gᴰ
        βᴰ gᴰ = (Cᴰ.rectify $ Cᴰ.≡out $
          Cᴰ.⟨⟩⋆⟨ sym $ Cᴰ.reind-filler _ _ ⟩
          ∙ Cᴰ.reind-filler _ _ ∙ Cᴰ.reind-filler _ _)
          ∙ f*yᴰ.βⱽ

        ηᴰ : (gᴰ : Cᴰ [ g ][ wᴰ , f*yᴰ.vertexⱽ ])
          → gᴰ ≡ f*yᴰ.introᴰ (gᴰ Cᴰ.⋆ᴰ π)
        ηᴰ gᴰ = Cᴰ.rectify $ Cᴰ.≡out $ sym $ f*yᴰ.∫ue.intro≡ $ change-base (C._⋆ f) C.isSetHom (sym $ C.⋆IdR g)
          (Cᴰ.⟨⟩⋆⟨ sym $ Cᴰ.reind-filler _ _ ⟩ ∙ Cᴰ.reind-filler _ _)

      UMP : Iso (Cᴰ [ g C.⋆ f ][ wᴰ , yᴰ ]) (Cᴰ [ g ][ wᴰ , f*yᴰ.vertexⱽ ])
      UMP = iso f*yᴰ.introᴰ (Cᴰ._⋆ᴰ π) (λ gfᴰ → sym $ ηᴰ gfᴰ) βᴰ

    module _ {xᴰ} where
      UMPⱽ : Iso (Cᴰ [ f ][ xᴰ , yᴰ ]) (Cᴰ.v[ x ] [ xᴰ , f*yᴰ.vertexⱽ ])
      UMPⱽ = iso introⱽ (Cᴰ._⋆ⱽᴰ π)
        (λ fⱽ → isoFun≡ UMP (Cᴰ.rectify $ Cᴰ.≡out $ sym (Cᴰ.reind-filler _ _) ∙ sym (Cᴰ.reind-filler _ _)))
        (λ fᴰ → Cᴰ.rectify $ Cᴰ.≡out $ sym (Cᴰ.reind-filler _ _) ∙ Cᴰ.≡in (βᴰ _) ∙ (sym $ Cᴰ.reind-filler _ _))
    open f*yᴰ hiding (βᴰ; βⱽ; ηᴰ; ηⱽ; introⱽ) public

  module FibrationNotation (isFib : isFibration Cᴰ) where
    private
      module Cⱽ = Fibers Cᴰ
      module CartesianLifts {x y}{f : C [ x , y ]}{yᴰ : Cᴰ.ob[ y ]} = CartesianLiftNotation (isFib yᴰ f)
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
        , λ fⱽ → Cᴰ.rectify $ Cᴰ.≡out $ f*yᴰ.∫ue.intro≡
            (change-base {C = Cᴰ [_][ _ , _ ]} (C._⋆ f) C.isSetHom
              (sym $ C.⋆IdL (f*yᴰ.∫ue.element .fst))
              (Cⱽ.⋆IdL _ ∙ sym (Cᴰ.reind-filler _ _) ∙ Cⱽ.⟨⟩⋆⟨ sym $ Cⱽ.reind-filler _ _ ⟩ ∙ Cᴰ.reind-filler _ _ )))

    open CartesianLifts hiding (vertexⱽ) public
    _*_ : ∀ {x}{y} (f : C [ x , y ]) (yᴰ : Cⱽ.ob[ y ])
      → Cⱽ.ob[ x ]
    f * yᴰ = CartesianLifts.vertexⱽ {f = f}{yᴰ}
    module _ {x}{y} (f : C [ x , y ]) where
      private
        f*F = FunctorComprehension (Cⱽ.HomᴰProf f) (fibration→HomᴰRepr f)
      open Functor
      open Iso
      _*F : Functor Cⱽ.v[ y ] Cⱽ.v[ x ]
      _*F = substFunctor f*F
        ((λ gⱽ → introⱽ (π Cᴰ.⋆ᴰⱽ gⱽ)) , (implicitFunExt (implicitFunExt $ funExt λ gⱽ → sym $ F-hom≡F-hom' gⱽ)))
        where
          F-hom≡F-hom' : ∀ {yⱽ yⱽ'}(gⱽ : Cⱽ.v[ y ] [ yⱽ , yⱽ' ])
            → introⱽ (π Cᴰ.⋆ᴰⱽ gⱽ) ≡ f*F ⟪ gⱽ ⟫
          F-hom≡F-hom' gⱽ = isoFun≡ UMPⱽ $ Cᴰ.rectify $ Cᴰ.≡out $
            Cᴰ.reind⟨ _ ⟩⟨ _ ⟩⟨ ((Cᴰ.reind-filler _ _ ∙ sym (Cᴰ.⋆IdL _)) ∙ (Cᴰ.≡in $ sym $ βᴰ _)) ⟩

    -- *F-id : ∀ {x}
    --   → NatIso ((C.id {x}) *F) Id
    -- *F-id {x} = record
    --   { trans = natTrans (λ xᴰ → π) λ {xᴰ}{yᴰ} fⱽ →
    --     Cⱽ.rectify $ Cⱽ.≡out $
    --       sym (Cⱽ.reind-filler _ _)
    --       ∙ Cᴰ.≡in (βⱽ _)
    --       ∙ Cⱽ.⋆IdL _
    --       ∙ {!!}
    --   ; nIso = {!!}
    --   }

    -- CartesianLiftF-Id :
    --   ∀ x → NatIso (CartesianLiftF-fiber (C.id {x})) Id
    -- CartesianLiftF-Id x = record { trans = {!!} ; nIso = {!!} }
    --   where
    --     t : NatTrans (CartesianLiftF-fiber (C.id {x})) Id
    --     t .NatTrans.N-ob xᴰ = Cⱽ.reind (C.⋆IdL C.id) id*xᴰ.elementᴰ
    --       where
    --         module id*xᴰ = UniversalElementⱽ (isFib xᴰ C.id)
    --     t .NatTrans.N-hom {xᴰ}{yᴰ} fⱽ = {!!}
    -- CartesianLiftF-Seq :
    --   ∀ {x y z}(f : C [ x , y ])(g : C [ y , z ])
    --     → NatIso
    --         (CartesianLiftF-fiber (f C.⋆ g))
    --         (CartesianLiftF-fiber f ∘F CartesianLiftF-fiber g)
    -- CartesianLiftF-Seq x = {!!}

    -- Triangle/Pentagon laws?

