{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.CartesianLift.Manual where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions
import Cubical.Categories.Displayed.Constructions.Reindex.Base as Reindex
import Cubical.Categories.Displayed.Presheaf.CartesianLift as CL

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓP ℓQ ℓPᴰ ℓQᴰ : Level

open Category
open Functor
open Functorᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {P : Presheaf C ℓP}
         where
  private
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P
  record CartesianLift {x : C .ob} (p : P.p[ x ]) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) : Type
    (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max (ℓ-max ℓCᴰ ℓCᴰ') ℓPᴰ)) where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ
    field
      p*Pᴰ : Cᴰ.ob[ x ]
      π : Pᴰ.p[ p ][ p*Pᴰ ]
      isCartesian : ∀ {z zᴰ}{g : C [ z , x ]} →
        isIso (λ (gᴰ : Cᴰ [ g ][ zᴰ , p*Pᴰ ]) → gᴰ Pᴰ.⋆ᴰ π)

    opaque
      intro :
        ∀ {z zᴰ}{g : C [ z , x ]}
        → Pᴰ.p[ g P.⋆ p ][ zᴰ ]
        → Cᴰ [ g ][ zᴰ , p*Pᴰ ]
      intro = isCartesian .fst
    opaque
      unfolding intro
      private
        intro⟨_⟩ :
          ∀ {z zᴰ}{g g' : C [ z , x ]}
          → {gpᴰ : Pᴰ.p[ g P.⋆ p ][ zᴰ ]}
          → {gpᴰ' : Pᴰ.p[ g' P.⋆ p ][ zᴰ ]}
          → (g , gpᴰ) ≡ (g' , gpᴰ')
          → (g , intro gpᴰ) ≡ (g' , intro gpᴰ')
        intro⟨ gp≡gp' ⟩ i .fst = gp≡gp' i .fst
        intro⟨ gp≡gp' ⟩ i .snd = intro $ gp≡gp' i .snd

      intro⟨_⟩⟨_⟩ :
        ∀ {z zᴰ}{g g' : C [ z , x ]}
        → {gpᴰ : Pᴰ.p[ g P.⋆ p ][ zᴰ ]}
        → {gpᴰ' : Pᴰ.p[ g' P.⋆ p ][ zᴰ ]}
        → g ≡ g'
        → Path Pᴰ.p[ _ ] (_ , gpᴰ) (_ , gpᴰ')
        → Path Cᴰ.Hom[ _ , _ ] (_ , intro gpᴰ) (_ , intro gpᴰ')
      intro⟨ g≡g' ⟩⟨ gpᴰ≡gpᴰ' ⟩ =
        intro⟨ ΣPathP (g≡g' , (Pᴰ.rectify $ Pᴰ.≡out $ gpᴰ≡gpᴰ')) ⟩

      β :
        ∀ {z zᴰ}{g : C [ z , x ]}
        → {gpᴰ : Pᴰ.p[ g P.⋆ p ][ zᴰ ]}
        → Path Pᴰ.p[ _ ]
            (_ , (intro gpᴰ Pᴰ.⋆ᴰ π))
            (_ , gpᴰ)
      β = Pᴰ.≡in $ isCartesian .snd .fst _

      intro≡ :
        ∀ {z zᴰ}{g : C [ z , x ]}
        → {gpᴰ : Pᴰ.p[ g P.⋆ p ][ zᴰ ]}
        → {gᴰ : Cᴰ [ g ][ zᴰ , p*Pᴰ ]}
        → Path Pᴰ.p[ _ ]
            (_ , gpᴰ)
            (_ , (gᴰ Pᴰ.⋆ᴰ π))
        → Path Cᴰ.Hom[ _ , _ ]
            (_ , intro gpᴰ)
            (_ , gᴰ)
      intro≡ gp≡gπ =
        intro⟨ refl ⟩⟨ gp≡gπ ⟩
        ∙ (Cᴰ.≡in (isCartesian .snd .snd _))

  module _ {x} (p : P.p[ x ]) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (cL : CartesianLift p Pᴰ) where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ
      module cL = CartesianLift cL
      module p*Pᴰ = PresheafⱽNotation (reindYo p Pᴰ)
    open UniversalElementⱽ
    ManualCartesianLift→CartesianLift : CL.CartesianLift p Pᴰ
    ManualCartesianLift→CartesianLift .vertexⱽ = cL.p*Pᴰ
    ManualCartesianLift→CartesianLift .elementⱽ = Cᴰ.idᴰ Pᴰ.⋆ᴰ cL.π
    ManualCartesianLift→CartesianLift .universalⱽ .fst = cL.isCartesian .fst
    ManualCartesianLift→CartesianLift .universalⱽ {y} {yᴰ} {f} .snd =
      subst
        motive
        (funExt (λ fᴰ → Pᴰ.rectify $ Pᴰ.≡out $
          Pᴰ.⟨⟩⋆⟨ sym $ Pᴰ.⋆IdL _ ⟩ ∙ Pᴰ.reind-filler _ _ ∙ Pᴰ.reind-filler _ _))
        (cL.isCartesian .snd)
      where
        motive : (Cᴰ [ f ][ yᴰ , cL.p*Pᴰ ] → Pᴰ.p[ f P.⋆ p ][ yᴰ ]) → Type _
        motive introⱽ = section introⱽ (cL.isCartesian .fst) × retract introⱽ (cL.isCartesian .fst)

  -- TODO: make this functorial
  -- i.e. an input displayed category over C whose objects are Σ[ c ] P.p[ c ] × Pᴰ

open CartesianLift
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
         where
  private
    module P = PresheafNotation P
  isFibration = ∀ {x} (p : P.p[ x ]) → CartesianLift p Pᴰ

  isFibrationManual→isFibration : isFibration → CL.isFibration Pᴰ
  isFibrationManual→isFibration isFib p =
    ManualCartesianLift→CartesianLift p Pᴰ (isFib p)

  module isFibrationNotation (isFibPᴰ : isFibration) where
    module _ {x} (p : P.p[ x ]) where
      open CartesianLift (isFibPᴰ p) using (p*Pᴰ) public
    module _ {x} {p : P.p[ x ]} where
      open CartesianLift (isFibPᴰ p) hiding (p*Pᴰ) public
