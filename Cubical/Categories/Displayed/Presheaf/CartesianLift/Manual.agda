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

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓP ℓQ ℓPᴰ ℓQᴰ : Level

open Category
open Functor
open Functorᴰ
open PshHom

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

  -- TODO: make this functorial
  -- i.e. an input displayed category over C whose objects are Σ[ c ] P.p[ c ] × Pᴰ

open CartesianLift
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
         where
  private
    module P = PresheafNotation P
  isFibration = ∀ {x} (p : P.p[ x ]) → CartesianLift p Pᴰ

  module isFibrationNotation (isFibPᴰ : isFibration) where
    module _ {x} (p : P.p[ x ]) where
      open CartesianLift (isFibPᴰ p) using (p*Pᴰ) public
    module _ {x} {p : P.p[ x ]} where
      open CartesianLift (isFibPᴰ p) hiding (p*Pᴰ) public
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
         (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) (α : PshHom P Q)
         (isFibQᴰ : isFibration Qᴰ)
         where
  private
    module Cᴰ = Fibers Cᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
    module isFibQᴰ = isFibrationNotation Qᴰ isFibQᴰ
  isFibrationReind : isFibration (reind {P = P} α Qᴰ)
  isFibrationReind p .p*Pᴰ = isFibQᴰ.p*Pᴰ (α .N-ob _ p)
  isFibrationReind p .π = isFibQᴰ.π
  isFibrationReind p .isCartesian .fst qᴰ =
    isFibQᴰ.intro $ Qᴰ.reind {e = α .N-hom _ _ _ p} qᴰ
  isFibrationReind p .isCartesian .snd .fst qᴰ =
    Qᴰ.rectify $ Qᴰ.≡out $
      sym (Qᴰ.reind-filler)
      ∙ isFibQᴰ.β
      ∙ (sym $ Qᴰ.reind-filler)
  isFibrationReind p .isCartesian .snd .snd gᴰ =
    Cᴰ.rectify $ Cᴰ.≡out $ isFibQᴰ.intro≡ $ sym $
      Qᴰ.reind-filler ∙ Qᴰ.reind-filler

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
         (F : Functor C D)
         where
  module _ {P : Presheaf D ℓP} (Pᴰ : Presheafᴰ P Dᴰ ℓPᴰ) (isFibPᴰ : isFibration Pᴰ) where
    isFibrationReindFunc
      : isFibration (reindFunc F Pᴰ)
    isFibrationReindFunc p .p*Pᴰ = p*Pᴰ (isFibPᴰ p)
    isFibrationReindFunc p .π = π (isFibPᴰ p)
    isFibrationReindFunc p .isCartesian = isCartesian (isFibPᴰ p)

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  {P : Presheaf C ℓP}{Q : Presheaf D ℓQ}
  (α : PshHet F P Q){Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ}
  (isFibQᴰ : isFibration Qᴰ)
  where
  isFibrationReindHet : isFibration (reindHet α Qᴰ)
  isFibrationReindHet = isFibrationReind _ α (isFibrationReindFunc F Qᴰ isFibQᴰ)
