-- Displayed and vertical (op)cartesian lifts and (op)fibrations
--
-- These apply to "doubly displayed" categories. Cᴰᴰ ↦ Cᴰ ↦ C
--
-- Given a morphism f : C [ x , y ] and lift yᴰ ↦ y, a cartesian lift f*yᴰ represents (yoRec f) * Cᴰ [-][-, yᴰ ]
--
-- Now consider that we have a lift yᴰᴰ ↦ yᴰ. We can define a displayed cartesian lift in two ways:
-- 1. A displayed cartesian lift f*yᴰᴰ over the cartesian lift f*yᴰ as a displayed universal property
-- 2. simply a cartesian lift of yᴰᴰ along (f , π)

-- The second is manifestly fiberwise (so preserved by reindexing) but
-- the former is better for elimination principles.

-- TODO:
-- any displayed notion should correspond to a property of the projection of the total category
-- In the case of a cartesian lift/fibration, we would expect this to be:
-- - if f*yᴰ is the lift of yᴰ along f
-- - and f*yᴰᴰ is displayed cartesian lift over f*yᴰ
-- - then we should have a cartesian lift f*(yᴰ,yᴰᴰ) in the displayed total category ∫Cᴰ Cᴰᴰ which definitionally projects to f*yᴰ and f*yᴰᴰ

-- In classical fibration terms, this corresponds to the fact that fibrations compose:
-- - if Cᴰᴰ is a fibration, then we have all vertical cartesian lifts
-- - so in turn we have all displayed cartesian lifts
-- - so in turn we have that the displayed total category ∫Cᴰ Cᴰᴰ ↦ C is a fibration
-- and classically the displayed total category is just the composition of projections Cᴰᴰ → Cᴰ → C

{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration.Displayed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Reindex
open import Cubical.Categories.Displayed.Instances.Reindex.Eq.Base
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable

private
  variable
    ℓ ℓ' ℓ'' ℓᴰ ℓᴰ' ℓᴰᴰ ℓᴰᴰ' ℓD ℓD' ℓCᴰ ℓCᴰ' : Level

open PshHom
open PshIso
open UniversalElement

-- TODO: generalize this all from fibrations to arbitrary (displayed) presheaves?
module Liftsᴰ⁺ⱽ (K : Category ℓ ℓ') (C : Categoryᴰ K ℓᴰ ℓᴰ') (Cᴰ : Categoryᴰ (∫C C) ℓᴰᴰ ℓᴰᴰ')
  {k1 k2} (≤ : K [ k1 , k2 ]) where
  private
    module K = Category K
    module C = Fibers C
    module Cᴰ = Fibers Cᴰ
  open PresheafᴰNotation renaming (∫ to ∫P)
  module _ (B : C.ob[ k2 ]) where
    ≤*-Spec : Presheafⱽ k1 C ℓᴰ'
    ≤*-Spec = CartesianLiftPshSpec (K [-, k2 ]) C (C [-][-, B ]) ≤

    ∫≤*-Spec : Presheaf (∫C C) (ℓ-max ℓ' ℓᴰ')
    ∫≤*-Spec = (∫P _ _ ≤*-Spec)

    π≤k : PshHom ∫≤*-Spec (∫C C [-, _ , B ])
    π≤k = ∫PshHomᴰ {α = yoRec (K [-, k2 ]) _} idPshHom ⋆PshHom (∫Repr-iso C) .PshIso.trans

  ≤*ᴰ-Specᴰ : ∀ {B}(Bᴰ : Cᴰ.ob[ k2 , B ]) → Presheafᴰ (∫≤*-Spec B) Cᴰ ℓᴰᴰ'
  ≤*ᴰ-Specᴰ {B} Bᴰ = reindPshᴰNatTrans (π≤k B) (Cᴰ [-][-, Bᴰ ])

  module _ {B} (≤*B : Representableⱽ C k1 (≤*-Spec B)) where
    ≤*-π : C [ _ ][ ≤*B .fst , B ]
    ≤*-π = ≤*B .snd .PshIso.trans .PshHom.N-ob (k1 , ≤*B .fst , K.id) C.idᴰ

    half-≤*-π' : PshHom (∫C C [-, _ , ≤*B .fst ]) (∫≤*-Spec B)
    half-≤*-π' = invPshIso (∫Repr-iso C) .PshIso.trans ⋆PshHom ∫PshHomⱽ (≤*B .snd .PshIso.trans)

    ≤*-π* ≤*-π*' : PshHom (∫C C [-, _ , ≤*B .fst ]) (∫C C [-, _ , B ])
    ≤*-π* = yoRec _ (_ , ≤*-π)
    ≤*-π*' = half-≤*-π' ⋆PshHom π≤k B

    ≤*-π*≡≤*-π*' : ≤*-π* ≡ ≤*-π*'
    ≤*-π*≡≤*-π*' = yoInd _ _ _ $ C.⋆IdL _

    module _ (Bᴰ : Cᴰ.ob[ _ , B ]) where
      ≤*ᴰ-Specⱽ ≤*ᴰ-Specⱽ' : Presheafⱽ (_ , ≤*B .fst) Cᴰ ℓᴰᴰ'
      ≤*ᴰ-Specⱽ = reindPshᴰNatTrans ≤*-π* $ Cᴰ [-][-, Bᴰ ]
      ≤*ᴰ-Specⱽ' = reindPshᴰNatTrans ≤*-π*' $ Cᴰ [-][-, Bᴰ ]

      ≤*ᴰ-Specⱽ≅ᴰ : PshIso ≤*ᴰ-Specⱽ (reindPshᴰNatTrans half-≤*-π' (≤*ᴰ-Specᴰ Bᴰ))
      ≤*ᴰ-Specⱽ≅ᴰ =
        reindPshᴰNatTrans-Path ≤*-π* ≤*-π*' ≤*-π*≡≤*-π*' (Cᴰ [-][-, Bᴰ ])
        ⋆PshIso (invPshIso $ reindPshᴰNatTrans-tri half-≤*-π' (π≤k B) ≤*-π*' (Cᴰ [-][-, Bᴰ ]) refl)

  module _ (≤* : Quadrable C ≤) where
    ∫≤* : ∀ B → RepresentationPshIso (∫≤*-Spec B)
    ∫≤* B = ∫Representableⱽ C k1 (≤*-Spec B) (≤* B)

    Quadrableᴰ Quadrableⱽ : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓᴰ) ℓᴰ') ℓᴰᴰ) ℓᴰᴰ')
    Quadrableᴰ = ∀ {B : C.ob[ k2 ]}(Bᴰ : Cᴰ.ob[ _ , B ]) → Representableᴰ Cᴰ (∫≤*-Spec B) (≤*ᴰ-Specᴰ Bᴰ) $ ∫≤* B
    Quadrableⱽ = ∀ {B : C.ob[ k2 ]} → Quadrable Cᴰ (_ , ≤*-π (≤* B) )

    Quadrableⱽ→ᴰ : Quadrableⱽ → Quadrableᴰ
    Quadrableⱽ→ᴰ ≤*ⱽ Bᴰ .fst = ≤*ⱽ Bᴰ .fst
    Quadrableⱽ→ᴰ ≤*ⱽ Bᴰ .snd = FiberwisePshIsoᴰ→PshIsoᴰ $
      ≤*ⱽ Bᴰ .snd ⋆PshIso ≤*ᴰ-Specⱽ≅ᴰ (≤* _) Bᴰ

    -- Notation for a displayed cartesian lift, mirroring
    -- CartesianLiftNotation. The generic laws of RepresentableᴰNotation
    -- live in the total space of ≤*ᴰ-Specᴰ Bᴰ; here they are converted
    -- to paths in Cᴰ.Hom[ _ , _ ] so clients can rectify them along a
    -- base path.
    module CartesianLiftᴰNotation {B : C.ob[ k2 ]} {Bᴰ : Cᴰ.ob[ _ , B ]}
      (≤*ᴰBᴰ : Representableᴰ Cᴰ (∫≤*-Spec B) (≤*ᴰ-Specᴰ Bᴰ) (∫≤* B))
      where
      private
        module Spec = PresheafNotation (∫≤*-Spec B)
        module Specᴰ = PresheafᴰNotation Cᴰ (∫≤*-Spec B) (≤*ᴰ-Specᴰ Bᴰ)
        module R = RepresentableᴰNotation Cᴰ (∫≤*-Spec B) (≤*ᴰ-Specᴰ Bᴰ) ≤*ᴰBᴰ

        toHom : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]}
          → Σ[ p ∈ Spec.p[ Γ ] ] Specᴰ.p[ p ][ Γᴰ ]
          → Cᴰ.Hom[ (Γ , Γᴰ) , (_ , Bᴰ) ]
        toHom (p , pᴰ) = π≤k B .N-ob _ p , pᴰ

      open R public using (vertexᴰ ; introᴰ ; cong-introᴰ)
        renaming (_⋆elementᴰ to _⋆πⱽ)

      πⱽ : Cᴰ [ K.id K.⋆ ≤ , ≤*-π (≤* B) ][ vertexᴰ , Bᴰ ]
      πⱽ = R.elementᴰ

      opaque
        ⟨_⟩⋆πⱽ : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {g g'}
          {gᴰ : Cᴰ [ g ][ Γᴰ , vertexᴰ ]} {gᴰ' : Cᴰ [ g' ][ Γᴰ , vertexᴰ ]}
          → gᴰ Cᴰ.∫≡ gᴰ'
          → (gᴰ ⋆πⱽ) Cᴰ.∫≡ (gᴰ' ⋆πⱽ)
        ⟨ gᴰ≡gᴰ' ⟩⋆πⱽ = cong toHom R.⟨ gᴰ≡gᴰ' ⟩⋆elementᴰ

        ⋆πⱽ-natural : ∀ {Δ Γ} {Δᴰ : Cᴰ.ob[ Δ ]} {Γᴰ : Cᴰ.ob[ Γ ]} {γ g}
          (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ]) (gᴰ : Cᴰ [ g ][ Γᴰ , vertexᴰ ])
          → ((γᴰ Cᴰ.⋆ᴰ gᴰ) ⋆πⱽ) Cᴰ.∫≡ (γᴰ Cᴰ.⋆ᴰ (gᴰ ⋆πⱽ))
        ⋆πⱽ-natural γᴰ gᴰ =
          cong toHom (R.⋆elementᴰ-natural γᴰ gᴰ) ∙ Cᴰ.reind-filler⁻ _

        ⋆πⱽ≡⋆ᴰπⱽ : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {g}
          (gᴰ : Cᴰ [ g ][ Γᴰ , vertexᴰ ])
          → (gᴰ ⋆πⱽ) Cᴰ.∫≡ (gᴰ Cᴰ.⋆ᴰ πⱽ)
        ⋆πⱽ≡⋆ᴰπⱽ gᴰ =
          cong toHom (R.⋆elementᴰ≡⋆ᴰelementᴰ gᴰ) ∙ Cᴰ.reind-filler⁻ _

        βᴰ : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {p : Spec.p[ Γ ]}
          (gfᴰ : Specᴰ.p[ p ][ Γᴰ ])
          → (introᴰ gfᴰ ⋆πⱽ) Cᴰ.∫≡ gfᴰ
        βᴰ gfᴰ = cong toHom (R.∫βᴰ gfᴰ)

        βᴰ' : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {p : Spec.p[ Γ ]}
          (gfᴰ : Specᴰ.p[ p ][ Γᴰ ])
          → (introᴰ gfᴰ Cᴰ.⋆ᴰ πⱽ) Cᴰ.∫≡ gfᴰ
        βᴰ' gfᴰ = sym (⋆πⱽ≡⋆ᴰπⱽ _) ∙ βᴰ gfᴰ

        ηᴰ : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {g}
          (gᴰ : Cᴰ [ g ][ Γᴰ , vertexᴰ ])
          → gᴰ Cᴰ.∫≡ introᴰ (gᴰ ⋆πⱽ)
        ηᴰ = R.∫ηᴰ

    module QuadrableᴰNotation (≤*ᴰ : Quadrableᴰ)
      {B : C.ob[ k2 ]} {Bᴰ : Cᴰ.ob[ _ , B ]} =
      CartesianLiftᴰNotation (≤*ᴰ Bᴰ)
