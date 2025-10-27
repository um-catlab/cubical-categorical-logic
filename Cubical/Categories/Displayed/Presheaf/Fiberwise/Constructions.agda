{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Fiberwise.Constructions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.More

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Fiberwise
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Morphism
-- open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex
--   renaming (reind to reindPshᴰ)
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
  -- renaming (π to Reindexπ; reindex to CatReindex)
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Fibration.Properties

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Functorᴰ
open Iso
open PshHom
open PshIso


-- A fiberwise presheaf is the definition of a presheaf that is
-- applicable to an indexed category C^op → Cat

-- i.e. if we have Cᴰ : C^op → Cat, then we want a section
-- Pⱽ : (x : C^op) → Psh Cᴰ.v[ x ] . This isn't right though.
--
-- (p : P[ x ]) → Psh Cᴰ.v[ x ]
-- (f : C [ y , x ]) → Psh Cᴰ.v[ x ] ⊸ Psh Cᴰ.v[ y ] over f*

module _ {C : Category ℓC ℓC'} {P : Presheaf C ℓP} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{isFib : isFibration Cᴰ}
  where
  private
    module P = PresheafNotation P
    module Cᴰ = Fibers Cᴰ
    module C = Category C
    module isFib = FibrationNotation isFib
  module _ (Pᶠ : Presheafᶠ P Cᴰ isFib ℓPᴰ)(Qᶠ : Presheafᶠ P Cᴰ isFib ℓQᴰ) where
    private
      module Pᶠ = Presheafᶠ Pᶠ
      module Qᶠ = Presheafᶠ Qᶠ
    _×ᶠ_ : Presheafᶠ P Cᴰ isFib (ℓ-max ℓPᴰ ℓQᴰ)
    _×ᶠ_ .Presheafᶠ.P-obᶠ p = Pᶠ.P-obᶠ p ×Psh Qᶠ.P-obᶠ p
    _×ᶠ_ .Presheafᶠ.P-homᶠ f p = (Pᶠ.P-homᶠ f p ×PshHom Qᶠ.P-homᶠ f p) ⋆PshHom invPshIso (restrictPsh× _ _ _) .trans
    _×ᶠ_ .Presheafᶠ.P-idᶠ (pᴰ , qᴰ) = ×≡Snd-hSet P.isSetPsh
      (Pᶠ.P-idᶠ (π₁ (Pᶠ.P-obᶠ _) (Qᶠ.P-obᶠ _) .N-ob _ (pᴰ , qᴰ)))
      (Qᶠ.P-idᶠ (π₂ (Pᶠ.P-obᶠ _) (Qᶠ.P-obᶠ _) .N-ob _ (pᴰ , qᴰ)))
    _×ᶠ_ .Presheafᶠ.P-seqᶠ g f (pᴰ , qᴰ) = ×≡Snd-hSet P.isSetPsh
      (Pᶠ.P-seqᶠ g f (π₁ (Pᶠ.P-obᶠ _) (Qᶠ.P-obᶠ _) .N-ob _ (pᴰ , qᴰ)))
      (Qᶠ.P-seqᶠ g f (π₂ (Pᶠ.P-obᶠ _) (Qᶠ.P-obᶠ _) .N-ob _ (pᴰ , qᴰ)))

    _⇒Largeᶠ_ : Presheafᶠ P Cᴰ isFib _
    _⇒Largeᶠ_ .Presheafᶠ.P-obᶠ p = (Pᶠ.P-obᶠ p) ⇒PshLarge (Qᶠ.P-obᶠ p)
    _⇒Largeᶠ_ .Presheafᶠ.P-homᶠ = {!!}
    _⇒Largeᶠ_ .Presheafᶠ.P-idᶠ = {!!}
    _⇒Largeᶠ_ .Presheafᶠ.P-seqᶠ = {!!}
  module _ (Pᶠ : Presheafᶠ P Cᴰ isFib ℓPᴰ)(Qᶠ : Presheafᶠ P Cᴰ isFib ℓQᴰ) where
    private
      module Pᶠ = Presheafᶠ Pᶠ
      module Qᶠ = Presheafᶠ Qᶠ

module _ {D : Category ℓD ℓD'}{C : Category ℓC ℓC'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}{isFibDᴰ : isFibration Dᴰ}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{isFibCᴰ : isFibration Cᴰ}
  {P : Presheaf C ℓP}
  where
  private
    module P = PresheafNotation P
    module Cᴰ = Fibers Cᴰ
    module C = Category C
    module isFibCᴰ = FibrationNotation isFibCᴰ
    module isFibDᴰ = FibrationNotation isFibDᴰ
  module _ {F : Functor D C}(Fᴰ : Functorᴰ F Dᴰ Cᴰ)(Pᶠ : Presheafᶠ P Cᴰ isFibCᴰ ℓPᴰ) where
    private
      module Pᶠ = Presheafᶠ Pᶠ
    -- we don't *need* Fᴰ to preserve cartesian lifts, right?
    restrictPshᶠ : Presheafᶠ (restrictPsh F P) Dᴰ isFibDᴰ ℓPᴰ
    restrictPshᶠ .Presheafᶠ.P-obᶠ p = restrictPsh (fiberF Fᴰ _) (Pᶠ.P-obᶠ p)
    restrictPshᶠ .Presheafᶠ.P-homᶠ f p .N-ob xᴰ pᴰ =
      isFibCᴰ.introⱽ (Fᴰ .F-homᴰ isFibDᴰ.π) Pᶠ.⋆ⱽᴰ (F ⟪ f ⟫ Pᶠ.* pᴰ)
    restrictPshᶠ .Presheafᶠ.P-homᶠ f p .N-hom xᴰ xᴰ' fⱽ pᴰ =
      Pᶠ.Pⱽ.⟨⟩⋆⟨ Pᶠ.*-natural _ _ _ ⟩
      ∙ {!!}
    restrictPshᶠ .Presheafᶠ.P-idᶠ pᴰ = {!!}
    restrictPshᶠ .Presheafᶠ.P-seqᶠ = {!!}
    
  --     F*Cᴰ = reindex Cᴰ F
  --     module F*Cᴰ = Fibers F*Cᴰ
  -- module _ (F : Functor D C) (Pᶠ : Presheafᶠ P Cᴰ isFib ℓPᴰ) where
  --   private
  --     module Pᶠ = Presheafᶠ Pᶠ
  --     F*Cᴰ = reindex Cᴰ F
  --     module F*Cᴰ = Fibers F*Cᴰ
  --   -- can this be more general?
  --   restrictPshᶠ : Presheafᶠ (restrictPsh F P) (reindex Cᴰ F) (isFibrationReindex F isFib) ℓPᴰ
  --   restrictPshᶠ .Presheafᶠ.P-obᶠ p = restrictPsh (fiberF (π Cᴰ F) _) (Pᶠ.P-obᶠ p)
  --   restrictPshᶠ .Presheafᶠ.P-homᶠ f p .N-ob xᴰ pᴰ = (F ⟪ f ⟫) Pᶠ.* pᴰ
  --   restrictPshᶠ .Presheafᶠ.P-homᶠ f p .N-hom xᴰ xᴰ' fⱽ pᴰ =
  --     ((F ⟪ f ⟫) Pᶠ.* ((fiberF (π Cᴰ F) _ ⟪ fⱽ ⟫) Pᶠ.Pⱽ.⋆ pᴰ))
  --       ≡⟨ Pᶠ.*-natural (F ⟪ f ⟫) (fiberF (π Cᴰ F) _ ⟪ fⱽ ⟫) pᴰ ∙
  --         Pᶠ.Pⱽ.⟨ Cᴰ.rectify $ Cᴰ.≡out $
  --           {!!}
  --           ∙ Cᴰ.reind-filler _ _
  --           ⟩⋆⟨⟩ ⟩
  --     _ ∎
  --   restrictPshᶠ .Presheafᶠ.P-idᶠ {d}{Fdᴰ}{p} pᴰ =
  --     {!!}
  --   restrictPshᶠ .Presheafᶠ.P-seqᶠ = {!!}
