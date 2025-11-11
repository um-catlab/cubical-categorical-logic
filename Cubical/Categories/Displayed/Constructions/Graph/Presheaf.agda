{-
  The Tabulator of a profunctor specializes to the displayed category of elements of a presheaf.
-}

module Cubical.Categories.Displayed.Constructions.Graph.Presheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct as BP
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Presheaf hiding (PshHom)
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.TotalCategory as TotalCat

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Constructions.StructureOver

private
  variable
    ℓC ℓC' ℓD ℓD' ℓP ℓQ ℓS : Level

open Category
open StructureOver
open Functor
open Functorᴰ
open Iso
open PshIso

module _ {C : Category ℓC ℓC'} (P : Presheaf C ℓP) where
  open StructureOver
  private
    module P = PresheafNotation P
    ElementStr : StructureOver C _ _
    ElementStr .ob[_] = P.p[_]
    -- this version lines up definitionally with fiber. See test-Element below
    ElementStr .Hom[_][_,_] f p q = (f P.⋆ q) ≡ p
    ElementStr .idᴰ = P.⋆IdL _
    ElementStr ._⋆ᴰ_ fy≡x gz≡y = P.⋆Assoc _ _ _ ∙ cong (_ P.⋆_) gz≡y ∙ fy≡x
    ElementStr .isPropHomᴰ = P.isSetPsh _ _
  Element : Categoryᴰ C ℓP ℓP
  Element = StructureOver→Catᴰ ElementStr

  hasPropHomsElement : hasPropHoms Element
  hasPropHomsElement = hasPropHomsStructureOver ElementStr

  private
    module ∫Element = Category (∫C Element)
    test-Element : ∀ x p y q
      → ∫Element.Hom[ (x , p) , (y , q) ] ≡ fiber (P._⋆ q) p
    test-Element x p y q = refl

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {P : Presheaf C ℓP}
  {Q : Presheaf D ℓQ}
  {F : Functor C D}
  (α : PshHet F P Q)
  where
  PshHet→ElementFunctorᴰ : Functorᴰ F (Element P) (Element Q)
  PshHet→ElementFunctorᴰ = mkPropHomsFunctor (hasPropHomsElement Q)
    (α .PshHom.N-ob _)
    λ f⋆p≡p' → (sym $ α .PshHom.N-hom _ _ _ _) ∙ cong (α .PshHom.N-ob _) f⋆p≡p'

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  (F : Functor C D)
  (x : C .ob)
  where
  Functor→ElementFunctorᴰ : Functorᴰ F (Element (C [-, x ])) (Element (D [-, F ⟅ x ⟆ ]))
  Functor→ElementFunctorᴰ = PshHet→ElementFunctorᴰ (Functor→PshHet F x)

module _ {C : Category ℓC ℓC'} (P : Presheaf C ℓP) (Q : Presheaf C ℓQ) (α : PshHom P Q) where
  private
    module α = PshHom α
  PshHom→ElementFunctorⱽ : Functorⱽ (Element P) (Element Q)
  PshHom→ElementFunctorⱽ = PshHet→ElementFunctorᴰ (α ⋆PshHom reindPshId≅ Q .trans)

module _
  {C : Category ℓC ℓC'}{D : Category ℓD ℓD'} (F : Functor C D) (Q : Presheaf D ℓQ)
  where
  private
    module Q = PresheafNotation Q
  reindPsh-intro : ∀ {P : Presheaf C ℓP}
    → (Functorᴰ F (Element P) (Element Q))
    → (Functorⱽ (Element P) (Element (reindPsh F Q)))
  reindPsh-intro {P = P} Fᴰ = mkPropHomsFunctor (hasPropHomsElement $ reindPsh F Q)
    (Fᴰ .F-obᴰ)
    (Fᴰ .F-homᴰ)

  reindPsh-π : Functorᴰ F (Element (reindPsh F Q)) (Element Q)
  reindPsh-π = mkPropHomsFunctor (hasPropHomsElement Q) (λ {x} z → z) λ {x} {y} {f} {xᴰ} {yᴰ} z → z

  reindPsh-UMPⱽ : ∀ {P : Presheaf C ℓP}
    → Iso (Functorⱽ (Element P) (Element (reindPsh F Q)))
          (Functorᴰ F (Element P) (Element Q))
  reindPsh-UMPⱽ .fun = reindPsh-π ∘Fᴰⱽ_
  reindPsh-UMPⱽ {P = P} .inv = reindPsh-intro {P = P}
  reindPsh-UMPⱽ .rightInv Fⱽ = Functorᴰ≡ (λ _ → refl) (λ _ → refl)
  reindPsh-UMPⱽ .leftInv Fᴰ = Functorᴰ≡ (λ _ → refl) (λ _ → refl)
