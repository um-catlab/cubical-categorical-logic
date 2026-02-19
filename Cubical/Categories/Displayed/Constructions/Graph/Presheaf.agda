{-
  The Tabulator of a profunctor specializes to the displayed category of elements of a presheaf.
-}

module Cubical.Categories.Displayed.Constructions.Graph.Presheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq
open import Cubical.HITs.Join as Join
open import Cubical.HITs.Join.More as Join
open import Cubical.HITs.PathEq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct as BP
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Presheaf hiding (PshHom)
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.StrictHom
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.TotalCategory as TotalCat

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Constructions.StructureOver
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.HLevels.More

private
  variable
    ℓ ℓC ℓC' ℓD ℓD' ℓP ℓQ ℓS : Level

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

  RedundElementStr : StructureOver C _ _
  RedundElementStr .ob[_] = P.p[_]
  RedundElementStr .Hom[_][_,_] f p q = PathEq (f P.⋆ q) p
  RedundElementStr .idᴰ = inl (P.⋆IdL _)
  RedundElementStr ._⋆ᴰ_ fyᴰ≡xᴰ gzᴰ≡yᴰ =
    inl (P.⋆Assoc _ _ _ ∙ P.⟨⟩⋆⟨ PathEq→Path P.isSetPsh gzᴰ≡yᴰ ⟩ ∙ PathEq→Path P.isSetPsh fyᴰ≡xᴰ)
  RedundElementStr .isPropHomᴰ = isPropPathEq P.isSetPsh

  RedundElement : Categoryᴰ C ℓP ℓP
  RedundElement = StructureOver→Catᴰ RedundElementStr

  -- Should we ask for a strict presheaf here?
  -- This can be better if the presheaf is strict
  EqElementStr : StructureOver C _ _
  EqElementStr .ob[_] = P.p[_]
  EqElementStr .Hom[_][_,_] f p q = (f P.⋆ q) Eq.≡ p
  EqElementStr .idᴰ = Eq.pathToEq (P.⋆IdL _)
  EqElementStr ._⋆ᴰ_ Eq.refl Eq.refl = Eq.pathToEq (P.⋆Assoc _ _ _)
  EqElementStr .isPropHomᴰ = Eq.isSet→isSetEq P.isSetPsh

  EqElement : Categoryᴰ C ℓP ℓP
  EqElement = StructureOver→Catᴰ EqElementStr

  hasPropHomsElement : hasPropHoms Element
  hasPropHomsElement = hasPropHomsStructureOver ElementStr

  hasPropHomsRedundElement : hasPropHoms RedundElement
  hasPropHomsRedundElement = hasPropHomsStructureOver RedundElementStr

  hasPropHomsEqElement : hasPropHoms EqElement
  hasPropHomsEqElement = hasPropHomsStructureOver EqElementStr

  private
    module ∫Element = Category (∫C Element)
    test-Element : ∀ x p y q
      → ∫Element.Hom[ (x , p) , (y , q) ] ≡ fiber (P._⋆ q) p
    test-Element x p y q = refl

  Element→EqElement : Functorⱽ Element EqElement
  Element→EqElement = mkPropHomsFunctor (hasPropHomsStructureOver EqElementStr) (λ {x} z → z) Eq.pathToEq

  EqElement→Element : Functorⱽ EqElement Element
  EqElement→Element = mkPropHomsFunctor (hasPropHomsStructureOver ElementStr) (λ {x} z → z) Eq.eqToPath

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
  {P : Presheaf C ℓP}
  {Q : Presheaf D ℓQ}
  {F : Functor C D}
  (α : PshHetStrict F P Q)
  where
  PshHet→ElementFunctorᴰStrict : Functorᴰ F (Element P) (Element Q)
  PshHet→ElementFunctorᴰStrict =
    mkPropHomsFunctor (hasPropHomsElement Q)
      (λ {x} → α .PshHomStrict.N-ob x) (α .PshHomStrict.N-hom _ _ _ _ _)

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {P : Presheaf C ℓP}
  {Q : Presheaf D ℓQ}
  {F : Functor C D}
  (α : PshHet' F P Q)
  where
  PshHet'→ElementFunctorᴰ : Functorᴰ F (RedundElement P) (RedundElement Q)
  PshHet'→ElementFunctorᴰ = mkPropHomsFunctor (hasPropHomsRedundElement Q)
    (λ {x} → α .PshHom'.N-ob x)
    (elimPropBoth (PresheafNotation.isSetPsh P) (λ _ → isPropPathEq (PresheafNotation.isSetPsh Q))
      (λ f⋆p≡p' → inl ((sym $ PathEq→Path (Q .F-ob (F-ob (F ^opF) _) .snd) (α .PshHom'.N-hom _ _ _ _)) ∙ cong (α .PshHom'.N-ob _) f⋆p≡p'))
      (λ { Eq.refl → symPE (Q .F-ob (F .F-ob _) .snd) (α .PshHom'.N-hom _ _ _ _) }))

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {P : Presheaf C ℓP}
  {Q : Presheaf D ℓQ}
  {F : Functor C D}
  (α : PshHetEq F P Q)
  where
  private
    module P = PresheafNotation P
    module Q = PresheafNotation Q
  PshHetEq→ElementFunctorᴰ : Functorᴰ F (EqElement P) (EqElement Q)
  PshHetEq→ElementFunctorᴰ = mkPropHomsFunctor (hasPropHomsEqElement Q)
    (λ {x} → α .PshHomEq.N-ob x)
    λ {x}{y}{f}{p}{q} fq≡p → α .PshHomEq.N-hom x y f q p fq≡p

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
  reindPsh-UMPⱽ .sec Fⱽ = Functorᴰ≡ (λ _ → refl)
    (λ _ → propHomsFiller (Element Q) (λ _ → λ _ _ → Q.isSetPsh _ _) _ _ _)
  reindPsh-UMPⱽ .ret Fᴰ = Functorᴰ≡ (λ _ → refl)
    (λ _ → propHomsFiller (Element Q) (λ _ → λ _ _ → Q.isSetPsh _ _) _ _ _)
