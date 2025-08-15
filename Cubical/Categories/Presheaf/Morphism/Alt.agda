{- This is intended to replace Presheaf.Morphism upstream -}
{-# OPTIONS --safe #-}
module Cubical.Categories.Presheaf.Morphism.Alt where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Constructions.Lift
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Limits
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable

{-

  Given two presheaves P and Q on the same category C, a morphism
  between them is a natural transformation. Here we generalize this to
  situations where P and Q are presheaves on *different*
  categories. This is equivalent to the notion of morphism of
  fibrations if viewing P and Q as discrete fibrations.

  Given a functor F : C → D, a presheaf P on C and a presheaf Q on D,
  we can define a homomorphism from P to Q over F as a natural
  transformation from P to Q o F^op. (if we had implicit cumulativity)

  These are the homs of a 2-category of presheaves displayed over the
  2-category of categories.

-}
private
  variable
    ℓc ℓc' ℓd ℓd' ℓp ℓq : Level

open Category
open Contravariant
open Functor
open NatTrans
open UniversalElement

module _ {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}
         (F : Functor C D)
         (P : Presheaf C ℓp)
         (Q : Presheaf D ℓq) where
  -- We define the displayed morphism by reindexing the codomain
  PshHet : Type (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓp) ℓq)
  PshHet = PshHom P (Q ∘F (F ^opF))

module _ {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}
         (F : Functor C D) (c : C .ob) where
  Functor→PshHet : PshHet F (C [-, c ]) (D [-, F ⟅ c ⟆ ])
  Functor→PshHet .fst = λ x → F .F-hom
  Functor→PshHet .snd = λ x y → F .F-seq

module _ {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}
         {F : Functor C D}
         {P : Presheaf C ℓp}
         {Q : Presheaf D ℓq}
         (Fᴰ : PshHet F P Q)
         where
  private
    module P = PresheafNotation P
    module Q = PresheafNotation Q
  ∫F : Functor (∫ᴾ P) (∫ᴾ Q)
  ∫F .F-ob (c , p) = F ⟅ c ⟆ , Fᴰ .fst c p
  ∫F .F-hom (f , tri) = (F ⟪ f ⟫) ,
    (sym $ Fᴰ .snd _ _ _ _)
    ∙ cong (Fᴰ .fst _) tri
  ∫F .F-id = Σ≡Prop (λ _ → Q.isSetPsh _ _) (F .F-id)
  ∫F .F-seq (f , _) (g , _) = Σ≡Prop (λ _ → Q.isSetPsh _ _) (F .F-seq f g)

  becomesUniversal :
    ∀ (v : C .ob) (e : P.p[ v ]) → Type _
  becomesUniversal v e = isUniversal D Q (F ⟅ v ⟆) (Fᴰ .fst _ e)

  becomesUniversal→UniversalElement :
    ∀ {v e}
    → becomesUniversal v e
    → UniversalElement D Q
  becomesUniversal→UniversalElement becomesUE .vertex = _
  becomesUniversal→UniversalElement becomesUE .element = _
  becomesUniversal→UniversalElement becomesUE .universal = becomesUE

  preservesUniversalElement : UniversalElement C P → Type _
  preservesUniversalElement ue =
    becomesUniversal (ue .vertex) (ue .element)

  preservesUniversalElements : Type _
  preservesUniversalElements = ∀ ue → preservesUniversalElement ue

  preservesUniversalElement→UniversalElement :
    (ue : UniversalElement C P)
    → preservesUniversalElement ue
    → UniversalElement D Q
  preservesUniversalElement→UniversalElement ue presUniversality =
    becomesUniversal→UniversalElement presUniversality

  -- If a presheaf preserves any universal element then it preserves
  -- all of them since universal elements are unique up to unique
  -- isomorphism. This is for free if the category is univalent
  -- because in that case UniversalElement C P is a Prop.

  -- This lemma, like other applications of Yoneda should be taken as
  -- an indication that it is probably fine to build the library
  -- around the seemingly weaker notion of preservesUniversalElement
  -- and push uses of this lemma to users rather than to pervasively
  -- use this in the library itself. YMMV
  preservesUniversalElement→PreservesUniversalElements :
    ∀ ue → preservesUniversalElement ue → preservesUniversalElements
  preservesUniversalElement→PreservesUniversalElements ue preservesUE ue' =
    isTerminalToIsUniversal D Q $
      preserveAnyTerminal→PreservesTerminals
        (∫ᴾ P)
        (∫ᴾ Q)
        ∫F
        (universalElementToTerminalElement C P ue)
        (isUniversalToIsTerminal D Q _ _ preservesUE)
        (universalElementToTerminalElement C P ue')
