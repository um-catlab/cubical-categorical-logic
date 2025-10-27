-- Reindexing a Presheaf by a Functor.

-- given presheaf Q on D and functor F : C → D we can reindex Q to be
-- a presheaf F* Q on C. This is just precomposition Q ∘ F^op

-- This corresponds to something wacky like "presheaves are a
-- 2-presheaf on the 2-category Cat".
module Cubical.Categories.Presheaf.Constructions.Reindex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Transport hiding (pathToIso)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Functions.FunExtEquiv

open import Cubical.Reflection.RecordEquiv.More
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Constructions.Lift
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Limits
open import Cubical.Categories.NaturalTransformation hiding (_∘ˡ_; _∘ˡⁱ_)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Properties renaming (PshIso to PshIsoLift)
open import Cubical.Categories.Profunctor.General

private
  variable
    ℓC ℓC' ℓD ℓD' ℓP ℓQ ℓR ℓS : Level

open Category
open Contravariant -- Grothendieck construction for presheaves
open Functor
open PshHom
open UniversalElement

-- Whiskering
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  -- TODO: this is a universe polymorphic functor. Evantuall
  -- reindPsh : Functor C D → Functor (Presheaf D) (Presheaf C)
  reindPsh : (F : Functor C D) (Q : Presheaf D ℓQ) → Presheaf C ℓQ
  reindPsh F Q = Q ∘F (F ^opF)

  reindPshHom : {P : Presheaf D ℓP}{Q : Presheaf D ℓQ}
    → (F : Functor C D) (α : PshHom P Q)
    → PshHom (reindPsh F P) (reindPsh F Q)
  reindPshHom F α .N-ob c = α .N-ob _
  reindPshHom F α .N-hom c c' f = α .N-hom _ _ _

  -- TODO: This is a consequence of functoriality...
  reindPshIso : {P : Presheaf D ℓP}{Q : Presheaf D ℓQ}
    → (F : Functor C D) (α : PshIso P Q)
    → PshIso (reindPsh F P) (reindPsh F Q)
  reindPshIso F α .PshIso.trans = reindPshHom F (α .PshIso.trans)
  reindPshIso F α .PshIso.nIso x .fst = α .PshIso.nIso _ .fst
  reindPshIso F α .PshIso.nIso x .snd .fst = α .PshIso.nIso _ .snd .fst
  reindPshIso F α .PshIso.nIso x .snd .snd = α .PshIso.nIso _ .snd .snd

  PshHet : (F : Functor C D) (P : Presheaf C ℓP) (Q : Presheaf D ℓQ) → Type _
  PshHet F P Q = PshHom P (reindPsh F Q)

  Functor→PshHet : (F : Functor C D) (c : C .ob)
    → PshHet F (C [-, c ]) (D [-, F ⟅ c ⟆ ])
  Functor→PshHet F c .N-ob _ = F .F-hom
  Functor→PshHet F c .N-hom _ _ = F .F-seq

  module _ {F : Functor C D}{P : Presheaf C ℓP}{Q : Presheaf D ℓQ}
    (α : PshHet F P Q)
    where
    private
      module P = PresheafNotation P
      module Q = PresheafNotation Q

    becomesUniversal : ∀ (v : C .ob) (e : P.p[ v ]) → Type _
    becomesUniversal v e = isUniversal D Q (F ⟅ v ⟆) (α .N-ob v e)

    preservesUniversalElement : UniversalElement C P → Type _
    preservesUniversalElement ue = becomesUniversal (ue .vertex) (ue .element)

    preservesUniversalElements = ∀ ue → preservesUniversalElement ue

    becomesUniversal→UniversalElement :
      ∀ {v e} → becomesUniversal v e → UniversalElement D Q
    becomesUniversal→UniversalElement isUniv .vertex = _
    becomesUniversal→UniversalElement isUniv .element = _
    becomesUniversal→UniversalElement isUniv .universal = isUniv

    preservesUniversalElement→UniversalElement :
      ∀ ue → preservesUniversalElement ue → UniversalElement D Q
    preservesUniversalElement→UniversalElement ue preservesUE
      = becomesUniversal→UniversalElement preservesUE

    ∫ᴾPshHet : Functor (∫ᴾ P) (∫ᴾ Q)
    ∫ᴾPshHet .F-ob (x , e) = F ⟅ x ⟆ , α .N-ob x e
    ∫ᴾPshHet .F-hom (f , fe≡e') = (F ⟪ f ⟫) ,
      (sym $ α .N-hom _ _ _ _) ∙ cong (α .N-ob _) fe≡e'
    ∫ᴾPshHet .F-id =
      Σ≡Prop (λ _ → Q.isSetPsh _ _ ) (F .F-id)
    ∫ᴾPshHet .F-seq (f , _) (g , _) =
      Σ≡Prop (λ _ → Q.isSetPsh _ _ ) (F .F-seq f g)

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
          ∫ᴾPshHet
          (universalElementToTerminalElement C P ue)
          (isUniversalToIsTerminal D Q _ _ preservesUE)
          (universalElementToTerminalElement C P ue')

-- Functoriality of reindexing in F
reindPshId≅ : {C : Category ℓC ℓC'} (P : Presheaf C ℓP)
  → PshIso P (reindPsh Id P)
reindPshId≅ P = eqToPshIso (reindPsh Id P) Eq.refl Eq.refl

-- -- TODO
-- reindPsh∘F≅ : PshIso (reindPsh F (reindPsh G P)) (reindPsh (G ∘ F) P)
