-- Reindexing a Presheaf by a Functor.

-- given presheaf Q on D and functor F : C → D we can reindex Q to be
-- a presheaf F* Q on C. This is just precomposition Q ∘ F^op

-- This corresponds to something wacky like "presheaves are a
-- 2-presheaf on the 2-category Cat".
module Cubical.Categories.Presheaf.Constructions.Reindex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function


open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq
import Cubical.HITs.Join as Join

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Instances.Elements
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits
open import Cubical.Categories.NaturalTransformation hiding (_∘ˡ_; _∘ˡⁱ_)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Profunctor.Constructions.Extension
open import Cubical.Categories.Presheaf.Constructions.Tensor

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓP ℓQ ℓR ℓS : Level

open Category
open Contravariant -- Grothendieck construction for presheaves
open Functor
open NatTrans
open NatIso
open PshHom
open PshIso
open UniversalElement

-- Whiskering
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  -- TODO: define this as a universe-polymorphic functor once we have that
  -- reindPsh : Functor C D → Functor (Presheaf D) (Presheaf C)
  reindPsh : (F : Functor C D) (Q : Presheaf D ℓQ) → Presheaf C ℓQ
  reindPsh F Q = Q ∘F (F ^opF)

  reindPshF : (F : Functor C D) → Functor (PresheafCategory D ℓQ) (PresheafCategory C ℓQ)
  reindPshF F = precomposeF (SET _) (F ^opF)

  -- This is just whiskering
  reindPshHom : {P : Presheaf D ℓP}{Q : Presheaf D ℓQ}
    → (F : Functor C D) (α : PshHom P Q)
    → PshHom (reindPsh F P) (reindPsh F Q)
  reindPshHom F α .N-ob c = α .N-ob _
  reindPshHom F α .N-hom c c' f = α .N-hom _ _ _

  -- TODO: This is a consequence of functoriality...
  reindPshIso : {P : Presheaf D ℓP}{Q : Presheaf D ℓQ}
    → (F : Functor C D) (α : PshIso P Q)
    → PshIso (reindPsh F P) (reindPsh F Q)
  reindPshIso F α .trans = reindPshHom F (α .trans)
  reindPshIso F α .nIso x .fst = α .nIso _ .fst
  reindPshIso F α .nIso x .snd .fst = α .nIso _ .snd .fst
  reindPshIso F α .nIso x .snd .snd = α .nIso _ .snd .snd

  -- this is right-whiskering
  reindNatTransPsh :
    {F G : Functor C D}
    → (α : NatTrans G F) (P : Presheaf D ℓP)
    → PshHom (reindPsh F P) (reindPsh G P)
  reindNatTransPsh α P .N-ob = λ c p → α.N-ob c P.⋆ p
    where
      module α = NatTrans α
      module P = PresheafNotation P
  reindNatTransPsh α P .N-hom =
    λ _ _ f p →
      sym (P.⋆Assoc _ _ _) ∙ P.⟨ sym $ α.N-hom f ⟩⋆⟨⟩ ∙ P.⋆Assoc _ _ _
    where
      module α = NatTrans α
      module P = PresheafNotation P

  reindNatIsoPsh :
    {F G : Functor C D}
    → (α : NatIso F G) (P : Presheaf D ℓP)
    → PshIso (reindPsh F P) (reindPsh G P)
  reindNatIsoPsh α P .trans = reindNatTransPsh (symNatIso α .trans) P
  reindNatIsoPsh α P .nIso x .fst = reindNatTransPsh (α .trans) P .N-ob _
  reindNatIsoPsh α P .nIso x .snd =
    (λ p → sym (P.⋆Assoc _ _ _) ∙ P.⟨ α .nIso x .isIsoC.sec ⟩⋆⟨⟩ ∙ P.⋆IdL p)
    , λ p → sym (P.⋆Assoc _ _ _) ∙ P.⟨ α .nIso x .isIsoC.ret ⟩⋆⟨⟩ ∙ P.⋆IdL p
    where
      module P = PresheafNotation P

  PshHet : (F : Functor C D) (P : Presheaf C ℓP) (Q : Presheaf D ℓQ) → Type _
  PshHet F P Q = PshHom P (reindPsh F Q)

  PshHet' : (F : Functor C D) (P : Presheaf C ℓP) (Q : Presheaf D ℓQ) → Type _
  PshHet' F P Q = PshHom' P (reindPsh F Q)

  PshHetEq : (F : Functor C D) (P : Presheaf C ℓP) (Q : Presheaf D ℓQ) → Type _
  PshHetEq F P Q = PshHomEq P (reindPsh F Q)

  Functor→PshHet : (F : Functor C D) (c : C .ob)
    → PshHet F (C [-, c ]) (D [-, F ⟅ c ⟆ ])
  Functor→PshHet F c .N-ob _ = F .F-hom
  Functor→PshHet F c .N-hom _ _ = F .F-seq

  -- This should not be in the reindex file. PshHet should go somewhere else
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

    veryStrictlyPreservesUniversalElement :
      (ueP : UniversalElement C P)
      → (e : Q.p[ F ⟅ ueP .vertex ⟆ ])
      → (ueQ : isUniversal D Q _ e)
      → (e ≡ α .N-ob _ (ueP .element))
      → preservesUniversalElement ueP
    veryStrictlyPreservesUniversalElement ueP e = substIsUniversal Q

    strictlyPreservesUniversalElement :
      (ueP : UniversalElement C P)
      (ueQ : UniversalElement D Q)
      → (vP≡vQ : F ⟅ ueP .vertex ⟆ Eq.≡ ueQ .vertex)
      → (eP≡eQ : Eq.mixedHEq (Eq.ap Q.p[_] vP≡vQ) (α .N-ob (ueP .vertex) (ueP .element)) (ueQ .element))
      → preservesUniversalElement ueP
    strictlyPreservesUniversalElement ueP ueQ Eq.refl eP≡eQ =
      veryStrictlyPreservesUniversalElement ueP (ueQ .element) (ueQ .universal) (sym eP≡eQ)

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

reindPshEqId≅ : {C : Category ℓC ℓC'} (P : Presheaf C ℓP)
  → PshIsoEq P (reindPsh Id P)
reindPshEqId≅ P .PshIsoEq.isos = λ _ → idIso
reindPshEqId≅ P .PshIsoEq.nat = λ c c' f p' p z → z

reindPshId≅' :  {C : Category ℓC ℓC'} (P : Presheaf C ℓP)
  → PshIso' P (reindPsh Id P)
reindPshId≅' P .PshIso'.isos = λ _ → idIso
reindPshId≅' P .PshIso'.nat = λ _ _ _ _ → Join.inr Eq.refl

reindPsh∘F≅ :
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  {E : Category ℓE ℓE'}
  (F : Functor C D)
  (G : Functor D E)
  (P : Presheaf E ℓP)
  → PshIso (reindPsh F (reindPsh G P)) (reindPsh (G ∘F F) P)
reindPsh∘F≅ F G P = eqToPshIso (reindPsh (G ∘F F) P) Eq.refl Eq.refl

reindPsh-square :
  {B : Category ℓB ℓB'}
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  {E : Category ℓE ℓE'}
  (F : Functor B C)
  (G : Functor C E)
  (H : Functor B D)
  (K : Functor D E)
  (P : Presheaf E ℓP)
  → (NatIso (G ∘F F) (K ∘F H))
  → PshIso (reindPsh F $ reindPsh G P) (reindPsh H $ reindPsh K P)
reindPsh-square F G H K P GF≅KH =
  reindPsh∘F≅ F G P
  ⋆PshIso reindNatIsoPsh GF≅KH P
  ⋆PshIso (invPshIso $ reindPsh∘F≅ H K P)

reindPsh-tri :
  {B : Category ℓB ℓB'}
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  (F : Functor B C)
  (G : Functor C D)
  (H : Functor B D)
  (P : Presheaf D ℓP)
  → (NatIso (G ∘F F) H)
  → PshIso (reindPsh F $ reindPsh G P) (reindPsh H P)
reindPsh-tri F G H P GF≅H = reindPsh∘F≅ F G P
  ⋆PshIso reindNatIsoPsh GF≅H P

module _ {C : Category ℓC ℓC'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  where
  PshHom→PshHet : PshHom P Q → PshHet Id P Q
  PshHom→PshHet α = α ⋆PshHom reindPshId≅ Q .trans
module _ {C : Category ℓC ℓC'} {P : Presheaf C ℓP} where
  idPshHet : PshHet Id P P
  idPshHet = PshHom→PshHet idPshHom

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {E : Category ℓE ℓE'}{F : Functor C D}{G : Functor D E}
  {P : Presheaf C ℓP}{Q : Presheaf D ℓQ}{R : Presheaf E ℓR}
  where
  _⋆PshHet_ : PshHet F P Q → PshHet G Q R → PshHet (G ∘F F) P R
  α ⋆PshHet β = α ⋆PshHom reindPshHom F β ⋆PshHom reindPsh∘F≅ F G R .trans

module _ {B : Category ℓB ℓB'}{C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where

  module _ (F : Functor B C) (P : Bifunctor (C ^op) D (SET ℓR)) (Q : Presheaf D ℓQ) where
    private
      F*P = CurriedToBifunctorL (reindPshF F ∘F CurryBifunctorL P)
      module F*extPQ = PresheafNotation (reindPsh F (ext P ⟅ Q ⟆))
      module extPQ = PresheafNotation (ext P ⟅ Q ⟆)
      module extF*PQ = PresheafNotation (ext F*P ⟅ Q ⟆)
      module P⊗Q = ext-⊗ P Q
      module F*P⊗Q = ext-⊗ F*P Q

    -- reindPsh F (c ↦ P(c,d) ⊗[ d ] Q(d,*))
    -- ≅ b ↦ P(F b, d) ⊗[ d ] Q(d, *)
    reindPsh-⊗ :
      PshIso (reindPsh F (ext P ⟅ Q ⟆))
             (ext ((CurriedToBifunctorL (reindPshF F ∘F CurryBifunctorL P))) ⟅ Q ⟆)
    reindPsh-⊗ .trans .N-ob = λ b → P⊗Q.rec extF*PQ.isSetPsh F*P⊗Q._,⊗_ F*P⊗Q.swap
    reindPsh-⊗ .trans .N-hom = λ b b' f → P⊗Q.ind (λ _ → extF*PQ.isSetPsh _ _) (λ _ _ → refl)
    reindPsh-⊗ .nIso =
      λ b → (F*P⊗Q.rec F*extPQ.isSetPsh P⊗Q._,⊗_ P⊗Q.swap)
      , F*P⊗Q.ind (λ _ → extF*PQ.isSetPsh _ _) (λ _ _ → refl)
      , P⊗Q.ind (λ _ → extPQ.isSetPsh _ _) λ _ _ → refl

  module _ (F : Functor B C) (P : Bifunctor (D ^op) C (SET ℓR)) (Q : Presheaf D ℓQ) where
    -- reindPsh F (c ↦ ∀[ d ] P(d,c) → Q(d,*))
    -- ≅ (b ↦ ∀[ d ] P(d,F b) → Q(d,*))
    reindPsh-PshHom :
      PshIso (reindPsh F $ appR (PshHomBif ∘Fl (CurryBifunctorL P ^opF)) Q)
             (appR (PshHomBif ∘Fl ((CurryBifunctorL (P ∘Fr F)) ^opF) ) Q)
    reindPsh-PshHom .trans .N-ob b α .N-ob = α .N-ob
    reindPsh-PshHom .trans .N-ob b α .N-hom = α .N-hom
    reindPsh-PshHom .trans .N-hom = λ _ _ f α → makePshHomPath refl
    reindPsh-PshHom .nIso b =
      the-psh-hom ,
      (λ _ → makePshHomPath refl) ,
      (λ _ → makePshHomPath refl)
      where
      the-psh-hom :
        PshHom (appR (compR P F) b)
        Q →
        PshHom (appR P (F-ob F b)) Q
      the-psh-hom β .N-ob = β .N-ob
      the-psh-hom β .N-hom = β .N-hom

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  reindPshF-cocont : (F : Functor C D) → CoContinuous (reindPshF F)
  reindPshF-cocont F Q =
    -- F* Q
    reindPshIso F (CoYoneda Q)
    -- F* ◇Q
    ⋆PshIso reindPsh-⊗ F (HomBif D) Q
    -- ◇ (F* Q)
