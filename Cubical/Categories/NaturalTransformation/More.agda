{-# OPTIONS --safe #-}
module Cubical.Categories.NaturalTransformation.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism renaming (iso to iIso)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Commutativity
open import Cubical.Categories.Morphism
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation.Base

open import Cubical.Categories.Instances.Functors

private
  variable
    ℓA ℓA' ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
    ℓ ℓ' ℓ'' : Level
    B C D E : Category ℓ ℓ'

open Category
open NatTrans
open NatIso
open isIsoC

infixl 8 _∘ᵛ_
infixl 8 _∘ʰ_
_∘ᵛ_ = compTrans
_∘ʰ_ = whiskerTrans

module _ {B : Category ℓB ℓB'}
         {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'} where
  open NatTrans
  whiskerTrans' : {F F' : Functor B C} {G G' : Functor C D}
                  (β : NatTrans G G') (α : NatTrans F F')
                  → NatTrans (G ∘F F) (G' ∘F F')
  whiskerTrans' {F}{F'}{G}{G'} β α = compTrans (G' ∘ʳ α) (β ∘ˡ F)

  whiskerTrans≡whiskerTrans' : {F F' : Functor B C} {G G' : Functor C D}
                               (β : NatTrans G G') (α : NatTrans F F') →
                               whiskerTrans β α ≡ whiskerTrans' β α
  whiskerTrans≡whiskerTrans' β α = makeNatTransPath (funExt (λ x → β .N-hom _))

_∘ʰ'_ = whiskerTrans'


α : {F : Functor B C} {G : Functor C D} {H : Functor D E}
  → NatTrans (H ∘F (G ∘F F)) ((H ∘F G) ∘F F)
α = pathToNatTrans F-assoc

α⁻¹ : {F : Functor B C} {G : Functor C D} {H : Functor D E}
   → NatTrans ((H ∘F G) ∘F F) (H ∘F (G ∘F F))
α⁻¹ = pathToNatTrans (sym F-assoc)

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  seqNatIso : {F G H : Functor C D} → NatIso F G → NatIso G H → NatIso F H
  seqNatIso ı ı' .trans = seqTrans (ı .trans) (ı' .trans)
  seqNatIso ı ı' .nIso x .inv = ı' .nIso x .inv ⋆⟨ D ⟩ ı .nIso x .inv
  seqNatIso ı ı' .nIso x .sec =
    D .⋆Assoc _ _ _
    ∙ cong (_⋆_ D (ı' .nIso x .inv))
      (sym (D .⋆Assoc _ _ _)
      ∙ cong (D ∘ ı' .trans .N-ob x) (ı .nIso x .sec)
      ∙ D .⋆IdL (ı' .trans .N-ob x))
    ∙ ı' .nIso x .sec
  seqNatIso ı ı' .nIso x .ret =
    (sym (D .⋆Assoc _ _ _))
    ∙ cong (_∘_ D (ı .nIso x .inv))
      (D .⋆Assoc _ _ _
      ∙ cong (D ⋆ ı .trans .N-ob x) (ı' .nIso x .ret)
      ∙ D .⋆IdR (ı .trans .N-ob x))
    ∙ ı .nIso x .ret

  CAT⋆IdR : {F : Functor C D} → NatIso (Id ∘F F) F
  CAT⋆IdR {F} .trans .N-ob = idTrans F .N-ob
  CAT⋆IdR {F} .trans .N-hom = idTrans F .N-hom
  CAT⋆IdR {F} .nIso = idNatIso F .nIso

  module _  {F F' G G' : Functor C D} {α : NatIso F G} {β : NatIso F' G'} where
    open Functor
    makeNatIsoPathP : ∀ (p : F ≡ F') (q : G ≡ G')
                      → PathP (λ i → (x : C .ob) → D [ (p i) .F-ob x ,
                                                       (q i) .F-ob x ])
                              (α .trans .N-ob) (β .trans .N-ob)
                      → PathP (λ i → NatIso (p i) (q i)) α β

    makeNatIsoPathP p q P i .trans =
      makeNatTransPathP {α = α .trans} {β = β .trans} p q P i
    makeNatIsoPathP p q P i .nIso x =
      isProp→PathP
        (λ i → isPropIsIso (makeNatIsoPathP p q P i .trans .N-ob x))
          (α .nIso _) (β .nIso _) i

module _ {B : Category ℓB ℓB'}{C : Category ℓC ℓC'}{D : Category ℓD ℓD'} where
  _∘ʳi_ : ∀ (K : Functor C D) → {G H : Functor B C} (β : NatIso G H)
       → NatIso (K ∘F G) (K ∘F H)
  _∘ʳi_ K β .trans = K ∘ʳ β .trans
  _∘ʳi_ K β .nIso x = preserveIsosF {F = K} (β .trans .N-ob _ , β .nIso x) .snd

  open Functor
  _∘ˡi_ : ∀ (K : Functor B C) → {G H : Functor C D} (β : NatIso G H)
       → NatIso (G ∘F K) (H ∘F K)
  _∘ˡi_ K β .trans = β .trans ∘ˡ K
  _∘ˡi_ K β .nIso b  = β .nIso (K ⟅ b ⟆)



  CAT⋆Assoc : {E : Category ℓE ℓE'}
            (F : Functor B C)(G : Functor C D)(H : Functor D E)
            → NatIso (H ∘F (G ∘F F)) ((H ∘F G) ∘F F)
  CAT⋆Assoc F G H .trans .N-ob = idTrans ((H ∘F G) ∘F F) .N-ob
  CAT⋆Assoc F G H .trans .N-hom = idTrans ((H ∘F G) ∘F F) .N-hom
  CAT⋆Assoc F G H .nIso = idNatIso ((H ∘F G) ∘F F) .nIso



module _ {A : Category ℓA ℓA'}
         {B : Category ℓB ℓB'}
         {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'} where
  preservesNatIsosF : ∀ (𝔽 : Functor (FUNCTOR A B) (FUNCTOR C D)) →
        {F G : Functor A B} → (β : NatIso F G)
      → NatIso (𝔽 ⟅ F ⟆) (𝔽 ⟅ G ⟆)
  preservesNatIsosF 𝔽 β =
    FUNCTORIso→NatIso C D
      (preserveIsosF {F = 𝔽}
        (NatIso→FUNCTORIso A B β)
      )
