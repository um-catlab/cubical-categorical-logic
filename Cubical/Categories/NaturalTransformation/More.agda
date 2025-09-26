module Cubical.Categories.NaturalTransformation.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism renaming (iso to iIso)
open import Cubical.Data.Sigma
import      Cubical.Data.Equality as Eq
open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Equality
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Commutativity
open import Cubical.Categories.Morphism
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties

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

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {F G : Functor C D}
         (α : NatTrans F G) where
  isNatIso : Type _
  isNatIso = ∀ x → isIsoC D (α .N-ob x)

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {F G : Functor C D}
         (α : F ≅ᶜ G) where
  NatIsoAt : ∀ x → CatIso D (F ⟅ x ⟆) (G ⟅ x ⟆)
  NatIsoAt x = (N-ob (α .trans) x) , (α .nIso x)


_∘ʳⁱ_ : ∀ (K : Functor C D) → {G H : Functor B C} (β : NatIso G H)
       → NatIso (K ∘F G) (K ∘F H)
(K ∘ʳⁱ β) .trans = K ∘ʳ (β .trans)
(K ∘ʳⁱ β) .nIso x = F-Iso {F = K} (β .trans ⟦ x ⟧ , β .nIso x) .snd

module _
  {F F' : Functor C D}
  where
  opNatTrans : (F ⇒ F') → ((F' ^opF) ⇒ (F ^opF))
  opNatTrans = ⇒^opFiso .Iso.fun

  opNatIso : NatIso F F' → NatIso (F' ^opF) (F ^opF)
  opNatIso = congNatIso^opFiso .Iso.fun

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  where

  _⋆NatTrans_ : ∀ {F G H : Functor C D} →
    NatTrans F G → NatTrans G H → NatTrans F H
  _⋆NatTrans_ = seqTrans

  _⋆NatIso_ : ∀ {F G H : Functor C D} →
    NatIso F G → NatIso G H → NatIso F H
  _⋆NatIso_ = seqNatIso

  infixr 9 _⋆NatTrans_
  infixr 9 _⋆NatIso_


module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  {E : Category ℓE ℓE'}
  (F : Functor C D)
  (G : Functor D E)
  where

  private
    module E = Category E

  ∘F-^opF-NatIso :
    NatIso
      ((G ^opF) ∘F (F ^opF))
      ((G ∘F F) ^opF)
  ∘F-^opF-NatIso .trans .N-ob x = E.id
  ∘F-^opF-NatIso .trans .N-hom f = E.⋆IdL _ ∙ (sym $ E.⋆IdR _)
  ∘F-^opF-NatIso .nIso x .inv = E.id
  ∘F-^opF-NatIso .nIso x .sec = E.⋆IdL (∘F-^opF-NatIso .nIso x .inv)
  ∘F-^opF-NatIso .nIso x .ret = E.⋆IdL (N-ob (∘F-^opF-NatIso .trans) x)
