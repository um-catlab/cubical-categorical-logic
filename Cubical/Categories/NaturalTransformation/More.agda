module Cubical.Categories.NaturalTransformation.More where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation.Base

private
  variable
    ℓA ℓA' ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
    ℓ ℓ' ℓ'' : Level
    B C D E : Category ℓ ℓ'

open Category
open NatTrans
open NatIso
open isIso

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
  isNatIso = ∀ x → isIso D (α .N-ob x)

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {F G : Functor C D}
         (α : F ≅ᶜ G) where
  NatIsoAt : ∀ x → CatIso D (F ⟅ x ⟆) (G ⟅ x ⟆)
  NatIsoAt x = (N-ob (α .trans) x) , (α .nIso x)


_∘ʳⁱ_ : ∀ (K : Functor C D) → {G H : Functor B C} (β : NatIso G H)
       → NatIso (K ∘F G) (K ∘F H)
(K ∘ʳⁱ β) .trans = K ∘ʳ (β .trans)
(K ∘ʳⁱ β) .nIso x = F-Iso {F = K} (β .trans ⟦ x ⟧ , β .nIso x) .snd

