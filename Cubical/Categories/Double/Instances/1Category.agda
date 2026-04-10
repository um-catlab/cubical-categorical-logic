{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Double.Instances.1Category where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.More
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Double.Base

open DoubleCategory

module _ {ℓ ℓ'} (C : Category ℓ ℓ') where
  private
    module C = Category C

  -- Category structure of C encoded with vertical morphisms
  -- Only identity horizontal morphisms and squares
  1Cat→DoubleCatⱽ : DoubleCategory _ _ _ _
  1Cat→DoubleCatⱽ .ob = C.ob
  1Cat→DoubleCatⱽ .Homⱽ[_,_] = C.Hom[_,_]
  1Cat→DoubleCatⱽ .idⱽ = C.id
  1Cat→DoubleCatⱽ ._⋆ⱽ_ = C._⋆_
  1Cat→DoubleCatⱽ .⋆ⱽIdL = C.⋆IdL
  1Cat→DoubleCatⱽ .⋆ⱽIdR = C.⋆IdR
  1Cat→DoubleCatⱽ .⋆ⱽAssoc = C.⋆Assoc
  1Cat→DoubleCatⱽ .Homᴴ[_,_] c c' = c Eq.≡ c'
  1Cat→DoubleCatⱽ .idᴴ = Eq.refl
  1Cat→DoubleCatⱽ ._⋆ᴴ_ = Eq._∙_
  1Cat→DoubleCatⱽ .Sq Eq.refl Eq.refl f g = f Eq.≡ g
  1Cat→DoubleCatⱽ .isSetSq {fᴴ = Eq.refl} {gᴴ = Eq.refl} =
    isProp→isSet $ Eq.isSet→isSetEq C.isSetHom
  1Cat→DoubleCatⱽ .idⱽSq {h = Eq.refl} = Eq.refl
  1Cat→DoubleCatⱽ .idᴴSq = Eq.refl
  1Cat→DoubleCatⱽ ._⋆ⱽSq_ {↑f = Eq.refl} {↓f = Eq.refl} {↓f' = Eq.refl}
    Eq.refl Eq.refl = Eq.refl
  1Cat→DoubleCatⱽ .⋆ⱽIdLSq {↑f = Eq.refl} {↓f = Eq.refl} Eq.refl i = Eq.refl
  1Cat→DoubleCatⱽ .⋆ⱽIdRSq {↑f = Eq.refl} {↓f = Eq.refl} Eq.refl i = Eq.refl
  1Cat→DoubleCatⱽ .⋆ⱽAssocSq
    {↑f = Eq.refl} {↓f = Eq.refl}
    {↑f' = Eq.refl} {↓f' = Eq.refl} Eq.refl Eq.refl Eq.refl i = Eq.refl
  1Cat→DoubleCatⱽ ._⋆ᴴSq_
    {↑f = Eq.refl} {↓f = Eq.refl}
    {↑f' = Eq.refl} {↓f' = Eq.refl} Eq.refl Eq.refl = Eq.refl
  1Cat→DoubleCatⱽ .λᴴ Eq.refl = Eq.refl
  1Cat→DoubleCatⱽ .λᴴ⁻ Eq.refl = Eq.refl
  1Cat→DoubleCatⱽ .λᴴλᴴ⁻ Eq.refl i = Eq.refl
  1Cat→DoubleCatⱽ .λᴴ⁻λᴴ Eq.refl i = Eq.refl
  1Cat→DoubleCatⱽ .λᴴ-nat {f = Eq.refl} {g = Eq.refl} Eq.refl i = Eq.refl
  1Cat→DoubleCatⱽ .ρᴴ Eq.refl = Eq.refl
  1Cat→DoubleCatⱽ .ρᴴ⁻ Eq.refl = Eq.refl
  1Cat→DoubleCatⱽ .ρᴴρᴴ⁻ Eq.refl i = Eq.refl
  1Cat→DoubleCatⱽ .ρᴴ⁻ρᴴ Eq.refl i = Eq.refl
  1Cat→DoubleCatⱽ .ρᴴ-nat {f = Eq.refl} {g = Eq.refl} Eq.refl i = Eq.refl
  1Cat→DoubleCatⱽ .αᴴ Eq.refl Eq.refl Eq.refl = Eq.refl
  1Cat→DoubleCatⱽ .αᴴ⁻ Eq.refl Eq.refl Eq.refl = Eq.refl
  1Cat→DoubleCatⱽ .αᴴαᴴ⁻  Eq.refl Eq.refl Eq.refl i = Eq.refl
  1Cat→DoubleCatⱽ .αᴴ⁻αᴴ Eq.refl Eq.refl Eq.refl i = Eq.refl
  1Cat→DoubleCatⱽ .αᴴ-nat
    {f₁ = Eq.refl} {f₂ = Eq.refl} {f₃ = Eq.refl}
    {g₁ = Eq.refl} {g₂ = Eq.refl} {g₃ = Eq.refl}
    Eq.refl Eq.refl Eq.refl i = Eq.refl
  1Cat→DoubleCatⱽ .pentagon Eq.refl Eq.refl Eq.refl Eq.refl i = Eq.refl
  1Cat→DoubleCatⱽ .triangle Eq.refl Eq.refl i = Eq.refl
  1Cat→DoubleCatⱽ .interchange
    {↑f = Eq.refl} {↑f' = Eq.refl}
    {↓f = Eq.refl} {↓f' = Eq.refl}
    {←g = Eq.refl} {→g = Eq.refl}
    Eq.refl Eq.refl Eq.refl Eq.refl = refl

  -- Category structure of C encoded with horizontal morphisms
  -- Only identity vertical morphisms and squares
  1Cat→DoubleCatᴴ : DoubleCategory _ _ _ _
  1Cat→DoubleCatᴴ .ob = C.ob
  1Cat→DoubleCatᴴ .Homⱽ[_,_] = _≡_
  1Cat→DoubleCatᴴ .idⱽ = refl
  1Cat→DoubleCatᴴ ._⋆ⱽ_ = _∙_
  1Cat→DoubleCatᴴ .⋆ⱽIdL f = sym $ lUnit f
  1Cat→DoubleCatᴴ .⋆ⱽIdR f = sym $ rUnit f
  1Cat→DoubleCatᴴ .⋆ⱽAssoc f g h = sym $ assoc f g h
  1Cat→DoubleCatᴴ .Homᴴ[_,_] = C.Hom[_,_]
  1Cat→DoubleCatᴴ .idᴴ = C.id
  1Cat→DoubleCatᴴ ._⋆ᴴ_ = C._⋆_
  1Cat→DoubleCatᴴ .Sq f g e e' = PathP (λ i → C [ e i , e' i ]) f g
  1Cat→DoubleCatᴴ .isSetSq = isProp→isSet (isOfHLevelPathP' 1 C.isSetHom _ _)
  1Cat→DoubleCatᴴ .idⱽSq = refl
  1Cat→DoubleCatᴴ .idᴴSq {v = p} i = C.id
  1Cat→DoubleCatᴴ ._⋆ⱽSq_ {←f = ←f} {→f = →f} {←f' = ←f'} {→f' = →f'} α β i =
    comp (λ j → C [ compPath-filler ←f ←f' j i , compPath-filler →f →f' j i ])
         (λ j → λ { (i = i0) → α i0 ; (i = i1) → β j })
         (α i)
  1Cat→DoubleCatᴴ .⋆ⱽIdLSq _ =
    isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatᴴ .⋆ⱽIdRSq _ =
    isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatᴴ .⋆ⱽAssocSq _ _ _ =
    isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatᴴ ._⋆ᴴSq_ α β i = α i C.⋆ β i
  1Cat→DoubleCatᴴ .λᴴ = C.⋆IdL
  1Cat→DoubleCatᴴ .λᴴ⁻ f = sym (C.⋆IdL f)
  1Cat→DoubleCatᴴ .λᴴλᴴ⁻ _ = isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatᴴ .λᴴ⁻λᴴ _ = isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatᴴ .λᴴ-nat _ = isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatᴴ .ρᴴ = C.⋆IdR
  1Cat→DoubleCatᴴ .ρᴴ⁻ f = sym (C.⋆IdR f)
  1Cat→DoubleCatᴴ .ρᴴρᴴ⁻ _ = isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatᴴ .ρᴴ⁻ρᴴ _ = isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatᴴ .ρᴴ-nat _ = isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatᴴ .αᴴ = C.⋆Assoc
  1Cat→DoubleCatᴴ .αᴴ⁻ f g h = sym (C.⋆Assoc f g h)
  1Cat→DoubleCatᴴ .αᴴαᴴ⁻ _ _ _ = isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatᴴ .αᴴ⁻αᴴ _ _ _ = isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatᴴ .αᴴ-nat _ _ _ = isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatᴴ .pentagon _ _ _ _ = isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatᴴ .triangle _ _ = isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _
  1Cat→DoubleCatᴴ .interchange _ _ _ _ = isSet→SquareP (λ _ _ → C.isSetHom) _ _ _ _

  1Cat→DoubleCatᴴEq : DoubleCategory _ _ _ _
  1Cat→DoubleCatᴴEq .ob = C.ob
  1Cat→DoubleCatᴴEq .Homⱽ[_,_] = Eq._≡_
  1Cat→DoubleCatᴴEq .idⱽ = Eq.refl
  1Cat→DoubleCatᴴEq ._⋆ⱽ_ = Eq._∙_
  1Cat→DoubleCatᴴEq .⋆ⱽIdL Eq.refl = refl
  1Cat→DoubleCatᴴEq .⋆ⱽIdR Eq.refl = refl
  1Cat→DoubleCatᴴEq .⋆ⱽAssoc Eq.refl Eq.refl Eq.refl = refl
  1Cat→DoubleCatᴴEq .Homᴴ[_,_] = C.Hom[_,_]
  1Cat→DoubleCatᴴEq .idᴴ = C.id
  1Cat→DoubleCatᴴEq ._⋆ᴴ_ = C._⋆_
  1Cat→DoubleCatᴴEq .Sq f g Eq.refl Eq.refl = f Eq.≡ g
  1Cat→DoubleCatᴴEq .isSetSq {fⱽ = Eq.refl} {gⱽ = Eq.refl} =
    isProp→isSet (Eq.isSet→isSetEq C.isSetHom)
  1Cat→DoubleCatᴴEq .idⱽSq = Eq.refl
  1Cat→DoubleCatᴴEq .idᴴSq {v = Eq.refl} = Eq.refl
  1Cat→DoubleCatᴴEq ._⋆ⱽSq_ {←f = Eq.refl} {→f = Eq.refl}
                            {←f' = Eq.refl} {→f' = Eq.refl} = Eq._∙_
  1Cat→DoubleCatᴴEq .⋆ⱽIdLSq {←f = Eq.refl} {→f = Eq.refl} Eq.refl = refl
  1Cat→DoubleCatᴴEq .⋆ⱽIdRSq {←f = Eq.refl} {→f = Eq.refl} Eq.refl = refl
  1Cat→DoubleCatᴴEq .⋆ⱽAssocSq
    {←f = Eq.refl} {→f = Eq.refl}
    {←f' = Eq.refl} {→f' = Eq.refl}
    {←f'' = Eq.refl} {→f'' = Eq.refl} Eq.refl Eq.refl Eq.refl = refl
  1Cat→DoubleCatᴴEq ._⋆ᴴSq_
    {←f = Eq.refl} {→f = Eq.refl} {→f' = Eq.refl} Eq.refl Eq.refl = Eq.refl
  1Cat→DoubleCatᴴEq .λᴴ = Eq.pathToEq ∘ C.⋆IdL
  1Cat→DoubleCatᴴEq .λᴴ⁻ = Eq.pathToEq ∘ sym ∘ C.⋆IdL
  1Cat→DoubleCatᴴEq .λᴴλᴴ⁻ _ = isProp→PathP (λ i → Eq.isSet→isSetEq C.isSetHom) _ _
  1Cat→DoubleCatᴴEq .λᴴ⁻λᴴ _ = isProp→PathP (λ i → Eq.isSet→isSetEq C.isSetHom) _ _
  1Cat→DoubleCatᴴEq .λᴴ-nat {v = Eq.refl}{u = Eq.refl} α =
    toPathP (Eq.isSet→isSetEq C.isSetHom _ _)
  1Cat→DoubleCatᴴEq .ρᴴ = Eq.pathToEq ∘ C.⋆IdR
  1Cat→DoubleCatᴴEq .ρᴴ⁻ = Eq.pathToEq ∘ sym ∘ C.⋆IdR
  1Cat→DoubleCatᴴEq .ρᴴρᴴ⁻ _ = isProp→PathP (λ i → Eq.isSet→isSetEq C.isSetHom) _ _
  1Cat→DoubleCatᴴEq .ρᴴ⁻ρᴴ _ = isProp→PathP (λ i → Eq.isSet→isSetEq C.isSetHom) _ _
  1Cat→DoubleCatᴴEq .ρᴴ-nat {v = Eq.refl}{u = Eq.refl} α =
    toPathP (Eq.isSet→isSetEq C.isSetHom _ _)
  1Cat→DoubleCatᴴEq .αᴴ _ _ _ = Eq.pathToEq $ C.⋆Assoc _ _ _
  1Cat→DoubleCatᴴEq .αᴴ⁻ _ _ _ = Eq.pathToEq $ sym $ C.⋆Assoc _ _ _
  1Cat→DoubleCatᴴEq .αᴴαᴴ⁻ _ _ _ = isProp→PathP (λ i → Eq.isSet→isSetEq C.isSetHom) _ _
  1Cat→DoubleCatᴴEq .αᴴ⁻αᴴ _ _ _ = isProp→PathP (λ i → Eq.isSet→isSetEq C.isSetHom) _ _
  1Cat→DoubleCatᴴEq .αᴴ-nat
    {v₁ = Eq.refl} {v₂ = Eq.refl} {v₃ = Eq.refl} {v₄ = Eq.refl} α₁ α₂ α₃ =
    toPathP (Eq.isSet→isSetEq C.isSetHom _ _)
  1Cat→DoubleCatᴴEq .pentagon _ _ _ _ = isProp→PathP (λ i → Eq.isSet→isSetEq C.isSetHom) _ _
  1Cat→DoubleCatᴴEq .triangle _ _ = isProp→PathP (λ i → Eq.isSet→isSetEq C.isSetHom) _ _
  1Cat→DoubleCatᴴEq .interchange
    {←f = Eq.refl} {←f' = Eq.refl}
    {→f = Eq.refl} {→f' = Eq.refl}
    {↑g = Eq.refl} {↓g = Eq.refl} _ _ _ _ = isProp→PathP (λ i → Eq.isSet→isSetEq C.isSetHom) _ _
