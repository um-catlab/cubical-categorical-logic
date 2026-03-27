{-# OPTIONS --prop #-}
module Cubical.Categories.Instances.WalkingArrow where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Prop

open import Cubical.Categories.Category

open Category
open Prop→Type

data Vertex : Type ℓ-zero where
  l r : Vertex

≤Vertex : Vertex → Vertex → Prop
≤Vertex l v = ⊤
≤Vertex r r = ⊤
≤Vertex r l = ⊥

private
  -- Just to demonstrate that we aren't losing anything here
  data ≤V' : Vertex → Vertex → Type where
    rfl : ∀ v → ≤V' v v
    lr : ≤V' l r

  ≤V'-iso : ∀ v1 v2 → Iso (Prop→Type (≤Vertex v1 v2)) (≤V' v1 v2)
  ≤V'-iso l l .Iso.fun _ = rfl l
  ≤V'-iso l r .Iso.fun _ = lr
  ≤V'-iso r r .Iso.fun _ = rfl r
  ≤V'-iso l l .Iso.inv _ = ı tt
  ≤V'-iso l r .Iso.inv _ = ı tt
  ≤V'-iso r r .Iso.inv _ = ı tt
  ≤V'-iso l _ .Iso.sec (rfl v) = refl
  ≤V'-iso r _ .Iso.sec (rfl v) = refl
  ≤V'-iso _ _ .Iso.sec lr = refl
  ≤V'-iso v1 v2 .Iso.ret _ = refl

≤V-refl : ∀ v → ≤Vertex v v
≤V-refl l = tt
≤V-refl r = tt

≤V-trans : ∀ {v1 v2 v3} → ≤Vertex v1 v2 → ≤Vertex v2 v3 → ≤Vertex v1 v3
≤V-trans {l} {l} {l} x x₁ = tt
≤V-trans {l} {l} {r} x x₁ = tt
≤V-trans {l} {r} {v3} x x₁ = tt
≤V-trans {r} {r} {v3} x x₁ = x₁

WalkingArrow : Category ℓ-zero ℓ-zero
WalkingArrow .ob = Vertex
WalkingArrow .Hom[_,_] v1 v2 = Prop→Type (≤Vertex v1 v2)
WalkingArrow .id = ı (≤V-refl _)
WalkingArrow ._⋆_ = λ f g → ı (≤V-trans (f .pf) (g .pf))
WalkingArrow .⋆IdL f = refl
WalkingArrow .⋆IdR f = refl
WalkingArrow .⋆Assoc f g h = refl
WalkingArrow .isSetHom = isProp→isSet isProp-Prop→Type
