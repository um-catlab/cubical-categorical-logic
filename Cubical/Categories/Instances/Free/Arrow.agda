-- Free category on one arrow. Also called the "walking arrow" category
module Cubical.Categories.Instances.Free.Arrow where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Bool
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Thin

data Endpoint : Type where
  l r : Endpoint

≤?Endpoint : Endpoint → Endpoint → Bool
≤?Endpoint l cod = true
≤?Endpoint r l = false
≤?Endpoint r r = true

≤Endpoint : Endpoint → Endpoint → Type
≤Endpoint dom cod = Bool→Type (≤?Endpoint dom cod)

ARROW-Preorder : Preorder ℓ-zero ℓ-zero
ARROW-Preorder .Preorder.ob = Endpoint
ARROW-Preorder .Preorder._≤_ = ≤Endpoint
ARROW-Preorder .Preorder.rfl {l} = tt
ARROW-Preorder .Preorder.rfl {r} = tt
ARROW-Preorder .Preorder.trans {l} {y} {z} = λ _ _ → tt
ARROW-Preorder .Preorder.trans {r} {r} {z} = λ z₁ z₂ → z₂
ARROW-Preorder .Preorder.isProp≤ = isProp-Bool→Type (≤?Endpoint _ _)

ARROW : Category ℓ-zero ℓ-zero
ARROW = ThinCategory ARROW-Preorder

module _ {ℓC}{ℓC'} (C : Category ℓC ℓC') where
  private module C = Category C
  -- do I want this to be an EqIso?
  ARROW-UMP : Iso (Functor ARROW C) (Σ[ x ∈ C.ob ] Σ[ y ∈ C.ob ] C.Hom[ x , y ])
  ARROW-UMP .Iso.fun F = F ⟅ l ⟆ , F ⟅ r ⟆ , F ⟪ tt ⟫
  ARROW-UMP .Iso.inv (x , y , f) .Functor.F-ob l = x
  ARROW-UMP .Iso.inv (x , y , f) .Functor.F-ob r = y
  ARROW-UMP .Iso.inv (x , y , f) .Functor.F-hom {l} {l} _ = C.id
  ARROW-UMP .Iso.inv (x , y , f) .Functor.F-hom {l} {r} _ = f
  ARROW-UMP .Iso.inv (x , y , f) .Functor.F-hom {r} {r} _ = C.id
  ARROW-UMP .Iso.inv (x , y , f) .Functor.F-id {l} = refl
  ARROW-UMP .Iso.inv (x , y , f) .Functor.F-id {r} = refl
  ARROW-UMP .Iso.inv (x , y , f) .Functor.F-seq {l} {l} {l} = λ _ _ → sym (C.⋆IdL _)
  ARROW-UMP .Iso.inv (x , y , f) .Functor.F-seq {l} {l} {r} = λ _ _ → sym (C.⋆IdL _)
  ARROW-UMP .Iso.inv (x , y , f) .Functor.F-seq {l} {r} {r} = λ _ _ → sym (C.⋆IdR _)
  ARROW-UMP .Iso.inv (x , y , f) .Functor.F-seq {r} {r} {r} = λ _ _ → sym (C.⋆IdL _)
  ARROW-UMP .Iso.sec = λ _ → refl
  ARROW-UMP .Iso.ret F = Functor≡
    (λ { l → refl ; r → refl })
    λ { {l} {l} f → sym (F .Functor.F-id)
      ; {l} {r} f → refl
      ; {r} {r} f → sym (F .Functor.F-id) }
