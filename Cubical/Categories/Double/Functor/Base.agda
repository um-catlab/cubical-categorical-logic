{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Double.Functor.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Double.Base

open DoubleCategory

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ ℓ₈ : Level

record LaxDoubleFunctor
  (D : DoubleCategory ℓ₁ ℓ₂ ℓ₃ ℓ₄)
  (E : DoubleCategory ℓ₅ ℓ₆ ℓ₇ ℓ₈)
  : Type (ℓ-max (ℓ-max (ℓ-max ℓ₁ ℓ₂) (ℓ-max ℓ₃ ℓ₄))
              (ℓ-max (ℓ-max ℓ₅ ℓ₆) (ℓ-max ℓ₇ ℓ₈)))
  where
  no-eta-equality
  private
    module D = DoubleCategory D
    module E = DoubleCategory E

  field
    F₀ : D.ob → E.ob
    Fⱽ : ∀ {x y} → D.Homⱽ[ x , y ] → E.Homⱽ[ F₀ x , F₀ y ]
    Fᴴ : ∀ {x y} → D.Homᴴ[ x , y ] → E.Homᴴ[ F₀ x , F₀ y ]
    Fˢ : ∀ {x y z w}
      {fᴴ : D.Homᴴ[ x , y ]} {gᴴ : D.Homᴴ[ z , w ]}
      {fⱽ : D.Homⱽ[ x , z ]} {gⱽ : D.Homⱽ[ y , w ]}
      → D.Sq fᴴ gᴴ fⱽ gⱽ
      → E.Sq (Fᴴ fᴴ) (Fᴴ gᴴ) (Fⱽ fⱽ) (Fⱽ gⱽ)

    -- Strict vertical preservation
    F-idⱽ : ∀ {x} → Fⱽ (D.idⱽ {x}) ≡ E.idⱽ
    F-seqⱽ : ∀ {x y z} (f : D.Homⱽ[ x , y ]) (g : D.Homⱽ[ y , z ])
      → Fⱽ (f D.⋆ⱽ g) ≡ Fⱽ f E.⋆ⱽ Fⱽ g

    -- Lax horizontal cells (globular squares)
    F-idᴴ : ∀ {x} → E.GlobSq E.idᴴ (Fᴴ (D.idᴴ {x}))
    F-seqᴴ : ∀ {x y z} (f : D.Homᴴ[ x , y ]) (g : D.Homᴴ[ y , z ])
      → E.GlobSq (Fᴴ f E.⋆ᴴ Fᴴ g) (Fᴴ (f D.⋆ᴴ g))

    -- Strict vertical preservation of squares
    F-idⱽSq : ∀ {x y} {h : D.Homᴴ[ x , y ]}
      → PathP (λ i → E.Sq (Fᴴ h) (Fᴴ h) (F-idⱽ i) (F-idⱽ i))
              (Fˢ D.idⱽSq) E.idⱽSq
    F-seqⱽSq : ∀ {x y z w a b}
      {↑f : D.Homᴴ[ x , y ]} {←f : D.Homⱽ[ x , z ]} {↓f : D.Homᴴ[ z , w ]}
      {→f : D.Homⱽ[ y , w ]} {←f' : D.Homⱽ[ z , a ]} {↓f' : D.Homᴴ[ a , b ]}
      {→f' : D.Homⱽ[ w , b ]}
      (α : D.Sq ↑f ↓f ←f →f) (β : D.Sq ↓f ↓f' ←f' →f')
      → PathP (λ i → E.Sq (Fᴴ ↑f) (Fᴴ ↓f') (F-seqⱽ ←f ←f' i) (F-seqⱽ →f →f' i))
              (Fˢ (α D.⋆ⱽSq β)) (Fˢ α E.⋆ⱽSq Fˢ β)

    -- Naturality of laxity cells
    F-idᴴ-nat : ∀ {x y} (v : D.Homⱽ[ x , y ])
      → PathP (λ i → E.Sq E.idᴴ (Fᴴ D.idᴴ)
                ((E.⋆ⱽIdR (Fⱽ v) ∙ sym (E.⋆ⱽIdL (Fⱽ v))) i)
                ((E.⋆ⱽIdR (Fⱽ v) ∙ sym (E.⋆ⱽIdL (Fⱽ v))) i))
        (E.idᴴSq E.⋆ⱽSq F-idᴴ)
        (F-idᴴ E.⋆ⱽSq Fˢ D.idᴴSq)

    F-seqᴴ-nat : ∀ {x₁ x₂ x₃ y₁ y₂ y₃}
      {f₁ : D.Homᴴ[ x₁ , x₂ ]} {f₂ : D.Homᴴ[ x₂ , x₃ ]}
      {g₁ : D.Homᴴ[ y₁ , y₂ ]} {g₂ : D.Homᴴ[ y₂ , y₃ ]}
      {v₁ : D.Homⱽ[ x₁ , y₁ ]} {v₂ : D.Homⱽ[ x₂ , y₂ ]} {v₃ : D.Homⱽ[ x₃ , y₃ ]}
      (α₁ : D.Sq f₁ g₁ v₁ v₂) (α₂ : D.Sq f₂ g₂ v₂ v₃)
      → PathP (λ i → E.Sq (Fᴴ f₁ E.⋆ᴴ Fᴴ f₂) (Fᴴ (g₁ D.⋆ᴴ g₂))
                ((E.⋆ⱽIdR (Fⱽ v₁) ∙ sym (E.⋆ⱽIdL (Fⱽ v₁))) i)
                ((E.⋆ⱽIdR (Fⱽ v₃) ∙ sym (E.⋆ⱽIdL (Fⱽ v₃))) i))
        ((Fˢ α₁ E.⋆ᴴSq Fˢ α₂) E.⋆ⱽSq F-seqᴴ g₁ g₂)
        (F-seqᴴ f₁ f₂ E.⋆ⱽSq Fˢ (α₁ D.⋆ᴴSq α₂))

  field
    -- Coherence with unitors and associator
    -- LHS composites have sides E.idⱽ ⋆ⱽ (E.idⱽ ⋆ⱽ Fⱽ D.idⱽ),
    -- RHS globular squares have sides E.idⱽ
    F-unit-l : ∀ {x y} (f : D.Homᴴ[ x , y ])
      → let pₗ = E.⋆ⱽIdL (E.idⱽ E.⋆ⱽ Fⱽ (D.idⱽ {x})) ∙ E.⋆ⱽIdL _ ∙ F-idⱽ
            pᵣ = E.⋆ⱽIdL (E.idⱽ E.⋆ⱽ Fⱽ (D.idⱽ {y})) ∙ E.⋆ⱽIdL _ ∙ F-idⱽ
        in PathP (λ i → E.Sq (E.idᴴ E.⋆ᴴ Fᴴ f) (Fᴴ f) (pₗ i) (pᵣ i))
          ((F-idᴴ E.⋆ᴴSq E.idⱽSq) E.⋆ⱽSq F-seqᴴ D.idᴴ f E.⋆ⱽSq Fˢ (D.λᴴ f))
          (E.λᴴ (Fᴴ f))

    F-unit-r : ∀ {x y} (f : D.Homᴴ[ x , y ])
      → let pₗ = E.⋆ⱽIdL (E.idⱽ E.⋆ⱽ Fⱽ (D.idⱽ {x})) ∙ E.⋆ⱽIdL _ ∙ F-idⱽ
            pᵣ = E.⋆ⱽIdL (E.idⱽ E.⋆ⱽ Fⱽ (D.idⱽ {y})) ∙ E.⋆ⱽIdL _ ∙ F-idⱽ
        in PathP (λ i → E.Sq (Fᴴ f E.⋆ᴴ E.idᴴ) (Fᴴ f) (pₗ i) (pᵣ i))
          ((E.idⱽSq E.⋆ᴴSq F-idᴴ) E.⋆ⱽSq F-seqᴴ f D.idᴴ E.⋆ⱽSq Fˢ (D.ρᴴ f))
          (E.ρᴴ (Fᴴ f))

    F-assoc : ∀ {x y z w}
      (f : D.Homᴴ[ x , y ]) (g : D.Homᴴ[ y , z ]) (h : D.Homᴴ[ z , w ])
      → let pₗ = cong (λ v → E.idⱽ E.⋆ⱽ (E.idⱽ E.⋆ⱽ v)) (F-idⱽ {x})
            pᵣ = cong (λ v → E.idⱽ E.⋆ⱽ (E.idⱽ E.⋆ⱽ v)) (F-idⱽ {w})
        in PathP (λ i → E.Sq ((Fᴴ f E.⋆ᴴ Fᴴ g) E.⋆ᴴ Fᴴ h) (Fᴴ (f D.⋆ᴴ (g D.⋆ᴴ h)))
                            (pₗ i) (pᵣ i))
          ((F-seqᴴ f g E.⋆ᴴSq E.idⱽSq) E.⋆ⱽSq F-seqᴴ (f D.⋆ᴴ g) h E.⋆ⱽSq Fˢ (D.αᴴ f g h))
          (E.αᴴ (Fᴴ f) (Fᴴ g) (Fᴴ h) E.⋆ⱽSq (E.idⱽSq E.⋆ᴴSq F-seqᴴ g h) E.⋆ⱽSq F-seqᴴ f (g D.⋆ᴴ h))
