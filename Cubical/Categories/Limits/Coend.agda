module Cubical.Categories.Limits.Coend where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Profunctor.General

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Functor
module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  (F : Bifunctor (C ^op) C D) where

  module C = Category C
  module D = Category D

  CowedgeΣ : ∀ (d : D.ob) → Type (ℓ-max (ℓ-max ℓC ℓC') ℓD')
  CowedgeΣ d =
    Σ[ ψ ∈ ((c : C.ob) → D [ F ⟅ c , c ⟆b , d ]) ]
    ({c c' : C.ob}(f : C [ c , c' ]) →
        (F ⟪ f ⟫r D.⋆  ψ c') ≡ ( F ⟪ f ⟫l D.⋆ ψ c))

  record Cowedge (d : D.ob) : Type (ℓ-max ℓC (ℓ-max ℓC' ℓD')) where
    field
      ψ : (c : C.ob) → D [ F ⟅ c , c ⟆b , d ]
        {-
          for all morphisms f : c ⇒ c' in category C,

          F₀(c',c)---F₁(id(c'),f)---> F₀(c',c')
           |                          |
           F₁(f,id(c))               ψ(c')
           ↓                          ↓
          F₀(c,c)---ψ(c)-----------> nadir
        -}
      extranatural : {c c' : C.ob}(f : C [ c , c' ]) →
        (F ⟪ f ⟫r D.⋆  ψ c') ≡ ( F ⟪ f ⟫l D.⋆ ψ c)

  open Cowedge
  Cowedge≡ : ∀ {d}{w w' : Cowedge d} → w .ψ ≡ w' .ψ → w ≡ w'
  Cowedge≡ p i .ψ = p i
  Cowedge≡ {d}{w}{w'} p i .extranatural {c}{c'} f =
    isProp→PathP {B = λ i → (F ⟪ f ⟫r D.⋆ p i c') ≡ ( F ⟪ f ⟫l D.⋆ p i c)}
      (λ i → D.isSetHom _ _ )
      (w .extranatural f )
      (w' .extranatural f)
      i

  isSetCowedge : ∀ {d} → isSet (Cowedge d)
  isSetCowedge {d} = isSetRetract {B = CowedgeΣ d}
    (λ x → x .ψ , x .extranatural)
    (λ x → record { ψ = x .fst ; extranatural = x .snd })
    (λ x → Cowedge≡ refl)
    (isSetΣSndProp
      (isSetΠ λ _ → D.isSetHom)
      λ _ → isPropImplicitΠ (λ _ → isPropImplicitΠ λ _ → isPropΠ λ _ →
        D.isSetHom _ _))

  CoendPsh : Presheaf (D ^op) (ℓ-max (ℓ-max ℓC ℓC') ℓD')
  CoendPsh .F-ob d = (Cowedge d) , isSetCowedge
  CoendPsh .F-hom f w .ψ c = w .ψ c D.⋆ f
  CoendPsh .F-hom f w .extranatural g =
    sym (D.⋆Assoc _ _ _)
    ∙ D.⟨ w .extranatural g ⟩⋆⟨ refl ⟩
    ∙ D.⋆Assoc _ _ _
  CoendPsh .F-id = funExt (λ w → Cowedge≡ (funExt (λ c → D.⋆IdR (w .ψ c))))
  CoendPsh .F-seq f g =
    funExt (λ w → Cowedge≡ (funExt (λ c → sym (D.⋆Assoc _ _ _))))

  Coend : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD')
  Coend = UniversalElement (D ^op) CoendPsh
