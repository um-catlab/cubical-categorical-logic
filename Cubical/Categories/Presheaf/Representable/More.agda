module Cubical.Categories.Presheaf.Representable.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Reflection.RecordEquiv

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Constructions.Opposite
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Properties
open import Cubical.Categories.Yoneda

private
  variable
    ℓc ℓc' ℓd ℓd' ℓp ℓq ℓr : Level

open PshHom

module _ {C : Category ℓc ℓc'} (P : Presheaf C ℓp) where
  private
    module C = Category C
    module P = PresheafNotation P
  -- Universe-polymorphic Yoneda recursion principle
  yoRec : ∀ {c} → P.p[ c ] → PshHom (C [-, c ]) P
  yoRec p .N-ob Γ f = f P.⋆ p
  yoRec p .N-hom Δ Γ γ f = P.⋆Assoc γ f p

  yoRecβ : ∀ {c}{p : P.p[ c ]} → yoRec p .N-ob _ C.id ≡ p
  yoRecβ = P.⋆IdL _

  yoRecη-elt : ∀ {c}(α : PshHom (C [-, c ]) P){Γ}{f : C [ Γ , c ]}
    → α .N-ob Γ f ≡ yoRec (α .N-ob _ C.id) .N-ob Γ f
  yoRecη-elt α =
    cong (α .N-ob _) (sym $ C.⋆IdR _)
    ∙ α .N-hom _ _ _ _

  yoRecη : ∀ {c}{α : PshHom (C [-, c ]) P}
    → α ≡ yoRec (α .N-ob _ C.id)
  yoRecη {α = α} = makePshHomPath (funExt (λ _ → funExt (λ _ → yoRecη-elt α)))

  IsoYoRec : ∀ c → Iso P.p[ c ] (PshHom (C [-, c ]) P)
  IsoYoRec c =
    iso yoRec (λ α → α .N-ob c C.id) (λ _ → sym $ yoRecη) (λ _ → yoRecβ)

  yoRec≡ : ∀ {c} {p : P.p[ c ]}{α}
    → p ≡ α .N-ob _ C.id
    → yoRec p ≡ α
  yoRec≡ = isoFun≡ (IsoYoRec _)

module _ {C : Category ℓc ℓc'}(P : Presheaf C ℓp)(Q : Presheaf C ℓq)(α : PshHom P Q) where
  private
    module P = PresheafNotation P
    module C = Category C

  yoRec-natural-elt : ∀ {Γ c}{f : C [ Γ , c ]}{p : P.p[ c ]}
    → α .N-ob _ (yoRec P p .N-ob _ f) ≡ yoRec Q (α .N-ob c p) .N-ob Γ f
  yoRec-natural-elt = α .N-hom _ _ _ _

  yoRec-natural : ∀ {c}{p : P.p[ c ]} → (yoRec P p) ⋆PshHom α ≡ yoRec Q (α .N-ob c p)
  yoRec-natural = makePshHomPath $ funExt λ _ → funExt λ _ → yoRec-natural-elt
