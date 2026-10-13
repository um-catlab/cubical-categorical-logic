module Cubical.Categories.Presheaf.StrictHom.RightAdjoint where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.StrictHom.Bifunctor
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Profunctor.StrictHom.Constructions.Extension

private
  variable
    ℓC ℓC' ℓD ℓD' ℓP ℓQ ℓR : Level

open Category
open Functor
open PshHomStrict
open Iso

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  where

  module _ (P : D o-[ ℓP ]-* C) where
    F⇒LargeProfStrict : C o-[ ℓ-max (ℓ-max (ℓ-max ℓD ℓD') ℓP) ℓR ]-* PRESHEAF D ℓR
    F⇒LargeProfStrict {ℓR = ℓR} =
      PshHomBifStrict ℓP ℓR ∘Fl (CurryBifunctorL' P ^opF)

  _F⇒LargeStrict_ : {ℓQ : Level} → (P : D o-[ ℓP ]-* C) (Q : Presheaf D ℓQ) → Presheaf C _
  _F⇒LargeStrict_ {ℓQ = ℓQ} P Q = appR (F⇒LargeProfStrict P {ℓR = ℓQ}) Q

  module _ (P : D o-[ ℓP ]-* C) (Q : Presheaf D ℓQ) where

    private
      module Q = PresheafNotation Q
      module P⇒Q = PresheafNotation (P F⇒LargeStrict Q)
      module P⊗P⇒Q {d} = ext-⊗ P (P F⇒LargeStrict Q) {d}
      module P⊗P⇒Q' = PresheafNotation (extStrict P ⟅ P F⇒LargeStrict Q ⟆)

    F⇒LargeStrict-app : PshHomStrict (extStrict P ⟅ P F⇒LargeStrict Q ⟆) Q
    F⇒LargeStrict-app .N-ob d =
      P⊗P⇒Q.rec Q.isSetPsh (λ p α → α .N-ob d p) λ _ _ _ → refl
    F⇒LargeStrict-app .N-hom c c' f =
      P⊗P⇒Q.ind (λ _ → isPropΠ2 λ _ _ → Q.isSetPsh _ _)
        λ p α ⊗ e →
          α .N-hom c c' f p _ refl
          ∙ cong (P⊗P⇒Q.rec Q.isSetPsh (λ p₁ α₁ → α₁ .N-ob c p₁) λ _ _ _ → refl) e


    module _ (R : Presheaf C ℓR) where
      private
        module R = PresheafNotation R
        module P⊗R {d} = ext-⊗ P R {d}
        module P⊗R' = PresheafNotation (extStrict P ⟅ R ⟆)

      F⇒LargeStrict-λ : PshHomStrict (extStrict P ⟅ R ⟆) Q → PshHomStrict R (P F⇒LargeStrict Q)
      F⇒LargeStrict-λ α .N-ob c r .N-ob d p = α .N-ob d (p P⊗R.,⊗ r)
      F⇒LargeStrict-λ α .N-ob c r .N-hom d d' f p p' e =
        α .N-hom d d' f (p P⊗R.,⊗ r) (p' P⊗R.,⊗ r) (cong₂ P⊗R._,⊗_ e refl)
      F⇒LargeStrict-λ α .N-hom c c' f r r' e =
         makePshHomStrictPath (funExt₂ λ d p →
           cong (α .N-ob d) (sym (P⊗R.swap p f r))
           ∙ cong (α .N-ob d) (cong₂ P⊗R._,⊗_ refl e)
         )

      F⇒LargeStrict-UMP :
        Iso (PshHomStrict R (P F⇒LargeStrict Q)) (PshHomStrict (extStrict P ⟅ R ⟆) Q)
      F⇒LargeStrict-UMP .fun α =
        extStrict-HomR P α ⋆PshHomStrict F⇒LargeStrict-app
      F⇒LargeStrict-UMP .inv = F⇒LargeStrict-λ
      F⇒LargeStrict-UMP .sec α =
        makePshHomStrictPath (funExt λ d → funExt (
          P⊗R.ind (λ _ → Q.isSetPsh _ _) λ p r → refl))
      F⇒LargeStrict-UMP .ret α = makePshHomStrictPath (funExt λ c → funExt λ r →
        makePshHomStrictPath (funExt₂ λ d p → refl))

  private
    testF⇒LargeStrict : ∀ (P : D o-[ ℓP ]-* C) (Q : Presheaf D ℓQ) c
      → ((P F⇒LargeStrict Q) .F-ob c) .fst ≡ (PshHomStrict (appR P c) Q)
    testF⇒LargeStrict _ _ _ = refl

module P⇒LargeStrict-cocontinuous
  {D : Category ℓD ℓD'}
  {E : Category ℓC ℓC'}
  {ℓP : Level → Level}
  (P : ∀ {ℓ} → Functor (PRESHEAF D ℓ) (PRESHEAF E (ℓP ℓ)))
  (P-cocontinuous : CoContinuous P)
  where
  private
    P-bif : E o-[ ℓP ℓD' ]-* D
    P-bif = CurriedToBifunctorLStrict (P ∘F CurryBifunctorL' (HomBif D))

  -- The "large" presheaf construction via profunctor extension
  P⇒Large : Presheaf E ℓQ → Presheaf D _
  P⇒Large Q = P-bif F⇒LargeStrict Q

  module _ (Q : Presheaf E ℓQ) (R : Presheaf D ℓR) where
    P⇒Large-UMP : Iso (PshHomStrict R (P⇒Large Q)) (PshHomStrict (P ⟅ R ⟆) Q)
    P⇒Large-UMP =
        PshHomStrict R (P⇒Large Q)
        Iso⟨ F⇒LargeStrict-UMP P-bif Q R ⟩
        PshHomStrict ((extStrict P-bif) ⟅ R ⟆) Q
        Iso⟨ precompPshIsoStrict (P-cocontinuous R) ⟩
        PshHomStrict (P ⟅ R ⟆) Q
        ∎Iso
