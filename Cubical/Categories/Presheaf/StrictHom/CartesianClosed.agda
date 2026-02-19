{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Presheaf.StrictHom.CartesianClosed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport hiding (pathToIso)
open import Cubical.Functions.FunExtEquiv

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Constructions.Lift
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory.Base
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.HLevels
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Props
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Exponentials
open import Cubical.Categories.NaturalTransformation hiding (_∘ˡ_; _∘ˡⁱ_)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt using
  (isPshIso' ; PshIso' ; PshHom ; _⋆NatTransPshHom_ ; _⋆PshHom_ ; PshIso)
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Properties renaming (PshIso to PshIsoLift)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.Tensor
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.Constructions.Exponential
open import Cubical.Categories.Presheaf.Constructions.BinProduct hiding (π₁ ; π₂)
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Yoneda

open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Isomorphism.More
private
  variable
    ℓ ℓ' ℓs ℓr ℓc ℓc' ℓp ℓq ℓP ℓQ ℓR ℓS ℓS' ℓS'' : Level
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓPᴰ ℓQᴰ ℓRᴰ : Level

open Functor
open Iso
open PshHomStrict

module _
  {C : Category ℓc ℓc'}
  {P : Presheaf C ℓp} {Q : Presheaf C ℓq}
  {R : Presheaf C ℓr} {S : Presheaf C ℓs}
  (α : PshHomStrict P Q)(β : PshHomStrict Q R)(γ : PshHomStrict R S)
  where

  ⋆PshHomAssoc :
    Path
      (PshHomStrict P S)
      ((α ⋆PshHomStrict β) ⋆PshHomStrict γ)
      (α ⋆PshHomStrict (β ⋆PshHomStrict γ))
  ⋆PshHomAssoc = refl
Unit*Psh-introStrict : ∀ {ℓA} {ℓ1} {C : Category ℓ ℓ'}{P : Presheaf C ℓA}
  → PshHomStrict {ℓq = ℓ1} P Unit*Psh
Unit*Psh-introStrict .N-ob = λ x _ → tt*
Unit*Psh-introStrict .N-hom c c' f p' p x = refl

module _
  {C : Category ℓc ℓc'}
  where
  module _ (P : Presheaf C ℓp)(Q : Presheaf C ℓq) where
    π₁ : PshHomStrict (P ×Psh Q) P
    π₁ .N-ob _ = fst
    π₁ .N-hom _ _ _ _ _ p≡ = cong fst p≡

    π₂ : PshHomStrict (P ×Psh Q) Q
    π₂ .N-ob _ = snd
    π₂ .N-hom _ _ _ _ _ p≡ = cong snd p≡

  module _
    {P : Presheaf C ℓp}
    {Q : Presheaf C ℓq}
    {R : Presheaf C ℓr}
    (α : PshHomStrict R P)
    (β : PshHomStrict R Q)
    where
    ×PshIntroStrict : PshHomStrict R (P ×Psh Q)
    ×PshIntroStrict .N-ob c x = (α .N-ob c x) , (β .N-ob c x)
    ×PshIntroStrict .N-hom c c' f p r r≡ =
      ΣPathP ((α .N-hom c c' f p r r≡) , (β .N-hom c c' f p r r≡))

    ×Pshβ₁Strict : ×PshIntroStrict ⋆PshHomStrict π₁ P Q ≡ α
    ×Pshβ₁Strict = refl

    ×Pshβ₂Strict : ×PshIntroStrict ⋆PshHomStrict π₂ P Q ≡ β
    ×Pshβ₂Strict = refl

  module _ {P : Presheaf C ℓp} {Q : Presheaf C ℓq} {R : Presheaf C ℓr} {S : Presheaf C ℓs}
    (α : PshHomStrict R P) (β : PshHomStrict S Q)
    where
    _×PshHomStrict_ : PshHomStrict (R ×Psh S) (P ×Psh Q)
    _×PshHomStrict_ = ×PshIntroStrict (π₁ _ _ ⋆PshHomStrict α) (π₂ _ _ ⋆PshHomStrict β)

  ΔPshHomStrict : {P : Presheaf C ℓp} → PshHomStrict P (P ×Psh P)
  ΔPshHomStrict = ×PshIntroStrict idPshHomStrict idPshHomStrict

  module _ (P : Presheaf C ℓp)(Q : Presheaf C ℓq) where
    ×PshStrict-UMP : ∀ {R : Presheaf C ℓr} →
      Iso (PshHomStrict R (P ×Psh Q)) (PshHomStrict R P × PshHomStrict R Q)
    ×PshStrict-UMP .Iso.fun α = (α ⋆PshHomStrict π₁ P Q) , (α ⋆PshHomStrict π₂ P Q)
    ×PshStrict-UMP .Iso.inv (α , β) = ×PshIntroStrict α β
    ×PshStrict-UMP .Iso.sec (α , β) = refl
    ×PshStrict-UMP .ret α = refl

open Category
module _ (C : Category ℓC ℓC') (ℓP : Level) where
  PSH1 : Terminal' (PRESHEAF C ℓP)
  PSH1 .UniversalElement.vertex = Unit*Psh
  PSH1 .UniversalElement.element = tt
  PSH1 .UniversalElement.universal _ =
    isoToIsEquiv
      (iso (λ _ → tt) (λ _ → Unit*Psh-introStrict)
         (λ _ → refl) (λ _ → refl))

  PSHBP : BinProducts (PRESHEAF C ℓP)
  PSHBP (P , Q) .UniversalElement.vertex = P ×Psh Q
  PSHBP (P , Q) .UniversalElement.element = π₁ P Q , π₂ P Q
  PSHBP (P , Q) .UniversalElement.universal R = isoToIsEquiv (×PshStrict-UMP P Q)

  Cartesian-PRESHEAF : CartesianCategory _ _
  Cartesian-PRESHEAF .CartesianCategory.C = PRESHEAF C ℓP
  Cartesian-PRESHEAF .CartesianCategory.term = PSH1
  Cartesian-PRESHEAF .CartesianCategory.bp = PSHBP

module _ {C : Category ℓC ℓC'} (P : Presheaf C ℓP) (Q : Presheaf C ℓQ) where
  _⇒PshLargeStrict_ : Presheaf C (ℓC ⊔ℓ ℓQ ⊔ℓ ℓC' ⊔ℓ ℓP)
  _⇒PshLargeStrict_ = PshHomStrictPsh Q ∘F ((-×P ∘F YOStrict) ^opF)
    where
    -×P : Functor (PRESHEAF C ℓC') (PRESHEAF C (ℓC' ⊔ℓ ℓP))
    -×P .F-ob R = R ×Psh P
    -×P .F-hom α = ×PshIntroStrict (π₁ _ _ ⋆PshHomStrict α) (π₂ _ _)
    -×P .F-id = makePshHomStrictPath refl
    -×P .F-seq _ _ = makePshHomStrictPath refl

module _ {C : Category ℓC ℓC'} (P : Presheaf C ℓP) (Q : Presheaf C ℓQ) where
  private
    module C = Category C
    module P = PresheafNotation P
    module Q = PresheafNotation Q

  appPshHomStrict : PshHomStrict ((P ⇒PshLargeStrict Q) ×Psh P) Q
  appPshHomStrict .N-ob c (α , p) = α .N-ob c (C.id , p)
  appPshHomStrict .N-hom c c' f (α , p) (β , p') e =
    α .N-hom c c' f (C.id , p) (f , f P.⋆ p) (ΣPathP (C.⋆IdR f , refl))
    ∙ cong (λ x → α .N-ob c (x , f P.⋆ p)) (sym (C.⋆IdL f))
    ∙ cong (λ γ → γ .N-ob c (C.id , f P.⋆ p)) (cong fst e)
    ∙ cong (λ x → β .N-ob c (C.id , x)) (cong snd e)

  module _ {R : Presheaf C ℓR} where
    private
      module R = PresheafNotation R

    λPshHomStrict : PshHomStrict (R ×Psh P) Q → PshHomStrict R (P ⇒PshLargeStrict Q)
    λPshHomStrict γ .N-ob c r .N-ob d (f , p) = γ .N-ob d (f R.⋆ r , p)
    λPshHomStrict γ .N-ob c r .N-hom e d g (f' , p') (f , p) eq =
      γ .N-hom e d g (f' R.⋆ r , p') (f R.⋆ r , p)
        (ΣPathP ((sym $ R.⋆Assoc _ _ _) ∙ R.⟨ cong fst eq ⟩⋆⟨⟩ , cong snd eq))
    λPshHomStrict γ .N-hom d c' h s' s eq =
      makePshHomStrictPath
      (funExt₂ λ e (f , p) →
        cong (λ x → γ .N-ob e (x , p))
          (R.⋆Assoc _ _ _ ∙ R.⟨⟩⋆⟨ eq ⟩))

    ⇒PshLargeStrict-UMP : Iso (PshHomStrict R (P ⇒PshLargeStrict Q))
                              (PshHomStrict (R ×Psh P) Q)
    ⇒PshLargeStrict-UMP .Iso.fun α =
      ×PshIntroStrict (π₁ R P ⋆PshHomStrict α) (π₂ R P) ⋆PshHomStrict appPshHomStrict
    ⇒PshLargeStrict-UMP .Iso.inv = λPshHomStrict
    ⇒PshLargeStrict-UMP .Iso.sec γ = makePshHomStrictPath
      (funExt₂ λ c (r , p) → cong (λ x → γ .N-ob c (x , p)) (R.⋆IdL r))
    ⇒PshLargeStrict-UMP .Iso.ret α = makePshHomStrictPath
      (funExt₂ λ c r → makePshHomStrictPath
        (funExt₂ λ d (f , p) →
          sym (cong (λ x → α .N-ob c r .N-ob d (x , p)) (sym (C.⋆IdL f))
          ∙ funExt⁻ (funExt⁻ (cong N-ob (α .N-hom d c f r (f R.⋆ r) refl)) d) (C.id , p))))

    ⇒PshLargeStrict-β : (γ : PshHomStrict (R ×Psh P) Q) →
      ×PshIntroStrict (π₁ R P ⋆PshHomStrict λPshHomStrict γ) (π₂ R P) ⋆PshHomStrict appPshHomStrict
        ≡ γ
    ⇒PshLargeStrict-β γ = makePshHomStrictPath
      (funExt₂ λ c (r , p) → cong (λ x → γ .N-ob c (x , p)) (R.⋆IdL r))

    ⇒PshLargeStrict-η : (α : PshHomStrict R (P ⇒PshLargeStrict Q)) →
      λPshHomStrict (×PshIntroStrict (π₁ R P ⋆PshHomStrict α) (π₂ R P) ⋆PshHomStrict appPshHomStrict)
        ≡ α
    ⇒PshLargeStrict-η α = makePshHomStrictPath
      (funExt₂ λ c r → makePshHomStrictPath
        (funExt₂ λ d (f , p) →
          sym (cong (λ x → α .N-ob c r .N-ob d (x , p)) (sym (C.⋆IdL f))
          ∙ funExt⁻ (funExt⁻ (cong N-ob (α .N-hom d c f r (f R.⋆ r) refl)) d) (C.id , p))))

module _ (C : Category ℓC ℓC') (ℓP : Level) where
  Exp-PRESHEAF :
    AllExponentiable (PRESHEAF C (ℓP ⊔ℓ ℓC ⊔ℓ ℓC'))
      (Cartesian-PRESHEAF C (ℓP ⊔ℓ ℓC ⊔ℓ ℓC') .CartesianCategory.bp)
  Exp-PRESHEAF P Q .UniversalElement.vertex = P ⇒PshLargeStrict Q
  Exp-PRESHEAF P Q .UniversalElement.element = appPshHomStrict P Q
  Exp-PRESHEAF P Q .UniversalElement.universal R =
    isoToIsEquiv (⇒PshLargeStrict-UMP P Q)

module _ (C : Category ℓC ℓC') (ℓP : Level) where
  CCC-PRESHEAF : CartesianClosedCategory _ _
  CCC-PRESHEAF .CartesianClosedCategory.CC = Cartesian-PRESHEAF C (ℓP ⊔ℓ ℓC' ⊔ℓ ℓC)
  CCC-PRESHEAF .CartesianClosedCategory.exps P Q = Exp-PRESHEAF C ℓP P Q
