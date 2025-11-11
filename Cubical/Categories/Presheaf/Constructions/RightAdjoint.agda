{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Presheaf.Constructions.RightAdjoint where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.Tensor
open import Cubical.Categories.Yoneda.More
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Profunctor.Constructions.Extension
open import Cubical.Categories.FunctorComprehension

private
  variable
    ℓ ℓ' ℓA ℓB ℓA' ℓB' ℓC ℓC' ℓD ℓD' ℓP ℓQ ℓR ℓS : Level

open Functor
open Iso
open PshHom
open PshIso

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  where
  private
    module D = Category D
  -- Any profunctor we can define a large presheaf of morphisms "out" of the profunctor

  -- TODO: define this as a bifunctor so we can use that it respects nat iso of profunctors
  module _ (P : Bifunctor (D ^op) C (SET ℓP)) where
    F⇒LargeProf : Bifunctor (C ^op) (PresheafCategory D ℓS) (SET (ℓ-max (ℓ-max (ℓ-max ℓD ℓD') ℓP) ℓS))
    F⇒LargeProf = PshHomBif ∘Fl (CurryBifunctorL P ^opF)

  _F⇒Large_ : (P : Bifunctor (D ^op) C (SET ℓP)) (Q : Presheaf D ℓQ)
    → Presheaf C _
  P F⇒Large Q = appR (F⇒LargeProf P) Q

  private
    testF⇒Large : ∀ (P : Bifunctor (D ^op) C (SET ℓP)) (Q : Presheaf D ℓQ) c
      → ⟨ (P F⇒Large Q) .F-ob c ⟩ ≡ PshHom {C = D} (CurryBifunctorL P ⟅ c ⟆) Q
    testF⇒Large _ _ _ = refl

  module _ (P : Bifunctor (D ^op) C (SET ℓP)) (Q : Presheaf D ℓQ) where
    private
      module Q = PresheafNotation Q
      module P⇒Q = PresheafNotation (P F⇒Large Q)
      module P⊗P⇒Q {d} = Tensor (CurryBifunctor P ⟅ d ⟆) (P F⇒Large Q)
      module P⊗P⇒Q' = PresheafNotation (ext P ⟅ P F⇒Large Q ⟆)

    F⇒Large-app : PshHom (ext P ⟅ P F⇒Large Q ⟆) Q
    F⇒Large-app = pshhom
      app
      app-natural
      where
        app : ∀ d → (appL P d ⊗ (P F⇒Large Q)) → Q.p[ d ]
        app d = P⊗P⇒Q.rec Q.isSetPsh (λ p α → α .N-ob d p) λ _ _ _ → refl

        app-natural : ∀ d d' (f : D [ d , d' ]) (p : (appL P d' ⊗ (P F⇒Large Q)))
          → app d (f P⊗P⇒Q'.⋆ p) ≡ (f Q.⋆ app d' p)
        app-natural d d' f = P⊗P⇒Q.ind (λ _ → Q.isSetPsh _ _)
          λ p q → q .N-hom d d' f p

    module _ (R : Presheaf C ℓR) where
      private
        module R = PresheafNotation R
        module P⊗R {d} = Tensor (CurryBifunctor P ⟅ d ⟆) R
        module P⊗R' = PresheafNotation (ext P ⟅ R ⟆)
        F⇒Large-λ-N-ob : ∀ (α : PshHom (ext P ⟅ R ⟆) Q) c → R.p[ c ] → P⇒Q.p[ c ]
        F⇒Large-λ-N-ob α c r .N-ob d p = α .N-ob d (p P⊗R.,⊗ r)
        F⇒Large-λ-N-ob α c r .N-hom d d' f p = α .N-hom d d' f (p P⊗R.,⊗ r)
      F⇒Large-λ : PshHom (ext P ⟅ R ⟆) Q → PshHom R (P F⇒Large Q)
      F⇒Large-λ α .N-ob = F⇒Large-λ-N-ob α
      F⇒Large-λ α .N-hom c c' f r = makePshHomPath $ λ i d p →
        α .N-ob d (P⊗R.swap p f r i)

      F⇒Large-λ⁻ : PshHom R (P F⇒Large Q) → PshHom (ext P ⟅ R ⟆) Q
      F⇒Large-λ⁻ α = pshhom app' app'-nat
        where
        app' : ∀ d → P⊗R'.p[ d ] → Q.p[ d ]
        app' d = P⊗R.rec Q.isSetPsh (λ p r → α .N-ob _ r .N-ob d p) λ p f r →
          funExt⁻ (funExt⁻ (cong N-ob (α .N-hom _ _ f r)) _) _
        app'-nat : ∀ d d' (f : D [ d , d' ]) (pr : P⊗R'.p[ d' ])
          → app' d (f P⊗R'.⋆ pr) ≡ (f Q.⋆ app' d' pr)
        app'-nat d d' f = P⊗R.ind (λ pr → Q.isSetPsh _ _) (λ p q → α .N-ob _ q .N-hom _ _ f p)

      F⇒Large-UMP : Iso (PshHom R (P F⇒Large Q)) (PshHom (ext P ⟅ R ⟆) Q)
      F⇒Large-UMP .fun = F⇒Large-λ⁻
      F⇒Large-UMP .inv = F⇒Large-λ
      -- F⇒Large-λ⁻ (F⇒Large-λ α) .N-ob d x ≡ α .N-ob d x
      F⇒Large-UMP .rightInv α = makePshHomPath $ funExt λ d → funExt $
        P⊗R.ind (λ pr → Q.isSetPsh _ _)
          (λ p r → refl)
      F⇒Large-UMP .leftInv α = makePshHomPath $ funExt λ c → funExt λ r → makePshHomPath $ funExt λ d → funExt λ p →
        refl

  -- If we have a functor, we can do better: morphisms "out" of a functor, are just elements at F ⟅ c ⟆
  F⇒SmallF : (F : Functor C D)
    → Profunctor (PresheafCategory D ℓQ) C ℓQ
  F⇒SmallF F = CurryBifunctor $ App ∘Fr (F ^opF)

  _F⇒Small_ : (F : Functor C D) (Q : Presheaf D ℓQ) → Presheaf C ℓQ
  F F⇒Small Q = F⇒SmallF F ⟅ Q ⟆

  private
    testF⇒Small : ∀ (F : Functor C D) (Q : Presheaf D ℓQ) c
      → ⟨ (F F⇒Small Q) .F-ob c ⟩ ≡ ⟨ Q .F-ob (F ⟅ c ⟆ )⟩
    testF⇒Small F Q c = refl

  -- By the Yoneda lemma, these two constructions agree when the profunctor is constructed as Yo ∘F F
  module _ (F : Functor C D) (P : Presheaf D ℓP) where
    private
      module P = PresheafNotation P
    F⇒Small≅F⇒Large : PshIso (F F⇒Small P) ((HomBif D ∘Fr F) F⇒Large P)
    -- This is just Yoneda, but doesn't fit definitionally.
    -- Need to work that out how to reuse that here
    F⇒Small≅F⇒Large .trans .N-ob c p .N-ob d f = f P.⋆ p
    F⇒Small≅F⇒Large .trans .N-ob c p .N-hom d d' g f = P.⋆Assoc g f p
    F⇒Small≅F⇒Large .trans .N-hom c c' f p = makePshHomPath (funExt λ d → funExt λ g →
      sym $ P.⋆Assoc _ _ _)
    F⇒Small≅F⇒Large .nIso x .fst α = α .N-ob _ D.id
    F⇒Small≅F⇒Large .nIso x .snd .fst α = makePshHomPath $ funExt λ d → funExt λ f →
      (sym $ α .N-hom _ _ f _) ∙ cong (α .N-ob d) (D.⋆IdR f)
    F⇒Small≅F⇒Large .nIso x .snd .snd p = P.⋆IdL p

    module _ (Q : Presheaf C ℓQ) where
      F⇒Small-UMP : Iso (PshHom Q (F F⇒Small P)) (PshHom (ext (HomBif D ∘Fr F) ⟅ Q ⟆) P)
      F⇒Small-UMP =
        compIso (postcomp⋆PshHom-Iso F⇒Small≅F⇒Large)
          (F⇒Large-UMP (compR (HomBif D) F) P Q)

  module P⇒Large-cocontinuous {ℓP : Level → Level}
    (P : ∀ {ℓ} → Functor (PresheafCategory C ℓ) (PresheafCategory D (ℓP ℓ)))
    (P-cocontinuous : CoContinuous P)
    where
    private
      P-bif : Bifunctor (D ^op) C (SET (ℓP ℓC'))
      P-bif = CurriedToBifunctorL (P ∘F CurryBifunctorL (HomBif C))

    P⇒Large : Presheaf D ℓQ → Presheaf C (ℓ-max (ℓ-max (ℓ-max ℓD ℓD') (ℓP ℓC')) ℓQ)
    P⇒Large Q = P-bif F⇒Large Q

    module _ (Q : Presheaf D ℓQ)(R : Presheaf C ℓR) where
      P⇒Large-UMP : Iso (PshHom R (P⇒Large Q)) (PshHom (P ⟅ R ⟆) Q)
      P⇒Large-UMP = compIso (F⇒Large-UMP P-bif Q R)
        (precomp⋆PshHom-Iso (P-cocontinuous R))
