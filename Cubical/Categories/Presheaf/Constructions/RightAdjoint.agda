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
open import Cubical.Categories.Profunctor.Relator
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
  module _ (P : D o-[ ℓP ]-* C) where
    F⇒LargeProf : C o-[ ℓ-max (ℓ-max (ℓ-max ℓD ℓD') ℓP) ℓS ]-* PresheafCategory D ℓS
    F⇒LargeProf = PshHomBif ∘Fl (CurryBifunctorL P ^opF)

  _F⇒Large_ : (P : D o-[ ℓP ]-* C) (Q : Presheaf D ℓQ)
    → Presheaf C _
  P F⇒Large Q = appR (F⇒LargeProf P) Q

  private
    testF⇒Large : ∀ (P : D o-[ ℓP ]-* C) (Q : Presheaf D ℓQ) c
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
      F⇒Large-UMP .rightInv α = makePshHomPath $ funExt λ d → funExt $
        P⊗R.ind (λ pr → Q.isSetPsh _ _)
          (λ p r → refl)
      F⇒Large-UMP .leftInv α = makePshHomPath $ funExt λ c → funExt λ r → makePshHomPath $ funExt λ d → funExt λ p →
        refl

  -- If we have a functor, we can do better: morphisms "out" of a functor, are just elements at F ⟅ c ⟆
  F⇒SmallF : (F : Functor C D)
    → Functor (PresheafCategory D ℓQ) (PresheafCategory C ℓQ)
  F⇒SmallF = reindPshF

  _F⇒Small_ : (F : Functor C D) (Q : Presheaf D ℓQ) → Presheaf C ℓQ
  F F⇒Small Q = F⇒SmallF F ⟅ Q ⟆

  private
    testF⇒Small' : ∀ (F : Functor C D) (Q : Presheaf D ℓQ)
      → (F F⇒Small Q) ≡ reindPsh F Q
    testF⇒Small' F Q = refl

  -- By the Yoneda lemma, these two constructions agree when the profunctor is constructed as Yo ∘F F
  module _ (F : Functor C D) (P : Presheaf D ℓP) where
    private
      module P = PresheafNotation P
    F⇒Small≅F⇒Large : PshIso (F F⇒Small P) ((HomBif D ∘Fr F) F⇒Large P)
    F⇒Small≅F⇒Large =
      -- F* P
      reindPshIso F (invPshIso (Yoneda P))
      -- F* □P
      ⋆PshIso reindPsh-PshHom F (HomBif D) P
      -- □ (F* P)

    module _ (Q : Presheaf C ℓQ) where
      F⇒Small-UMP : Iso (PshHom Q (F F⇒Small P)) (PshHom (ext (HomBif D ∘Fr F) ⟅ Q ⟆) P)
      F⇒Small-UMP =
        compIso (postcomp⋆PshHom-Iso F⇒Small≅F⇒Large)
          (F⇒Large-UMP (compR (HomBif D) F) P Q)

  -- In practice, we typically have a functor of presheaves, not a profunctor.
  -- This functor has a right adjoint when it is co-continuous,
  -- meaning it is determined by its restriction to representables
  module P⇒Large-cocontinuous {ℓP : Level → Level}
    (P : ∀ {ℓ} → Functor (PresheafCategory C ℓ) (PresheafCategory D (ℓP ℓ)))
    (P-cocontinuous : CoContinuous P)
    where
    private
      P-bif : D o-[ ℓP ℓC' ]-* C
      P-bif = CurriedToBifunctorL (P ∘F CurryBifunctorL (HomBif C))

    P⇒Large : Presheaf D ℓQ → Presheaf C (ℓ-max (ℓ-max (ℓ-max ℓD ℓD') (ℓP ℓC')) ℓQ)
    P⇒Large Q = P-bif F⇒Large Q

    module _ (Q : Presheaf D ℓQ)(R : Presheaf C ℓR) where
      P⇒Large-UMP : Iso (PshHom R (P⇒Large Q)) (PshHom (P ⟅ R ⟆) Q)
      P⇒Large-UMP = compIso (F⇒Large-UMP P-bif Q R)
        (precomp⋆PshHom-Iso (P-cocontinuous R))

  -- This is the most common situation:
  -- - We have a functor P on presheaves that is cocontinuous
  -- - P preserves representability
  --
  -- in that case we get a small construction on presheaves using the
  -- representables but get the UMP for the large one.
  module P⇒Large-cocontinuous-repr {ℓP : Level → Level}
    (P : ∀ {ℓ} → Functor (PresheafCategory C ℓ) (PresheafCategory D (ℓP ℓ)))
    (P-cocontinuous : CoContinuous P)
    (P-repr : UniversalElements {C = C}{D = D} (P ∘F (CurryBifunctorL $ HomBif C)))
    where
    open P⇒Large-cocontinuous P P-cocontinuous public
    private
      P-F : Functor C D
      P-F = FunctorComprehension (P ∘F (CurryBifunctorL $ HomBif C)) P-repr

    P⇒Small : Presheaf D ℓQ → Presheaf C ℓQ
    P⇒Small = P-F F⇒Small_

    module _ (Q : Presheaf D ℓQ)(R : Presheaf C ℓR) where
      P⇒Small-UMP : Iso (PshHom R (P⇒Small Q)) (PshHom (P ⟅ R ⟆) Q)
      -- Bifunctor (D ^op) C (SET ℓD')
      -- Bifunctor (D ^op) C (SET (ℓP ℓC'))
      P⇒Small-UMP =
        -- PshHom R (P ⇒Small Q)
        compIso (F⇒Small-UMP P-F Q R) $
        -- (PshHom (ext (YO ∘ F) R) Q)
        (precomp⋆PshHom-Iso
          -- P R
          (P-cocontinuous R ⋆PshIso
          -- ext (P ∘ Yo) R
          ext-Iso (FunctorComprehension-Iso (P ∘F CurryBifunctorL (HomBif C)) P-repr) R))
          -- ext (YO ∘ F) R
        -- PshHom (P R) Q

      -- -- The following alternate proof instead needs that (_⇒Large Q) is functorial, but this would require natiso of functors between presheaf categories
      -- P⇒Small-UMP' : Iso (PshHom R (P⇒Small Q)) (PshHom (P ⟅ R ⟆) Q)
      -- -- Bifunctor (D ^op) C (SET ℓD')
      -- -- Bifunctor (D ^op) C (SET (ℓP ℓC'))
      -- P⇒Small-UMP' =
      --   -- PshHom R (P ⇒Small Q)
      --   compIso (postcomp⋆PshHom-Iso
      --     -- P⇒Small Q
      --     (F⇒Small≅F⇒Large P-F Q ⋆PshIso
      --     -- (ext (P ∘ Yo)) ⇒Large Q
      --     {!!})) -- need: (P ≅ P') ⇒ P ⇒Large Q ≅ P' ⇒Large Q
      --            -- for functors P, P' : Psh C → Psh D
      --     -- P ⇒Large Q
      --     $
      --   (P⇒Large-UMP Q R)
      --   -- PshHom (P R) Q
