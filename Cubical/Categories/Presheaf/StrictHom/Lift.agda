-- Level lifting for the category `PRESHEAF` of presheaves and STRICT
-- (forded) presheaf morphisms.
--
-- `Cubical.Categories.Instances.Sets.LiftF` lifts a set to a larger
-- universe; this is the presheaf-level analogue.  It exists because
-- free constructions typically produce an object at a level strictly
-- above the level of their generators, so the resulting free/forgetful
-- adjunction is only a RELATIVE adjunction, stated along a lift (cf.
-- `Cubical.Algebra.Theory.Free.Adjunction`, which does exactly this on
-- the `SET` side using `LiftF`).
--
-- The point of the file is `liftHomIso`: mapping out of a lifted
-- presheaf is the same as mapping out of the original, so a relative
-- adjunction argument can compose with it.
module Cubical.Categories.Presheaf.StrictHom.Lift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base

private
  variable
    ℓC ℓC' ℓP ℓQ ℓ' : Level

open Category
open Functor
open Iso
open PshHomStrict

module _ {C : Category ℓC ℓC'} (ℓ' : Level) where
  LiftPshOb : Presheaf C ℓP → Presheaf C (ℓ-max ℓP ℓ')
  LiftPshOb P = LiftF ℓ' ∘F P

  module _ {P : Presheaf C ℓP} {Q : Presheaf C ℓQ} where
    LiftPshHom : PshHomStrict P Q
      → PshHomStrict (LiftPshOb P) (LiftPshOb Q)
    LiftPshHom α .N-ob c x = lift (α .N-ob c (x .lower))
    LiftPshHom α .N-hom c c' f p' p e =
      cong lift (α .N-hom c c' f (p' .lower) (p .lower) (cong lower e))

    -- Mapping *out* of a lifted presheaf is the same as mapping out of
    -- the original one.  No level constraint relates ℓP and ℓQ here.
    liftPshHomIso : Iso (PshHomStrict (LiftPshOb P) Q) (PshHomStrict P Q)
    liftPshHomIso .fun α .N-ob c p = α .N-ob c (lift p)
    liftPshHomIso .fun α .N-hom c c' f p' p e =
      α .N-hom c c' f (lift p') (lift p) (cong lift e)
    liftPshHomIso .inv β .N-ob c x = β .N-ob c (x .lower)
    liftPshHomIso .inv β .N-hom c c' f p' p e =
      β .N-hom c c' f (p' .lower) (p .lower) (cong lower e)
    liftPshHomIso .sec β = refl
    liftPshHomIso .ret α = refl

module _ {C : Category ℓC ℓC'} (ℓP ℓ' : Level) where
  LiftPsh : Functor (PRESHEAF C ℓP) (PRESHEAF C (ℓ-max ℓP ℓ'))
  LiftPsh .F-ob = LiftPshOb ℓ'
  LiftPsh .F-hom = LiftPshHom ℓ'
  LiftPsh .F-id = refl
  LiftPsh .F-seq α β = refl

  -- The hom-level equivalence a (relative) adjunction argument
  -- consumes: maps out of `LiftPsh ⟅ P ⟆` in `PRESHEAF C (ℓP ⊔ ℓ')`
  -- are exactly strict presheaf maps out of `P`.
  liftHomIso : (P : Presheaf C ℓP) (Q : Presheaf C (ℓ-max ℓP ℓ'))
    → Iso (PRESHEAF C (ℓ-max ℓP ℓ') [ LiftPsh ⟅ P ⟆ , Q ])
          (PshHomStrict P Q)
  liftHomIso P Q = liftPshHomIso ℓ'

  -- `liftHomIso` is natural in `Q` (postcomposition), definitionally.
  liftHomIsoNat : (P : Presheaf C ℓP) (Q R : Presheaf C (ℓ-max ℓP ℓ'))
    (α : PRESHEAF C (ℓ-max ℓP ℓ') [ LiftPsh ⟅ P ⟆ , Q ])
    (β : PRESHEAF C (ℓ-max ℓP ℓ') [ Q , R ])
    → liftHomIso P R .fun
        (_⋆PshHomStrict_ {P = LiftPsh ⟅ P ⟆} {Q = Q} {R = R} α β)
      ≡ _⋆PshHomStrict_ {P = P} {Q = Q} {R = R} (liftHomIso P Q .fun α) β
  liftHomIsoNat P Q R α β = refl

  -- ... and natural in `P` (precomposition along a lifted map).
  liftHomIsoNatDom : (P P' : Presheaf C ℓP) (Q : Presheaf C (ℓ-max ℓP ℓ'))
    (γ : PRESHEAF C ℓP [ P' , P ])
    (α : PRESHEAF C (ℓ-max ℓP ℓ') [ LiftPsh ⟅ P ⟆ , Q ])
    → liftHomIso P' Q .fun
        (_⋆PshHomStrict_ {P = LiftPsh ⟅ P' ⟆} {Q = LiftPsh ⟅ P ⟆} {R = Q}
          (LiftPsh ⟪ γ ⟫) α)
      ≡ _⋆PshHomStrict_ {P = P'} {Q = P} {R = Q} γ (liftHomIso P Q .fun α)
  liftHomIsoNatDom P P' Q γ α = refl

  isFullyFaithfulLiftPsh : isFullyFaithful LiftPsh
  isFullyFaithfulLiftPsh P Q = isoToIsEquiv theIso
    where
      theIso : Iso (PshHomStrict P Q)
                   (PshHomStrict (LiftPshOb ℓ' P) (LiftPshOb ℓ' Q))
      theIso .fun = LiftPshHom ℓ'
      theIso .inv α .N-ob c p = α .N-ob c (lift p) .lower
      theIso .inv α .N-hom c c' f p' p e =
        cong lower (α .N-hom c c' f (lift p') (lift p) (cong lift e))
      theIso .sec α = refl
      theIso .ret α = refl

-- Lifting by `ℓ-zero` is the identity, up to natural isomorphism.
module _ {C : Category ℓC ℓC'} (ℓP : Level) where
  private
    module P' = PshIsoStrict

  liftZeroPshIso : (P : Presheaf C ℓP)
    → PshIsoStrict (LiftPshOb ℓ-zero P) P
  liftZeroPshIso P .P'.trans .N-ob c x = x .lower
  liftZeroPshIso P .P'.trans .N-hom c c' f p' p e = cong lower e
  liftZeroPshIso P .P'.nIso c = lift , (λ _ → refl) , (λ _ → refl)

  liftZeroNatIso : NatIso (LiftPsh ℓP ℓ-zero) (Id {C = PRESHEAF C ℓP})
  liftZeroNatIso .NatIso.trans .NatTrans.N-ob P =
    liftZeroPshIso P .P'.trans
  liftZeroNatIso .NatIso.trans .NatTrans.N-hom α = refl
  liftZeroNatIso .NatIso.nIso P .isIso.inv .N-ob c p = lift p
  liftZeroNatIso .NatIso.nIso P .isIso.inv .N-hom c c' f p' p e = cong lift e
  liftZeroNatIso .NatIso.nIso P .isIso.sec = refl
  liftZeroNatIso .NatIso.nIso P .isIso.ret = refl
