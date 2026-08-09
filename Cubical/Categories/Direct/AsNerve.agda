{-# OPTIONS --lossy-unification #-}
-- ▷ is the nerve of ↡F, and next is NerveMap applied to ↡incl.
module Cubical.Categories.Direct.AsNerve where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Limits.Weighted
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.StrictDownset

open Functor
open NatTrans
open PshHomStrict

private
  variable
    ℓ ℓ' ℓD ℓP : Level

module _ {C : Category ℓ ℓ'} {Wo : WFOrder ℓD ℓ'} (dir : DirectStr C Wo) where
  open Category C

  ↡inclNT : NatTrans (↡F dir) (YOStrict {C = C})
  ↡inclNT .N-ob = ↡incl dir
  ↡inclNT .N-hom a = makePshHomStrictPath refl

  ▷≡Nerve : (P : Presheaf C ℓP)
          → Path (Presheaf C (ℓ-max ℓ (ℓ-max ℓ' ℓP)))
                 (▷Psh dir {ℓP = ℓP} P) (Nerve {ℓw = ℓ'} {ℓd = ℓP} (↡F dir) P)
  ▷≡Nerve P = Functor≡ (λ _ → refl) (λ _ → refl)

  yoNerve : (P : Presheaf C ℓP) → PshHomStrict P (Nerve (YOStrict {C = C}) P)
  yoNerve P .N-ob c = evalW P c .Iso.inv
  yoNerve P .N-hom c c' f p' p e = makePshHomStrictPath (funExt λ y → funExt λ g →
    funExt⁻ (P .F-seq f g) p' ∙ cong (P .F-hom g) e)

  next≡ : (P : Presheaf C (ℓ-max ℓ ℓ')) (x : ob) (p : ⟨ P .F-ob x ⟩)
        → next dir P .N-ob x p
          ≡ NerveMap ↡inclNT P .N-ob x (yoNerve P .N-ob x p)
  next≡ P x p = makePshHomStrictPath refl
