{-# OPTIONS --lossy-unification #-}
-- Guarded recursion over the walking cospan
module Cubical.Categories.Direct.Examples.Cospan where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Empty as ⊥ using ()
open import Cubical.Data.Nat using (ℕ ; _+_ ; _·_ ; isSetℕ)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor using (Functor)
open import Cubical.Categories.Presheaf.Base using (Presheaf)
open import Cubical.Categories.Presheaf.StrictHom.Base
  using (PshHomStrict ; pshhom ; PshHomStrictN-homTy ; makePshHomStrictPath)
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Instances.Cospan
import Cubical.Categories.Direct.StrictDownset as SD

open Functor
open Iso
open PshHomStrict

private
  dir = CospanDirect

module _ {ℓP} (P : Presheaf CospanCat ℓP) where
  private
    legs : ⟨ P .F-ob L ⟩ × ⟨ P .F-ob R ⟩
         → ∀ y → ⟨ SD.↡Psh dir M .F-ob y ⟩ → ⟨ P .F-ob y ⟩
    legs (x , y) L _       = x
    legs (x , y) R _       = y
    legs (x , y) M (_ , q) = ⊥.rec q

    legs-hom : ∀ xy → PshHomStrictN-homTy (SD.↡Psh dir M) P (legs xy)
    legs-hom (x , y) L L g p' p e = funExt⁻ (P .F-id) x
    legs-hom (x , y) R R g p' p e = funExt⁻ (P .F-id) y
    legs-hom (x , y) L R g p' p e = ⊥.rec g
    legs-hom (x , y) R L g p' p e = ⊥.rec g
    legs-hom (x , y) M L g p' p e = ⊥.rec g
    legs-hom (x , y) M R g p' p e = ⊥.rec g
    legs-hom (x , y) c M g (f' , q') p e = ⊥.rec q'

  ▷M-Iso : Iso ⟨ SD.▷Psh dir P .F-ob M ⟩ (⟨ P .F-ob L ⟩ × ⟨ P .F-ob R ⟩)
  ▷M-Iso .fun β = β .N-ob L (tt , tt) , β .N-ob R (tt , tt)
  ▷M-Iso .inv xy = pshhom (legs xy) (legs-hom xy)
  ▷M-Iso .sec xy = refl
  ▷M-Iso .ret β = makePshHomStrictPath (funExt λ where
    L → funExt λ _ → refl
    R → funExt λ _ → refl
    M → funExt λ { (_ , q) → ⊥.rec q })

module Join (a b : ℕ) where
  A : Ob → hSet ℓ-zero
  A _ = ℕ , isSetℕ

  step : ∀ x → ⟨ SD.▷Fam dir {ℓF = ℓ-zero} A x ⟩ → ⟨ A x ⟩
  step L β = a + a
  step R β = b · b
  step M β = SD.▷FamApp dir {ℓF = ℓ-zero} A {y = L} β tt tt
           + SD.▷FamApp dir {ℓF = ℓ-zero} A {y = R} β tt tt

  join : ℕ
  join = SD.löbFam dir {ℓF = ℓ-zero} A step M

  join-eq : join ≡ (a + a) + b · b
  join-eq = SD.löbFam-unfold dir {ℓF = ℓ-zero} A step M

private
  _ : Join.join 2 3 ≡ 13
  _ = refl
