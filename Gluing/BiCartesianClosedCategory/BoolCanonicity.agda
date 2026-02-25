{-# OPTIONS --lossy-unification #-}
module Gluing.BiCartesianClosedCategory.BoolCanonicity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sum.Properties
open import Cubical.Data.Unit
open import Cubical.Data.Quiver.Base
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Limits.BiCartesianClosed.Base
open import Cubical.Categories.Displayed.Constructions.Weaken.UncurriedProperties
open import Cubical.Categories.Constructions.Free.BiCartesianClosedCategory.Forded as FreeBiCCC
  renaming ([_,_] to [_,+_])
open import Cubical.Categories.Constructions.Free.BiCartesianClosedCategory.Quiver

open import Gluing.BiCartesianClosedCategory.Canonicity

open Category
open Functor

module _ where
  data OB : Type where
    ans : OB

  data MOR : Type ℓ-zero where
    tr fl : MOR

  open QuiverOver

  +×⇒QUIVER : +×⇒Quiver ℓ-zero ℓ-zero
  +×⇒QUIVER .+×⇒Quiver.ob = OB
  +×⇒QUIVER .+×⇒Quiver.Q .mor = MOR
  +×⇒QUIVER .+×⇒Quiver.Q .dom tr = ⊤
  +×⇒QUIVER .+×⇒Quiver.Q .dom fl = ⊤
  +×⇒QUIVER .+×⇒Quiver.Q .cod tr = ↑ ans
  +×⇒QUIVER .+×⇒Quiver.Q .cod fl = ↑ ans

  private
    module FREEBICCC = BiCartesianClosedCategory (FREE +×⇒QUIVER)

  [t] [f] : FREEBICCC.Hom[ ⊤ , ↑ ans ]
  [t] = ↑ₑ +×⇒QUIVER tr
  [f] = ↑ₑ +×⇒QUIVER fl

  CanonicalFormBool : FREEBICCC.Hom[ ⊤ , ↑ ans ] → hSet ℓ-zero
  CanonicalFormBool e =
    ((e ≡ [t]) ⊎ (e ≡ [f])) ,
    isSet⊎ (isProp→isSet (FREEBICCC.isSetHom _ _)) (isProp→isSet (FREEBICCC.isSetHom _ _))

  ⊤→⊤IsId : ∀ (e : FREEBICCC.Hom[ ⊤ , ⊤ ]) → e ≡ idₑ Eq.refl
  ⊤→⊤IsId e = !⊤.𝟙extensionality
    where module !⊤ = TerminalNotation FREEBICCC.term

  canonicalize-bool' : ∀ (e : FREEBICCC.C [ ⊤ , ↑ ans ]) →
    ⟨ CanonicalFormBool (idₑ Eq.refl ⋆ₑ e) ⟩
  canonicalize-bool' =
    canonicalize +×⇒QUIVER
    (mkElimInterpᴰ
      (λ { ans e → CanonicalFormBool e })
      λ {tr e _ → inl (cong₂ _⋆ₑ_ (⊤→⊤IsId e) refl ∙ FREEBICCC.⋆IdL _)
       ; fl e _ → inr (cong₂ _⋆ₑ_ (⊤→⊤IsId e) refl ∙ FREEBICCC.⋆IdL _)})

  canonicalize-bool : ∀ (e : FREEBICCC.C [ ⊤ , ↑ ans ]) → ⟨ CanonicalFormBool e ⟩
  canonicalize-bool e =
    subst (λ z → CanonicalFormBool z .fst) (FREEBICCC.⋆IdL _) (canonicalize-bool' e)

  canonicity : Iso (FREEBICCC.C [ ⊤ , ↑ ans ]) Bool
  canonicity .Iso.fun e = Sum.rec (λ _ → true) (λ _ → false) (canonicalize-bool e)
  canonicity .Iso.inv = λ { true → ↑ₑ +×⇒QUIVER tr ; false → ↑ₑ +×⇒QUIVER fl }
  canonicity .Iso.sec = λ {true → refl ; false → refl}
  canonicity .Iso.ret e =
    Sum.elim {C = λ z →
       (canonicity .Iso.inv) (Sum.rec (λ _ → true) (λ _ → false) z) ≡ e}
       sym sym (canonicalize-bool e)
