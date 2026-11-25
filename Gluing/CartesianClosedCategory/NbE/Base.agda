{-# OPTIONS --lossy-unification #-}
module Gluing.CartesianClosedCategory.NbE.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Nerve
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Base
open import
  Cubical.Categories.Instances.Free.CartesianClosedCategory.UncurriedElim
open import Cubical.Categories.Displayed.Instances.Terminal.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Instances.Codomain.Presheaves.Base
open import
  Cubical.Categories.Displayed.Instances.Codomain.Presheaves.Quantifier

open import Gluing.CartesianClosedCategory.Renamings
open import Gluing.CartesianClosedCategory.NormalForms

private
  variable ℓQ ℓQ' : Level

open Functor

module _ (Q : ×⇒Quiver ℓQ ℓQ') where
  private
    module FREECCC = CartesianClosedCategory (FreeCartesianClosedCategory Q)
    ℓ = ℓ-max ℓQ ℓQ'
    R = REN Q

  nerve : Functor FREECCC.C (PresheafCategory R ℓ)
  nerve = RightAdjointProf (RenamingTerm Q)

  nerve-pres-bp : preservesProvidedBinProducts nerve FREECCC.bp
  nerve-pres-bp = RightAdjointProf-pres-bp (RenamingTerm Q) FREECCC.bp

  NbEMotive : CartesianClosedCategoryᴰ (FreeCartesianClosedCategory Q) _ _
  NbEMotive = elimLocalMotive Q (nerve , nerve-pres-bp) (PSHCodCCCⱽ ℓQ')

module NfPresheaf (Q : ×⇒Quiver ℓQ ℓQ') where
  private
    ℓ = ℓ-max ℓQ ℓQ'
    R = REN Q
    rT = renamingTerm Q

  Nf[_] : ∀ A → Presheafᴰ (nerve Q ⟅ A ⟆) (Unitᴰ R) ℓ
  Nf[ A ] .F-ob (Γ , _ , t) =
    (Σ[ n ∈ Nf Q Γ A ] (⌈_⌉ Q n ≡ t))
    , isSetΣ isSetNf (λ _ → isProp→isSet (isSetExpr _ _))
  Nf[ A ] .F-hom (ρ , _ , e) (n , p) =
    renNf Q ρ n
    , renNf-natural Q ρ n ∙ cong (rT ρ ⋆ₑ_) p ∙ e
  Nf[ A ] .F-id = funExt λ (n , p) →
    ΣPathPProp (λ _ → isSetExpr _ _) (renNf-id Q n)
  Nf[ A ] .F-seq f g = funExt λ (n , p) →
    ΣPathPProp (λ _ → isSetExpr _ _)
      (sym (renNf-seq Q (g .fst) (f .fst) n))
