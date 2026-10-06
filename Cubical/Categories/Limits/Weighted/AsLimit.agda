{-# OPTIONS --lossy-unification #-}
-- ⟦ W , D ⟧ is the limit in SET of D over the category of elements of W.
module Cubical.Categories.Limits.Weighted.AsLimit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Opposite
open import Cubical.Categories.Instances.TotalCategory as TotalCat
  using (∫C ; Fst)
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.AsRepresentable
open import Cubical.Categories.Limits.Conical
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Displayed.Instances.Graph.Presheaf using (EqElement)
open import Cubical.Categories.Limits.Weighted

open Category
open Functor
open NatTrans
open PshHomStrict
open UniversalElement

private
  variable
    ℓj ℓj' ℓw ℓd : Level

module _ {J : Category ℓj ℓj'} (W : Presheaf J ℓw) (D : Presheaf J ℓd) where

  private
    L : Level
    L = ℓ-max (ℓ-max ℓj ℓj') (ℓ-max ℓw ℓd)

  Elts : Category (ℓ-max ℓj ℓw) (ℓ-max ℓj' ℓw)
  Elts = ∫C (EqElement W)

  Diag : Functor (Elts ^op) (SET L)
  Diag = LiftF (ℓ-max (ℓ-max ℓj ℓj') ℓw) ∘F (D ∘F (Fst ^opF))

  tautCone : NatTrans (ΔCone ⟅ ⟦ W , D ⟧ ⟆) Diag
  tautCone .N-ob (j , w) α = lift (α .N-ob j w)
  tautCone .N-hom {j' , w'} {j , w} (f , e) =
    funExt λ α → cong lift (sym (α .N-hom j j' f w' w (Eq.eqToPath e)))

  tautLimit : limit Diag
  tautLimit .vertex = ⟦ W , D ⟧
  tautLimit .element = tautCone
  tautLimit .universal V = isoToIsEquiv (iso _ glue
    (λ c → makeNatTransPath refl)
    (λ m → funExt λ v → limPath refl))
    where
    glue : NatTrans (ΔCone ⟅ V ⟆) Diag → ⟨ V ⟩ → PshHomStrict W D
    glue c v = pshhom
      (λ j w → c .N-ob (j , w) v .lower)
      (λ j j' f w' w e → cong lower (sym (funExt⁻ (c .N-hom (f , Eq.pathToEq e)) v)))

module _ {ℓ : Level} {J : Category ℓ ℓ} (W D : Presheaf J ℓ) where

  Elts₀ : Category ℓ ℓ
  Elts₀ = ∫C (EqElement W)

  Diag₀ : Functor (Elts₀ ^op) (SET ℓ)
  Diag₀ = D ∘F (Fst ^opF)

  tautCone₀ : NatTrans (ΔCone ⟅ ⟦ W , D ⟧ ⟆) Diag₀
  tautCone₀ .N-ob (j , w) α = α .N-ob j w
  tautCone₀ .N-hom {j' , w'} {j , w} (f , e) =
    funExt λ α → sym (α .N-hom j j' f w' w (Eq.eqToPath e))

  tautLimit₀ : limit Diag₀
  tautLimit₀ .vertex = ⟦ W , D ⟧
  tautLimit₀ .element = tautCone₀
  tautLimit₀ .universal V = isoToIsEquiv (iso _ glue
    (λ c → makeNatTransPath refl)
    (λ m → funExt λ v → limPath refl))
    where
    glue : NatTrans (ΔCone ⟅ V ⟆) Diag₀ → ⟨ V ⟩ → PshHomStrict W D
    glue c v = pshhom
      (λ j w → c .N-ob (j , w) v)
      (λ j j' f w' w e → sym (funExt⁻ (c .N-hom (f , Eq.pathToEq e)) v))
