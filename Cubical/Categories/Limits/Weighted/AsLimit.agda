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
open import Cubical.Categories.Limits.Limits
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Displayed.Instances.Graph.Presheaf using (EqElement)
open import Cubical.Categories.Limits.Weighted

open Category
open Functor
open Cone
open PshHomStrict

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

  tautCone : Cone Diag ⟦ W , D ⟧
  tautCone .coneOut (j , w) α = lift (α .N-ob j w)
  tautCone .coneOutCommutes {j' , w'} {j , w} (f , e) =
    funExt λ α → cong lift (α .N-hom j j' f w' w (Eq.eqToPath e))

  isLimTautCone : isLimCone Diag ⟦ W , D ⟧ tautCone
  isLimTautCone V cc = (m , isCM) , uniq
    where
      m : ⟨ V ⟩ → PshHomStrict W D
      m v = pshhom
        (λ j w → cc .coneOut (j , w) v .lower)
        (λ c c' f p' p e →
          cong lower (funExt⁻ (cc .coneOutCommutes (f , Eq.pathToEq e)) v))

      isCM : isConeMor cc tautCone m
      isCM (j , w) = refl

      uniq : (y : Σ[ g ∈ (⟨ V ⟩ → PshHomStrict W D) ] isConeMor cc tautCone g)
           → (m , isCM) ≡ y
      uniq (m' , p') = Σ≡Prop (λ g → isPropIsConeMor cc tautCone g)
        (funExt λ v → limPath (funExt λ j → funExt λ w →
          sym (cong lower (funExt⁻ (p' (j , w)) v))))

-- At a single level there is no Lift: the diagram is D itself.
module _ {ℓ : Level} {J : Category ℓ ℓ} (W D : Presheaf J ℓ) where

  Elts₀ : Category ℓ ℓ
  Elts₀ = ∫C (EqElement W)

  Diag₀ : Functor (Elts₀ ^op) (SET ℓ)
  Diag₀ = D ∘F (Fst ^opF)

  tautCone₀ : Cone Diag₀ ⟦ W , D ⟧
  tautCone₀ .coneOut (j , w) α = α .N-ob j w
  tautCone₀ .coneOutCommutes {j' , w'} {j , w} (f , e) =
    funExt λ α → α .N-hom j j' f w' w (Eq.eqToPath e)

  isLimTautCone₀ : isLimCone Diag₀ ⟦ W , D ⟧ tautCone₀
  isLimTautCone₀ V cc = (m , isCM) , uniq
    where
      m : ⟨ V ⟩ → PshHomStrict W D
      m v = pshhom
        (λ j w → cc .coneOut (j , w) v)
        (λ c c' f p' p e →
          funExt⁻ (cc .coneOutCommutes (f , Eq.pathToEq e)) v)

      isCM : isConeMor cc tautCone₀ m
      isCM (j , w) = refl

      uniq : (y : Σ[ g ∈ (⟨ V ⟩ → PshHomStrict W D) ] isConeMor cc tautCone₀ g)
           → (m , isCM) ≡ y
      uniq (m' , p') = Σ≡Prop (λ g → isPropIsConeMor cc tautCone₀ g)
        (funExt λ v → limPath (funExt λ j → funExt λ w →
          sym (funExt⁻ (p' (j , w)) v)))
