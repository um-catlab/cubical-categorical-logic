{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Instances.Sets.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit

open import Cubical.HITs.SetCoequalizer as SetCoeq

open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Exponentials
open import Cubical.Categories.Instances.Sets hiding (PullbacksSET)
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Coend
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.BiCartesianClosed.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.IndexedProduct.Base
open import Cubical.Categories.Limits.Pullback.Alt

private
  variable ℓ ℓC ℓC' : Level

open UniversalElement
open Category

TerminalSET : Terminal' (SET ℓ)
TerminalSET .vertex = Unit* , isSetUnit*
TerminalSET .element = tt
TerminalSET .universal X .equiv-proof y = uniqueExists
  (λ _ → tt*)
  (isPropUnit tt tt)
  (λ _ p' q' → isSetUnit tt tt p' q')
  (λ _ _ → funExt λ _ → isPropUnit* tt* tt*)

InitialSET : Initial' (SET ℓ)
InitialSET .vertex = ⊥* , λ ()
InitialSET .element = _
InitialSET .universal A = isoToIsEquiv (iso (λ _ → tt) (λ z ()) (λ _ → refl) (λ a → funExt λ ()))

module _ {C : Category ℓC ℓC'}
  (F : Bifunctor (C ^op) C (SET (ℓ-max ℓC ℓC')))
  where
  open UniversalElement

  CoendSET : Coend F
  CoendSET = record
    { vertex = nadir , squash
    ; element = elt
    ; universal = λ A → isIsoToIsEquiv
      ( intro
      , (λ b → Cowedge≡ F refl)
      , λ f → sym (uniqueness lmap rmap (A .snd) _ _ _ λ _ → refl))
    } where
    open Cowedge
    open SetCoeq.UniversalProperty
    lmap : Σ[ X ∈ ob C ]
           Σ[ Y ∈ ob C ]
           Σ[ f ∈ (C)[ Y , X ] ] ⟨ F ⟅ X , Y ⟆b ⟩
           →  Σ[ X ∈ ob C ] ⟨ F ⟅ X , X ⟆b ⟩
    lmap (X , Y , f , Fxy ) = X , ( F ⟪ f ⟫r ) Fxy

    rmap : Σ[ X ∈ ob C ]
           Σ[ Y ∈ ob C ]
           Σ[ f ∈ (C)[ Y , X ] ] ⟨ F ⟅ X , Y ⟆b ⟩
           →  Σ[ X ∈ ob C ] ⟨ F ⟅ X , X ⟆b ⟩
    rmap (X , Y , f , Fxy ) = Y , ( F ⟪ f ⟫l ) Fxy

    nadir = SetCoequalizer lmap rmap

    elt : Cowedge F (nadir , squash)
    elt .ψ c Fcc = inc (c , Fcc)
    elt .extranatural f =
      funExt (λ Fc'c → coeq (_ , _ , f , Fc'c))

    module _ {X : hSet (ℓ-max ℓC ℓC')} where
      intro : Cowedge F X → SetCoequalizer lmap rmap → ⟨ X ⟩
      intro w = inducedHom (X .snd) _ λ (_ , _ , _ , _) →
        funExt⁻ (w .extranatural _) _

module _ {ℓSET : Level} where
  BinProductsSET : BinProducts (SET ℓSET)
  BinProductsSET (X , Y) .vertex = X .fst × Y .fst , isSet× (X .snd) (Y .snd)
  BinProductsSET (X , Y) .element = fst , snd
  BinProductsSET (X , Y) .universal Z .equiv-proof (f , g) =
    uniqueExists (λ z → f z , g z) refl
    (λ h → isSet×
      (SET ℓSET .isSetHom {x = Z} {y = X})
      (SET ℓSET .isSetHom {x = Z} {y = Y})
      ((λ z → (h z) .fst) , λ z → (h z) .snd) (f , g))
    λ h p i z → (sym p) i .fst z , (sym p) i .snd z

  BinCoProductsSET : BinCoProducts (SET ℓSET)
  BinCoProductsSET (X , Y) .vertex = _ , isSet⊎ (X .snd) (Y .snd)
  BinCoProductsSET (X , Y) .element = inl , inr
  BinCoProductsSET (X , Y) .universal Z =
    isoToIsEquiv (iso _ (λ (f , g) → Sum.rec f g) (λ _ → refl)
          (λ h → funExt (Sum.elim
                          {C = λ x → Sum.rec (λ z → h (inl z)) (λ z → h (inr z)) x ≡ h x}
                          (λ _ → refl) (λ _ → refl))))

module _ {ℓ ℓSET : Level} (X : Type ℓ) where
  IxProductsSET : (Xs : X → hSet (ℓ-max ℓ ℓSET)) → ΠTy (SET (ℓ-max ℓ ℓSET)) Xs
  IxProductsSET Xs .vertex .fst = ∀ x → Xs x .fst
  IxProductsSET Xs .vertex .snd = isSetΠ (λ x → Xs x .snd)
  IxProductsSET Xs .element x f = f x
  IxProductsSET Xs .universal Γ = isIsoToIsEquiv
    ( (λ z z₁ x → z x z₁)
    , ((λ b → refl) , λ _ → refl))

module _ {ℓSET : Level} where
  ExponentialsSET : AllExponentiable (SET ℓSET) (BinProductsSET)
  ExponentialsSET X Y .vertex = (SET ℓSET)[ X , Y ] , isSet→ (Y .snd)
  ExponentialsSET X Y .element (f , x) = f x
  ExponentialsSET X Y .universal Z = isIsoToIsEquiv
    ( (λ f x z → f (x , z))
    , (λ _ → refl)
    , λ _ → refl)

module _ {ℓSET : Level} where
  SETCC : CartesianCategory (ℓ-suc ℓSET) ℓSET
  SETCC .CartesianCategory.C = SET ℓSET
  SETCC .CartesianCategory.term = TerminalSET
  SETCC .CartesianCategory.bp = BinProductsSET

  SETCCC : CartesianClosedCategory (ℓ-suc ℓSET) ℓSET
  SETCCC .CartesianClosedCategory.CC = SETCC
  SETCCC .CartesianClosedCategory.exps = ExponentialsSET

  SETBiCCC : BiCartesianClosedCategory (ℓ-suc ℓSET) ℓSET
  SETBiCCC .BiCartesianClosedCategory.CCC = SETCCC
  SETBiCCC .BiCartesianClosedCategory.sums = BinCoProductsSET
  SETBiCCC .BiCartesianClosedCategory.init = InitialSET

module _ {ℓSET : Level} where
  PullbacksSET : Pullbacks (SET ℓSET)
  PullbacksSET {l = l}{r = r} f g .vertex .fst .fst =
    Σ[ (x , y) ∈ ⟨ l ⟩ × ⟨ r ⟩ ] f x ≡ g y
  PullbacksSET {l = l}{m = m}{r = r} f g .vertex .fst .snd =
    isSetΣ (isSet× (l .snd) (r .snd)) λ _ → isProp→isSet (m .snd _ _)
  PullbacksSET f g .vertex .snd ((x , y) , e) = f x
  PullbacksSET f g .element .fst .fst ((x , y) , e) = x
  PullbacksSET f g .element .fst .snd = refl
  PullbacksSET f g .element .snd .fst ((x , y) , e) = y
  PullbacksSET f g .element .snd .snd = funExt λ ((x , y) , e) → sym e
  PullbacksSET {m = m} f g .universal (u , h) =
    isIsoToIsEquiv $
      (λ x → (λ z → (x .fst .fst z , x .snd .fst z) ,
                    funExt⁻ (x .fst .snd ∙ (sym (x .snd .snd))) z) , (x .fst .snd)) ,
      (λ _ → ΣPathP ((ΣPathPProp (λ _ → isSet→ (m .snd) _ _) refl) ,
                    (ΣPathPProp (λ _ → isSet→ (m .snd) _ _) refl))) ,
      (λ _ → ΣPathP ((funExt λ _ → ΣPathPProp (λ _ → m .snd _ _) refl) ,
                    isProp→PathP (λ _ → isSet→ (m .snd) _ _) _ _))
