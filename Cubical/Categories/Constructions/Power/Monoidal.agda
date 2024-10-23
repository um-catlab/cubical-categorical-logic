{-

  Given a monoidal structure on X, 𝓟 X has a monoidal category
  structure given by a simple version of the Day convolution.

-}

{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.Power.Monoidal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.List as List hiding ([_]; rec)

open import Cubical.Algebra.Monoid

open import Cubical.Categories.Category.Base
open import Cubical.Categories.HLevels
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.Power
open import Cubical.Categories.Instances.Discrete
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.Monoidal.Properties
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More hiding (α)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Monoidal.Base

private
  variable
    ℓ ℓ' ℓQ ℓQ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open Functor
open MonoidalCategory
open MonoidalStr
open TensorStr
open NatTrans
open NatIso
open isIso
module _ (M : Monoid ℓ-zero) (ℓ : Level) where
  private
    module M = MonoidStr (M .snd)
    𝓟M : Category (ℓ-suc ℓ) ℓ
    𝓟M = PowerCategory ⟨ M ⟩ (SET ℓ)

    Grammar = ⟨ M ⟩ → Type ℓ
    Term : Grammar → Grammar → Type ℓ
    Term A B = ∀ m → A m → B m

    Day⊗ : Grammar → Grammar → Grammar
    Day⊗ A B m = Σ[ sp ∈ fiber (λ x → x .fst M.· x .snd ) m ]
      A (sp .fst .fst) × B (sp .fst .snd)
      -- , isSetΣ (isSetΣ (isSet× M.is-set M.is-set) λ _ → isProp→isSet (M.is-set _ _))
      --   λ _ → isSet× (A _ .snd) (B _ .snd)

    Bilinear : (A B C : Grammar) → Type ℓ
    Bilinear A B C = ∀ ma mb → A ma → B mb → C (ma M.· mb)

    Day⊗-rec : ∀ {A B C} → Bilinear A B C → Term (Day⊗ A B) C
    Day⊗-rec {C = C} f m (((ma , mb) , ma·mb≡m) , (a , b)) =
      subst (λ m' → C m') ma·mb≡m (f ma mb a b)

    Day⊗-intro :  ∀ {A B} → Bilinear A B (Day⊗ A B)
    Day⊗-intro ma mb a b = ((ma , mb) , refl) , a , b

    Dayε : Grammar
    Dayε m = Lift (m ≡ M.ε) -- , isProp→isSet (isOfHLevelLift 1 (M.is-set _ _))

    Day⊗ₕ : ∀ {A A' B B'}
      → Term A A' → Term B B' → Term (Day⊗ A B) (Day⊗ A' B')
    Day⊗ₕ f g m (split , _) .fst = split
    Day⊗ₕ f g m (((ma , mb) , ma·mb≡m) , (a , b)) .snd = f ma a , g mb b

    ⌊_⌋ : 𝓟M .ob → Grammar
    ⌊ A ⌋ m = ⟨ A m ⟩

    DayF : Functor (𝓟M ×C 𝓟M) 𝓟M
    DayF .F-ob (A , B) m .fst = Day⊗ ⌊ A ⌋ ⌊ B ⌋ m
    DayF .F-ob (A , B) m .snd =
      isSetΣ (isSetΣ (isSet× M.is-set M.is-set) λ _ → isProp→isSet (M.is-set _ _)) λ _ → isSet× (A _ .snd) (B _ .snd)
    DayF .F-hom (f , g) = Day⊗ₕ f g
    DayF .F-id = refl
    DayF .F-seq _ _ = refl

    Day-assoc : DayF ∘F (𝟙⟨ PowerCategory ⟨ M ⟩ (SET ℓ) ⟩ ×F DayF) ⇒
      DayF ∘F
      (DayF ×F 𝟙⟨ PowerCategory ⟨ M ⟩ (SET ℓ) ⟩) ∘F
      ×C-assoc (PowerCategory ⟨ M ⟩ (SET ℓ))
      (PowerCategory ⟨ M ⟩ (SET ℓ)) (PowerCategory ⟨ M ⟩ (SET ℓ))
    Day-assoc .N-ob (A , B , C) m (sp1 , (a , sp2 , b , c )) =
      ( _ ,
      (sym (M.·Assoc _ _ _)
      ∙ cong₂ M._·_ refl (sp2 .snd)
      ∙ sp1 .snd))
      , ((_ , refl) , (a , b))
      , c
    Day-assoc .N-hom f = funExt λ m → funExt λ abc →
      ΣPathP ((ΣPathP (refl , refl)) , (ΣPathP (refl , refl)))

    Day-unit-l : DayF ∘F
      rinj (PowerCategory ⟨ M ⟩ (SET ℓ)) (PowerCategory ⟨ M ⟩ (SET ℓ))
      (λ a → (Dayε a , isProp→isSet (isOfHLevelLift 1 (M.is-set _ _))))
      ⇒ 𝟙⟨ PowerCategory ⟨ M ⟩ (SET ℓ) ⟩
    Day-unit-l .N-ob A m εa = subst (λ m → ⟨ A m ⟩)
      (sym (M.·IdL _)
      ∙ cong₂ M._·_ (sym (εa .snd .fst .lower)) refl
      ∙ εa .fst .snd)
      (εa .snd .snd)
    Day-unit-l .N-hom = {!!}

  𝓟 : MonoidalCategory (ℓ-suc ℓ) ℓ
  𝓟 .C = PowerCategory ⟨ M ⟩ (SET ℓ)
  𝓟 .monstr .tenstr .─⊗─ = DayF
  𝓟 .monstr .tenstr .unit a .fst = Dayε a
  𝓟 .monstr .tenstr .unit a .snd =
    isProp→isSet (isOfHLevelLift 1 (M.is-set _ _))
  𝓟 .monstr .α .trans = Day-assoc
  𝓟 .monstr .α .nIso (A , B , C) .inv m (sp1 , ((sp2 , a , b) , c )) =
    (_ , M.·Assoc _ _ _ ∙ cong₂ M._·_ (sp2 .snd) refl ∙ (sp1 .snd))
    , (a , ((_ , refl) , (b , c)))
  𝓟 .monstr .α .nIso x .sec = funExt λ m → funExt λ sp →
    ΣPathP (ΣPathP ({!!} , {!!}) , {!!})
  𝓟 .monstr .α .nIso x .ret = {!!}
  -- .trans .N-ob 
  -- 𝓟 .monstr .α .trans .N-hom f = funExt λ m → funExt λ a → {!!}
  -- 𝓟 .monstr .α .nIso (A , B , C) .isIso.inv 
  -- 𝓟 .monstr .α .nIso (A , B , C) .isIso.sec = funExt λ m → funExt λ sp → {!!}
  -- 𝓟 .monstr .α .nIso (A , B , C) .isIso.ret = {!!}
  𝓟 .monstr .η = {!!}
  𝓟 .monstr .ρ = {!!}
  𝓟 .monstr .pentagon = {!!}
  𝓟 .monstr .triangle = {!!}
