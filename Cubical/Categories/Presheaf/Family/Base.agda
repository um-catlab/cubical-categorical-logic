-- Presheaves on C are monadic/comonadic on families over the objects of C
module Cubical.Categories.Presheaf.Family.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Categories.Category
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence
import Cubical.Categories.NaturalTransformation as NT
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Power
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Adjoint.Monad
open import Cubical.Categories.Displayed.Instances.EilenbergMoore
open import Cubical.Categories.Displayed.Instances.CoEilenbergMoore
open import Cubical.Categories.Displayed.Instances.EilenbergMoore.Comparison
open import Cubical.Categories.Displayed.Instances.CoEilenbergMoore.Comparison

private
  variable
    ℓ ℓ' ℓC ℓC' : Level

open Category
open Functor
open PshHomStrict

-- families of sets over the objects of C (`ob` is `C.ob → hSet ℓ`)
Families : (C : Category ℓC ℓC') (ℓ : Level) → Category _ _
Families C ℓ = PowerCategory (C .ob) (SET ℓ)

module _ {ℓ} (C : Category ℓC ℓC') where
  private
    module C = Category C
    ell = ℓ-max ℓ (ℓ-max ℓC ℓC')

  Fam : Category _ _
  Fam = Families C ell

  PSH : Category _ _
  PSH = PRESHEAF C ell

  PSH→Fam : Functor PSH Fam
  PSH→Fam .F-ob = F-ob
  PSH→Fam .F-hom = N-ob
  PSH→Fam .F-id = refl
  PSH→Fam .F-seq _ _ = refl

  Cofree : Functor Fam PSH
  Cofree .F-ob A .F-ob x .fst = (y : C.ob) → C.Hom[ y , x ] → A y .fst
  Cofree .F-ob A .F-ob x .snd = isSetΠ λ y → isSetΠ λ _ → A y .snd
  Cofree .F-ob A .F-hom f t y h = t y (h C.⋆ f)
  Cofree .F-ob A .F-id =
    funExt λ t → funExt λ y → funExt λ h → cong (t y) (C.⋆IdR h)
  Cofree .F-ob A .F-seq f g =
    funExt λ t → funExt λ y → funExt λ h → cong (t y) (sym (C.⋆Assoc _ _ _))
  Cofree .F-hom φ .N-ob c t y h = φ y (t y h)
  Cofree .F-hom φ .N-hom c c' g t' t e i y h = φ y (e i y h)
  Cofree .F-id = makePshHomStrictPath refl
  Cofree .F-seq _ _ = makePshHomStrictPath refl

  open UnitCounit
  open _⊣_

  CofreeFamAdj : PSH→Fam ⊣ Cofree
  CofreeFamAdj .η .NT.NatTrans.N-ob P .N-ob x p y h = P .F-hom h p
  CofreeFamAdj .η .NT.NatTrans.N-ob P .N-hom c c' g p' p e =
    funExt λ y → funExt λ h →
      funExt⁻ (P .F-seq g h) p' ∙ cong (P .F-hom h) e
  CofreeFamAdj .η .NT.NatTrans.N-hom {P} {Q} α =
    makePshHomStrictPath
      (funExt λ x → funExt λ p → funExt λ y → funExt λ h →
        α .N-hom y x h p (P .F-hom h p) refl)
  CofreeFamAdj .ε .NT.NatTrans.N-ob A y t = t y C.id
  CofreeFamAdj .ε .NT.NatTrans.N-hom {A} {B} φ = refl
  CofreeFamAdj .triangleIdentities = record
    { Δ₁ = λ P → funExt λ y → funExt λ p → funExt⁻ (P .F-id) p
    ; Δ₂ = λ A → makePshHomStrictPath
        (funExt λ x → funExt λ t → funExt λ y → funExt λ h →
          cong (t y) (C.⋆IdL h)) }

  module COFREE = _⊣_ CofreeFamAdj

  private
    -- the comonad PSH→Fam ∘F Cofree on Fam
    Wᶜ : Comonad Fam
    Wᶜ = adjComonad PSH→Fam Cofree CofreeFamAdj

  PSH→coEM : Functor PSH (coEM Wᶜ)
  PSH→coEM = ComparisonCoEM PSH→Fam Cofree CofreeFamAdj

  coEM→PSH : Functor (coEM Wᶜ) PSH
  coEM→PSH .F-ob X .F-ob x = X .fst .fst x
  coEM→PSH .F-ob X .F-hom {a} {b} h p = X .fst .snd a p b h
  coEM→PSH .F-ob X .F-id {a} = funExt λ p i → X .snd .fst i a p
  coEM→PSH .F-ob X .F-seq {a} {b} {c} h k =
    funExt λ p i → X .snd .snd i a p b h c k
  coEM→PSH .F-hom mor = pshhom
    (λ x p → mor .fst .fst x p)
    (λ c c' f p' p hyp →
      cong (λ t → t c f) (funExt⁻ (funExt⁻ (mor .fst .snd) c') p')
      ∙ cong (mor .fst .fst c) hyp)
  coEM→PSH .F-id = makePshHomStrictPath refl
  coEM→PSH .F-seq f g = makePshHomStrictPath refl

  PSH≃coEM : PSH ≃ᶜ coEM Wᶜ
  PSH≃coEM = equivᶜ PSH→coEM ∣ winv ∣₁
    where
      open NT.NatIso
      open isIso

      co≡ = coEMHom≡ {W = Wᶜ}

      ηIso : NT.NatIso 𝟙⟨ PSH ⟩ (coEM→PSH ∘F PSH→coEM)
      ηIso .trans = NT.natTrans
        (λ P → pshhom (λ c z → z) (λ c c' f p' p z → z))
        (λ α → makePshHomStrictPath refl)
      ηIso .nIso P .inv = pshhom (λ c z → z) (λ c c' f p' p z → z)
      ηIso .nIso P .sec = refl
      ηIso .nIso P .ret = refl

      εIso : NT.NatIso (PSH→coEM ∘F coEM→PSH) 𝟙⟨ coEM Wᶜ ⟩
      εIso .trans = NT.natTrans
        (λ X → ((λ a z → z) , refl) , _)
        (λ {x = x} {y = y} α → co≡ {X = x} {Y = y} refl)
      εIso .nIso X .inv = ((λ a z → z) , refl) , _
      εIso .nIso X .sec = co≡ {X = X} {Y = X} refl
      εIso .nIso X .ret = co≡ {X = X} {Y = X} refl

      winv : WeakInverse PSH→coEM
      winv .WeakInverse.invFunc = coEM→PSH
      winv .WeakInverse.η = ηIso
      winv .WeakInverse.ε = εIso

  PshFamComonadicity : ForgetCoEM Wᶜ ∘F PSH→coEM ≡ PSH→Fam
  PshFamComonadicity = Functor≡ (λ _ → refl) (λ _ → refl)

  -- need a set of object to guarantee that the Σ-type below is a set
  module _ (isSetCob : isSet (C .ob)) where
    Free : Functor Fam PSH
    Free .F-ob A .F-ob x .fst = Σ[ y ∈ C.ob ] (C.Hom[ x , y ] × A y .fst)
    Free .F-ob A .F-ob x .snd =
      isSetΣ isSetCob λ y → isSet× C.isSetHom (A y .snd)
    Free .F-ob A .F-hom f (y , g , a) = y , (f C.⋆ g) , a
    Free .F-ob A .F-id =
      funExt λ (y , g , a) → ΣPathP (refl , ΣPathP (C.⋆IdL g , refl))
    Free .F-ob A .F-seq f g =
      funExt λ (y , h , a) → ΣPathP (refl , ΣPathP (C.⋆Assoc _ _ _ , refl))
    Free .F-hom φ .N-ob c (y , g , a) = y , g , φ y a
    Free .F-hom φ .N-hom c c' k s' s e i =
      e i .fst , e i .snd .fst , φ (e i .fst) (e i .snd .snd)
    Free .F-id = makePshHomStrictPath refl
    Free .F-seq _ _ = makePshHomStrictPath refl

    FreeFamAdj : Free ⊣ PSH→Fam
    FreeFamAdj .η .NT.NatTrans.N-ob A x a = x , C.id , a
    FreeFamAdj .η .NT.NatTrans.N-hom φ = refl
    FreeFamAdj .ε .NT.NatTrans.N-ob P .N-ob x (y , f , p) = P .F-hom f p
    FreeFamAdj .ε .NT.NatTrans.N-ob P .N-hom c c' k (y , f , p) s e =
      sym (funExt⁻ (P .F-seq f k) p)
      ∙ cong (λ s₀ → P .F-hom (s₀ .snd .fst) (s₀ .snd .snd)) e
    FreeFamAdj .ε .NT.NatTrans.N-hom {P} {Q} α =
      makePshHomStrictPath
        (funExt λ x → funExt λ (y , f , p) →
          α .N-hom x y f p (P .F-hom f p) refl)
    FreeFamAdj .triangleIdentities = record
      { Δ₁ = λ A → makePshHomStrictPath
          (funExt λ x → funExt λ (y , g , a) →
            ΣPathP (refl , ΣPathP (C.⋆IdR g , refl)))
      ; Δ₂ = λ P → funExt λ x → funExt λ p → funExt⁻ (P .F-id) p }

    module FREE = _⊣_ FreeFamAdj

    private
      Tᵃ : Functor Fam Fam
      Tᵃ = PSH→Fam ∘F Free

      Tmonᵃ : Monad Fam
      Tmonᵃ = Tᵃ , MonadFromAdjunction Free PSH→Fam FreeFamAdj

    PSH→EM : Functor PSH (EM Tmonᵃ)
    PSH→EM = ComparisonEM Free PSH→Fam FreeFamAdj

    EM→PSH : Functor (EM Tmonᵃ) PSH
    EM→PSH .F-ob X .F-ob x = X .fst .fst x
    EM→PSH .F-ob X .F-hom {a} {b} h p = X .fst .snd b (a , h , p)
    EM→PSH .F-ob X .F-id {a} = funExt λ p i → X .snd .fst i a p
    EM→PSH .F-ob X .F-seq {a} {b} {c} h k =
      funExt λ p i → X .snd .snd i c (b , k , (a , h , p))
    EM→PSH .F-hom mor = pshhom
      (λ x p → mor .fst .fst x p)
      (λ c c' f p' p hyp →
        sym (funExt⁻ (funExt⁻ (mor .fst .snd) c) (c' , f , p'))
        ∙ cong (mor .fst .fst c) hyp)
    EM→PSH .F-id = makePshHomStrictPath refl
    EM→PSH .F-seq f g = makePshHomStrictPath refl

    PSH≃EM : PSH ≃ᶜ EM Tmonᵃ
    PSH≃EM = equivᶜ PSH→EM ∣ winv ∣₁
      where
        open NT.NatIso
        open isIso

        em≡ = emHom≡ {Mon = Tmonᵃ}

        ηIso : NT.NatIso 𝟙⟨ PSH ⟩ (EM→PSH ∘F PSH→EM)
        ηIso .trans = NT.natTrans
          (λ P → pshhom (λ c z → z) (λ c c' f p' p z → z))
          (λ α → makePshHomStrictPath refl)
        ηIso .nIso P .inv = pshhom (λ c z → z) (λ c c' f p' p z → z)
        ηIso .nIso P .sec = refl
        ηIso .nIso P .ret = refl

        εIso : NT.NatIso (PSH→EM ∘F EM→PSH) 𝟙⟨ EM Tmonᵃ ⟩
        εIso .trans = NT.natTrans
          (λ X → ((λ a z → z) , refl) , _)
          (λ {x = x} {y = y} α → em≡ {X = x} {Y = y} refl)
        εIso .nIso X .inv = ((λ a z → z) , refl) , _
        εIso .nIso X .sec = em≡ {X = X} {Y = X} refl
        εIso .nIso X .ret = em≡ {X = X} {Y = X} refl

        winv : WeakInverse PSH→EM
        winv .WeakInverse.invFunc = EM→PSH
        winv .WeakInverse.η = ηIso
        winv .WeakInverse.ε = εIso

    PshFamMonadicity : ForgetEM Tmonᵃ ∘F PSH→EM ≡ PSH→Fam
    PshFamMonadicity = Functor≡ (λ _ → refl) (λ _ → refl)
