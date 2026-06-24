-- Presheaves on C are monadic/comonadic on families over the objects of C
module Cubical.Categories.Presheaf.Family.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

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
open import Cubical.Categories.Instances.Product
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Adjoint.Monad
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Algebras
open import Cubical.Categories.Displayed.Instances.Coalgebras
open import Cubical.Categories.Displayed.Instances.EilenbergMoore
open import Cubical.Categories.Displayed.Instances.CoEilenbergMoore
open import Cubical.Categories.Displayed.Instances.EilenbergMoore.Comparison
open import Cubical.Categories.Displayed.Instances.CoEilenbergMoore.Comparison
open import Cubical.Categories.Displayed.Instances.StructureOver.Base

private
  variable
    ℓ ℓ' ℓC ℓC' : Level

open Category
open Categoryᴰ
open Functor
open PshHomStrict

module _ {ℓ} (C : Category ℓC ℓC') where
  private
    module C = Category C
    ell = ℓ-max ℓ (ℓ-max ℓC ℓC')

    Fam : Category _ _
    Fam = PowerCategory (C.ob) (SET ell)

    Psh : Category _ _
    Psh = PRESHEAF C ell

  Psh→Fam : Functor Psh Fam
  Psh→Fam .F-ob = F-ob
  Psh→Fam .F-hom = N-ob
  Psh→Fam .F-id = refl
  Psh→Fam .F-seq _ _ = refl

  Cofree : Functor Fam Psh
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

  CofreeFamAdj : Psh→Fam ⊣ Cofree
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
    Wᶜ : Functor Fam Fam
    Wᶜ = Psh→Fam ∘F Cofree

    mᶜ : IsMonad ((Psh→Fam ^opF) ∘F (Cofree ^opF))
    mᶜ = MonadFromAdjunction (Cofree ^opF) (Psh→Fam ^opF)
           (opositeAdjunction CofreeFamAdj)

    εᶜ : ∀ x → Fam [ Functor.F-ob Wᶜ x , x ]
    εᶜ x = NT.NatTrans.N-ob (IsMonad.η mᶜ) x

    δᶜ : ∀ x → Fam [ Functor.F-ob Wᶜ x , Functor.F-ob Wᶜ (Functor.F-ob Wᶜ x) ]
    δᶜ x = NT.NatTrans.N-ob (IsMonad.μ mᶜ) x

  COALG : Category _ _
  COALG = coEMCategory Wᶜ εᶜ δᶜ

  Psh→COALG : Functor Psh COALG
  Psh→COALG = ComparisonCoEM Psh→Fam Cofree CofreeFamAdj

  COALG→Psh : Functor COALG Psh
  COALG→Psh .F-ob X .F-ob x = X .fst .fst x
  COALG→Psh .F-ob X .F-hom {a} {b} h p = X .fst .snd a p b h
  COALG→Psh .F-ob X .F-id {a} = funExt λ p i → X .snd .fst i a p
  COALG→Psh .F-ob X .F-seq {a} {b} {c} h k =
    funExt λ p i → X .snd .snd i a p b h c k
  COALG→Psh .F-hom mor = pshhom
    (λ x p → mor .fst .fst x p)
    (λ c c' f p' p hyp →
      cong (λ t → t c f) (funExt⁻ (funExt⁻ (mor .fst .snd) c') p')
      ∙ cong (mor .fst .fst c) hyp)
  COALG→Psh .F-id = makePshHomStrictPath refl
  COALG→Psh .F-seq f g = makePshHomStrictPath refl

  -- comonadicity
  Psh≃COALG : Psh ≃ᶜ COALG
  Psh≃COALG = equivᶜ Psh→COALG ∣ winv ∣₁
    where
      ηIso : NT.NatIso 𝟙⟨ Psh ⟩ (COALG→Psh ∘F Psh→COALG)
      ηIso = record
        { trans = NT.natTrans
            (λ P → pshhom (λ c z → z) (λ c c' f p' p z → z))
            (λ α → makePshHomStrictPath refl)
        ; nIso = λ P → record
            { inv = pshhom (λ c z → z) (λ c c' f p' p z → z)
            ; sec = refl ; ret = refl } }

      εIso : NT.NatIso (Psh→COALG ∘F COALG→Psh) 𝟙⟨ COALG ⟩
      εIso = record
        { trans = NT.natTrans
            (λ X → ((λ a z → z) , refl) , _)
            (λ {x = x} {y = y} α → co≡ {X = x} {Y = y} refl)
        ; nIso = λ X → record
            { inv = ((λ a z → z) , refl) , _
            ; sec = co≡ {X = X} {Y = X} refl
            ; ret = co≡ {X = X} {Y = X} refl } }
        where
          co≡ = coEMHom≡ {W = Wᶜ} {ε = εᶜ} {δ = δᶜ}

      winv : WeakInverse Psh→COALG
      winv .WeakInverse.invFunc = COALG→Psh
      winv .WeakInverse.η = ηIso
      winv .WeakInverse.ε = εIso

  -- need a set of object to guarantee that the Σ-type below is a set
  module _ (isSetCob : isSet (C .ob)) where
    Free : Functor Fam Psh
    Free .F-ob A .F-ob x .fst = Σ[ y ∈ C.ob ] (C.Hom[ x , y ] × A y .fst)
    Free .F-ob A .F-ob x .snd = isSetΣ isSetCob λ y → isSet× C.isSetHom (A y .snd)
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

    FreeFamAdj : Free ⊣ Psh→Fam
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
      Tᵃ = Psh→Fam ∘F Free

      Tmonᵃ : Monad Fam
      Tmonᵃ = Tᵃ , MonadFromAdjunction Free Psh→Fam FreeFamAdj

    ALG : Category _ _
    ALG = EMCategory Tmonᵃ

    Psh→ALG : Functor Psh ALG
    Psh→ALG = ComparisonEM Free Psh→Fam FreeFamAdj

    ALG→Psh : Functor ALG Psh
    ALG→Psh .F-ob X .F-ob x = X .fst .fst x
    ALG→Psh .F-ob X .F-hom {a} {b} h p = X .fst .snd b (a , h , p)
    ALG→Psh .F-ob X .F-id {a} = funExt λ p i → X .snd .fst i a p
    ALG→Psh .F-ob X .F-seq {a} {b} {c} h k =
      funExt λ p i → X .snd .snd i c (b , k , (a , h , p))
    ALG→Psh .F-hom mor = pshhom
      (λ x p → mor .fst .fst x p)
      (λ c c' f p' p hyp →
        sym (funExt⁻ (funExt⁻ (mor .fst .snd) c) (c' , f , p'))
        ∙ cong (mor .fst .fst c) hyp)
    ALG→Psh .F-id = makePshHomStrictPath refl
    ALG→Psh .F-seq f g = makePshHomStrictPath refl

    -- monadicity
    Psh≃ALG : Psh ≃ᶜ ALG
    Psh≃ALG = equivᶜ Psh→ALG ∣ winv ∣₁
      where
        ηIso : NT.NatIso 𝟙⟨ Psh ⟩ (ALG→Psh ∘F Psh→ALG)
        ηIso = record
          { trans = NT.natTrans
              (λ P → pshhom (λ c z → z) (λ c c' f p' p z → z))
              (λ α → makePshHomStrictPath refl)
          ; nIso = λ P → record
              { inv = pshhom (λ c z → z) (λ c c' f p' p z → z)
              ; sec = refl ; ret = refl } }

        εIso : NT.NatIso (Psh→ALG ∘F ALG→Psh) 𝟙⟨ ALG ⟩
        εIso = record
          { trans = NT.natTrans
              (λ X → ((λ a z → z) , refl) , _)
              (λ {x = x} {y = y} α → em≡ {X = x} {Y = y} refl)
          ; nIso = λ X → record
              { inv = ((λ a z → z) , refl) , _
              ; sec = em≡ {X = X} {Y = X} refl
              ; ret = em≡ {X = X} {Y = X} refl } }
          where
            em≡ = emHom≡ {Mon = Tmonᵃ}

        winv : WeakInverse Psh→ALG
        winv .WeakInverse.invFunc = ALG→Psh
        winv .WeakInverse.η = ηIso
        winv .WeakInverse.ε = εIso
