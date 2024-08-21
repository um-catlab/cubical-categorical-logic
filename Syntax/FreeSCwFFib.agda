{-
  The free fibration of simple categories with families?
-}

{-# OPTIONS --safe #-}
module Syntax.FreeSCwFFib where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf

open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Displayed.Limits.BinProduct.Concrete
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal.More
open import Agda.Builtin.Cubical.Equiv
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Foundations.Univalence

private
  variable
    ℓC ℓC' ℓT ℓT' ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' ℓCᴰᴰ ℓCᴰᴰ' : Level

open Category
open Functor
module FreeSCwFFib
  (C : Category ℓC ℓC')
  (Ty : Type ℓT)
  (TM : ∀ (A : Ty) → Presheaf C ℓT')
  (GTy : Ty → Type ℓTᴰ)
  where
  Tm : C .ob → Ty → Type ℓT'
  Tm Γ A = ⟨ TM A ⟅ Γ ⟆ ⟩

  act : ∀ {Δ Γ A} → C [ Δ , Γ ] → Tm Γ A → Tm Δ A
  act γ M = TM _ .F-hom γ M

  actId : ∀ {Γ A} → (M : Tm Γ A) → act (C .id) M ≡ M
  actId = funExt⁻ (TM _ .F-id)

  actAssoc : ∀ {Θ Δ Γ A}(δ : C [ Θ , Δ ])(γ : C [ Δ , Γ ]) (M : Tm Γ A)
    → act (δ ⋆⟨ C ⟩ γ) M ≡ act δ (act γ M)
  actAssoc δ γ = funExt⁻ (TM _ .F-seq γ δ)

  data Ctxᴰ (Γ : C .ob) : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓT ℓT')) ℓTᴰ)
  data Tyᴰ (A : Ty) : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓT ℓT')) ℓTᴰ)
  data Ctxᴰ Γ where
    ⊤ₑ : Ctxᴰ Γ
    _∧ₑ_ : Ctxᴰ Γ → Ctxᴰ Γ → Ctxᴰ Γ
    pb-subst : ∀ {Δ} (δ : C [ Γ , Δ ]) → Ctxᴰ Δ → Ctxᴰ Γ
    pb-tm    : ∀ {A} (M : Tm Γ A) → Tyᴰ A → Ctxᴰ Γ
  data Tyᴰ A where
    iTy : GTy A → Tyᴰ A

  module _
    (GTm : ∀ {Γ A} → Tm Γ A → Type ℓTᴰ')
    (GTmDom : ∀ {Γ A} → {M : Tm Γ A} → GTm M → Ctxᴰ Γ)
    (GTmCod : ∀ {Γ A} → {M : Tm Γ A} → GTm M → Tyᴰ A)
    where
    data Substᴰ : ∀ {Δ Γ} (γ : C [ Δ , Γ ]) → Ctxᴰ Δ → Ctxᴰ Γ → Type ((ℓ-max (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓT ℓT')) (ℓ-max ℓTᴰ ℓTᴰ')))
    data Tmᴰ : ∀ {Γ A} (M : Tm Γ A) → Ctxᴰ Γ → Tyᴰ A → Type ((ℓ-max (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓT ℓT')) (ℓ-max ℓTᴰ ℓTᴰ')))
    _≡[_]ₑ_ : ∀ {Δ Γ} {Δᴰ Γᴰ} {γ γ' : C [ Δ , Γ ]}
      → Substᴰ γ Δᴰ Γᴰ
      → γ ≡ γ'
      → Substᴰ γ' Δᴰ Γᴰ
      → Type _
    _≡[_]ₑ_ {Δᴰ = Δᴰ}{Γᴰ} γᴰ p γᴰ' = PathP (λ i → Substᴰ (p i) Δᴰ Γᴰ) γᴰ γᴰ'

    _≡[_]tₑ_ : ∀ {Γ A Γᴰ Aᴰ} {M M' : Tm Γ A}
      → Tmᴰ M Γᴰ Aᴰ
      → M ≡ M'
      → Tmᴰ M' Γᴰ Aᴰ
      → Type _
    _≡[_]tₑ_ {Γᴰ = Γᴰ}{Aᴰ} Mᴰ p Mᴰ' = PathP (λ i → Tmᴰ (p i) Γᴰ Aᴰ) Mᴰ Mᴰ'
    
    actᴰ' : ∀ {Δ Γ A}{Δᴰ Γᴰ Aᴰ}
        → {γ : C [ Δ , Γ ]}{M : Tm Γ A}
        → Substᴰ γ Δᴰ Γᴰ → Tmᴰ M Γᴰ Aᴰ
        → Tmᴰ (act γ M) Δᴰ Aᴰ
    pbt-πₑ' : ∀ {Γ A}{Aᴰ}{M : Tm Γ A} → Tmᴰ M (pb-tm M Aᴰ) Aᴰ
    data Substᴰ where
      idᴰₑ : ∀ {Γ} {Γᴰ} → Substᴰ (C .id {Γ}) Γᴰ Γᴰ
      _⋆ᴰₑ_ : ∀ {Γ Δ Θ} {Γᴰ Δᴰ Θᴰ} {f : C [ Γ , Δ ]}{g : C [ Δ , Θ ]}
        → Substᴰ f Γᴰ Δᴰ
        → Substᴰ g Δᴰ Θᴰ
        → Substᴰ (f ⋆⟨ C ⟩ g) Γᴰ Θᴰ
      ⋆IdLᴰₑ : ∀ {Γ Δ} {Γᴰ Δᴰ} {f : C [ Γ , Δ ]}
        → (fᴰ : Substᴰ f Γᴰ Δᴰ)
        → (idᴰₑ ⋆ᴰₑ fᴰ) ≡[ C .⋆IdL f ]ₑ fᴰ
      ⋆IdRᴰₑ : ∀ {Γ Δ} {Γᴰ Δᴰ} {f : C [ Γ , Δ ]}
        → (fᴰ : Substᴰ f Γᴰ Δᴰ)
        → (fᴰ ⋆ᴰₑ idᴰₑ) ≡[ C .⋆IdR f ]ₑ fᴰ
      ⋆Assocᴰₑ : ∀ {w Γ Δ Θ} {wᴰ Γᴰ Δᴰ Θᴰ}
        {f : C [ w , Γ ]}{g : C [ Γ , Δ ]}{h : C [ Δ , Θ ]}
        (fᴰ : Substᴰ f wᴰ Γᴰ)
        (gᴰ : Substᴰ g Γᴰ Δᴰ)
        (hᴰ : Substᴰ h Δᴰ Θᴰ)
        → ((fᴰ ⋆ᴰₑ gᴰ) ⋆ᴰₑ hᴰ) ≡[ C .⋆Assoc f g h ]ₑ (fᴰ ⋆ᴰₑ (gᴰ ⋆ᴰₑ hᴰ))
      !ᴰₑ : ∀ {Γ Δ}{Γᴰ} (f : C [ Γ , Δ ]) → Substᴰ f Γᴰ ⊤ₑ
      ⊤η :  ∀ {Γ Δ}{Γᴰ} {f : C [ Γ , Δ ]} (fᴰ : Substᴰ f Γᴰ ⊤ₑ) → fᴰ ≡ !ᴰₑ f
      π₁ᴰₑ : ∀ {Γ}{Γᴰ₁ Γᴰ₂} → Substᴰ (C .id {Γ}) (Γᴰ₁ ∧ₑ Γᴰ₂) Γᴰ₁
      π₂ᴰₑ : ∀ {Γ}{Γᴰ₁ Γᴰ₂} → Substᴰ (C .id {Γ}) (Γᴰ₁ ∧ₑ Γᴰ₂) Γᴰ₂
      _,pₑ_ : ∀ {Γ Δ} {Γᴰ₁ Γᴰ₂ Δᴰ} {f : C [ Δ , Γ ]}
        → Substᴰ f Δᴰ Γᴰ₁
        → Substᴰ f Δᴰ Γᴰ₂
        → Substᴰ f Δᴰ (Γᴰ₁ ∧ₑ Γᴰ₂)
      ∧β₁ₑ :  ∀ {Γ Δ} {Γᴰ₁ Γᴰ₂ Δᴰ} {f : C [ Δ , Γ ]}
        → (fᴰ₁ : Substᴰ f Δᴰ Γᴰ₁)
        → (fᴰ₂ : Substᴰ f Δᴰ Γᴰ₂)
        → ((fᴰ₁ ,pₑ fᴰ₂) ⋆ᴰₑ π₁ᴰₑ) ≡[ C .⋆IdR f ]ₑ fᴰ₁
      ∧β₂ₑ :  ∀ {Γ Δ} {Γᴰ₁ Γᴰ₂ Δᴰ} {f : C [ Δ , Γ ]}
        → (fᴰ₁ : Substᴰ f Δᴰ Γᴰ₁)
        → (fᴰ₂ : Substᴰ f Δᴰ Γᴰ₂)
        → ((fᴰ₁ ,pₑ fᴰ₂) ⋆ᴰₑ π₂ᴰₑ) ≡[ C .⋆IdR f ]ₑ fᴰ₂
      ∧ηₑ : ∀ {Γ Δ} {Γᴰ₁ Γᴰ₂ Δᴰ} {f : C [ Δ , Γ ]}
        → (fᴰ : Substᴰ f Δᴰ (Γᴰ₁ ∧ₑ Γᴰ₂))
        → fᴰ ≡[ sym (C .⋆IdR f) ]ₑ ((fᴰ ⋆ᴰₑ π₁ᴰₑ) ,pₑ (fᴰ ⋆ᴰₑ π₂ᴰₑ))

      pbs-πₑ : ∀ {Γ Δ}{Δᴰ}{g : C [ Γ , Δ ]} → Substᴰ g (pb-subst g Δᴰ) Δᴰ
      pbs-introₑ :
        ∀ {Γ Δ Θ}{Θᴰ Δᴰ}{f : C [ Θ , Γ ]}{g : C [ Γ , Δ ]}
        → Substᴰ (f ⋆⟨ C ⟩ g) Θᴰ Δᴰ
        → Substᴰ f Θᴰ (pb-subst g Δᴰ)
      pbs-βₑ :
        ∀ {Γ Δ Θ}{Θᴰ Δᴰ}{f : C [ Θ , Γ ]}{g : C [ Γ , Δ ]}
        → (fgᴰ : Substᴰ (f ⋆⟨ C ⟩ g) Θᴰ Δᴰ)
        → (pbs-introₑ fgᴰ ⋆ᴰₑ pbs-πₑ) ≡ fgᴰ
      pbs-ηₑ :
        ∀ {Γ Δ Θ}{Θᴰ Δᴰ}{f : C [ Θ , Γ ]}{g : C [ Γ , Δ ]}
        → (fᴰ : Substᴰ f Θᴰ (pb-subst g Δᴰ))
        → fᴰ ≡ pbs-introₑ (fᴰ ⋆ᴰₑ pbs-πₑ)

      pbt-introₑ : ∀ {Δ Γ A}{Δᴰ Aᴰ}{γ : C [ Δ , Γ ]}{M : Tm Γ A}
        → Tmᴰ (act γ M) Δᴰ Aᴰ
        → Substᴰ γ Δᴰ (pb-tm M Aᴰ)
      pbt-ηₑ : ∀ {Δ Γ A}{Δᴰ Aᴰ}{γ : C [ Δ , Γ ]}{M : Tm Γ A}
        → (γᴰ : Substᴰ γ Δᴰ (pb-tm M Aᴰ))
        → γᴰ ≡ pbt-introₑ (actᴰ' γᴰ pbt-πₑ')

      isSetHomᴰₑ : ∀ {Γ Δ}{Γᴰ Δᴰ}{f : C [ Γ , Δ ]} → isSet (Substᴰ f Γᴰ Δᴰ)
    data Tmᴰ where
      iTm : ∀ {Γ A}{M : Tm Γ A} (g : GTm M) → Tmᴰ M (GTmDom g) (GTmCod g)
      actᴰ : ∀ {Δ Γ A}{Δᴰ Γᴰ Aᴰ}
        → {γ : C [ Δ , Γ ]}{M : Tm Γ A}
        → Substᴰ γ Δᴰ Γᴰ → Tmᴰ M Γᴰ Aᴰ
        → Tmᴰ (act γ M) Δᴰ Aᴰ

      actIdᴰ : ∀ {Γ A}{Γᴰ Aᴰ}
        → {M : Tm Γ A}
        → (Mᴰ : Tmᴰ M Γᴰ Aᴰ)
        → actᴰ idᴰₑ Mᴰ ≡[ actId M ]tₑ Mᴰ
      actAssocᴰ : ∀ {Θ Δ Γ A}{Θᴰ Δᴰ Γᴰ Aᴰ}
        {δ : C [ Θ , Δ ]}{γ : C [ Δ , Γ ]}{M : Tm Γ A}
        → (δᴰ : Substᴰ δ Θᴰ Δᴰ)(γᴰ : Substᴰ γ Δᴰ Γᴰ) (Mᴰ : Tmᴰ M Γᴰ Aᴰ)
        → actᴰ (δᴰ ⋆ᴰₑ γᴰ) Mᴰ ≡[ actAssoc δ γ M ]tₑ actᴰ δᴰ (actᴰ γᴰ Mᴰ)

      pbt-πₑ : ∀ {Γ A}{Aᴰ}{M : Tm Γ A} → Tmᴰ M (pb-tm M Aᴰ) Aᴰ
      pbt-βₑ : ∀ {Δ Γ A}{Δᴰ Aᴰ}{γ : C [ Δ , Γ ]}{M : Tm Γ A}
        → (Mᴰ : Tmᴰ (act γ M) Δᴰ Aᴰ)
        → actᴰ (pbt-introₑ Mᴰ) pbt-πₑ ≡ Mᴰ

      isSetTmᴰ : ∀ {Γ A Γᴰ Aᴰ}{M : Tm Γ A} → isSet (Tmᴰ M Γᴰ Aᴰ)
      
    actᴰ' = actᴰ
    pbt-πₑ' = pbt-πₑ
