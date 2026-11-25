{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.ChosenReind where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Displayed.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

record ChosenReind {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ')) where
  private
    module Cᴰ = Categoryᴰ Cᴰ
  field
    reind⟨_⟩ : ∀ {x y} {f g : C [ x , y ]} {a b} → f ≡ g
      → Cᴰ.Hom[ f ][ a , b ] → Cᴰ.Hom[ g ][ a , b ]
    reind-filler : ∀ {x y} {f g : C [ x , y ]} {a b} (e : f ≡ g)
      (fᴰ : Cᴰ.Hom[ f ][ a , b ])
      → PathP (λ i → Cᴰ.Hom[ e i ][ a , b ]) fᴰ (reind⟨ e ⟩ fᴰ)

module ChosenReindNotation {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  ⦃ cr : ChosenReind Cᴰ ⦄ where
  private
    module C = Category C
  module F = Fibers Cᴰ
  open Categoryᴰ Cᴰ public
  open ChosenReind cr public

  private
    loop : ∀ {x} → C.id C.⋆ C.id ≡ C.id {x}
    loop = C.⋆IdL C.id

  infixr 9 _⋆ⱽ_ _⋆ⱽᴰ_ _⋆ᴰⱽ_

  idᴰ⟨_⟩ : ∀ {x} {h : C [ x , x ]} → C.id ≡ h → (a : ob[ x ])
    → Hom[ h ][ a , a ]
  idᴰ⟨ e ⟩ a = reind⟨ e ⟩ idᴰ

  comp⟨_⟩ : ∀ {x y z} {f : C [ x , y ]} {g : C [ y , z ]} {h : C [ x , z ]}
    {a b c} → f C.⋆ g ≡ h → Hom[ f ][ a , b ] → Hom[ g ][ b , c ]
    → Hom[ h ][ a , c ]
  comp⟨ e ⟩ fᴰ gᴰ = reind⟨ e ⟩ (fᴰ ⋆ᴰ gᴰ)

  Hom[_,_]ⱽ : ∀ {x} → ob[ x ] → ob[ x ] → Type ℓCᴰ'
  Hom[ a , b ]ⱽ = Hom[ C.id ][ a , b ]

  _⋆ⱽ_ : ∀ {x} {a b c : ob[ x ]} → Hom[ a , b ]ⱽ → Hom[ b , c ]ⱽ
    → Hom[ a , c ]ⱽ
  _⋆ⱽ_ = comp⟨ loop ⟩

  _⋆ⱽᴰ_ : ∀ {x y} {f : C [ x , y ]} {a b c} → Hom[ a , b ]ⱽ
    → Hom[ f ][ b , c ] → Hom[ f ][ a , c ]
  _⋆ⱽᴰ_ {f = f} = comp⟨ C.⋆IdL f ⟩

  _⋆ᴰⱽ_ : ∀ {x y} {f : C [ x , y ]} {a b c} → Hom[ f ][ a , b ]
    → Hom[ b , c ]ⱽ → Hom[ f ][ a , c ]
  _⋆ᴰⱽ_ {f = f} = comp⟨ C.⋆IdR f ⟩

  open F public using (_∫≡_ ; rectifyOut ; ⟨_⟩⋆⟨_⟩ ; ⋆IdL ; ⋆IdR ; ⋆Assoc)

  reind-∫≡ : ∀ {x y} {f g : C [ x , y ]} (p : f ≡ g) {a b}
    (fᴰ : Hom[ f ][ a , b ]) → reind⟨ p ⟩ fᴰ ∫≡ fᴰ
  reind-∫≡ p fᴰ = ΣPathP (sym p , symP (reind-filler p fᴰ))

  reind⟨⟩≡subst : ∀ {x y} {f g : C [ x , y ]} (e : f ≡ g) {a b}
    (fᴰ : Hom[ f ][ a , b ])
    → reind⟨ e ⟩ fᴰ ≡ subst (λ h → Hom[ h ][ a , b ]) e fᴰ
  reind⟨⟩≡subst e {a} {b} fᴰ =
    rectifyOut
      (reind-∫≡ e fᴰ ∙ ΣPathP (e , subst-filler (λ h → Hom[ h ][ a , b ]) e fᴰ))

  associative : ∀ {w x y z} {f : C [ w , x ]} {g : C [ x , y ]}
    {h : C [ y , z ]} {k : C [ w , y ]} {l : C [ x , z ]} {m : C [ w , z ]}
    (e₁ : f C.⋆ g ≡ k) (e₂ : k C.⋆ h ≡ m) (e₃ : g C.⋆ h ≡ l)
    (e₄ : f C.⋆ l ≡ m) {a b c d} (fᴰ : Hom[ f ][ a , b ])
    (gᴰ : Hom[ g ][ b , c ]) (hᴰ : Hom[ h ][ c , d ])
    → comp⟨ e₂ ⟩ (comp⟨ e₁ ⟩ fᴰ gᴰ) hᴰ ≡ comp⟨ e₄ ⟩ fᴰ (comp⟨ e₃ ⟩ gᴰ hᴰ)
  associative e₁ e₂ e₃ e₄ fᴰ gᴰ hᴰ =
    rectifyOut
      (reind-∫≡ e₂ _
      ∙ ⟨ reind-∫≡ e₁ _ ⟩⋆⟨ refl ⟩
      ∙ ⋆Assoc (_ , fᴰ) (_ , gᴰ) (_ , hᴰ)
      ∙ sym (⟨ refl ⟩⋆⟨ reind-∫≡ e₃ _ ⟩)
      ∙ sym (reind-∫≡ e₄ _))

  unit-leftᴰ : ∀ {x y} {f : C [ x , y ]} (e : C.id C.⋆ f ≡ f) {a b}
    (fᴰ : Hom[ f ][ a , b ]) → comp⟨ e ⟩ idᴰ fᴰ ≡ fᴰ
  unit-leftᴰ e fᴰ = rectifyOut (reind-∫≡ e _ ∙ ⋆IdL (_ , fᴰ))

  unit-rightᴰ : ∀ {x y} {f : C [ x , y ]} (e : f C.⋆ C.id ≡ f) {a b}
    (fᴰ : Hom[ f ][ a , b ]) → comp⟨ e ⟩ fᴰ idᴰ ≡ fᴰ
  unit-rightᴰ e fᴰ = rectifyOut (reind-∫≡ e _ ∙ ⋆IdR (_ , fᴰ))

  Fibre : C.ob → Category ℓCᴰ ℓCᴰ'
  Fibre x .Category.ob = ob[ x ]
  Fibre x .Category.Hom[_,_] = Hom[_,_]ⱽ
  Fibre x .Category.id = idᴰ
  Fibre x .Category._⋆_ = _⋆ⱽ_
  Fibre x .Category.⋆IdL = unit-leftᴰ loop
  Fibre x .Category.⋆IdR = unit-rightᴰ loop
  Fibre x .Category.⋆Assoc uⱽ vⱽ wⱽ = associative loop loop loop loop uⱽ vⱽ wⱽ
  Fibre x .Category.isSetHom = isSetHomᴰ

  reind-id : ∀ {x y} {f : C [ x , y ]} (p : f ≡ f) {a b}
    (fᴰ : Hom[ f ][ a , b ]) → reind⟨ p ⟩ fᴰ ≡ fᴰ
  reind-id p fᴰ = rectifyOut (reind-∫≡ p fᴰ)

  reind-comp : ∀ {x y z} {f : C [ x , y ]} {g : C [ y , z ]}
    {h k : C [ x , z ]} (e : f C.⋆ g ≡ h) (q : h ≡ k) (e' : f C.⋆ g ≡ k)
    {a b c} (fᴰ : Hom[ f ][ a , b ]) (gᴰ : Hom[ g ][ b , c ])
    → reind⟨ q ⟩ (comp⟨ e ⟩ fᴰ gᴰ) ≡ comp⟨ e' ⟩ fᴰ gᴰ
  reind-comp e q e' fᴰ gᴰ =
    rectifyOut (reind-∫≡ q _ ∙ reind-∫≡ e _ ∙ sym (reind-∫≡ e' _))

  reind-reind : ∀ {x y} {f g h : C [ x , y ]} (p : f ≡ g) (q : g ≡ h)
    (r : f ≡ h) {a b} (fᴰ : Hom[ f ][ a , b ])
    → reind⟨ q ⟩ (reind⟨ p ⟩ fᴰ) ≡ reind⟨ r ⟩ fᴰ
  reind-reind p q r fᴰ =
    rectifyOut (reind-∫≡ q _ ∙ reind-∫≡ p fᴰ ∙ sym (reind-∫≡ r fᴰ))

  reind≡→∫≡ : ∀ {x y} {f g : C [ x , y ]} (p : f ≡ g) {a b}
    {fᴰ : Hom[ f ][ a , b ]} {gᴰ : Hom[ g ][ a , b ]}
    → reind⟨ p ⟩ fᴰ ≡ gᴰ → fᴰ ∫≡ gᴰ
  reind≡→∫≡ {g = g} p {fᴰ = fᴰ} q = sym (reind-∫≡ p fᴰ) ∙ cong (g ,_) q

  comp≡Freind' : ∀ {x y z} {f : C [ x , y ]} {g : C [ y , z ]}
    {h : C [ x , z ]} (e e' : f C.⋆ g ≡ h) {a b c}
    (fᴰ : Hom[ f ][ a , b ]) (gᴰ : Hom[ g ][ b , c ])
    → comp⟨ e ⟩ fᴰ gᴰ ≡ F.reind e' (fᴰ ⋆ᴰ gᴰ)
  comp≡Freind' e e' fᴰ gᴰ =
    rectifyOut (reind-∫≡ e _ ∙ F.reind-filler e')

  comp≡Freind : ∀ {x y z} {f : C [ x , y ]} {g : C [ y , z ]}
    {h : C [ x , z ]} (e : f C.⋆ g ≡ h) {a b c} (fᴰ : Hom[ f ][ a , b ])
    (gᴰ : Hom[ g ][ b , c ]) → comp⟨ e ⟩ fᴰ gᴰ ≡ F.reind e (fᴰ ⋆ᴰ gᴰ)
  comp≡Freind e = comp≡Freind' e e

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  open ChosenReind

  instance
    ChosenReind^op : ⦃ cr : ChosenReind Cᴰ ⦄ → ChosenReind (Cᴰ ^opᴰ)
    ChosenReind^op ⦃ cr ⦄ .reind⟨_⟩ = cr .reind⟨_⟩
    ChosenReind^op ⦃ cr ⦄ .reind-filler = cr .reind-filler

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  open ChosenReind

  private
    module F = Fibers Cᴰ

  TransportReind : ChosenReind Cᴰ
  TransportReind .reind⟨_⟩ = F.reind
  TransportReind .reind-filler e fᴰ = F.rectifyOut {e' = e} (F.reind-filler e)

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  instance
    TransportReindInst : ChosenReind Cᴰ
    TransportReindInst = TransportReind Cᴰ
  {-# INCOHERENT TransportReindInst #-}
