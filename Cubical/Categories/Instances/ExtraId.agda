{-
  Given a category C, produces an equivalent category ExtraId C whose Hom sets have a new identity morphism freely adjoined
-}

module Cubical.Categories.Instances.ExtraId where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.HLevels

import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base

private
  variable ℓ ℓC ℓC' ℓD ℓD' : Level

open Category
open Functor

module _ (C : Category ℓC ℓC') where
  eqToId : ∀ {x y} → x Eq.≡ y → C [ x , y ]
  eqToId Eq.refl = C .id

  -- This is equivalent to the MappingCylinder of eqToId
  data ExtraIdHom (x y : C .ob) : Type (ℓ-max ℓC ℓC') where
    synId : x Eq.≡ y → ExtraIdHom x y
    semHom : C [ x , y ] → ExtraIdHom x y
    synId≡id : ∀ (eq : x Eq.≡ y) → synId eq ≡ semHom (eqToId eq)

  elim : ∀ {x}
    → {M : ∀ y → ExtraIdHom x y → Type ℓ}
    → (Mid : M _ (synId Eq.refl))
    → (MHom : ∀ {y}(f : C [ x , y ]) → M _ (semHom f))
    → PathP (λ i → M _ (synId≡id Eq.refl i)) Mid (MHom (C .id))
    → ∀ y f → M y f
  elim Mid MHom M≡ _ (synId Eq.refl) = Mid
  elim Mid MHom M≡ _ (semHom f) = MHom f
  elim Mid MHom M≡ _ (synId≡id Eq.refl i) = M≡ i

  ExtraIdHom→Hom : ∀ {x} → ∀ y (f : ExtraIdHom x y) → C [ x , y ]
  ExtraIdHom→Hom = elim (C .id) (λ {y} f → f) refl

  isSetExtraIdHom : ∀ {x y} → isSet (ExtraIdHom x y)
  isSetExtraIdHom {x}{y} = isSetRetract (ExtraIdHom→Hom y) semHom
    (lemma y)
    (C .isSetHom)
    where
      lemma : ∀ y (f : ExtraIdHom x y) → semHom (ExtraIdHom→Hom y f) ≡ f
      lemma = elim (sym $ synId≡id Eq.refl) (λ f → refl)
        (λ i j → synId≡id Eq.refl (i ∨ ~ j))

  elimProp : ∀ {x}
    → {M : ∀ y → ExtraIdHom x y → Type ℓ}
    → (∀ {y} f → isProp (M y f))
    → (MHom : ∀ {y} (f : C [ x , y ]) → M _ (semHom f))
    → ∀ y f → M y f
  elimProp {ℓ}{x}{M} isPropM MHom = elim (subst (M x) (sym (synId≡id Eq.refl)) (MHom (C .id)))
    MHom
    (isProp→PathP (λ i → isPropM (synId≡id Eq.refl i)) _ _)

  elimProp2 : ∀ {x}
    → {M : ∀ y (f : ExtraIdHom x y) z (g : ExtraIdHom y z) → Type ℓ}
    → (∀ {y}{z} f g → isProp (M y f z g))
    → (MHom : ∀ {y z} f g → M y (semHom f) z (semHom g))
    → ∀ y f z g → M y f z g
  elimProp2 {x = x} isPropM MHom = elimProp (λ f → isPropΠ2 λ x₁ → isPropM f)
    λ {y} f → elimProp (λ {y = y₁} → isPropM (semHom f)) (λ {y = y₁} → MHom f)

  elimProp3 : ∀ {x}
    → {M : ∀ y (f : ExtraIdHom x y) z (g : ExtraIdHom y z) w (h : ExtraIdHom z w) → Type ℓ}
    → (∀ {y}{z}{w} f g h → isProp (M y f z g w h))
    → (MHom : ∀ {y z w} f g h → M y (semHom f) z (semHom g) w (semHom h))
    → ∀ y f z g w h → M y f z g w h
  elimProp3 isPropM MHom = elimProp2 (λ f g → isPropΠ2 (λ x₁ → isPropM f g))
    (λ f g → elimProp (λ {y = y₁} → isPropM (semHom f) (semHom g)) (λ {y = y₁} → MHom f g))

  ⋆ExtraId : ∀ {x} → ∀ y → ExtraIdHom x y → ∀ z → ExtraIdHom y z → ExtraIdHom x z
  ⋆ExtraId = elim (λ z z₁ → z₁) (λ f → elim (semHom f) (λ g → semHom (f ⋆⟨ C ⟩ g)) (cong semHom $ sym $ C .⋆IdR f))
    (funExt₂ (elimProp (λ _ → isSetExtraIdHom _ _)
      (λ f → cong semHom $ sym $ C .⋆IdL f)))

  ExtraId : Category ℓC (ℓ-max ℓC ℓC')
  ExtraId .ob = C .ob
  ExtraId .Hom[_,_] = ExtraIdHom
  ExtraId .id = synId Eq.refl
  ExtraId ._⋆_ f g = ⋆ExtraId _ f _ g
  ExtraId .⋆IdL {x = x} f = refl
  ExtraId .⋆IdR {x = x} = ⋆IdR' _ where
    ⋆IdR' : ∀ y → (f : ExtraIdHom x y) → ⋆ExtraId y f y (synId Eq.refl) ≡ f
    ⋆IdR' = elimProp (λ _ → isSetExtraIdHom _ _) (λ _ → refl)
  ExtraId .⋆Assoc {x} f g h = ⋆Assoc' _ f _ g _ h where
    ⋆Assoc' : ∀ y (f : ExtraIdHom x y) z (g : ExtraIdHom y z)
      w (h : ExtraIdHom z w) →
      ⋆ExtraId z (⋆ExtraId y f z g) w h ≡
      ⋆ExtraId y f w (⋆ExtraId z g w h)
    ⋆Assoc' = elimProp3 (λ f g h → isSetExtraIdHom _ _)
      (λ f g h → cong semHom $ C .⋆Assoc f g h)
  ExtraId .isSetHom = isSetExtraIdHom

  σ : Functor C ExtraId
  σ .F-ob = λ z → z
  σ .F-hom = semHom
  σ .F-id = sym (synId≡id Eq.refl)
  σ .F-seq = λ _ _ → refl

  module _ {D : Category ℓD ℓD'} (F : Functor C D) where
    recF-hom : ∀ x y → ExtraId [ x , y ] → D [ F .F-ob x , F .F-ob y ]
    recF-hom x = elim (D .id) (F .F-hom) (sym $ F .F-id)

    recF : Functor ExtraId D
    recF .F-ob = F .F-ob
    recF .F-hom {x}{y} = recF-hom x y
    recF .F-id = refl
    recF .F-seq {x} f g = F-seq' _ f _ g
      where
      F-seq' : ∀ y (f : ExtraId [ x , y ]) z (g : ExtraId [ y , z ]) →
        recF-hom x z (seq' ExtraId f g) ≡
        seq' D (recF-hom x y f) (recF-hom y z g)
      F-seq' = elimProp2 (λ f g → D .isSetHom _ _) (F .F-seq)

  π : Functor ExtraId C
  π = recF Id
