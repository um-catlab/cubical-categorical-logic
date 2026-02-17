
module Cubical.Categories.Functors.More where

open import Cubical.Foundations.Prelude
import Cubical.Data.Equality as Eq
-- open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
-- open import Cubical.Categories.Isomorphism.More
-- open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor.Base
-- open import Cubical.Categories.Functor.Compose
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
-- open import Cubical.Foundations.Equiv
-- open import Cubical.Foundations.Equiv.Properties
-- open import Cubical.Functions.Embedding
-- open import Cubical.HITs.PropositionalTruncation as Prop

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
    C : Category ℓC ℓC'
    D : Category ℓD ℓD'
    E : Category ℓE ℓE'

open Category
open Functor
open NatTrans

FunctorEq : {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  → (F G : Functor C D) → Type _
FunctorEq {C = C}{D = D} F G = Σ[ ob≡ ∈ (F .F-ob Eq.≡ G .F-ob) ]
  Eq.HEq (Eq.ap ((λ F-ob₁ → ∀ {x} {y} → C [ x , y ] → D [ F-ob₁ x , F-ob₁ y ])) ob≡)
    (F .F-hom)
    (G .F-hom)

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  (F : Functor C D)
  (F-hom-singl : ∀ {x y} (f : C [ x , y ]) → singl (F ⟪ f ⟫))
  where
  -- I lifted these definitions to make it easier to make them opaque,
  -- but I have ultimately ended up keeping them transparent.
  F-hom-ty : Type _
  F-hom-ty = ∀ {x y} (f : C [ x , y ]) → D [ F ⟅ x ⟆ , F ⟅ y ⟆ ]
  F-hom' : F-hom-ty
  F-hom' f = F-hom-singl f .fst

  F-hom≡F-hom' : Path F-hom-ty (F .F-hom) F-hom'
  F-hom≡F-hom' = implicitFunExt (implicitFunExt (funExt λ f → F-hom-singl f .snd))

  Fid : {x : C .ob} → F-hom' (C .id {x}) ≡ D .id
  Fid {x} = subst (λ (F-hom'' : F-hom-ty) → F-hom'' (C .id {x}) ≡ D .id) F-hom≡F-hom' (F .F-id)

  Fseq : {x y z : C .ob} (f : C [ x , y ]) (g : C [ y , z ]) →
    F-hom' (seq' C f g) ≡ seq' D (F-hom' f) (F-hom' g)
  Fseq = λ f g →
    subst
     (λ (F-hom'' : F-hom-ty) →
        F-hom'' (seq' C f g) ≡ seq' D (F-hom'' f) (F-hom'' g))
     F-hom≡F-hom' (F .F-seq f g)

  improveF-hom : Functor C D
  improveF-hom = record
    { F-ob = F .F-ob
    ; F-hom = F-hom'
    ; F-id = Fid
    ; F-seq = Fseq
    }

ConstantComposeFunctor :
  (C : Category ℓC ℓC') (D : Category ℓD ℓD' ) (c : C .ob)
  (F : Functor C D) →
  Constant (D ^op) D (F .F-ob c) ≡ F ∘F Constant (D ^op) C c
ConstantComposeFunctor C D c F = Functor≡
  (λ c → ( refl ))
    (λ f → (
      D .id
     ≡⟨ sym (F .F-id) ⟩
       F ⟪ Constant (D ^op) C c ⟪ f ⟫ ⟫ ∎
  ))

-- The data of a functor, parameterized by the action on objects
record ActionOnMorphisms
  (C : Category ℓC ℓC')
  (D : Category ℓD ℓD')
  (F₀ : C .ob → D .ob) : Type (ℓ-max (ℓ-max ℓC ℓC') ℓD') where
  no-eta-equality

  open Category

  field
    F-hom : {x y : C .ob} → C [ x , y ] → D [ F₀ x , F₀ y ]
    F-id  : {x : C .ob} → F-hom (C .id) ≡ D .id {x = F₀ x}
    F-seq : {x y z : C .ob} (f : C [ x , y ]) (g : C [ y , z ])
          → F-hom (f ⋆⟨ C ⟩ g) ≡ (F-hom f) ⋆⟨ D ⟩ (F-hom g)

open ActionOnMorphisms

ActionOnMorphisms→Functor :
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}{F₀ : C .ob → D .ob}
                          → ActionOnMorphisms C D F₀
                          → Functor C D
ActionOnMorphisms→Functor {F₀ = F₀} F₁ .F-ob = F₀
ActionOnMorphisms→Functor {F₀ = F₀} F₁ .F-hom = F₁ .F-hom
ActionOnMorphisms→Functor {F₀ = F₀} F₁ .F-id = F₁ .F-id
ActionOnMorphisms→Functor {F₀ = F₀} F₁ .F-seq = F₁ .F-seq


module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         (F : Functor C D)
         where
  open NatTrans
  open NatIso
  open isIso
  hasIsoRetraction→isFaithful : (F⁻ : Functor D C) (ret : F⁻ ∘F F ≅ᶜ Id)
    → isFaithful F
  hasIsoRetraction→isFaithful F⁻ ret x y f g F⟪f⟫≡F⟪g⟫ =
    ⋆CancelL (NatIsoAt ret _)
      (sym (ret .trans .N-hom f)
      ∙ cong₂ (seq' C) (cong (F⁻ .F-hom) F⟪f⟫≡F⟪g⟫) refl
      ∙ ret .trans .N-hom g)

module _ {ℓA ℓA' ℓB ℓB' : Level}
  {A : Category ℓA ℓA'}{B : Category ℓB ℓB'}
  {C : Category ℓC ℓC'}
  (F : Functor A B)(G : Functor B C) where
  isFaithful-GF→isFaithful-F : isFaithful (G ∘F F) → isFaithful F
  isFaithful-GF→isFaithful-F faith x y f g p =
    faith x y f g (congS (λ Ff → G ⟪ Ff ⟫) p)

module _ {ℓA ℓA' ℓB ℓB' : Level}
  {A : Category ℓA ℓA'}{B : Category ℓB ℓB'}
  {F G : Functor A B}
  (α : NatIso F G)
  where
  private
    module A = Category A
    module B = Category B
  isFaithful≅ : isFaithful G → isFaithful F
  isFaithful≅ faith x y f g p =
    faith x y f g
      (NatIso.sqLR α
      ∙ cong₂ B._⋆_ (cong₂ B._⋆_ refl p) refl
      ∙ sym (NatIso.sqLR α))
