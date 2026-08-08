{-# OPTIONS --lossy-unification #-}
{-

  TELESCOPES OF A CATEGORY WITH FAMILIES, DIFFERENCE-LIST STYLE.

  `Cubical.Categories.Displayed.Forded.Ext` presents a context former
  as a uniform operation on the slice over C, and gets definitional
  unitality and associativity of concatenation for free.  But `Ext`'s
  concatenation feeds the NEXT former the base map `p S∘ disp`, which
  forgets the extension --- so as it stands `Ext` only models
  NON-DEPENDENT iteration.

  `Tele` below is `Ext` plus one field: a COMPREHENSION functor

      cmp : (E : Category) (p : StrictFunctor E C) → StrictFunctor (at E p) C

  which names the extended context, and concatenation feeds `cmp`, not
  `p S∘ disp`, to the next former.  All three components are still
  definitionally unital and associative in any association, and
  `fromExt` shows the `Ext` story is the special case `cmp = p S∘ disp`.

  A category with families supplies exactly one such former, `tyTele`:
  its displayed category is "one more type", homs are context morphisms
  between the extended contexts that commute with the projections, and
  `cmp` reads off that morphism.  Iterating it gives DEPENDENT
  telescopes --- the second type genuinely lives over the first
  extended context --- and telescope concatenation is definitionally
  associative, unlike the `List`-of-types presentation used in
  WithFamilies.Simple.Instances.Free.

  LEVELS: as in Forded.agda, `Tele` pins every category to a single
  level pair, so `Ty` has to be at ℓC.  Real telescopes raise levels;
  that wants Cubical.Categories.LocallySmall.

-}
module Cubical.Categories.WithFamilies.Forded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functors.Strict.Base
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Displayed.Forded
open import Cubical.Categories.WithFamilies.Base

private
  variable
    ℓC ℓC' ℓT ℓT' : Level

open StrictFunctor
open Categoryᶠᴰ
open Ext

-- ------------------------------------------------------------------
-- A DEPENDENT context former.
record Tele (C : Category ℓC ℓC') : Type (ℓ-suc (ℓ-max ℓC ℓC')) where
  field
    at   : (E : Category ℓC ℓC') → StrictFunctor E C → Category ℓC ℓC'
    disp : (E : Category ℓC ℓC') (p : StrictFunctor E C)
         → StrictFunctor (at E p) E
    -- the extended context: what the next former is indexed by
    cmp  : (E : Category ℓC ℓC') (p : StrictFunctor E C)
         → StrictFunctor (at E p) C

open Tele

module _ {C : Category ℓC ℓC'} where
  εT : Tele C
  εT .at   E p = E
  εT .disp E p = SId
  εT .cmp  E p = p

  _·ᵀ_ : Tele C → Tele C → Tele C
  (Δ ·ᵀ Θ) .at E p = Θ .at (Δ .at E p) (Δ .cmp E p)
  (Δ ·ᵀ Θ) .disp E p =
    Δ .disp E p S∘ Θ .disp (Δ .at E p) (Δ .cmp E p)
  (Δ ·ᵀ Θ) .cmp E p = Θ .cmp (Δ .at E p) (Δ .cmp E p)

  teleT-lUnit : (Δ : Tele C) → (εT ·ᵀ Δ) ≡ Δ
  teleT-lUnit Δ = refl

  teleT-rUnit : (Δ : Tele C) → (Δ ·ᵀ εT) ≡ Δ
  teleT-rUnit Δ = refl

  teleT-assoc : (Δ Θ Ξ : Tele C)
    → ((Δ ·ᵀ Θ) ·ᵀ Ξ) ≡ (Δ ·ᵀ (Θ ·ᵀ Ξ))
  teleT-assoc Δ Θ Ξ = refl

  -- `Ext` is the special case where the extended context is just the
  -- old one --- i.e. the NON-DEPENDENT former --- and the embedding is
  -- a strict homomorphism.
  fromExt : Ext C → Tele C
  fromExt Δ .at   E p = Δ .at E p
  fromExt Δ .disp E p = Δ .disp E p
  fromExt Δ .cmp  E p = p S∘ Δ .disp E p

  fromExt-ε : fromExt εE ≡ εT
  fromExt-ε = refl

  fromExt-· : (Δ Θ : Ext C) → fromExt (Δ · Θ) ≡ (fromExt Δ ·ᵀ fromExt Θ)
  fromExt-· Δ Θ = refl

-- ------------------------------------------------------------------
-- A CwF's ONE-TYPE former.
module CwFᶠNotation (𝒞 : CwF ℓC ℓC' ℓT ℓT') where
  C : Category ℓC ℓC'
  C = 𝒞 .fst

  Ty : Presheaf C ℓT
  Ty = 𝒞 .snd .fst

  Tm : Presheafᴰ Ty (Unitᴰ C) ℓT'
  Tm = 𝒞 .snd .snd .fst

  ext : ∀ Γ A → UniversalElement C (Comprehension Ty Tm Γ A)
  ext = 𝒞 .snd .snd .snd .snd

  module C = Category C
  module Ty = PresheafNotation Ty

  infixl 5 _⨾_
  -- the extended context
  _⨾_ : (Γ : C.ob) → Ty.p[ Γ ] → C.ob
  Γ ⨾ A = ext Γ A .UniversalElement.vertex

  -- its projection
  π : ∀ {Γ} (A : Ty.p[ Γ ]) → C [ Γ ⨾ A , Γ ]
  π {Γ} A = ext Γ A .UniversalElement.element .fst

module _ (𝒞 : CwF ℓC ℓC' ℓT ℓT') where
  open CwFᶠNotation 𝒞

  -- "one more type": objects over Γ are types in Γ, and a morphism
  -- over γ is a context morphism of the EXTENDED contexts commuting
  -- with the projections.  All the laws are C's laws, because the side
  -- condition is a path in a hom-set, hence a proposition.
  𝒯ᶠᴰ : Categoryᶠᴰ C ℓT ℓC'
  𝒯ᶠᴰ .ob[_] Γ = Ty.p[ Γ ]
  𝒯ᶠᴰ .Hom[_][_,_] {Γ} {Δ} γ A B =
    Σ[ h ∈ C [ Γ ⨾ A , Δ ⨾ B ] ] (h C.⋆ π B ≡ π A C.⋆ γ)
  𝒯ᶠᴰ .idᴰ {Γ} {A} i ei =
    C.id ,
    (C.⋆IdL _ ∙ sym (C.⋆IdR _) ∙ cong (π A C.⋆_) (Eq.eqToPath ei))
  𝒯ᶠᴰ .⋆ᴰ {xᴰ = A} {zᴰ = E} f g h e (h₁ , c₁) (h₂ , c₂) =
    (h₁ C.⋆ h₂) ,
    ( C.⋆Assoc h₁ h₂ (π E)
    ∙ cong (h₁ C.⋆_) c₂
    ∙ sym (C.⋆Assoc _ _ g)
    ∙ cong (C._⋆ g) c₁
    ∙ C.⋆Assoc (π A) f g
    ∙ cong (π A C.⋆_) (Eq.eqToPath e))
  𝒯ᶠᴰ .⋆IdLᴰ i ei f e fᴰ =
    ΣPathP (C.⋆IdL _ , isProp→PathP (λ _ → C.isSetHom _ _) _ _)
  𝒯ᶠᴰ .⋆IdRᴰ f i ei e fᴰ =
    ΣPathP (C.⋆IdR _ , isProp→PathP (λ _ → C.isSetHom _ _) _ _)
  𝒯ᶠᴰ .⋆Assocᴰ f g h fg efg gh egh k e₁ e₂ fᴰ gᴰ hᴰ =
    ΣPathP (C.⋆Assoc _ _ _ , isProp→PathP (λ _ → C.isSetHom _ _) _ _)
  𝒯ᶠᴰ .idᴰ-coh i i' ei ei' p =
    ΣPathP (refl , isProp→PathP (λ _ → C.isSetHom _ _) _ _)
  𝒯ᶠᴰ .⋆ᴰ-coh f g h h' e e' p fᴰ gᴰ =
    ΣPathP (refl , isProp→PathP (λ _ → C.isSetHom _ _) _ _)
  𝒯ᶠᴰ .isSetHomᴰ =
    isSetΣ C.isSetHom (λ _ → isProp→isSet (C.isSetHom _ _))

-- The former itself.  `at`/`disp` are exactly `⌜ 𝒯ᶠᴰ ⌝`; the new datum
-- is `cmp`, which reads the context morphism out of the displayed hom.
module _ (𝒞 : CwF ℓC ℓC' ℓC ℓT') where
  open CwFᶠNotation 𝒞

  tyTele : Tele C
  tyTele .at   E p = ∫ᶠ (reindexS p (𝒯ᶠᴰ 𝒞))
  tyTele .disp E p = Fstᶠ (reindexS p (𝒯ᶠᴰ 𝒞))
  tyTele .cmp  E p .F-ob (e , A) = p .F-ob e ⨾ A
  tyTele .cmp  E p .F-hom (f , (h , c)) = h
  tyTele .cmp  E p .F-id f e = Eq.ap (λ z → z .snd .fst) e
  tyTele .cmp  E p .F-seq f g h e = Eq.ap (λ z → z .snd .fst) e

  -- `at` and `disp` really are the `Ext` bridge, on the nose
  tyTele-at : tyTele .at ≡ ⌜ 𝒯ᶠᴰ 𝒞 ⌝ .at
  tyTele-at = refl

  tyTele-disp : tyTele .disp ≡ ⌜ 𝒯ᶠᴰ 𝒞 ⌝ .disp
  tyTele-disp = refl

  -- one step of the telescope recovers context extension on the nose
  tyTele-cmp : ∀ Γ A → tyTele .cmp C SId .F-ob (Γ , A) ≡ Γ ⨾ A
  tyTele-cmp Γ A = refl

  -- ... and two steps recover ITERATED context extension, with the
  -- second type genuinely living over the first extended context.
  tyTele-cmp² : ∀ Γ (A : Ty.p[ Γ ]) (B : Ty.p[ Γ ⨾ A ])
    → (tyTele ·ᵀ tyTele) .cmp C SId .F-ob ((Γ , A) , B) ≡ Γ ⨾ A ⨾ B
  tyTele-cmp² Γ A B = refl

  -- concatenation of CwF telescopes is definitionally unital and
  -- associative, in any association
  tyTele-assoc :
    ((tyTele ·ᵀ tyTele) ·ᵀ tyTele) ≡ (tyTele ·ᵀ (tyTele ·ᵀ tyTele))
  tyTele-assoc = refl

  tyTele-assoc-at :
    ((tyTele ·ᵀ tyTele) ·ᵀ tyTele) .at C SId
    ≡ (tyTele ·ᵀ (tyTele ·ᵀ tyTele)) .at C SId
  tyTele-assoc-at = refl

  tyTele-assoc-cmp :
    ((tyTele ·ᵀ tyTele) ·ᵀ tyTele) .cmp C SId
    ≡ (tyTele ·ᵀ (tyTele ·ᵀ tyTele)) .cmp C SId
  tyTele-assoc-cmp = refl

  tyTele-unitL : (εT ·ᵀ (tyTele ·ᵀ tyTele)) ≡ (tyTele ·ᵀ tyTele)
  tyTele-unitL = refl

  tyTele-unitMid : ((tyTele ·ᵀ εT) ·ᵀ tyTele) ≡ (tyTele ·ᵀ tyTele)
  tyTele-unitMid = refl

  tyTele-unitR : ((tyTele ·ᵀ tyTele) ·ᵀ εT) ≡ (tyTele ·ᵀ tyTele)
  tyTele-unitR = refl
