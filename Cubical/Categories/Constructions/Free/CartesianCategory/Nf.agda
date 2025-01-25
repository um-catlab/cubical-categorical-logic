module Cubical.Categories.Constructions.Free.CartesianCategory.Nf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Relation.Nullary
import Cubical.Data.Sigma as Σ
import Cubical.Data.Equality as Eq
open import Cubical.Data.Empty
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver

private
  variable
    ℓq ℓq' : Level

module _ (Q : ×Quiver ℓq ℓq')
  where
  open Category
  private
    module Q = ×QuiverNotation Q
  module _ (DiscreteOb : Discrete Q.Ob) (DiscreteMor : Discrete Q.Mor) where
    private
      isEqSet : {τ : Q.Ob} {τ' : Q.Ob} → isProp (τ Eq.≡ τ')
      isEqSet p q = sym (Eq.pathToEq-eqToPath _) ∙ congS Eq.pathToEq (Discrete→isSet DiscreteOb _ _ (Eq.eqToPath p) (Eq.eqToPath q)) ∙ Eq.pathToEq-eqToPath _

      isEqSet' : {f : Q.Mor} {g : Q.Mor} → isProp (f Eq.≡ g)
      isEqSet' p q = sym (Eq.pathToEq-eqToPath _) ∙ congS Eq.pathToEq (Discrete→isSet DiscreteMor _ _ (Eq.eqToPath p) (Eq.eqToPath q)) ∙ Eq.pathToEq-eqToPath _

    -- in "classic" natural deduction style, parameterize everything by the context,
    module _ (Γ : Q.Ob) where
      data NormalForm : (τ : Q.Ob) → Type (ℓ-max ℓq ℓq')
      data NeutralTerm : (τ : Q.Ob) → Type (ℓ-max ℓq ℓq')

      data NeutralTerm where
        -- TODO: note about why we need this extra Id
        var : ∀{τ} → (τ Eq.≡ Γ) → NeutralTerm τ
        proj₁ : ∀{τ₁ τ₂} → NeutralTerm (τ₁ × τ₂) → NeutralTerm τ₁
        proj₂ : ∀{τ₁ τ₂} → NeutralTerm (τ₁ × τ₂) → NeutralTerm τ₂
        -- TODO: and here
        symb : ∀{τ} → (f : Q.mor) → (τ Eq.≡ ↑ (Q.cod f)) → NormalForm (Q.dom f) → NeutralTerm τ

      data NormalForm where
        -- shift only at ground types to enforce η-long normal forms
        shift : ∀{x} → NeutralTerm (↑ x) → NormalForm (↑ x)
        pair : ∀{τ₁ τ₂} → NormalForm τ₁ → NormalForm τ₂ → NormalForm (τ₁ × τ₂)
        uniq : NormalForm ⊤

      codeNeutralTerm : ∀{τ} → NeutralTerm τ → NeutralTerm τ → Type (ℓ-max ℓq ℓq')
      codeNormalForm : ∀{τ} → NormalForm τ → NormalForm τ → Type (ℓ-max ℓq ℓq')

      -- trivial code for NeutralTerms
      codeNeutralTerm (var p) (var q) = Lift {j = ℓq'} (p ≡ q)
      codeNeutralTerm (var _) (proj₁ _) = ⊥*
      codeNeutralTerm (var _) (proj₂ _) = ⊥*
      codeNeutralTerm (var _) (symb _ _ _) = ⊥*
      codeNeutralTerm (proj₁ _) (var _) = ⊥*
      codeNeutralTerm (proj₁ {τ₂ = τ₂} x) (proj₁ {τ₂ = τ₃} y) =
        Σ (τ₂ Eq.≡ τ₃) λ p  → codeNeutralTerm (Eq.transport (λ τ → NeutralTerm (_ × τ)) p x) y
      codeNeutralTerm (proj₁ _) (proj₂ _) = ⊥*
      codeNeutralTerm (proj₁ _) (symb _ _ _) = ⊥*
      codeNeutralTerm (proj₂ _) (var _) = ⊥*
      codeNeutralTerm (proj₂ _) (proj₁ _) = ⊥*
      codeNeutralTerm (proj₂ {τ₁ = τ₁} x) (proj₂ {τ₁ = τ₂} y) =
        Σ (τ₁ Eq.≡ τ₂) (λ p → codeNeutralTerm (Eq.transport (λ τ → NeutralTerm (τ × _)) p x) y)
      codeNeutralTerm (proj₂ _) (symb _ _ _) = ⊥*
      codeNeutralTerm (symb _ _ _) (var _) = ⊥*
      codeNeutralTerm (symb _ _ _) (proj₁ _) = ⊥*
      codeNeutralTerm (symb _ _ _) (proj₂ _) = ⊥*
      codeNeutralTerm (symb f p x) (symb g q y) =
        Σ (f Eq.≡ g) (λ r → (Eq.transport (λ h → _ Eq.≡ ↑ Q.cod h) r p ≡ q) Σ.× (codeNormalForm (Eq.transport (λ h → NormalForm (Q.dom h)) r x) y))

      codeNormalForm (shift x) (shift y) = codeNeutralTerm x y
      codeNormalForm (pair w x) (pair y z) = (codeNormalForm w y) Σ.× (codeNormalForm x z)
      codeNormalForm uniq uniq = Unit*

      reflCodeNeutralTerm : ∀{τ} → (x : NeutralTerm τ) → codeNeutralTerm x x
      reflCodeNormalForm : ∀{τ} → (x : NormalForm τ) → codeNormalForm x x

      reflCodeNeutralTerm (var p) = lift refl
      reflCodeNeutralTerm (proj₁ x) = Eq.refl , reflCodeNeutralTerm x
      reflCodeNeutralTerm (proj₂ x) = Eq.refl , reflCodeNeutralTerm x
      reflCodeNeutralTerm (symb f p x) = Eq.refl , refl , reflCodeNormalForm x

      reflCodeNormalForm (shift x) = reflCodeNeutralTerm x
      reflCodeNormalForm (pair x y) = reflCodeNormalForm x , reflCodeNormalForm y
      reflCodeNormalForm uniq = tt*

      encodeNeutralTerm : ∀{τ} → (x y : NeutralTerm τ) → x ≡ y → codeNeutralTerm x y
      encodeNeutralTerm x y p = subst (codeNeutralTerm x) p (reflCodeNeutralTerm x)

      encodeNormalForm : ∀{τ} → (x y : NormalForm τ) → x ≡ y → codeNormalForm x y
      encodeNormalForm x y p = subst (codeNormalForm x) p (reflCodeNormalForm x)

      decodeNeutralTerm : ∀{τ} → (x y : NeutralTerm τ) → codeNeutralTerm x y → x ≡ y
      decodeNormalForm : ∀{τ} → (x y : NormalForm τ) → codeNormalForm x y → x ≡ y

      decodeNeutralTerm (var p) (var q) (lift r) = congS var r
      decodeNeutralTerm (proj₁ x) (proj₁ y) (Eq.refl , q) = congS proj₁ $ decodeNeutralTerm _ _ q
      decodeNeutralTerm (proj₂ x) (proj₂ y) (Eq.refl , q) = congS proj₂ $ decodeNeutralTerm _ _ q
      decodeNeutralTerm (symb f p x) (symb g q y) (Eq.refl , r , s) = cong₂ (symb f) r (decodeNormalForm x y s)

      decodeNormalForm (shift x) (shift y) p = congS shift $ decodeNeutralTerm x y p
      decodeNormalForm (pair w x) (pair y z) p = cong₂ pair (decodeNormalForm w y (p .fst)) (decodeNormalForm x z (p .snd))
      decodeNormalForm uniq uniq _ = refl

      DiscreteNeutralTerm : ∀{τ} → Discrete (NeutralTerm τ)
      DiscreteNormalForm : ∀{τ} → Discrete (NormalForm τ)

      DiscreteNeutralTerm (var p) (var q) = cong-var-Dec (yes (isEqSet p q))
        where
        inj-var : ∀{τ : Q.Ob}
          {p q : τ Eq.≡ Γ} →
          var p ≡ var q → p ≡ q
        inj-var r = encodeNeutralTerm _ _ r .lower

        cong-var-Dec : ∀{τ : Q.Ob}
          {p q : τ Eq.≡ Γ} →
          Dec (p ≡ q) →
          Dec (var p ≡ var q)
        cong-var-Dec (yes p) = yes $ congS var p
        cong-var-Dec (no ¬p) = no $ ¬p ∘S inj-var

      DiscreteNeutralTerm (var x) (proj₁ y) = no $ λ p → subst (λ {(var _) → Unit ; _ → ⊥}) p tt
      DiscreteNeutralTerm (var x) (proj₂ y) = no $ λ p → subst (λ {(var _) → Unit ; _ → ⊥}) p tt
      DiscreteNeutralTerm (var x) (symb f x₁ x₂) = no $ λ p → subst (λ {(var _) → Unit ; _ → ⊥}) p tt
      DiscreteNeutralTerm (proj₁ x) (var x₁) = no $ λ p → subst (λ {(proj₁ _) → Unit ; _ → ⊥}) p tt
      DiscreteNeutralTerm (proj₁ x) (proj₁ y) = cong-proj₁-Dec (subst Dec Eq.PathPathEq (DiscreteOb _ _)) x y
        where
        inj-proj₁ : ∀{τ₁ τ₂ τ₃}
          {x : NeutralTerm (τ₁ × τ₂)} {y : NeutralTerm (τ₁ × τ₃)} →
          proj₁ x ≡ proj₁ y →
          Σ (τ₂ Eq.≡ τ₃) λ p → Eq.transport (λ τ → NeutralTerm (_ × τ)) p x ≡ y
        inj-proj₁ p = encodeNeutralTerm _ _ p .fst , (decodeNeutralTerm _ _ $ encodeNeutralTerm _ _ p .snd)

        cong-proj₁-Dec' : ∀{τ₁ τ₂} →
          (x : NeutralTerm (τ₁ × τ₂)) (y : NeutralTerm (τ₁ × τ₂)) →
          Dec (x ≡ y) →
          Dec (proj₁ x ≡ proj₁ y)
        cong-proj₁-Dec' x y (yes p) = yes $ congS proj₁ p
        cong-proj₁-Dec' x y (no ¬p) = no $ λ q → ¬p ((congS (λ z → Eq.transport (λ τ → NeutralTerm (_ × τ)) z x) (isEqSet _ _ )) ∙ inj-proj₁ q .snd)

        cong-proj₁-Dec : ∀{τ₁ τ₂ τ₃} →
          (p : Dec (τ₂ Eq.≡ τ₃)) →
          (x : NeutralTerm (τ₁ × τ₂))
          (y : NeutralTerm (τ₁ × τ₃)) →
          Dec (proj₁ x ≡ proj₁ y)
        cong-proj₁-Dec (yes Eq.refl) x y = cong-proj₁-Dec' x y (DiscreteNeutralTerm x y)
        cong-proj₁-Dec (no ¬p) _ _ = no $ λ q → ¬p $ inj-proj₁ q .fst

      DiscreteNeutralTerm (proj₁ x) (proj₂ y) = no $ λ p → subst (λ {(proj₁ _) → Unit ; _ → ⊥}) p tt
      DiscreteNeutralTerm (proj₁ x) (symb f x₁ x₂) = no $ λ p → subst (λ {(proj₁ _) → Unit ; _ → ⊥}) p tt
      DiscreteNeutralTerm (proj₂ x) (var x₁) = no $ λ p → subst (λ {(proj₂ _) → Unit ; _ → ⊥}) p tt
      DiscreteNeutralTerm (proj₂ x) (proj₁ y) = no $ λ p → subst (λ {(proj₂ _) → Unit ; _ → ⊥}) p tt
      DiscreteNeutralTerm (proj₂ x) (proj₂ y) = cong-proj₂-Dec (subst Dec Eq.PathPathEq (DiscreteOb _ _)) x y
        where
        inj-proj₂ : ∀{τ₁ τ₂ τ₃}
          {x : NeutralTerm (τ₁ × τ₃)} {y : NeutralTerm (τ₂ × τ₃)} →
          proj₂ x ≡ proj₂ y →
          Σ (τ₁ Eq.≡ τ₂) λ p → Eq.transport (λ τ → NeutralTerm (τ × _)) p x ≡ y
        inj-proj₂ p = encodeNeutralTerm _ _ p .fst , (decodeNeutralTerm _ _ $ encodeNeutralTerm _ _ p .snd)

        cong-proj₂-Dec' : ∀{τ₁ τ₂} →
          (x : NeutralTerm (τ₁ × τ₂)) (y : NeutralTerm (τ₁ × τ₂)) →
          Dec (x ≡ y) →
          Dec (proj₂ x ≡ proj₂ y)
        cong-proj₂-Dec' x y (yes p) = yes $ congS proj₂ p
        cong-proj₂-Dec' x y (no ¬p) = no $ λ q → ¬p ((congS (λ z → Eq.transport (λ τ → NeutralTerm (τ × _)) z x) (isEqSet _ _ )) ∙ inj-proj₂ q .snd)

        cong-proj₂-Dec : ∀{τ₁ τ₂ τ₃} →
          (p : Dec (τ₁ Eq.≡ τ₂)) →
          (x : NeutralTerm (τ₁ × τ₃))
          (y : NeutralTerm (τ₂ × τ₃)) →
          Dec (proj₂ x ≡ proj₂ y)
        cong-proj₂-Dec (yes Eq.refl) x y = cong-proj₂-Dec' x y (DiscreteNeutralTerm x y)
        cong-proj₂-Dec (no ¬p) _ _ = no $ λ q → ¬p $ inj-proj₂ q .fst

      DiscreteNeutralTerm (proj₂ x) (symb f x₁ x₂) = no $ λ p → subst (λ {(proj₂ _) → Unit ; _ → ⊥}) p tt
      DiscreteNeutralTerm (symb f x x₁) (var x₂) = no $ λ p → subst (λ {(symb _ _ _) → Unit ; _ → ⊥}) p tt
      DiscreteNeutralTerm (symb f x x₁) (proj₁ y) = no $ λ p → subst (λ {(symb _ _ _) → Unit ; _ → ⊥}) p tt
      DiscreteNeutralTerm (symb f x x₁) (proj₂ y) = no $ λ p → subst (λ {(symb _ _ _) → Unit ; _ → ⊥}) p tt
      DiscreteNeutralTerm (symb f p x) (symb g q y) = cong-symb-Dec _ _ (subst Dec Eq.PathPathEq (DiscreteMor _ _)) _ _ _ _
        where
        inj-symb : ∀{τ f g p q x y} →
          symb f p x ≡ symb g q y →
          Σ (f Eq.≡ g) λ r → (Eq.transport (λ h → τ Eq.≡ ↑ Q.cod h) r p ≡ q) Σ.× (Eq.transport (λ h → NormalForm (Q.dom h)) r x ≡ y)
        inj-symb u = encodeNeutralTerm _ _ u .fst , encodeNeutralTerm _ _ u .snd .fst , decodeNormalForm _ _ (encodeNeutralTerm _ _ u .snd .snd)

        cong-symb-Dec' : ∀{τ} {f : Q.mor} {p q : τ Eq.≡ (↑ Q.cod f)} →
          p ≡ q →
          (x y : NormalForm (Q.dom f)) →
          Dec (x ≡ y) →
          Dec (symb f p x ≡ symb f q y)
        cong-symb-Dec' r x y (yes p) = yes $ cong₃ symb refl r p
        cong-symb-Dec' r x y (no ¬p) = no $ λ s → ¬p (congS (λ z → Eq.transport (λ h → NormalForm (Q.dom h)) z x) (isEqSet' _ _)  ∙ inj-symb s .snd .snd)

        cong-symb-Dec : ∀{τ}
          (f g : Q.mor) →
          Dec (f Eq.≡ g) →
          (p : τ Eq.≡ (↑ Q.cod f)) (q : τ Eq.≡ (↑ Q.cod g)) →
          (x : NormalForm (Q.dom f)) (y : NormalForm (Q.dom g)) →
          Dec (symb f p x ≡ symb g q y)
        cong-symb-Dec f g (yes Eq.refl) p q x y = cong-symb-Dec' (isEqSet p q) x y (DiscreteNormalForm x y)
        cong-symb-Dec f g (no ¬p) p q x y = no (λ r → ¬p $ inj-symb r .fst)

      DiscreteNormalForm (shift x) (shift y) = cong-shift-Dec (DiscreteNeutralTerm x y)
        where
        inj-shift : ∀{x} {y z : NeutralTerm (↑ x)} → shift y ≡ shift z → y ≡ z
        inj-shift = decodeNeutralTerm _ _ ∘S encodeNormalForm _ _

        cong-shift-Dec : ∀{x} → {x y : NeutralTerm (↑ x)} → Dec (x ≡ y) →  Dec (shift x ≡ shift y)
        cong-shift-Dec (yes p) = yes $ congS shift p
        cong-shift-Dec (no ¬p) = no $ λ q → ¬p $ inj-shift q

      DiscreteNormalForm (pair w x) (pair y z) = cong-pair-Dec (DiscreteNormalForm w y) (DiscreteNormalForm x z)
        where
        inj-pair : ∀{τ₁ τ₂} →
          {w y : NormalForm τ₁} {x z : NormalForm τ₂} →
          pair w x ≡ pair y z → (w ≡ y) Σ.× (x ≡ z)
        inj-pair p = Σ.map-× (decodeNormalForm _ _) (decodeNormalForm _ _) (encodeNormalForm _ _ p)

        cong-pair-Dec : ∀{τ₁ τ₂} →
          {w y : NormalForm τ₁} {x z : NormalForm τ₂} →
          Dec (w ≡ y) →
          Dec (x ≡ z) →
          Dec (pair w x ≡ pair y z)
        cong-pair-Dec (yes p) (yes q) = yes $ cong₂ pair p q
        cong-pair-Dec (no ¬p) _ = no $ λ q → ¬p $ inj-pair q .fst
        cong-pair-Dec _ (no ¬p) = no $ λ q → ¬p $ inj-pair q .snd

      DiscreteNormalForm uniq uniq = yes refl

      -- all that, just for this
      isSetNormalForm : ∀{τ} → isSet (NormalForm τ)
      isSetNormalForm = Discrete→isSet DiscreteNormalForm

    -- this is the "type directed" shift
    SHIFT : ∀{Γ τ} → NeutralTerm Γ τ → NormalForm Γ τ
    SHIFT {τ = ↑ _} ne = shift ne
    SHIFT {τ = τ₁ × τ₂} ne = pair (SHIFT $ proj₁ ne) (SHIFT $ proj₂ ne)
    SHIFT {τ = ⊤} _ = uniq
    -- there's also a constructor-directed (syntax directed?) shift, but it doesn't obviously have any nice properties?

    ID : ∀{τ} → NormalForm τ τ
    ID = SHIFT (var Eq.refl)

    PROJ₁ : ∀{Γ τ₁ τ₂} → NormalForm Γ (τ₁ × τ₂) → NormalForm Γ τ₁
    PROJ₁ (pair n₁ _) = n₁

    PROJ₂ : ∀{Γ τ₁ τ₂} → NormalForm Γ (τ₁ × τ₂) → NormalForm Γ τ₂
    PROJ₂ (pair _ n₂) = n₂

    -- substitution, in composition order (*not* "diagramatic" order)
    Nf/Nf : ∀{Γ Δ τ} → NormalForm Δ τ → NormalForm Γ Δ → NormalForm Γ τ
    Ne/Nf : ∀{Γ Δ τ} → NeutralTerm Δ τ → NormalForm Γ Δ → NormalForm Γ τ
    Nf/Ne : ∀{Γ Δ τ} → NormalForm Δ τ → NeutralTerm Γ Δ → NormalForm Γ τ
    Ne/Ne : ∀{Γ Δ τ} → NeutralTerm Δ τ → NeutralTerm Γ Δ → NeutralTerm Γ τ

    Nf/Nf (shift ne) nf = Ne/Nf ne nf
    Nf/Nf (pair nf₁ nf₂) nf₃ = pair (Nf/Nf nf₁ nf₃) (Nf/Nf nf₂ nf₃)
    Nf/Nf uniq nf₂ = uniq

    Ne/Nf (var Eq.refl) = idfun _ --subst (NormalForm _) (sym p) --idfun _
    Ne/Nf (proj₁ ne) nf = PROJ₁ $ Ne/Nf ne nf
    Ne/Nf (proj₂ ne) nf = PROJ₂ $ Ne/Nf ne nf
    Ne/Nf (symb f Eq.refl nf₁) nf₂ = shift $ symb f Eq.refl $ Nf/Nf nf₁ nf₂

    Nf/Ne (shift ne₁) ne₂ = shift $ Ne/Ne ne₁ ne₂
    Nf/Ne (pair nf₁ nf₂) ne = pair (Nf/Ne nf₁ ne) (Nf/Ne nf₂ ne)
    Nf/Ne uniq _ = uniq

    Ne/Ne (var Eq.refl) = idfun _
    Ne/Ne (proj₁ ne₁) ne₂ = proj₁ $ Ne/Ne ne₁ ne₂
    Ne/Ne (proj₂ ne₁) ne₂ = proj₂ $ Ne/Ne ne₁ ne₂
    Ne/Ne (symb f p nf) ne = symb f p $ Nf/Ne nf ne

    IDL : ∀{Γ τ} (n : NormalForm Γ τ) → Nf/Nf n ID ≡ n
    IDL-Ne : ∀{Γ τ} (n : NeutralTerm Γ τ) → Ne/Nf n ID ≡ SHIFT n

    IDL (shift ne) = IDL-Ne ne
    IDL (pair nf₁ nf₂) = cong₂ pair (IDL nf₁) (IDL nf₂)
    IDL uniq = refl

    IDL-Ne (var Eq.refl) = refl
    IDL-Ne (proj₁ ne) = congS PROJ₁ $ IDL-Ne ne
    IDL-Ne (proj₂ ne) = congS PROJ₂ $ IDL-Ne ne
    IDL-Ne (symb f Eq.refl nf) = congS (shift ∘S symb f Eq.refl) $ IDL nf

    _∘proj₁ : ∀{Γ Δ τ} → NeutralTerm Γ τ → NeutralTerm (Γ × Δ) τ
    _∘PROJ₁ : ∀{Γ Δ τ} → NormalForm Γ τ → NormalForm (Γ × Δ) τ

    (var Eq.refl) ∘proj₁ = proj₁ (var Eq.refl)
    (proj₁ ne) ∘proj₁ = proj₁ $ ne ∘proj₁
    (proj₂ ne) ∘proj₁ = proj₂ $ ne ∘proj₁
    (symb f p nf) ∘proj₁ = symb f p $ nf ∘PROJ₁

    (shift ne) ∘PROJ₁ = shift $ ne ∘proj₁
    (pair nf₁ nf₂) ∘PROJ₁ = pair (nf₁ ∘PROJ₁) (nf₂ ∘PROJ₁)
    uniq ∘PROJ₁ = uniq

    _∘proj₂ : ∀{Γ Δ τ} → NeutralTerm Δ τ → NeutralTerm (Γ × Δ) τ
    _∘PROJ₂ : ∀{Γ Δ τ} → NormalForm Δ τ → NormalForm (Γ × Δ) τ

    (var Eq.refl) ∘proj₂ = proj₂ (var Eq.refl)
    (proj₁ ne) ∘proj₂ = proj₁ $ ne ∘proj₂
    (proj₂ ne) ∘proj₂ = proj₂ $ ne ∘proj₂
    (symb f p nf) ∘proj₂ = symb f p $ nf ∘PROJ₂

    (shift ne) ∘PROJ₂ = shift $ ne ∘proj₂
    (pair nf₁ nf₂) ∘PROJ₂ = pair (nf₁ ∘PROJ₂) (nf₂ ∘PROJ₂)
    uniq ∘PROJ₂ = uniq

    -- these types of proofs should somehow be automatic...
    SHIFT-∘proj₁ : ∀{Γ Δ τ} {ne : NeutralTerm Γ τ} → SHIFT {Γ = Γ × Δ} (ne ∘proj₁) ≡ (SHIFT ne) ∘PROJ₁
    SHIFT-∘proj₁ {τ = ↑ _} = refl
    SHIFT-∘proj₁ {τ = τ₁ × τ₂} = cong₂ pair SHIFT-∘proj₁ SHIFT-∘proj₁
    SHIFT-∘proj₁ {τ = ⊤} = refl

    SHIFT-∘proj₂ : ∀{Γ Δ τ} {ne : NeutralTerm Δ τ} → SHIFT {Γ = Γ × Δ} (ne ∘proj₂) ≡ (SHIFT ne) ∘PROJ₂
    SHIFT-∘proj₂ {τ = ↑ _} = refl
    SHIFT-∘proj₂ {τ = τ₁ × τ₂} = cong₂ pair SHIFT-∘proj₂ SHIFT-∘proj₂
    SHIFT-∘proj₂ {τ = ⊤} = refl

    -- ast of pairs with "pointed" NormalForm
    data Embedded Γ τ (n : NormalForm Γ τ) : Q.Ob → Type (ℓ-max ℓq ℓq') where
      root : Embedded Γ τ n τ
      left : ∀{τ' τ''} → Embedded Γ τ n τ' → NormalForm Γ τ'' → Embedded Γ τ n (τ' × τ'')
      right : ∀{τ' τ''} → NormalForm Γ τ' → Embedded Γ τ n τ'' → Embedded Γ τ n (τ' × τ'')

    -- "project" the point
    ⟨_⟩ : ∀{Γ τ n Δ} →
      Embedded Γ τ n Δ → NeutralTerm Δ τ
    ⟨ root ⟩ = var Eq.refl
    ⟨ left e _ ⟩ = ⟨ e ⟩ ∘proj₁
    ⟨ right _ e ⟩ = ⟨ e ⟩ ∘proj₂

    -- "forget" the point
    ∣_∣ : ∀{Γ τ n Δ} →
      Embedded Γ τ n Δ → NormalForm Γ Δ
    ∣_∣ {n = n} root = n
    ∣_∣ (left e nf) = pair ∣ e ∣ nf
    ∣_∣ (right nf e) = pair nf ∣ e ∣

    β₁-Ne/Nf : ∀{Γ τ₁ τ₂ τ₃} →
      (ne : NeutralTerm τ₁ τ₃) →
      (nf₁ : NormalForm Γ τ₁) →
      (nf₂ : NormalForm Γ τ₂) →
      Ne/Nf (ne ∘proj₁) (pair nf₁ nf₂) ≡ Ne/Nf ne nf₁
    β₁-Nf/Nf : ∀{Γ τ₁ τ₂ τ₃} →
      (nf₃ : NormalForm τ₁ τ₃) →
      (nf₁ : NormalForm Γ τ₁) →
      (nf₂ : NormalForm Γ τ₂) →
      Nf/Nf (nf₃ ∘PROJ₁) (pair nf₁ nf₂) ≡ Nf/Nf nf₃ nf₁

    β₁-Ne/Nf (var Eq.refl) _ _ = refl
    β₁-Ne/Nf (proj₁ ne) _ _ = congS PROJ₁ $ β₁-Ne/Nf ne _ _
    β₁-Ne/Nf (proj₂ ne) _ _ = congS PROJ₂ $ β₁-Ne/Nf ne _ _
    β₁-Ne/Nf (symb f Eq.refl nf₁) _ _ = congS (shift ∘S symb f Eq.refl) $ β₁-Nf/Nf nf₁ _ _

    β₁-Nf/Nf (shift ne) = β₁-Ne/Nf ne
    β₁-Nf/Nf (pair nf₁ nf₂) _ _ = cong₂ pair (β₁-Nf/Nf nf₁ _ _) (β₁-Nf/Nf nf₂ _ _)
    β₁-Nf/Nf uniq nf₁ nf₂ = refl

    β₂-Ne/Nf : ∀{Γ τ₁ τ₂ τ₃} →
      (ne : NeutralTerm τ₂ τ₃) →
      (nf₁ : NormalForm Γ τ₁) →
      (nf₂ : NormalForm Γ τ₂) →
      Ne/Nf (ne ∘proj₂) (pair nf₁ nf₂) ≡ Ne/Nf ne nf₂
    β₂-Nf/Nf : ∀{Γ τ₁ τ₂ τ₃} →
      (nf₃ : NormalForm τ₂ τ₃) →
      (nf₁ : NormalForm Γ τ₁) →
      (nf₂ : NormalForm Γ τ₂) →
      Nf/Nf (nf₃ ∘PROJ₂) (pair nf₁ nf₂) ≡ Nf/Nf nf₃ nf₂
    β₂-Ne/Nf (var Eq.refl) _ _ = refl
    β₂-Ne/Nf (proj₁ ne) _ _ = congS PROJ₁ $ β₂-Ne/Nf ne _ _
    β₂-Ne/Nf (proj₂ ne) _ _ = congS PROJ₂ $ β₂-Ne/Nf ne _ _
    β₂-Ne/Nf (symb f Eq.refl nf₁) _ _ = congS (shift ∘S symb f Eq.refl) $ β₂-Nf/Nf nf₁ _ _

    β₂-Nf/Nf (shift ne) = β₂-Ne/Nf ne
    β₂-Nf/Nf (pair nf₁ nf₂) _ _ = cong₂ pair (β₂-Nf/Nf nf₁ _ _) (β₂-Nf/Nf nf₂ _ _)
    β₂-Nf/Nf uniq _ _ = refl

    -- this is the "big" inductive lemma for IDR
    IDR-lem : ∀{Γ τ Δ} →
      (n : NormalForm Γ τ)
      (ast : Embedded Γ τ n Δ) →
      Nf/Nf (SHIFT ⟨ ast ⟩) ∣ ast ∣ ≡ n
    IDR-lem {τ = ↑ x} _ root = refl
    IDR-lem {τ = ↑ x} n (left ast nf) = β₁-Ne/Nf ⟨ ast ⟩ ∣ ast ∣ nf ∙  IDR-lem n ast
    IDR-lem {τ = ↑ x} n (right nf ast) = β₂-Ne/Nf ⟨ ast ⟩ nf ∣ ast ∣ ∙ IDR-lem n ast
    IDR-lem {τ = τ₁ × τ₂} (pair n₁ n₂) root = cong₂ pair (IDR-lem n₁ $ left root n₂) (IDR-lem n₂ $ right n₁ root)
    IDR-lem {τ = τ₁ × τ₂} (pair n₁ n₂) (left ast nf) = cong₂ pair
      (congS (λ x → Nf/Nf x $ pair ∣ ast ∣ nf) (SHIFT-∘proj₁) ∙ β₁-Nf/Nf (SHIFT _) ∣ ast ∣ nf)
      (congS (λ x → Nf/Nf x $ pair ∣ ast ∣ nf) (SHIFT-∘proj₁) ∙ β₁-Nf/Nf (SHIFT _) ∣ ast ∣ nf)
      ∙ IDR-lem (pair n₁ n₂) ast
    IDR-lem {τ = τ₁ × τ₂} (pair n₁ n₂) (right nf ast) = cong₂ pair
      (congS (λ x → Nf/Nf x $ pair nf ∣ ast ∣) (SHIFT-∘proj₂) ∙ β₂-Nf/Nf (SHIFT _) nf ∣ ast ∣)
      (congS (λ x → Nf/Nf x $ pair nf ∣ ast ∣) (SHIFT-∘proj₂) ∙ β₂-Nf/Nf (SHIFT _) nf ∣ ast ∣)
      ∙ IDR-lem (pair n₁ n₂) ast
    IDR-lem {τ = ⊤} uniq _ = refl

    IDR : ∀{Γ τ} (n : NormalForm Γ τ) → Nf/Nf ID n ≡ n
    IDR n = IDR-lem n root

    Nf/Nf-PROJ₁ : ∀{Γ Δ τ₁ τ₂} (n₁ : NormalForm Δ (τ₁ × τ₂)) (n₂ : NormalForm Γ Δ) →
      Nf/Nf (PROJ₁ n₁) n₂ ≡ PROJ₁ (Nf/Nf n₁ n₂)
    Nf/Nf-PROJ₁ (pair _ _) _ = refl

    Nf/Nf-PROJ₂ : ∀{Γ Δ τ₁ τ₂} (n₁ : NormalForm Δ (τ₁ × τ₂)) (n₂ : NormalForm Γ Δ) →
      Nf/Nf (PROJ₂ n₁) n₂ ≡ PROJ₂ (Nf/Nf n₁ n₂)
    Nf/Nf-PROJ₂ (pair _ _) _ = refl

    ASSOC-Nf/Nf/Nf : ∀{Γ Δ Θ τ} →
      (n₃ : NormalForm Θ τ)
      (n₂ : NormalForm Δ Θ)
      (n₁ : NormalForm Γ Δ) →
      Nf/Nf n₃ (Nf/Nf n₂ n₁) ≡ Nf/Nf (Nf/Nf n₃ n₂) n₁
    ASSOC-Ne/Nf/Nf : ∀{Γ Δ Θ τ} →
      (n₃ : NeutralTerm Θ τ)
      (n₂ : NormalForm Δ Θ)
      (n₁ : NormalForm Γ Δ) →
      Ne/Nf n₃ (Nf/Nf n₂ n₁) ≡ Nf/Nf (Ne/Nf n₃ n₂) n₁

    ASSOC-Nf/Nf/Nf (shift ne) = ASSOC-Ne/Nf/Nf ne
    ASSOC-Nf/Nf/Nf (pair n₃ n₄) n₂ n₁ = cong₂ pair (ASSOC-Nf/Nf/Nf n₃ n₂ n₁) (ASSOC-Nf/Nf/Nf n₄ n₂ n₁)
    ASSOC-Nf/Nf/Nf uniq _ _ = refl

    ASSOC-Ne/Nf/Nf (var Eq.refl) _ _ = refl
    ASSOC-Ne/Nf/Nf (proj₁ n₃) n₂ n₁ = congS PROJ₁ (ASSOC-Ne/Nf/Nf n₃ n₂ n₁) ∙ sym (Nf/Nf-PROJ₁ (Ne/Nf n₃ n₂) n₁)
    ASSOC-Ne/Nf/Nf (proj₂ n₃) n₂ n₁ = congS PROJ₂ (ASSOC-Ne/Nf/Nf n₃ n₂ n₁) ∙ sym (Nf/Nf-PROJ₂ (Ne/Nf n₃ n₂) n₁)
    ASSOC-Ne/Nf/Nf (symb f Eq.refl nf) n₂ n₁ = congS (shift ∘S symb f Eq.refl) $ ASSOC-Nf/Nf/Nf nf n₂ n₁

    |Nf| : Category _ _
    |Nf| .ob = Q.Ob
    |Nf| .Hom[_,_] Γ τ = NormalForm Γ τ
    |Nf| .id = ID
    |Nf| ._⋆_ m n = Nf/Nf n m
    |Nf| .⋆IdL = IDL
    |Nf| .⋆IdR = IDR
    |Nf| .⋆Assoc n₁ n₂ n₃ = ASSOC-Nf/Nf/Nf n₃ n₂ n₁
    |Nf| .isSetHom = isSetNormalForm _

    Nf : CartesianCategory _ _
    Nf .fst = |Nf|
    Nf .snd .fst = ⊤ , (λ Γ → uniq , λ {uniq → refl})
    Nf .snd .snd Γ Δ = record { binProdOb = Γ × Δ
                              ; binProdPr₁ = PROJ₁ ID
                              ; binProdPr₂ = PROJ₂ ID
                              ; univProp = λ f g → Σ.uniqueExists
                                (pair f g)
                                ((IDR-lem f $ left root g) , (IDR-lem g $ right f root))
                                (λ h → isProp× (isSetNormalForm _ _ _) (isSetNormalForm _ _ _))
                                λ {(pair f' g') p → cong₂ pair (sym (p .fst) ∙ (IDR-lem f' $ left root g')) (sym (p .snd) ∙ (IDR-lem g' $ right f' root)) }}
    open import Cubical.Categories.Limits.Cartesian.Functor
    open import Cubical.Categories.Constructions.Free.CartesianCategory.Base
    |FreeCC| = |FreeCartesianCategory| Q
    R : CartesianFunctor |Nf| |FreeCC|
    R = {!!}
