{-

  The eliminator of the syntax into DISPLAYED MODELS.

  Multicategory.Syntax.ElimProp eliminates into prop-valued motives,
  which is cheap — every path constructor is discharged by isProp — but
  a prop-valued motive cannot carry data, which is exactly why the
  normalization theorem proved with it could only say a normal form
  EXISTS.  For the normal form itself the motive must be set-valued,
  and then each equation of the theory has to be met in the target.

  The point of this file is that they are met by FIELDS, once: a
  displayed model is a displayed cartesian multicategory over the
  syntax — whose three clone laws a reindexing supplies generically —
  together with displayed structure for each former and a displayed
  law for each remaining path constructor.  The syntax is cartesian
  closed (⊤', _×'_, _⇒'_ and nothing else), so that is six point
  fields and eleven law fields; elim discharges all fourteen path
  constructors against them, and no induction is re-run at a use site.

  The object part S-ob is a field rather than a parameter so that the
  displayed context of a binder is `λ i → S-ob ((Γ ,, A) i)` on the
  nose: ⊎ has no η, so a Sum.elim there would force a transport in
  every binder case.

-}
module Multicategory.Elim where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sum as Sum hiding (elim; rec)
open import Cubical.Data.Unit

open import Multicategory.Cartesian
open import Multicategory.Displayed
open import Multicategory.Multifunctor
open import Multicategory.Syntax

private
  variable
    ℓᴰ ℓᴰ' : Level

record DisplayedModel {ℓᴰ ℓᴰ' : Level}
    (Mᴰ : CartesianMulticategoryᴰ Syn ℓᴰ ℓᴰ')
    : Type (ℓ-suc (ℓ-max (ℓ-suc ℓ-zero) (ℓ-max ℓᴰ ℓᴰ'))) where
  open CartesianMulticategoryᴰ Mᴰ public

  field
    S-ob : (A : Ty) → obᴰ A

  -- the displayed hom over t, at the objects S-ob picks out
  ⟦_⟧ᴰ : {I : Type} {Γ : Ctxt I} {A : Ty} → Tm I Γ A → Type ℓᴰ'
  ⟦_⟧ᴰ {I} {Γ} {A} t = MHomᴰ[ t ][ (λ i → S-ob (Γ i)) , S-ob A ]

  field
    ttᴰ : {I : Type} {Γ : Ctxt I} → ⟦ tt' {I} {Γ} ⟧ᴰ
    pairᴰ : {I : Type} {Γ : Ctxt I} {A B : Ty}
      {a : Tm I Γ A} {b : Tm I Γ B} → ⟦ a ⟧ᴰ → ⟦ b ⟧ᴰ → ⟦ pair a b ⟧ᴰ
    fstᴰ : {I : Type} {Γ : Ctxt I} {A B : Ty} {t : Tm I Γ (A ×' B)}
      → ⟦ t ⟧ᴰ → ⟦ fst' t ⟧ᴰ
    sndᴰ : {I : Type} {Γ : Ctxt I} {A B : Ty} {t : Tm I Γ (A ×' B)}
      → ⟦ t ⟧ᴰ → ⟦ snd' t ⟧ᴰ
    lamᴰ : {I : Type} {Γ : Ctxt I} {A B : Ty}
      {t : Tm (I ⊎ Unit) (Γ ,, A) B} → ⟦ t ⟧ᴰ → ⟦ lam t ⟧ᴰ
    appᴰ : {I : Type} {Γ : Ctxt I} {A B : Ty}
      {t : Tm I Γ (A ⇒' B)} {u : Tm I Γ A} → ⟦ t ⟧ᴰ → ⟦ u ⟧ᴰ
      → ⟦ app t u ⟧ᴰ

  -- the displayed laws.  The three clone laws are already ⋆Varᴰ /
  -- ⋆Idᴰ / ⋆Assocᴰ of Mᴰ; these are the eleven that remain.
  --
  -- THE FORDED LAWS CARRY DISPLAYED FORDS.  A base rule like ⇒β does
  -- not mention the extended environment `Sum.elim var (λ _ → u)`; it
  -- takes an arbitrary `f` together with `fl`/`fr` saying what it is
  -- pointwise.  The displayed rule must then take an arbitrary `fᴰ`
  -- over `f` TOGETHER WITH displayed fords `flᴰ`/`frᴰ` over `fl`/`fr`
  -- — otherwise it demands that `tᴰ ⋆ᴰ fᴰ` be independent of which
  -- `fᴰ` lies over `f`, which is true only when ⟦_⟧ᴰ is prop-valued.
  -- That is exactly what blocks a proof-relevant displayed model, and
  -- it costs nothing: `elim` has `λ k → elim (fl i k)` for free, and
  -- Multicategory.Model's standard model already uses precisely these
  -- witnesses in the shape `cong (λ s → ⟦ s ⟧ γ) (fl i)`.
  field
    ⊤ηᴰ : {I : Type} {Γ : Ctxt I} {t : Tm I Γ ⊤'} (tᴰ : ⟦ t ⟧ᴰ)
      → tᴰ ≡[ ⊤η t ] ttᴰ
    pair-natᴰ : {I J : Type} {Γ : Ctxt I} {Δ : Ctxt J} {A B : Ty}
      {a : Tm I Γ A} {b : Tm I Γ B} {f : (i : I) → Tm J Δ (Γ i)}
      (aᴰ : ⟦ a ⟧ᴰ) (bᴰ : ⟦ b ⟧ᴰ) (fᴰ : (i : I) → ⟦ f i ⟧ᴰ)
      → (pairᴰ aᴰ bᴰ ⋆ᴰ fᴰ)
        ≡[ pair-nat a b f ] pairᴰ (aᴰ ⋆ᴰ fᴰ) (bᴰ ⋆ᴰ fᴰ)
    fst-natᴰ : {I J : Type} {Γ : Ctxt I} {Δ : Ctxt J} {A B : Ty}
      {t : Tm I Γ (A ×' B)} {f : (i : I) → Tm J Δ (Γ i)}
      (tᴰ : ⟦ t ⟧ᴰ) (fᴰ : (i : I) → ⟦ f i ⟧ᴰ)
      → (fstᴰ tᴰ ⋆ᴰ fᴰ) ≡[ fst-nat t f ] fstᴰ (tᴰ ⋆ᴰ fᴰ)
    snd-natᴰ : {I J : Type} {Γ : Ctxt I} {Δ : Ctxt J} {A B : Ty}
      {t : Tm I Γ (A ×' B)} {f : (i : I) → Tm J Δ (Γ i)}
      (tᴰ : ⟦ t ⟧ᴰ) (fᴰ : (i : I) → ⟦ f i ⟧ᴰ)
      → (sndᴰ tᴰ ⋆ᴰ fᴰ) ≡[ snd-nat t f ] sndᴰ (tᴰ ⋆ᴰ fᴰ)
    ×β₁ᴰ : {I : Type} {Γ : Ctxt I} {A B : Ty}
      {a : Tm I Γ A} {b : Tm I Γ B} (aᴰ : ⟦ a ⟧ᴰ) (bᴰ : ⟦ b ⟧ᴰ)
      → fstᴰ (pairᴰ aᴰ bᴰ) ≡[ ×β₁ a b ] aᴰ
    ×β₂ᴰ : {I : Type} {Γ : Ctxt I} {A B : Ty}
      {a : Tm I Γ A} {b : Tm I Γ B} (aᴰ : ⟦ a ⟧ᴰ) (bᴰ : ⟦ b ⟧ᴰ)
      → sndᴰ (pairᴰ aᴰ bᴰ) ≡[ ×β₂ a b ] bᴰ
    ×ηᴰ : {I : Type} {Γ : Ctxt I} {A B : Ty} {t : Tm I Γ (A ×' B)}
      (tᴰ : ⟦ t ⟧ᴰ) → pairᴰ (fstᴰ tᴰ) (sndᴰ tᴰ) ≡[ ×η t ] tᴰ
    app-natᴰ : {I J : Type} {Γ : Ctxt I} {Δ : Ctxt J} {A B : Ty}
      {t : Tm I Γ (A ⇒' B)} {u : Tm I Γ A} {f : (i : I) → Tm J Δ (Γ i)}
      (tᴰ : ⟦ t ⟧ᴰ) (uᴰ : ⟦ u ⟧ᴰ) (fᴰ : (i : I) → ⟦ f i ⟧ᴰ)
      → (appᴰ tᴰ uᴰ ⋆ᴰ fᴰ)
        ≡[ app-nat t u f ] appᴰ (tᴰ ⋆ᴰ fᴰ) (uᴰ ⋆ᴰ fᴰ)

    -- the binder laws.  The base rules ford their extended
    -- environment, so these take the displayed environment over it.
    lam-natᴰ : {I J : Type} {Γ : Ctxt I} {Δ : Ctxt J} {A B : Ty}
      {t : Tm (I ⊎ Unit) (Γ ,, A) B} {f : (i : I) → Tm J Δ (Γ i)}
      {f↑ : (i : I ⊎ Unit) → Tm (J ⊎ Unit) (Δ ,, A) ((Γ ,, A) i)}
      {f↑l : (i : I) → f↑ (inl i) ≡ (f i ⟪ (λ j → var (inl j)) ⟫)}
      {f↑r : f↑ (inr tt) ≡ var (inr tt)}
      (tᴰ : ⟦ t ⟧ᴰ) (fᴰ : (i : I) → ⟦ f i ⟧ᴰ)
      (f↑ᴰ : (i : I ⊎ Unit) → ⟦ f↑ i ⟧ᴰ)
      (f↑lᴰ : (i : I)
        → f↑ᴰ (inl i) ≡[ f↑l i ] (fᴰ i ⋆ᴰ (λ j → varᴰ (inl j))))
      (f↑rᴰ : f↑ᴰ (inr tt) ≡[ f↑r ] varᴰ (inr tt))
      → (lamᴰ tᴰ ⋆ᴰ fᴰ) ≡[ lam-nat t f f↑ f↑l f↑r ] lamᴰ (tᴰ ⋆ᴰ f↑ᴰ)
    ⇒βᴰ : {I : Type} {Γ : Ctxt I} {A B : Ty}
      {t : Tm (I ⊎ Unit) (Γ ,, A) B} {u : Tm I Γ A}
      {f : (i : I ⊎ Unit) → Tm I Γ ((Γ ,, A) i)}
      {fl : (i : I) → f (inl i) ≡ var i} {fr : f (inr tt) ≡ u}
      (tᴰ : ⟦ t ⟧ᴰ) (uᴰ : ⟦ u ⟧ᴰ) (fᴰ : (i : I ⊎ Unit) → ⟦ f i ⟧ᴰ)
      (flᴰ : (i : I) → fᴰ (inl i) ≡[ fl i ] varᴰ i)
      (frᴰ : fᴰ (inr tt) ≡[ fr ] uᴰ)
      → appᴰ (lamᴰ tᴰ) uᴰ ≡[ ⇒β t u f fl fr ] (tᴰ ⋆ᴰ fᴰ)
    -- ⇒η is not forded — its environment is literally `var ∘ inl` — so
    -- the displayed weakening is `varᴰ ∘ inl` and is not a parameter.
    ⇒ηᴰ : {I : Type} {Γ : Ctxt I} {A B : Ty} {t : Tm I Γ (A ⇒' B)}
      (tᴰ : ⟦ t ⟧ᴰ)
      → lamᴰ (appᴰ (tᴰ ⋆ᴰ (λ j → varᴰ {Γ = Γ ,, A} (inl j)))
                   (varᴰ (inr tt)))
        ≡[ ⇒η t ] tᴰ

-- THE ELIMINATOR.  Fourteen path constructors: three clone laws from
-- Mᴰ, eleven fields, and trunc.
module _ {Mᴰ : CartesianMulticategoryᴰ Syn ℓᴰ ℓᴰ'} (M : DisplayedModel Mᴰ) where
  open DisplayedModel M

  elim : {I : Type} {Γ : Ctxt I} {A : Ty} (t : Tm I Γ A) → ⟦ t ⟧ᴰ
  elim (var i) = varᴰ i
  elim (t ⟪ f ⟫) = elim t ⋆ᴰ (λ i → elim (f i))
  elim tt' = ttᴰ
  elim (pair a b) = pairᴰ (elim a) (elim b)
  elim (fst' t) = fstᴰ (elim t)
  elim (snd' t) = sndᴰ (elim t)
  elim (lam t) = lamᴰ (elim t)
  elim (app t u) = appᴰ (elim t) (elim u)
  elim (⟪⟫var i f k) = ⋆Varᴰ i (λ i → elim (f i)) k
  elim (⟪⟫id t k) = ⋆Idᴰ (elim t) k
  elim (⟪⟫⟪⟫ t f g k) =
    ⋆Assocᴰ (elim t) (λ i → elim (f i)) (λ j → elim (g j)) k
  elim (⊤η t k) = ⊤ηᴰ (elim t) k
  elim (pair-nat a b f k) =
    pair-natᴰ (elim a) (elim b) (λ i → elim (f i)) k
  elim (fst-nat t f k) = fst-natᴰ (elim t) (λ i → elim (f i)) k
  elim (snd-nat t f k) = snd-natᴰ (elim t) (λ i → elim (f i)) k
  elim (×β₁ a b k) = ×β₁ᴰ (elim a) (elim b) k
  elim (×β₂ a b k) = ×β₂ᴰ (elim a) (elim b) k
  elim (×η t k) = ×ηᴰ (elim t) k
  elim (lam-nat t f f↑ f↑l f↑r k) =
    lam-natᴰ (elim t) (λ i → elim (f i)) (λ i → elim (f↑ i))
      (λ i k' → elim (f↑l i k')) (λ k' → elim (f↑r k')) k
  elim (app-nat t u f k) =
    app-natᴰ (elim t) (elim u) (λ i → elim (f i)) k
  elim (⇒β t u f fl fr k) =
    ⇒βᴰ (elim t) (elim u) (λ i → elim (f i))
      (λ i k' → elim (fl i k')) (λ k' → elim (fr k')) k
  elim (⇒η t k) = ⇒ηᴰ (elim t) k
  elim (trunc t u p q k k') =
    isOfHLevel→isOfHLevelDep 2 (λ _ → isSetMHomᴰ)
      (elim t) (elim u) (cong elim p) (cong elim q) (trunc t u p q) k k'

-- RECURSION INTO MODELS is the special case at the constant displayed
-- multicategory.  A DisplayedModel over `weakenᴰ Syn M` is exactly a
-- model of the theory in M, and elim's output is already a
-- multimorphism of M — so the two multifunctor laws are refl: elim
-- sends var to varᴰ = M.var and _⟪_⟫ to _⋆ᴰ_ = M._⋆_ definitionally.
module _ {ℓM ℓM' : Level} (M : CartesianMulticategory ℓ-zero ℓM ℓM')
  (D : DisplayedModel (weakenᴰ Syn M)) where
  open Multifunctor

  rec : Multifunctor Syn M
  rec .F-ob = DisplayedModel.S-ob D
  rec .F-hom = elim D
  rec .F-var i = refl
  rec .F-⋆ t f = refl
