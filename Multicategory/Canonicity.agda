{-

  Canonicity for the syntax of Multicategory.Syntax, by gluing.

  The glue is a displayed cartesian multicategory over the syntax whose
  fibre over a type is a predicate on its CLOSED terms, and whose
  displayed hom over t is "t takes related environments to related
  results".  That is Famᴰ PROPₘ reindexed along the global-sections
  multifunctor, unfolded.

  The fundamental theorem is a Sectionᴰ of that displayed multicategory,
  and canonicity is read off from it at the empty arity.

-}
module Multicategory.Canonicity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty
open import Cubical.HITs.PropositionalTruncation as PT

open import Multicategory.Cartesian
open import Multicategory.Multifunctor
open import Multicategory.Displayed
open import Multicategory.Reindex
open import Multicategory.Family
open import Multicategory.Examples
open import Multicategory.Syntax
open import Multicategory.Elim as E using (DisplayedModel)

private
  ℓ1 : Level
  ℓ1 = ℓ-suc ℓ-zero

-- the empty context, and closed terms
∅ : Ctxt ⊥
∅ ()

Cl : Ty → Type ℓ1
Cl A = Tm ⊥ ∅ A

-- any vacuous substitution on a closed term is the identity
closed-id : {A : Ty} (t : Cl A) (f : (i : ⊥) → Tm ⊥ ∅ (∅ i)) → (t ⟪ f ⟫) ≡ t
closed-id t f = cong (t ⟪_⟫) (funExt (λ ())) ∙ ⟪⟫id t

-- THE LOGICAL PREDICATE.  Prop-valued, so every displayed law and
-- every path-constructor case below is automatic.
P : (A : Ty) → Cl A → hProp ℓ1
P ⊤' t = Unit* , isPropUnit*
P (A ×' B) t =
  (⟨ P A (fst' t) ⟩ × ⟨ P B (snd' t) ⟩)
  , isProp× (str (P A (fst' t))) (str (P B (snd' t)))
P (A ⇒' B) t =
  ((u : Cl A) → ⟨ P A u ⟩ → ⟨ P B (app t u) ⟩)
  , isPropΠ2 (λ u _ → str (P B (app t u)))
P (A +' B) t =
  ∥ (Σ[ a ∈ Cl A ] (t ≡ inl' a) × ⟨ P A a ⟩)
  ⊎ (Σ[ b ∈ Cl B ] (t ≡ inr' b) × ⟨ P B b ⟩) ∥₁
  , squash₁

-- environments, their extension, and the extension of a lifted
-- environment: the one computation the binder cases need
Env : {I : Type} → Ctxt I → Type ℓ1
Env {I} Γ = (i : I) → Cl (Γ i)

EnvP : {I : Type} {Γ : Ctxt I} → Env Γ → Type ℓ1
EnvP {I} {Γ} γ = (i : I) → ⟨ P (Γ i) (γ i) ⟩

module _ {I : Type} {Γ : Ctxt I} {A : Ty} where
  ext : (γ : Env Γ) (u : Cl A) → Env (Γ ,, A)
  ext γ u = Sum.elim γ (λ _ → u)

  extP : {γ : Env Γ} {u : Cl A} → EnvP γ → ⟨ P A u ⟩ → EnvP (ext γ u)
  extP γᴰ uᴰ = Sum.elim γᴰ (λ _ → uᴰ)

  -- the environment γ, weakened under a binder
  γ↑ : (γ : Env Γ) → (i : I ⊎ Unit) → Tm (⊥ ⊎ Unit) (∅ ,, A) ((Γ ,, A) i)
  γ↑ γ = Sum.elim (λ i → γ i ⟪ (λ j → var (inl j)) ⟫) (λ _ → var (inr tt))

  -- substituting u for the bound variable in the weakened environment
  -- gives the extended environment back
  γ↑-ext : (γ : Env Γ) (u : Cl A) (i : I ⊎ Unit)
    → (γ↑ γ i ⟪ Sum.elim var (λ _ → u) ⟫) ≡ ext γ u i
  γ↑-ext γ u (inl i) =
    ⟪⟫⟪⟫ (γ i) (λ j → var (inl j)) (Sum.elim var (λ _ → u))
    ∙ closed-id (γ i) _
  γ↑-ext γ u (inr _) = ⟪⟫var (inr tt) (Sum.elim var (λ _ → u))

-- THE GLOBAL SECTIONS multifunctor: a type goes to its set of closed
-- terms, and a multimorphism to substitution into closed terms.  Its
-- two laws are the syntax's clone laws — not refl, because the syntax
-- is not strict.
open Multifunctor

GS : Multifunctor Syn (SETₘ {ℓ-zero} {ℓ1})
GS .F-ob A = Cl A , trunc
GS .F-hom t γ = t ⟪ γ ⟫
GS .F-var i = funExt (λ γ → ⟪⟫var i γ)
GS .F-⋆ t f = funExt (λ δ → ⟪⟫⟪⟫ t f δ)

-- THE GLUE, as a reindexing: predicates on closed terms are the family
-- construction at PROP, and the glue is that pulled back along global
-- sections.  Nothing here is hand-rolled.
open CartesianMulticategoryᴰ

Glue : CartesianMulticategoryᴰ Syn (ℓ-suc ℓ1) ℓ1
Glue = reindexᴰ GS (Famᴰ {ℓI = ℓ-zero} {ℓ = ℓ1} (PROPₘ {ℓI = ℓ-zero} {ℓ = ℓ1}))

-- its displayed homs are what the fundamental theorem needs, on the
-- nose: t sends related environments to related results
_ : {I : Type} {Γ : Ctxt I} {A : Ty}
    {Γᴰ : (i : I) → Cl (Γ i) → hProp ℓ1} {Aᴰ : Cl A → hProp ℓ1}
    (t : Tm I Γ A)
  → Glue .MHomᴰ[_][_,_] {I = I} {Γ = Γ} {A = A} t Γᴰ Aᴰ
    ≡ ((γ : Env Γ) → ((i : I) → ⟨ Γᴰ i (γ i) ⟩) → ⟨ Aᴰ (t ⟪ γ ⟫) ⟩)
_ = λ t → refl

-- THE FUNDAMENTAL THEOREM, as a DISPLAYED MODEL.  Note what is absent:
-- there is no variable case and no substitution case, because varᴰ and
-- _⋆ᴰ_ come with the glue.  Nine operations and sixteen laws remain,
-- and the laws are one line each only because P is prop-valued — in a
-- data-valued model they would be the real content.
private
  D : {I : Type} {Γ : Ctxt I} {A : Ty} → Tm I Γ A → Type ℓ1
  D {I} {Γ} {A} t = (γ : Env Γ) → EnvP γ → ⟨ P A (t ⟪ γ ⟫) ⟩

  isPropD : {I : Type} {Γ : Ctxt I} {A : Ty} (t : Tm I Γ A) → isProp (D t)
  isPropD {A = A} t = isPropΠ2 (λ γ _ → str (P A (t ⟪ γ ⟫)))

module DM = DisplayedModel

CanModel : DisplayedModel Glue
CanModel .DM.S-ob = P
-- unit
CanModel .DM.ttᴰ γ γᴰ = tt*
-- products
CanModel .DM.pairᴰ {A = A} {B = B} {a = a} {b = b} da db γ γᴰ =
  subst (λ s → ⟨ P A s ⟩)
    (sym (cong fst' (pair-nat a b γ) ∙ ×β₁ (a ⟪ γ ⟫) (b ⟪ γ ⟫)))
    (da γ γᴰ)
  , subst (λ s → ⟨ P B s ⟩)
    (sym (cong snd' (pair-nat a b γ) ∙ ×β₂ (a ⟪ γ ⟫) (b ⟪ γ ⟫)))
    (db γ γᴰ)
CanModel .DM.fstᴰ {A = A} {t = t} dt γ γᴰ =
  subst (λ s → ⟨ P A s ⟩) (sym (fst-nat t γ)) (dt γ γᴰ .fst)
CanModel .DM.sndᴰ {B = B} {t = t} dt γ γᴰ =
  subst (λ s → ⟨ P B s ⟩) (sym (snd-nat t γ)) (dt γ γᴰ .snd)
-- functions
CanModel .DM.lamᴰ {B = B} {t = t} dt γ γᴰ u uᴰ =
  subst (λ s → ⟨ P B s ⟩)
    (sym (cong (λ s → app s u)
            (lam-nat t γ (γ↑ γ) (λ i → refl) refl)
          ∙ ⇒β (t ⟪ γ↑ γ ⟫) u (Sum.elim var (λ _ → u)) (λ i → refl) refl
          ∙ ⟪⟫⟪⟫ t (γ↑ γ) (Sum.elim var (λ _ → u))
          ∙ cong (t ⟪_⟫) (funExt (γ↑-ext γ u))))
    (dt (ext γ u) (extP γᴰ uᴰ))
CanModel .DM.appᴰ {B = B} {t = t} {u = u} dt du γ γᴰ =
  subst (λ s → ⟨ P B s ⟩) (sym (app-nat t u γ))
    (dt γ γᴰ (u ⟪ γ ⟫) (du γ γᴰ))
-- sums
CanModel .DM.inlᴰ {a = a} da γ γᴰ =
  ∣ inl (a ⟪ γ ⟫ , inl-nat a γ , da γ γᴰ) ∣₁
CanModel .DM.inrᴰ {b = b} db γ γᴰ =
  ∣ inr (b ⟪ γ ⟫ , inr-nat b γ , db γ γᴰ) ∣₁
CanModel .DM.caseᴰ {C = C} {t = t} {l = l} {r = r} dt dl dr γ γᴰ =
  PT.rec (str (P C (case' t l r ⟪ γ ⟫)))
    (Sum.elim
      (λ (a , p , aᴰ) →
        subst (λ s → ⟨ P C s ⟩)
          (sym (case-nat t l r γ (γ↑ γ) (λ i → refl) refl
                                 (γ↑ γ) (λ i → refl) refl
                ∙ cong (λ s → case' s (l ⟪ γ↑ γ ⟫) (r ⟪ γ↑ γ ⟫)) p
                ∙ +β₁ a (l ⟪ γ↑ γ ⟫) (r ⟪ γ↑ γ ⟫)
                    (Sum.elim var (λ _ → a)) (λ i → refl) refl
                ∙ ⟪⟫⟪⟫ l (γ↑ γ) (Sum.elim var (λ _ → a))
                ∙ cong (l ⟪_⟫) (funExt (γ↑-ext γ a))))
          (dl (ext γ a) (extP γᴰ aᴰ)))
      (λ (b , p , bᴰ) →
        subst (λ s → ⟨ P C s ⟩)
          (sym (case-nat t l r γ (γ↑ γ) (λ i → refl) refl
                                 (γ↑ γ) (λ i → refl) refl
                ∙ cong (λ s → case' s (l ⟪ γ↑ γ ⟫) (r ⟪ γ↑ γ ⟫)) p
                ∙ +β₂ b (l ⟪ γ↑ γ ⟫) (r ⟪ γ↑ γ ⟫)
                    (Sum.elim var (λ _ → b)) (λ i → refl) refl
                ∙ ⟪⟫⟪⟫ r (γ↑ γ) (Sum.elim var (λ _ → b))
                ∙ cong (r ⟪_⟫) (funExt (γ↑-ext γ b))))
          (dr (ext γ b) (extP γᴰ bᴰ))))
    (dt γ γᴰ)
-- the sixteen laws, all by prop-valuedness of P
CanModel .DM.⊤ηᴰ {t = t} tᴰ = isProp→PathP (λ k → isPropD (⊤η t k)) _ _
CanModel .DM.pair-natᴰ {a = a} {b = b} {f = f} aᴰ bᴰ fᴰ =
  isProp→PathP (λ k → isPropD (pair-nat a b f k)) _ _
CanModel .DM.fst-natᴰ {t = t} {f = f} tᴰ fᴰ =
  isProp→PathP (λ k → isPropD (fst-nat t f k)) _ _
CanModel .DM.snd-natᴰ {t = t} {f = f} tᴰ fᴰ =
  isProp→PathP (λ k → isPropD (snd-nat t f k)) _ _
CanModel .DM.×β₁ᴰ {a = a} {b = b} aᴰ bᴰ =
  isProp→PathP (λ k → isPropD (×β₁ a b k)) _ _
CanModel .DM.×β₂ᴰ {a = a} {b = b} aᴰ bᴰ =
  isProp→PathP (λ k → isPropD (×β₂ a b k)) _ _
CanModel .DM.×ηᴰ {t = t} tᴰ = isProp→PathP (λ k → isPropD (×η t k)) _ _
CanModel .DM.app-natᴰ {t = t} {u = u} {f = f} tᴰ uᴰ fᴰ =
  isProp→PathP (λ k → isPropD (app-nat t u f k)) _ _
CanModel .DM.inl-natᴰ {a = a} {f = f} aᴰ fᴰ =
  isProp→PathP (λ k → isPropD (inl-nat a f k)) _ _
CanModel .DM.inr-natᴰ {b = b} {f = f} bᴰ fᴰ =
  isProp→PathP (λ k → isPropD (inr-nat b f k)) _ _
CanModel .DM.lam-natᴰ {t = t} {f = f} {f↑ = f↑} {f↑l = f↑l} {f↑r = f↑r}
  tᴰ fᴰ f↑ᴰ _ _ =
  isProp→PathP (λ k → isPropD (lam-nat t f f↑ f↑l f↑r k)) _ _
CanModel .DM.⇒βᴰ {t = t} {u = u} {f = f} {fl = fl} {fr = fr} tᴰ uᴰ fᴰ _ _ =
  isProp→PathP (λ k → isPropD (⇒β t u f fl fr k)) _ _
CanModel .DM.⇒ηᴰ {t = t} tᴰ = isProp→PathP (λ k → isPropD (⇒η t k)) _ _
CanModel .DM.case-natᴰ {t = t} {l = l} {r = r} {f = f}
  {fᴬ = fᴬ} {fᴬl = fᴬl} {fᴬr = fᴬr} {fᴮ = fᴮ} {fᴮl = fᴮl} {fᴮr = fᴮr}
  tᴰ lᴰ rᴰ fᴰ fᴬᴰ fᴮᴰ _ _ _ _ =
  isProp→PathP
    (λ k → isPropD (case-nat t l r f fᴬ fᴬl fᴬr fᴮ fᴮl fᴮr k)) _ _
CanModel .DM.+β₁ᴰ {a = a} {l = l} {r = r} {f = f} {fl = fl} {fr = fr}
  aᴰ lᴰ rᴰ fᴰ _ _ = isProp→PathP (λ k → isPropD (+β₁ a l r f fl fr k)) _ _
CanModel .DM.+β₂ᴰ {b = b} {l = l} {r = r} {f = f} {fl = fl} {fr = fr}
  bᴰ lᴰ rᴰ fᴰ _ _ = isProp→PathP (λ k → isPropD (+β₂ b l r f fl fr k)) _ _
CanModel .DM.+ηᴰ {t = t} {h = h} {f = f} {fl = fl} {fr = fr}
  {gᴬ = gᴬ} {gᴬl = gᴬl} {gᴬr = gᴬr} {gᴮ = gᴮ} {gᴮl = gᴮl} {gᴮr = gᴮr}
  tᴰ hᴰ fᴰ gᴬᴰ gᴮᴰ _ _ _ _ _ _ =
  isProp→PathP
    (λ k → isPropD (+η t h f fl fr gᴬ gᴬl gᴬr gᴮ gᴮl gᴮr k)) _ _

-- the fundamental theorem itself
fund : {I : Type} {Γ : Ctxt I} {A : Ty} (t : Tm I Γ A) → D t
fund = E.elim CanModel

open Sectionᴰ

-- and as a section of the glue
FTLR : Sectionᴰ Glue
FTLR .S-ob = P
FTLR .S-hom = fund
FTLR .S-var {Γ = Γ} i =
  isPropΠ2 (λ γ _ → str (P (Γ i) _)) _ _
FTLR .S-⋆ {A = A} f g =
  isPropΠ2 (λ γ _ → str (P A _)) _ _

-- every closed term satisfies the predicate
closed-P : {A : Ty} (t : Cl A) → ⟨ P A t ⟩
closed-P {A} t =
  subst (λ s → ⟨ P A s ⟩) (closed-id t (λ ())) (fund t (λ ()) (λ ()))

-- CANONICITY for sums: every closed term of a sum type is an injection
canonicity+ : {A B : Ty} (t : Cl (A +' B))
  → ∥ (Σ[ a ∈ Cl A ] t ≡ inl' a) ⊎ (Σ[ b ∈ Cl B ] t ≡ inr' b) ∥₁
canonicity+ t =
  PT.map (Sum.elim (λ (a , p , _) → inl (a , p))
                   (λ (b , p , _) → inr (b , p)))
         (closed-P t)

-- … so the booleans are exactly true and false
Bool' : Ty
Bool' = ⊤' +' ⊤'

true' false' : Cl Bool'
true' = inl' tt'
false' = inr' tt'

canonicityBool : (t : Cl Bool') → ∥ (t ≡ true') ⊎ (t ≡ false') ∥₁
canonicityBool t =
  PT.map (Sum.elim (λ (a , p) → inl (p ∙ cong inl' (⊤η a)))
                   (λ (b , p) → inr (p ∙ cong inr' (⊤η b))))
         (canonicity+ t)

-- CANONICAL FORMS for the other formers.  These need no gluing: they
-- are the η rules, which is exactly the sense in which sums are the
-- hard case.
canonicity⊤ : (t : Cl ⊤') → t ≡ tt'
canonicity⊤ = ⊤η

canonicity× : {A B : Ty} → Iso (Cl (A ×' B)) (Cl A × Cl B)
canonicity× .Iso.fun t = fst' t , snd' t
canonicity× .Iso.inv (a , b) = pair a b
canonicity× .Iso.sec (a , b) = ΣPathP (×β₁ a b , ×β₂ a b)
canonicity× .Iso.ret t = ×η t

canonicity⇒ : {A B : Ty} (t : Cl (A ⇒' B))
  → Σ[ t' ∈ Tm (⊥ ⊎ Unit) (∅ ,, A) B ] t ≡ lam t'
canonicity⇒ t = _ , sym (⇒η t)
