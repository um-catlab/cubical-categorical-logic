{-# OPTIONS --lossy-unification #-}
-- Free cartesian closed category generated from base objects and generators
--
-- "Forded" version using strict equality constraints for canonical forms
-- Uses Eq.transport for the lambda β/η rules to handle context changes

module Cubical.Categories.Constructions.Free.CartesianClosedCategory.Forded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Section.Base as Cat
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Constructions.Reindex.Base as Reindex
open import Cubical.Categories.Displayed.Constructions.Reindex.CartesianClosed
open import Cubical.Categories.Displayed.Constructions.Weaken.Base as Wk
open import Cubical.Categories.Displayed.Constructions.Weaken.UncurriedProperties

open import Cubical.Categories.Constructions.Free.CartesianClosedCategory.Quiver

private
  variable
    ℓQ ℓQ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' : Level

open Category hiding (_∘_)
open Section
open UniversalElement

module _ (Q : ×⇒Quiver ℓQ ℓQ') where
  private module Q = ×⇒Quiver Q

  -- Expression type with equality constraints for canonical forms
  data Expr (A B : Q.obExpr) : Type (ℓ-max ℓQ ℓQ') where
    -- Freely added Category structure
    genₑ : ∀ t → (Q.dom t Eq.≡ A) → (Q.cod t Eq.≡ B) → Expr A B
    idₑ : A Eq.≡ B → Expr A B
    _⋆ₑ_ : ∀ {C} → (e : Expr A C) → (e' : Expr C B) → Expr A B
    ⋆ₑIdL : (e : Expr A B) → idₑ Eq.refl ⋆ₑ e ≡ e
    ⋆ₑIdR : (e : Expr A B) → e ⋆ₑ idₑ Eq.refl ≡ e
    ⋆ₑAssoc : ∀ {C D} (e : Expr A C)(f : Expr C D)(g : Expr D B)
            → (e ⋆ₑ f) ⋆ₑ g ≡ e ⋆ₑ (f ⋆ₑ g)
    isSetExpr : isSet (Expr A B)
    -- Freely added Terminal structure
    !ₑ : (⊤ Eq.≡ B) → Expr A B
    ⊤η : (p : ⊤ Eq.≡ B) (t : Expr A B) → t ≡ !ₑ p
    -- Freely added BinProducts structure
    π₁ : ∀ {Γ Δ} → ((Γ × Δ) Eq.≡ A) → (Γ Eq.≡ B) → Expr A B
    π₂ : ∀ {Γ Δ} → ((Γ × Δ) Eq.≡ A) → (Δ Eq.≡ B) → Expr A B
    ⟨_,_⟩ : ∀ {Δ Δ'} → Expr A Δ → Expr A Δ' → ((Δ × Δ') Eq.≡ B) → Expr A B
    ×β₁ : ∀ {Δ'}{t : Expr A B}{t' : Expr A Δ'}
        → ⟨ t , t' ⟩ Eq.refl ⋆ₑ π₁ Eq.refl Eq.refl ≡ t
    ×β₂ : ∀ {Δ}{t : Expr A Δ}{t' : Expr A B}
        → ⟨ t , t' ⟩ Eq.refl ⋆ₑ π₂ Eq.refl Eq.refl ≡ t'
    ×η : ∀ {Δ Δ'}(p : (Δ × Δ') Eq.≡ B)(t : Expr A B)
       → t ≡ ⟨ t ⋆ₑ π₁ p Eq.refl , t ⋆ₑ π₂ p Eq.refl ⟩ p
    -- Freely added Exponentials structure
    eval : ∀ {Δ Θ} → (((Δ ⇒ Θ) × Δ) Eq.≡ A) → (Θ Eq.≡ B) → Expr A B
    -- lam takes body : Expr (A × Δ) Θ and produces Expr A (Δ ⇒ Θ)
    lam : ∀ {Δ Θ} → Expr (A × Δ) Θ → ((Δ ⇒ Θ) Eq.≡ B) → Expr A B
    -- Lambda beta: context is Γ × Δ, need to transport to A
    -- When pA = Eq.refl, this reduces to the standard β rule
    λβ : ∀ {Γ Δ} (pA : (Γ × Δ) Eq.≡ A) (t : Expr (Γ × Δ) B)
       → Eq.transport (λ X → Expr X B) pA
           (⟨ π₁ Eq.refl Eq.refl ⋆ₑ lam t Eq.refl , π₂ Eq.refl Eq.refl ⟩ Eq.refl
            ⋆ₑ eval Eq.refl Eq.refl)
         ≡ Eq.transport (λ X → Expr X B) pA t
    -- Lambda eta: B = Δ ⇒ Θ, need to transport t to use in body
    λη : ∀ {Δ Θ} (pB : (Δ ⇒ Θ) Eq.≡ B) (t : Expr A B)
       → t ≡ lam (⟨ π₁ Eq.refl Eq.refl ⋆ₑ Eq.transport (Expr A) (Eq.sym pB) t
                  , π₂ Eq.refl Eq.refl ⟩ Eq.refl
               ⋆ₑ eval Eq.refl Eq.refl) pB

  -- Convenience constructors
  ↑ₑ : ∀ t → Expr (Q.dom t) (Q.cod t)
  ↑ₑ t = genₑ t Eq.refl Eq.refl

  π₁' : ∀ {Γ Δ} → Expr (Γ × Δ) Γ
  π₁' = π₁ Eq.refl Eq.refl

  π₂' : ∀ {Γ Δ} → Expr (Γ × Δ) Δ
  π₂' = π₂ Eq.refl Eq.refl

  ⟨_,_⟩' : ∀ {Γ Δ Δ'} → Expr Γ Δ → Expr Γ Δ' → Expr Γ (Δ × Δ')
  ⟨ t , t' ⟩' = ⟨ t , t' ⟩ Eq.refl

  !ₑ' : ∀ {Γ} → Expr Γ ⊤
  !ₑ' = !ₑ Eq.refl

  eval' : ∀ {Δ Θ} → Expr ((Δ ⇒ Θ) × Δ) Θ
  eval' = eval Eq.refl Eq.refl

  lam' : ∀ {Γ Δ Θ} → Expr (Γ × Δ) Θ → Expr Γ (Δ ⇒ Θ)
  lam' t = lam t Eq.refl

  open CartesianCategory using (C; term; bp)
  open CartesianClosedCategory using (CC; exps)

  |FreeCartesianClosedCategory| : Category _ _
  |FreeCartesianClosedCategory| .ob = Q.obExpr
  |FreeCartesianClosedCategory| .Hom[_,_] = Expr
  |FreeCartesianClosedCategory| .id = idₑ Eq.refl
  |FreeCartesianClosedCategory| ._⋆_ = _⋆ₑ_
  |FreeCartesianClosedCategory| .⋆IdL = ⋆ₑIdL
  |FreeCartesianClosedCategory| .⋆IdR = ⋆ₑIdR
  |FreeCartesianClosedCategory| .⋆Assoc = ⋆ₑAssoc
  |FreeCartesianClosedCategory| .isSetHom = isSetExpr

  FreeCartesianClosedCategory : CartesianClosedCategory _ _
  FreeCartesianClosedCategory .CC .C = |FreeCartesianClosedCategory|
  FreeCartesianClosedCategory .CC .term .vertex = ⊤
  FreeCartesianClosedCategory .CC .term .element = tt
  FreeCartesianClosedCategory .CC .term .universal _ =
    isIsoToIsEquiv ((λ z → !ₑ') , ((λ b → refl) , λ _ → sym $ ⊤η Eq.refl _))
  FreeCartesianClosedCategory .CC .bp (Γ , Δ) .vertex = Γ × Δ
  FreeCartesianClosedCategory .CC .bp (Γ , Δ) .element = π₁' , π₂'
  FreeCartesianClosedCategory .CC .bp (Γ , Δ) .universal Θ = isIsoToIsEquiv
    ( (λ z → ⟨ z .fst , z .snd ⟩')
    , (λ _ → ΣPathP (×β₁ , ×β₂))
    , (λ _ → sym $ ×η Eq.refl _))
  FreeCartesianClosedCategory .exps Δ Θ .vertex = Δ ⇒ Θ
  FreeCartesianClosedCategory .exps Δ Θ .element = eval'
  FreeCartesianClosedCategory .exps Δ Θ .universal Γ = isIsoToIsEquiv
    (lam' , (λ t → λβ Eq.refl t) , (λ t → sym $ λη Eq.refl t))

  -- Elimination principle
  private
    module FreeCCC = CartesianClosedCategory FreeCartesianClosedCategory

  module _ (CCCᴰ : CartesianClosedCategoryᴰ FreeCartesianClosedCategory ℓCᴰ ℓCᴰ') where
    open CartesianClosedCategoryᴰ CCCᴰ
    open UniversalElementᴰNotation

    module _ (ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]) where
      elimOb : ∀ A → Cᴰ.ob[ A ]
      elimOb (↑ o) = ı-ob o
      elimOb ⊤ = termᴰ .fst
      elimOb (A × B) = bpᴰ (elimOb A) (elimOb B) .fst
      elimOb (A ⇒ B) = expᴰ (elimOb A) (elimOb B) .fst

    record ElimInterpᴰ : Type (ℓ-max (ℓ-max ℓQ ℓQ') (ℓ-max ℓCᴰ ℓCᴰ')) where
      constructor mkElimInterpᴰ
      field
        ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]
        ı-hom : ∀ e → Cᴰ.Hom[ ↑ₑ e ][ elimOb ı-ob (Q.dom e) , elimOb ı-ob (Q.cod e) ]

    module _ (ı : ElimInterpᴰ) where
      open ElimInterpᴰ ı

      elimHom : ∀ {A B} (e : Expr A B)
        → Cᴰ.Hom[ e ][ elimOb ı-ob A , elimOb ı-ob B ]
      elimHom (genₑ t Eq.refl Eq.refl) = ı-hom t
      elimHom (idₑ Eq.refl) = Cᴰ.idᴰ
      elimHom (e ⋆ₑ e') = elimHom e Cᴰ.⋆ᴰ elimHom e'
      elimHom (⋆ₑIdL f i) = Cᴰ.⋆IdLᴰ (elimHom f) i
      elimHom (⋆ₑIdR f i) = Cᴰ.⋆IdRᴰ (elimHom f) i
      elimHom (⋆ₑAssoc f g h i) = Cᴰ.⋆Assocᴰ (elimHom f) (elimHom g) (elimHom h) i
      elimHom (isSetExpr f g p q i j) =
        isSetHomᴰ' Cᴰ (elimHom f) (elimHom g) (λ i → elimHom (p i)) (λ i → elimHom (q i)) i j
      elimHom (!ₑ Eq.refl) = termᴰ.introᴰ tt
      elimHom (⊤η Eq.refl f i) = Cᴰ.rectify {e' = ⊤η Eq.refl f} (termᴰ.ηᴰ (elimHom f)) i
      elimHom (π₁ Eq.refl Eq.refl) = bpᴰ.πᴰ₁
      elimHom (π₂ Eq.refl Eq.refl) = bpᴰ.πᴰ₂
      elimHom (⟨ f , g ⟩ Eq.refl) = bpᴰ.introᴰ ((elimHom f) , (elimHom g))
      elimHom (×β₁ {t = t} {t' = t'} i) = Cᴰ.rectify {e' = ×β₁} (bpᴰ.×βᴰ₁ (elimHom t) (elimHom t')) i
      elimHom (×β₂ {t = t} {t' = t'} i) = Cᴰ.rectify {e' = ×β₂} (bpᴰ.×βᴰ₂ (elimHom t) (elimHom t')) i
      elimHom (×η {Δ} {Δ'} Eq.refl t i) = Cᴰ.rectify {e' = ×η Eq.refl t} (bpᴰ.×ηᴰ (elimHom t)) i
      elimHom (eval Eq.refl Eq.refl) = appᴰ
      elimHom (lam e Eq.refl) = λᴰ (elimHom e)
      elimHom (λβ Eq.refl t i) = Cᴰ.rectify {e' = λβ Eq.refl t} (Cᴰ.≡out $ ⇒βᴰ (elimHom t)) i
      elimHom (λη Eq.refl t i) = Cᴰ.rectify {e' = λη Eq.refl t} (Cᴰ.≡out $ ⇒ηᴰ (elimHom t)) i

      elim : GlobalSection Cᴰ
      elim .F-obᴰ = elimOb ı-ob
      elim .F-homᴰ = elimHom
      elim .F-idᴰ = refl
      elim .F-seqᴰ = λ _ _ → refl

      -- elim strictly preserves the terminal object:
      -- F-obᴰ maps ⊤ to the displayed terminal vertex
      elimPreservesTerminal : elim .F-obᴰ ⊤ ≡ termᴰ .fst
      elimPreservesTerminal = refl

      -- F-homᴰ maps the terminal morphism !ₑ' to the displayed intro
      elimPreservesTerminalMor : ∀ {Γ} →
        elim .F-homᴰ (!ₑ' {Γ}) ≡ termᴰ.introᴰ tt
      elimPreservesTerminalMor = refl

      -- elim strictly preserves binary products:
      -- F-obᴰ maps A × B to the displayed product vertex
      elimPreservesBinProducts : ∀ A B →
        elim .F-obᴰ (A × B) ≡ bpᴰ (elim .F-obᴰ A) (elim .F-obᴰ B) .fst
      elimPreservesBinProducts A B = refl

      -- F-homᴰ maps π₁' to the displayed first projection
      elimPreservesπ₁ : ∀ {A B} →
        elim .F-homᴰ (π₁' {A} {B}) ≡ bpᴰ.πᴰ₁
      elimPreservesπ₁ = refl

      -- F-homᴰ maps π₂' to the displayed second projection
      elimPreservesπ₂ : ∀ {A B} →
        elim .F-homᴰ (π₂' {A} {B}) ≡ bpᴰ.πᴰ₂
      elimPreservesπ₂ = refl

      -- F-homᴰ maps pairing to the displayed pairing
      elimPreservesPairing : ∀ {Γ A B} (f : Expr Γ A) (g : Expr Γ B) →
        elim .F-homᴰ (⟨ f , g ⟩') ≡ bpᴰ.introᴰ (elimHom f , elimHom g)
      elimPreservesPairing f g = refl

      -- elim strictly preserves exponentials:
      -- F-obᴰ maps A ⇒ B to the displayed exponential vertex
      elimPreservesExp : ∀ A B →
        elim .F-obᴰ (A ⇒ B) ≡ expᴰ (elim .F-obᴰ A) (elim .F-obᴰ B) .fst
      elimPreservesExp A B = refl

      -- F-homᴰ maps eval' to the displayed application
      elimPreservesEval : ∀ {A B} →
        elim .F-homᴰ (eval' {A} {B}) ≡ appᴰ
      elimPreservesEval = refl

      -- F-homᴰ maps lam' to the displayed lambda abstraction
      elimPreservesLam : ∀ {Γ A B} (e : Expr (Γ × A) B) →
        elim .F-homᴰ (lam' e) ≡ λᴰ (elimHom e)
      elimPreservesLam e = refl

  -- Local elimination
  module _
    {D : CartesianCategory ℓD ℓD'}
    (F : CartesianFunctor (FreeCartesianClosedCategory .CC) (D .C))
    (CCCⱽ : CartesianClosedCategoryⱽ D ℓCᴰ ℓCᴰ')
    where
    elimLocalMotive : CartesianClosedCategoryᴰ FreeCartesianClosedCategory _ _
    elimLocalMotive = CartesianClosedCategoryⱽ→CartesianClosedCategoryᴰ
      FreeCartesianClosedCategory
      (CCCⱽReindex CCCⱽ F)

    elimLocal : (ı : ElimInterpᴰ elimLocalMotive) → Section (F .fst) (CCCⱽ .CartesianClosedCategoryⱽ.Cᴰ)
    elimLocal ı = GlobalSectionReindex→Section _ _ (elim elimLocalMotive ı)

  -- Recursion (non-dependent functors)
  module _ (CCC : CartesianClosedCategory ℓC ℓC') where
    private
      wkC = weakenCCC FreeCartesianClosedCategory CCC
      module CCC = CartesianClosedCategory CCC

    rec : (ı : ElimInterpᴰ wkC) → Functor FreeCCC.C CCC.C
    rec ı = introS⁻ (elim wkC ı)
