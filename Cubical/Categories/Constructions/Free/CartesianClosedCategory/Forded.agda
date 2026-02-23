{-# OPTIONS --lossy-unification #-}
-- Free cartesian closed category generated from base objects and generators
--
-- "Forded" version using strict equality constraints for canonical forms
-- Uses Eq.transport for the lambda β/η rules to handle context changes

module Cubical.Categories.Constructions.Free.CartesianClosedCategory.Forded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation hiding (_⇒_)
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.Terminal as Term
open import Cubical.Categories.Limits.Terminal.More as Term
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Limits.CartesianSection
open import Cubical.Categories.Displayed.Limits.CartesianClosedSection
open import Cubical.Categories.Displayed.Instances.Arrow.Limits
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
open Functor
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

      elimCartesianClosed : CartesianClosedSection CCCᴰ
      elimCartesianClosed .CartesianClosedSection.cartesianSection
        .CartesianSection.section = elim
      elimCartesianClosed .CartesianClosedSection.cartesianSection
        .CartesianSection.F-obᴰ-⊤ = refl
      elimCartesianClosed .CartesianClosedSection.cartesianSection
        .CartesianSection.F-obᴰ-× _ _ = refl
      elimCartesianClosed .CartesianClosedSection.F-obᴰ-⇒ _ _ = refl

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

  module _ (CCC : CartesianClosedCategory ℓC ℓC') where
    private
      wkC = weakenCCC FreeCartesianClosedCategory CCC
      module CCC = CartesianClosedCategory CCC

    rec : (ı : ElimInterpᴰ wkC) → Functor FreeCCC.C CCC.C
    rec ı = introS⁻ (elim wkC ı)

    recCartesian : (ı : ElimInterpᴰ wkC)
      → CartesianFunctor (FreeCartesianClosedCategory .CC) CCC.C
    recCartesian ı = rec ı , λ c c' →
      CCC.bp (rec ı .F-ob c , rec ı .F-ob c') .universal

  -- CCC functors out of the FreeCartesianClosedCategory
  -- are naturally isomorphic to each other
  module _
    {D : Category ℓD ℓD'}
    ((F , F-bp) (G , G-bp) : CartesianFunctor (FreeCartesianClosedCategory .CC) D)
    (F-1 : Term.preservesTerminal |FreeCartesianClosedCategory| D F)
    (G-1 : Term.preservesTerminal |FreeCartesianClosedCategory| D G)
    (⇒-iso : ∀ {A B} → CatIso D (F ⟅ A ⟆) (G ⟅ A ⟆)
                       → CatIso D (F ⟅ B ⟆) (G ⟅ B ⟆)
                       → CatIso D (F ⟅ A ⇒ B ⟆) (G ⟅ A ⇒ B ⟆))
    (⇒-lam : ∀ {A B Γ} (f : CatIso D (F ⟅ A ⟆) (G ⟅ A ⟆))
                        (g : CatIso D (F ⟅ B ⟆) (G ⟅ B ⟆))
                        (γ : CatIso D (F ⟅ Γ ⟆) (G ⟅ Γ ⟆))
             → (h : Expr (Γ × A) B)
             → (D ._⋆_ (F ⟪ lam' h ⟫) (⇒-iso f g .fst))
               ≡ (D ._⋆_ (γ .fst) (G ⟪ lam' h ⟫)))
    where
    open IsoCommaStructure F G
    private module D = Category D

    module _
      (⇒-eval : ∀ {A B} (f : CatIso D (F ⟅ A ⟆) (G ⟅ A ⟆))
                         (g : CatIso D (F ⟅ B ⟆) (G ⟅ B ⟆))
               → F ⟪ eval' ⟫ D.⋆ g .fst
                 ≡ IsoCommaBinProductsᴰ
                     (FreeCartesianClosedCategory .CC .bp) F-bp G-bp
                     (⇒-iso f g) f .fst .fst
                   D.⋆ G ⟪ eval' ⟫)
      where

      private
        CCCᴰF,G-IsoC : CartesianClosedCategoryᴰ FreeCartesianClosedCategory _ _
        CCCᴰF,G-IsoC .CartesianClosedCategoryᴰ.CCᴰ
          .CartesianCategoryᴰ.Cᴰ = IsoCommaᴰΔ
        CCCᴰF,G-IsoC .CartesianClosedCategoryᴰ.CCᴰ
          .CartesianCategoryᴰ.termᴰ =
          IsoCommaTerminalᴰ (FreeCartesianClosedCategory .CC .term) F-1 G-1
        CCCᴰF,G-IsoC .CartesianClosedCategoryᴰ.CCᴰ
          .CartesianCategoryᴰ.bpᴰ =
          IsoCommaBinProductsᴰ (FreeCartesianClosedCategory .CC .bp) F-bp G-bp
        CCCᴰF,G-IsoC .CartesianClosedCategoryᴰ.expᴰ
          {A = A} f {B = B} g =
          ⇒-iso f g , (⇒-eval f g , tt) , isUniv
          where
          isUniv : isUniversalᴰ IsoCommaᴰΔ _ _
            (FreeCCC.exps A B) (⇒-eval f g , tt)
          isUniv Γ Γᴰ .inv u uᴰ .fst = ⇒-lam f g Γᴰ u
          isUniv Γ Γᴰ .inv _ _ .snd = tt
          isUniv Γ Γᴰ .rightInv _ _ =
            isProp→PathP (λ _ → isPropΣ (D.isSetHom _ _) λ _ → isPropUnit) _ _
          isUniv Γ Γᴰ .leftInv _ _ =
            isProp→PathP (λ _ → isPropΣ (D.isSetHom _ _) λ _ → isPropUnit) _ _

      module _ (ı : ElimInterpᴰ CCCᴰF,G-IsoC) where
        FreeCCCFunctor≅ : NatIso F G
        FreeCCCFunctor≅ =
          sectionToNatIso (elimCartesianClosed CCCᴰF,G-IsoC ı
            .CartesianClosedSection.section)
