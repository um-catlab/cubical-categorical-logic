{-# OPTIONS --lossy-unification #-}
-- Free cartesian category generated from base objects and generators
--
-- "Forded" version using strict equality constraints for canonical forms

module Cubical.Categories.Instances.Free.CartesianCategory.Forded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Unit
open import Cubical.Data.Quiver.Base
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.UnderlyingGraph
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Terminal as Term
open import Cubical.Categories.Limits.Terminal.More as Term
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Constructions.Reindex

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Instances.Comma
open import Cubical.Categories.Displayed.Section.Base as Cat
open import Cubical.Categories.Displayed.Limits.CartesianSection
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Instances.Reindex.Base as Reindex
open import Cubical.Categories.Displayed.Instances.Reindex.Cartesian
open import Cubical.Categories.Displayed.Instances.Weaken.Base as Wk
open import Cubical.Categories.Displayed.Instances.Weaken.UncurriedProperties
open import Cubical.Categories.Displayed.Instances.Path as PathCat
  using (PathC; PathReflection)
open import Cubical.Categories.Displayed.Instances.Path.Displayed as PathC
  using (PathCᴰ)
open import Cubical.Categories.Displayed.BinProduct

open import
  Cubical.Categories.Instances.Free.CartesianCategory.ProductQuiver

private
  variable
    ℓQ ℓQ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open Section
open Functor
open UniversalElement

module _ (Q : ×Quiver ℓQ ℓQ') where
  private module Q = ×Quiver Q

  -- Expression type with equality constraints for canonical forms
  data Exp (A B : Q.Expr) : Type (ℓ-max ℓQ ℓQ') where
    genₑ : ∀ t → (Q.dom t Eq.≡ A) → (Q.cod t Eq.≡ B) → Exp A B
    idₑ : A Eq.≡ B → Exp A B
    _⋆ₑ_ : ∀ {C} → (e : Exp A C) → (e' : Exp C B) → Exp A B
    ⋆ₑIdL : (e : Exp A B) → idₑ Eq.refl ⋆ₑ e ≡ e
    ⋆ₑIdR : (e : Exp A B) → e ⋆ₑ idₑ Eq.refl ≡ e
    ⋆ₑAssoc : ∀ {C D} (e : Exp A C)(f : Exp C D)(g : Exp D B)
            → (e ⋆ₑ f) ⋆ₑ g ≡ e ⋆ₑ (f ⋆ₑ g)
    isSetExp : isSet (Exp A B)
    -- Terminal object structure
    !ₑ : (⊤ Eq.≡ B) → Exp A B
    ⊤η : (p : ⊤ Eq.≡ B) (t : Exp A B) → t ≡ !ₑ p
    -- Binary product structure
    π₁ : ∀ {Γ Δ} → ((Γ × Δ) Eq.≡ A) → (Γ Eq.≡ B) → Exp A B
    π₂ : ∀ {Γ Δ} → ((Γ × Δ) Eq.≡ A) → (Δ Eq.≡ B) → Exp A B
    ⟨_,_⟩ : ∀ {Δ Δ'} → Exp A Δ → Exp A Δ' → ((Δ × Δ') Eq.≡ B) → Exp A B
    -- Beta rules: t : Exp A B, so the product is B × Δ' (or Δ × B)
    ×β₁ : ∀ {Δ'}{t : Exp A B}{t' : Exp A Δ'}
        → ⟨ t , t' ⟩ Eq.refl ⋆ₑ π₁ Eq.refl Eq.refl ≡ t
    ×β₂ : ∀ {Δ}{t : Exp A Δ}{t' : Exp A B}
        → ⟨ t , t' ⟩ Eq.refl ⋆ₑ π₂ Eq.refl Eq.refl ≡ t'
    -- Eta rule: B must be a product
    ×η : ∀ {Δ Δ'}(p : (Δ × Δ') Eq.≡ B)(t : Exp A B)
       → t ≡ ⟨ t ⋆ₑ π₁ p Eq.refl , t ⋆ₑ π₂ p Eq.refl ⟩ p

  ↑ₑ : ∀ t → Exp (Q.dom t) (Q.cod t)
  ↑ₑ t = genₑ t Eq.refl Eq.refl

  π₁' : ∀ {Γ Δ} → Exp (Γ × Δ) Γ
  π₁' = π₁ Eq.refl Eq.refl

  π₂' : ∀ {Γ Δ} → Exp (Γ × Δ) Δ
  π₂' = π₂ Eq.refl Eq.refl

  ⟨_,_⟩' : ∀ {Γ Δ Δ'} → Exp Γ Δ → Exp Γ Δ' → Exp Γ (Δ × Δ')
  ⟨ t , t' ⟩' = ⟨ t , t' ⟩ Eq.refl

  !ₑ' : ∀ {Γ} → Exp Γ ⊤
  !ₑ' = !ₑ Eq.refl

  |FreeCartesianCategory| : Category _ _
  |FreeCartesianCategory| .ob = Q.Expr
  |FreeCartesianCategory| .Hom[_,_] = Exp
  |FreeCartesianCategory| .id = idₑ Eq.refl
  |FreeCartesianCategory| ._⋆_ = _⋆ₑ_
  |FreeCartesianCategory| .⋆IdL = ⋆ₑIdL
  |FreeCartesianCategory| .⋆IdR = ⋆ₑIdR
  |FreeCartesianCategory| .⋆Assoc = ⋆ₑAssoc
  |FreeCartesianCategory| .isSetHom = isSetExp

  open CartesianCategory using (C; term; bp)

  FreeCartesianCategory : CartesianCategory _ _
  FreeCartesianCategory .C = |FreeCartesianCategory|
  FreeCartesianCategory .term .vertex = ⊤
  FreeCartesianCategory .term .element = tt
  FreeCartesianCategory .term .universal _ =
    isIsoToIsEquiv ((λ z → !ₑ') , ((λ b → refl) , λ _ → sym $ ⊤η Eq.refl _))
  FreeCartesianCategory .bp (Γ , Δ) .vertex = Γ × Δ
  FreeCartesianCategory .bp (Γ , Δ) .element = π₁' , π₂'
  FreeCartesianCategory .bp (Γ , Δ) .universal Θ = isIsoToIsEquiv
    ( (λ z → ⟨ z .fst , z .snd ⟩')
    , (λ _ → ΣPathP (×β₁ , ×β₂))
    , (λ _ → sym $ ×η Eq.refl _))

  -- Elimination principle (global sections)
  module _ (CCᴰ : CartesianCategoryᴰ FreeCartesianCategory ℓCᴰ ℓCᴰ') where
    open CartesianCategoryᴰ CCᴰ
    open UniversalElementᴰNotation

    module _ (ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]) where
      elimOb : ∀ A → Cᴰ.ob[ A ]
      elimOb (↑ o) = ı-ob o
      elimOb (A × B) = bpᴰ (elimOb A) (elimOb B) .fst
      elimOb ⊤ = termᴰ .fst

    record ElimInterpᴰ : Type (ℓ-max (ℓ-max ℓQ ℓQ') (ℓ-max ℓCᴰ ℓCᴰ')) where
      constructor mkElimInterpᴰ
      field
        ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]
        ı-hom : ∀ e
          → Cᴰ.Hom[ ↑ₑ e ][ elimOb ı-ob (Q.dom e) , elimOb ı-ob (Q.cod e) ]

    module _ (ı : ElimInterpᴰ) where
      open ElimInterpᴰ ı

      elimHom : ∀ {A A'} (f : |FreeCartesianCategory| [ A , A' ]) →
        Cᴰ [ f ][ elimOb ı-ob A , elimOb ı-ob A' ]
      elimHom (genₑ t Eq.refl Eq.refl) = ı-hom t
      elimHom (idₑ Eq.refl) = Cᴰ.idᴰ
      elimHom (f ⋆ₑ g) = elimHom f Cᴰ.⋆ᴰ elimHom g
      elimHom (⋆ₑIdL f i) = Cᴰ.⋆IdLᴰ (elimHom f) i
      elimHom (⋆ₑIdR f i) = Cᴰ.⋆IdRᴰ (elimHom f) i
      elimHom (⋆ₑAssoc f g h i) = Cᴰ.⋆Assocᴰ (elimHom f) (elimHom g) (elimHom h) i
      elimHom (isSetExp f g p q i j) =
        isSetHomᴰ' Cᴰ (elimHom f) (elimHom g) (λ i → elimHom (p i)) (λ i → elimHom (q i)) i j
      elimHom (!ₑ Eq.refl) = termᴰ.introᴰ tt
      elimHom (⊤η Eq.refl f i) = Cᴰ.rectify {e' = ⊤η Eq.refl f} (termᴰ.ηᴰ (elimHom f)) i
      elimHom (π₁ Eq.refl Eq.refl) = bpᴰ.πᴰ₁
      elimHom (π₂ Eq.refl Eq.refl) = bpᴰ.πᴰ₂
      elimHom (⟨ f , g ⟩ Eq.refl) = bpᴰ.introᴰ ((elimHom f) , (elimHom g))
      elimHom (×β₁ {t = t} {t' = t'} i) = Cᴰ.rectify {e' = ×β₁} (bpᴰ.×βᴰ₁ (elimHom t) (elimHom t')) i
      elimHom (×β₂ {t = t} {t' = t'} i) = Cᴰ.rectify {e' = ×β₂} (bpᴰ.×βᴰ₂ (elimHom t) (elimHom t')) i
      elimHom (×η {Δ} {Δ'} Eq.refl t i) = Cᴰ.rectify {e' = ×η Eq.refl t} (bpᴰ.×ηᴰ (elimHom t)) i

      elim : GlobalSection Cᴰ
      elim .F-obᴰ = elimOb ı-ob
      elim .F-homᴰ = elimHom
      elim .F-idᴰ = refl
      elim .F-seqᴰ = λ _ _ → refl

      -- elim is a cartesian section: it strictly preserves
      -- the terminal object and binary products
      elimCartesian : CartesianSection CCᴰ
      elimCartesian .CartesianSection.section = elim
      elimCartesian .CartesianSection.F-obᴰ-⊤ = refl
      elimCartesian .CartesianSection.F-obᴰ-× _ _ = refl

  -- Local elimination
  module _
    {D : Category ℓD ℓD'}
    (F : Functor |FreeCartesianCategory| D)
    (CCⱽ : CartesianCategoryⱽ D ℓCᴰ ℓCᴰ')
    where
    open CartesianCategoryⱽ CCⱽ

    elimLocalMotive : CartesianCategoryᴰ FreeCartesianCategory ℓCᴰ ℓCᴰ'
    elimLocalMotive = CartesianCategoryⱽ→CartesianCategoryᴰ FreeCartesianCategory
      (CartesianCategoryⱽReindex CCⱽ F)

    elimLocal : (ı : ElimInterpᴰ elimLocalMotive) → Section F Cᴰ
    elimLocal ı = GlobalSectionReindex→Section Cᴰ F (elim elimLocalMotive ı)

  -- Recursion (non-dependent functors)
  module _ (CC : CartesianCategory ℓC ℓC') where
    private
      wkC = weakenCartesianCategory FreeCartesianCategory CC

    rec : (ı : ElimInterpᴰ wkC) → Functor |FreeCartesianCategory| (CC .CartesianCategory.C)
    rec ı = introS⁻ (elim wkC ı)

    -- rec is a cartesian functor: this follows from
    -- elimCartesian strictly preserving binary products.
    recCartesian : (ı : ElimInterpᴰ wkC)
      → CartesianFunctor FreeCartesianCategory (CC .CartesianCategory.C)
    recCartesian ı = rec ı , λ c c' →
      CC .bp (rec ı .F-ob c , rec ı .F-ob c') .universal

    -- Cartesian functors out of the FreeCartesianCategory
    -- are naturally isomorphic to each other
    module _
      {D : Category ℓD ℓD'}
      ((F , F-bp) (G , G-bp) : CartesianFunctor FreeCartesianCategory D)

      -- shouldn't this be part of the definition of CartesianFunctor
      -- i.e. preserves finite prods, not just binary
      (F-1 : Term.preservesTerminal |FreeCartesianCategory| D F)
      (G-1 : Term.preservesTerminal |FreeCartesianCategory| D G)
      where
      private
        F,G-IsoC : Categoryᴰ |FreeCartesianCategory| _ _
        F,G-IsoC = Reindex.reindex (IsoCommaᴰ F G) (Δ |FreeCartesianCategory|)
        module D = Category D

      open isIsoOver

      CCCᴰF,G-IsoC : CartesianCategoryᴰ FreeCartesianCategory _ _
      CCCᴰF,G-IsoC .CartesianCategoryᴰ.Cᴰ = F,G-IsoC
      CCCᴰF,G-IsoC .CartesianCategoryᴰ.termᴰ =
        F⊤≅G⊤ , _ , isUniv
        where
        F⊤ : Terminal D
        F⊤ = _ , F-1 (Terminal'ToTerminal $ FreeCartesianCategory .term)

        F⊤' = terminalToUniversalElement F⊤

        G⊤ : Terminal D
        G⊤ = _ , G-1 (Terminal'ToTerminal $ FreeCartesianCategory .term)

        G⊤' = terminalToUniversalElement G⊤

        module F⊤ = TerminalNotation F⊤'
        module G⊤ = TerminalNotation G⊤'

        F⊤≅G⊤ : CatIso D (F ⟅ ⊤ ⟆) (G ⟅ ⊤ ⟆)
        F⊤≅G⊤ = terminalToIso D F⊤ G⊤

        isUniv : isUniversalᴰ F,G-IsoC _ _
          (FreeCartesianCategory .term) tt
        isUniv Γ Γᴰ .inv _ _ .fst = G⊤.𝟙extensionality
        isUniv Γ Γᴰ .inv _ _ .snd = _
        isUniv Γ Γᴰ .rightInv = λ _ _ → refl
        isUniv Γ Γᴰ .leftInv u v =
          isProp→PathP (λ _ → isPropΣ (D.isSetHom _ _) λ _ → isPropUnit) _ _
      CCCᴰF,G-IsoC .CartesianCategoryᴰ.bpᴰ {A = A}{B = B} f g =
        F×≅G× , ((sym G×.×β₁ , tt) , (sym G×.×β₂ , tt)) , isUniv
        where
        module FCC× = BinProductNotation (FreeCartesianCategory .bp (A , B))
        F× = preservesUniversalElement→UniversalElement
              (preservesBinProdCones F A B)
              (FreeCartesianCategory .bp (A , B)) (F-bp A B)
        G× = preservesUniversalElement→UniversalElement
              (preservesBinProdCones G A B)
              (FreeCartesianCategory .bp (A , B)) (G-bp A B)
        module F× = BinProductNotation F×
        module G× = BinProductNotation G×

        forward = (F×.π₁ D.⋆ f .fst) G×.,p (F×.π₂ D.⋆ g .fst)
        backward = (G×.π₁ D.⋆ f .snd .isIso.inv) F×.,p (G×.π₂ D.⋆ g .snd .isIso.inv)

        F×≅G× : CatIso D _ _
        F×≅G× .fst = forward
        F×≅G× .snd .isIso.inv = backward
        F×≅G× .snd .isIso.sec = G×.,p-extensionality
          (D.⋆Assoc _ _ _
          ∙ D.⟨ refl ⟩⋆⟨ G×.×β₁ ⟩
          ∙ sym (D.⋆Assoc _ _ _)
          ∙ D.⟨ F×.×β₁ ⟩⋆⟨ refl ⟩
          ∙ D.⋆Assoc _ _ _
          ∙ D.⟨ refl ⟩⋆⟨ f .snd .isIso.sec ⟩
          ∙ D.⋆IdR _
          ∙ sym (D.⋆IdL _))
          (D.⋆Assoc _ _ _
          ∙ D.⟨ refl ⟩⋆⟨ G×.×β₂ ⟩
          ∙ sym (D.⋆Assoc _ _ _)
          ∙ D.⟨ F×.×β₂ ⟩⋆⟨ refl ⟩
          ∙ D.⋆Assoc _ _ _
          ∙ D.⟨ refl ⟩⋆⟨ g .snd .isIso.sec ⟩
          ∙ D.⋆IdR _
          ∙ sym (D.⋆IdL _))
        F×≅G× .snd .isIso.ret = F×.,p-extensionality
          (D.⋆Assoc _ _ _
          ∙ D.⟨ refl ⟩⋆⟨ F×.×β₁ ⟩
          ∙ sym (D.⋆Assoc _ _ _)
          ∙ D.⟨ G×.×β₁ ⟩⋆⟨ refl ⟩
          ∙ D.⋆Assoc _ _ _
          ∙ D.⟨ refl ⟩⋆⟨ f .snd .isIso.ret ⟩
          ∙ D.⋆IdR _
          ∙ sym (D.⋆IdL _))
          (D.⋆Assoc _ _ _
          ∙ D.⟨ refl ⟩⋆⟨ F×.×β₂ ⟩
          ∙ sym (D.⋆Assoc _ _ _)
          ∙ D.⟨ G×.×β₂ ⟩⋆⟨ refl ⟩
          ∙ D.⋆Assoc _ _ _
          ∙ D.⟨ refl ⟩⋆⟨ g .snd .isIso.ret ⟩
          ∙ D.⋆IdR _
          ∙ sym (D.⋆IdL _))

        isUniv : isUniversalᴰ F,G-IsoC _ _
          (FreeCartesianCategory .bp (A , B))
          ((sym G×.×β₁ , tt) , (sym G×.×β₂ , tt))
        isUniv Γ Γᴰ .inv (u₁ , u₂) ((sq₁ , _) , (sq₂ , _)) .fst =
          G×.,p-extensionality
            (D.⋆Assoc _ _ _
            ∙ D.⟨ refl ⟩⋆⟨ G×.×β₁ ⟩
            ∙ sym (D.⋆Assoc _ _ _)
            ∙ D.⟨ sym (F .F-seq _ _) ∙ cong (F .F-hom) FCC×.×β₁ ⟩⋆⟨ refl ⟩
            ∙ sq₁
            ∙ D.⟨ refl ⟩⋆⟨ sym (cong (G .F-hom) FCC×.×β₁) ∙ G .F-seq _ _ ⟩
            ∙ sym (D.⋆Assoc _ _ _))
            (D.⋆Assoc _ _ _
            ∙ D.⟨ refl ⟩⋆⟨ G×.×β₂ ⟩
            ∙ sym (D.⋆Assoc _ _ _)
            ∙ D.⟨ sym (F .F-seq _ _) ∙ cong (F .F-hom) FCC×.×β₂ ⟩⋆⟨ refl ⟩
            ∙ sq₂
            ∙ D.⟨ refl ⟩⋆⟨ sym (cong (G .F-hom) FCC×.×β₂) ∙ G .F-seq _ _ ⟩
            ∙ sym (D.⋆Assoc _ _ _))
        isUniv Γ Γᴰ .inv _ _ .snd = tt
        isUniv Γ Γᴰ .rightInv _ _ =
          isProp→PathP (λ _ → isProp×
            (isPropΣ (D.isSetHom _ _) λ _ → isPropUnit)
            (isPropΣ (D.isSetHom _ _) λ _ → isPropUnit)) _ _
        isUniv Γ Γᴰ .leftInv _ _ =
          isProp→PathP (λ _ → isPropΣ (D.isSetHom _ _) λ _ → isPropUnit) _ _

      -- A global section of the IsoComma gives a natural isomorphism
      sectionToNatIso : GlobalSection F,G-IsoC → NatIso F G
      sectionToNatIso S .NatIso.trans .NatTrans.N-ob x = S .F-obᴰ x .fst
      sectionToNatIso S .NatIso.trans .NatTrans.N-hom f = S .F-homᴰ f .fst
      sectionToNatIso S .NatIso.nIso x = S .F-obᴰ x .snd

      module _ (ı : ElimInterpᴰ CCCᴰF,G-IsoC) where
        FreeCartesianCatFunctor≅ : NatIso F G
        FreeCartesianCatFunctor≅ =
          sectionToNatIso (elimCartesian CCCᴰF,G-IsoC ı .CartesianSection.section)
