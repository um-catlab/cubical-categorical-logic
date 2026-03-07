{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Instances.Free.CartesianCategory.UncurriedElim where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Unit

open import
  Cubical.Categories.Instances.Free.CartesianCategory.ProductQuiver
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Morphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Terminal as Term
open import Cubical.Categories.Limits.Terminal.More as Term
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.Reindex

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties

open import Cubical.Categories.Displayed.Instances.Reindex.Base as Reindex
open import Cubical.Categories.Displayed.Instances.Reindex.Cartesian
open import Cubical.Categories.Displayed.Instances.Weaken.Base
open import Cubical.Categories.Displayed.Instances.Weaken.UncurriedProperties
open import Cubical.Categories.Displayed.Instances.Comma
open import Cubical.Categories.Displayed.Limits.CartesianSection
open import Cubical.Categories.Displayed.BinProduct

open import Cubical.Categories.Instances.Free.CartesianCategory.Base
open import Cubical.Categories.Instances.Free.CartesianCategory.ProductQuiver

private
  variable
    ℓQ ℓQ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Functor
open Section
open PshHom
open PshIso

module _ (Q : ×Quiver ℓQ ℓQ') where
  private module Q = ×Quiver Q
  module _
    (CCᴰ : CartesianCategoryᴰ (FreeCartesianCategory Q) ℓCᴰ ℓCᴰ')
    where
    open CartesianCategoryᴰ CCᴰ
    open UniversalElementᴰNotation
    module _ (ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]) where
      elimOb : ∀ A → Cᴰ.ob[ A ]
      elimOb (↑ o) = ı-ob o
      elimOb (A × B) = bpᴰ (elimOb A) (elimOb B) .fst
      elimOb ⊤ = termᴰ .fst

    record Interpᴰ : Type (ℓ-max (ℓ-max ℓQ ℓQ') (ℓ-max ℓCᴰ ℓCᴰ')) where
      constructor mkInterpᴰ
      field
        ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]
        ı-hom : ∀ e
          → Cᴰ.Hom[ ↑ₑ e ][ elimOb ı-ob (Q.dom e) , elimOb ı-ob (Q.cod e) ]

    module _ (ı : Interpᴰ) where
      open Interpᴰ ı
      elimHom : ∀ {A A'} (f : |FreeCartesianCategory| Q [ A , A' ]) →
        Cᴰ [ f ][ elimOb ı-ob A , elimOb ı-ob A' ]
      elimHom (↑ₑ t) = ı-hom t
      elimHom idₑ = Cᴰ.idᴰ
      elimHom (f ⋆ₑ g) = elimHom f Cᴰ.⋆ᴰ elimHom g
      elimHom (⋆ₑIdL f i) = Cᴰ.⋆IdLᴰ (elimHom f) i
      elimHom (⋆ₑIdR f i) = Cᴰ.⋆IdRᴰ (elimHom f) i
      elimHom (⋆ₑAssoc f g h i) = Cᴰ.⋆Assocᴰ (elimHom f) (elimHom g) (elimHom h) i
      elimHom (isSetExp f g p q i j) =
        isSetHomᴰ' Cᴰ (elimHom f) (elimHom g) (λ i → elimHom (p i)) (λ i → elimHom (q i)) i j
      elimHom !ₑ = termᴰ.introᴰ tt
      elimHom (⊤η f i) = Cᴰ.rectify {e' = ⊤η f} (termᴰ.ηᴰ (elimHom f)) i
      elimHom (π₁ {A}{B}) = bpᴰ.πᴰ₁
      elimHom (π₂ {A}{B}) = bpᴰ.πᴰ₂
      elimHom ⟨ f , g ⟩ = bpᴰ.introᴰ ((elimHom f) , (elimHom g))
      -- these rectifies are I think because universalElement is based on equiv not iso
      elimHom (×β₁ {Γ}{A}{B}{f}{g} i) = Cᴰ.rectify {e' = ×β₁} (bpᴰ.×βᴰ₁ (elimHom f) (elimHom g)) i
      elimHom (×β₂ {Γ}{A}{B}{f}{g} i) = Cᴰ.rectify {e' = ×β₂} (bpᴰ.×βᴰ₂ (elimHom f) (elimHom g)) i
      elimHom (×η {Γ}{A}{B}{f} i) = Cᴰ.rectify {e' = ×η} (bpᴰ.×ηᴰ (elimHom f)) i

      elim : GlobalSection Cᴰ
      elim .F-obᴰ = elimOb ı-ob
      elim .F-homᴰ = elimHom
      elim .F-idᴰ = refl
      elim .F-seqᴰ = λ _ _ → refl

      elimCartesian : CartesianSection CCᴰ
      elimCartesian .CartesianSection.section = elim
      elimCartesian .CartesianSection.F-obᴰ-⊤ = refl
      elimCartesian .CartesianSection.F-obᴰ-× _ _ = refl

  module _
    {D : Category ℓD ℓD'}
    (F : Functor (|FreeCartesianCategory| Q) D)
    (CCⱽ : CartesianCategoryⱽ D ℓCᴰ ℓCᴰ')
    where
    open CartesianCategoryⱽ CCⱽ

    elimLocalMotive : CartesianCategoryᴰ (FreeCartesianCategory Q) ℓCᴰ ℓCᴰ'
    elimLocalMotive = CartesianCategoryⱽ→CartesianCategoryᴰ (FreeCartesianCategory Q)
      (CartesianCategoryⱽReindex CCⱽ F)

    elimLocal : (ı : Interpᴰ elimLocalMotive) → Section F Cᴰ
    elimLocal ı = GlobalSectionReindex→Section Cᴰ F (elim elimLocalMotive ı)

  module _ (CC : CartesianCategory ℓC ℓC') where
    private
      wkC = weakenCartesianCategory (FreeCartesianCategory Q) CC
    -- TODO: rec preserves finite products, should follow from
    -- properties of weaken/elim preserved displayed fin products
    rec : (ı : Interpᴰ wkC) → Functor (|FreeCartesianCategory| Q) (CC .CartesianCategory.C)
    rec ı = introS⁻ (elim wkC ı)

  -- Cartesian functors out of the FreeCartesianCategory
  -- are naturally isomorphic to each other
  module _
    {D : Category ℓD ℓD'}
    ((F , F-bp) (G , G-bp) : CartesianFunctor (FreeCartesianCategory Q) D)
    (F-1 : Term.preservesTerminal (|FreeCartesianCategory| Q) D F)
    (G-1 : Term.preservesTerminal (|FreeCartesianCategory| Q) D G)
    where
    private
      F,G-IsoC : Categoryᴰ (|FreeCartesianCategory| Q) _ _
      F,G-IsoC = Reindex.reindex (IsoCommaᴰ F G) (Δ (|FreeCartesianCategory| Q))
      module D = Category D

    open isIsoOver

    CCCᴰF,G-IsoC : CartesianCategoryᴰ (FreeCartesianCategory Q) _ _
    CCCᴰF,G-IsoC .CartesianCategoryᴰ.Cᴰ = F,G-IsoC
    CCCᴰF,G-IsoC .CartesianCategoryᴰ.termᴰ =
      F⊤≅G⊤ , _ , isUniv
      where
      F⊤ : Terminal D
      F⊤ = _ , F-1 (Terminal'ToTerminal $ FreeCartesianCategory Q .CartesianCategory.term)

      F⊤' = terminalToUniversalElement F⊤

      G⊤ : Terminal D
      G⊤ = _ , G-1 (Terminal'ToTerminal $ FreeCartesianCategory Q .CartesianCategory.term)

      G⊤' = terminalToUniversalElement G⊤

      module F⊤ = TerminalNotation F⊤'
      module G⊤ = TerminalNotation G⊤'

      F⊤≅G⊤ : CatIso D (F ⟅ ⊤ ⟆) (G ⟅ ⊤ ⟆)
      F⊤≅G⊤ = terminalToIso D F⊤ G⊤

      isUniv : isUniversalᴰ F,G-IsoC _ _
        (FreeCartesianCategory Q .CartesianCategory.term) tt
      isUniv Γ Γᴰ .inv _ _ .fst = G⊤.𝟙extensionality
      isUniv Γ Γᴰ .inv _ _ .snd = _
      isUniv Γ Γᴰ .rightInv = λ _ _ → refl
      isUniv Γ Γᴰ .leftInv u v =
        isProp→PathP (λ _ → isPropΣ (D.isSetHom _ _) λ _ → isPropUnit) _ _
    CCCᴰF,G-IsoC .CartesianCategoryᴰ.bpᴰ {A = A}{B = B} f g =
      F×≅G× , ((sym G×.×β₁ , tt) , (sym G×.×β₂ , tt)) , isUniv
      where
      module FCC× = BinProductNotation
        (FreeCartesianCategory Q .CartesianCategory.bp (A , B))
      F× = preservesUniversalElement→UniversalElement
            (preservesBinProdCones F A B)
            (FreeCartesianCategory Q .CartesianCategory.bp (A , B))
            (F-bp A B)
      G× = preservesUniversalElement→UniversalElement
            (preservesBinProdCones G A B)
            (FreeCartesianCategory Q .CartesianCategory.bp (A , B))
            (G-bp A B)
      module F× = BinProductNotation F×
      module G× = BinProductNotation G×

      forward = (F×.π₁ D.⋆ f .fst) G×.,p (F×.π₂ D.⋆ g .fst)
      backward = (G×.π₁ D.⋆ f .snd .isIso.inv) F×.,p
        (G×.π₂ D.⋆ g .snd .isIso.inv)

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
        (FreeCartesianCategory Q .CartesianCategory.bp (A , B))
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

    module _ (ı : Interpᴰ CCCᴰF,G-IsoC) where
      FreeCartesianCatFunctor≅ : NatIso F G
      FreeCartesianCatFunctor≅ =
        sectionToNatIso (elimCartesian CCCᴰF,G-IsoC ı .CartesianSection.section)
