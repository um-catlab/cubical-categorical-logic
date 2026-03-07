{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Instances.Free.BiCartesianClosedCategory.UncurriedElim where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.BiCartesianClosed.Base

open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Quiver
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Limits.BiCartesianClosedV
open import Cubical.Categories.Displayed.Limits.CartesianSection
open import Cubical.Categories.Displayed.Limits.CartesianClosedSection
open import Cubical.Categories.Displayed.Limits.BiCartesianClosedSection
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Instances.Reindex.Base
open import Cubical.Categories.Displayed.Instances.Reindex.Cartesian
open import Cubical.Categories.Displayed.Instances.Reindex.CartesianClosed
open import Cubical.Categories.Displayed.Instances.Weaken.Base
open import Cubical.Categories.Displayed.Instances.Weaken.UncurriedProperties

private
  variable
    ℓQ ℓQ' ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' : Level

open Section

module _ (Q : +×⇒Quiver ℓQ ℓQ') where
  private
    module Q = +×⇒Quiver Q
    module FreeBCCC = BiCartesianClosedCategory (FreeBiCartesianClosedCategory Q)

  module _ (BCCCᴰ : BiCartesianClosedCategoryᴰ (FreeBiCartesianClosedCategory Q) ℓCᴰ ℓCᴰ') where
    open BiCartesianClosedCategoryᴰ BCCCᴰ

    private
      module initᴰ' = UniversalElementᴰNotation (Cᴰ ^opᴰ) _ _ initᴰ

    module _ (ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]) where
      elimOb : ∀ A → Cᴰ.ob[ A ]
      elimOb (↑ o) = ı-ob o
      elimOb ⊤ = termᴰ .fst
      elimOb ⊥ = initᴰ .fst
      elimOb (A × B) = bpᴰ (elimOb A) (elimOb B) .fst
      elimOb (A + B) = bcpᴰ (elimOb A) (elimOb B) .fst
      elimOb (A ⇒ B) = expᴰ (elimOb A) (elimOb B) .fst

    record Interpᴰ : Type (ℓ-max (ℓ-max ℓQ ℓQ') (ℓ-max ℓCᴰ ℓCᴰ')) where
      constructor interpᴰ
      field
        ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]
        ı-hom : ∀ e → Cᴰ.Hom[ ↑ₑ e ][ elimOb ı-ob (Q.dom e) , elimOb ı-ob (Q.cod e) ]

    module _ (ı : Interpᴰ) where
      open Interpᴰ ı

      elimHom : ∀ {A B} (e : Expr Q A B)
        → Cᴰ.Hom[ e ][ elimOb ı-ob A , elimOb ı-ob B ]
      elimHom (↑ₑ t) = ı-hom t
      elimHom idₑ = Cᴰ.idᴰ
      elimHom (e ⋆ₑ e') = elimHom e Cᴰ.⋆ᴰ elimHom e'
      elimHom (⋆ₑIdL f i) = Cᴰ.⋆IdLᴰ (elimHom f) i
      elimHom (⋆ₑIdR f i) = Cᴰ.⋆IdRᴰ (elimHom f) i
      elimHom (⋆ₑAssoc f g h i) = Cᴰ.⋆Assocᴰ (elimHom f) (elimHom g) (elimHom h) i
      elimHom (isSetExpr f g p q i j) =
        isSetHomᴰ' Cᴰ (elimHom f) (elimHom g) (λ i → elimHom (p i)) (λ i → elimHom (q i)) i j
      -- Terminal
      elimHom !ₑ = termᴰ.introᴰ tt
      elimHom (⊤η f i) = Cᴰ.rectify {e' = ⊤η f} (termᴰ.ηᴰ (elimHom f)) i
      -- Initial
      elimHom absurd = initᴰ'.introᴰ tt
      elimHom (⊥η f i) = Cᴰ.rectify {e' = ⊥η f} (initᴰ'.ηᴰ (elimHom f)) i
      -- Products
      elimHom (π₁ {A}{B}) = bpᴰ.πᴰ₁
      elimHom (π₂ {A}{B}) = bpᴰ.πᴰ₂
      elimHom ⟨ f , g ⟩ = bpᴰ.introᴰ ((elimHom f) , (elimHom g))
      elimHom (×β₁ {Γ}{A}{B}{f}{g} i) = Cᴰ.rectify {e' = ×β₁} (bpᴰ.×βᴰ₁ (elimHom f) (elimHom g)) i
      elimHom (×β₂ {Γ}{A}{B}{f}{g} i) = Cᴰ.rectify {e' = ×β₂} (bpᴰ.×βᴰ₂ (elimHom f) (elimHom g)) i
      elimHom (×η {Γ}{A}{B}{f} i) = Cᴰ.rectify {e' = ×η} (bpᴰ.×ηᴰ (elimHom f)) i
      -- Coproducts
      elimHom (σ₁ {A}{B}) = πᴰ₁
      elimHom (σ₂ {A}{B}) = πᴰ₂
      elimHom [ f , g ] = introᴰ ((elimHom f) , (elimHom g))
      elimHom (+β₁ {t = t} {t' = t'} i) = Cᴰ.rectify {e' = +β₁} (×βᴰ₁ (elimHom t) (elimHom t')) i
      elimHom (+β₂ {t = t} {t' = t'} i) = Cᴰ.rectify {e' = +β₂} (×βᴰ₂ (elimHom t) (elimHom t')) i
      elimHom (+η {t = t} i) = Cᴰ.rectify {e' = +η} (×ηᴰ (elimHom t)) i
      -- Exponentials
      elimHom eval = appᴰ
      elimHom (λ- e) = λᴰ (elimHom e)
      elimHom (λβ e i) = Cᴰ.rectify {e' = λβ e} (Cᴰ.≡out $ ⇒βᴰ (elimHom e)) i
      elimHom (λη e i) = Cᴰ.rectify {e' = λη e} (Cᴰ.≡out $ ⇒ηᴰ (elimHom e)) i

      elim : GlobalSection Cᴰ
      elim .F-obᴰ = elimOb ı-ob
      elim .F-homᴰ = elimHom
      elim .F-idᴰ = refl
      elim .F-seqᴰ = λ _ _ → refl

      elimBiCartesianClosed : BiCartesianClosedSection BCCCᴰ
      elimBiCartesianClosed .BiCartesianClosedSection.cartesianClosedSection
        .CartesianClosedSection.cartesianSection
        .CartesianSection.section = elim
      elimBiCartesianClosed .BiCartesianClosedSection.cartesianClosedSection
        .CartesianClosedSection.cartesianSection
        .CartesianSection.F-obᴰ-⊤ = refl
      elimBiCartesianClosed .BiCartesianClosedSection.cartesianClosedSection
        .CartesianClosedSection.cartesianSection
        .CartesianSection.F-obᴰ-× _ _ = refl
      elimBiCartesianClosed .BiCartesianClosedSection.cartesianClosedSection
        .CartesianClosedSection.F-obᴰ-⇒ _ _ = refl
      elimBiCartesianClosed .BiCartesianClosedSection.F-obᴰ-⊥ = refl
      elimBiCartesianClosed .BiCartesianClosedSection.F-obᴰ-+ _ _ = refl

  module _
    {D : CartesianCategory ℓD ℓD'}
    (F : CartesianFunctor
      (FreeBiCartesianClosedCategory Q .BiCartesianClosedCategory.CCC
        .CartesianClosedCategory.CC)
      (D .CartesianCategory.C))
    (BCCCⱽ : BiCartesianClosedCategoryⱽ D ℓCᴰ ℓCᴰ')
    where
    open BiCartesianClosedCategoryⱽ BCCCⱽ

    private
      F-op : Functor (FreeBCCC.C ^op) (D .CartesianCategory.C ^op)
      F-op .Functor.F-ob = F .fst .Functor.F-ob
      F-op .Functor.F-hom = F .fst .Functor.F-hom
      F-op .Functor.F-id = F .fst .Functor.F-id
      F-op .Functor.F-seq f g = F .fst .Functor.F-seq g f

      opDⱽ : CartesianCategoryⱽ (D .CartesianCategory.C ^op) _ _
      opDⱽ .CartesianCategoryⱽ.Cᴰ = Cᴰ ^opᴰ
      opDⱽ .CartesianCategoryⱽ.termⱽ = initⱽ
      opDⱽ .CartesianCategoryⱽ.bpⱽ = bcpⱽ
      opDⱽ .CartesianCategoryⱽ.cartesianLifts = opcartesianLifts

      reindexedOpⱽ = CartesianCategoryⱽReindex opDⱽ F-op

      reindexedBCCCⱽ : BiCartesianClosedCategoryⱽ FreeBCCC.CC _ _
      reindexedBCCCⱽ .BiCartesianClosedCategoryⱽ.CCCⱽ = CCCⱽReindex CCCⱽ F
      reindexedBCCCⱽ .BiCartesianClosedCategoryⱽ.initⱽ x =
        initⱽ' .fst ,
        pshiso (pshhom (λ y → initⱽ' .snd .PshIso.trans .PshHom.N-ob y)
               (λ _ _ _ _ → refl))
               (initⱽ' .snd .PshIso.nIso)
        where initⱽ' = reindexedOpⱽ .CartesianCategoryⱽ.termⱽ x
      reindexedBCCCⱽ .BiCartesianClosedCategoryⱽ.bcpⱽ x y =
        bcpⱽ' .fst ,
        pshiso (pshhom (λ z → bcpⱽ' .snd .PshIso.trans .PshHom.N-ob z)
                       λ c c' f p → bcpⱽ' .snd .PshIso.trans .PshHom.N-hom c c' f p)
               (bcpⱽ' .snd .PshIso.nIso)
        where bcpⱽ' = reindexedOpⱽ .CartesianCategoryⱽ.bpⱽ x y
      reindexedBCCCⱽ .BiCartesianClosedCategoryⱽ.opcartesianLifts x y z =
        opcartlift' .fst ,
        pshiso (pshhom (λ y → opcartlift' .snd .PshIso.trans .PshHom.N-ob y)
                       (λ c c' f p → opcartlift' .snd .PshIso.trans .PshHom.N-hom c c' f p))
                (opcartlift' .snd .PshIso.nIso)
        where opcartlift' = reindexedOpⱽ .CartesianCategoryⱽ.cartesianLifts x y z

    elimLocalMotive : BiCartesianClosedCategoryᴰ (FreeBiCartesianClosedCategory Q) _ _
    elimLocalMotive = BiCartesianClosedCategoryⱽ→BiCartesianClosedCategoryᴰ
      (FreeBiCartesianClosedCategory Q) reindexedBCCCⱽ

    elimLocal : (ı : Interpᴰ elimLocalMotive) → Section (F .fst) Cᴰ
    elimLocal ı = GlobalSectionReindex→Section _ _ (elim elimLocalMotive ı)

  module _ (BCCC : BiCartesianClosedCategory ℓC ℓC') where
    private
      wkC = weakenBCCC (FreeBiCartesianClosedCategory Q) BCCC
      module BCCC' = BiCartesianClosedCategory BCCC

    rec : (ı : Interpᴰ wkC) → Functor FreeBCCC.C BCCC'.C
    rec ı = introS⁻ (elim wkC ı)
