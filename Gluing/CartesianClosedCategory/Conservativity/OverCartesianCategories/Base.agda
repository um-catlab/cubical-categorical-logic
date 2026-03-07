{-# OPTIONS --lossy-unification #-}
module Gluing.CartesianClosedCategory.Conservativity.OverCartesianCategories.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure hiding (⟨_⟩)
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Quiver.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.More
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.Terminal as Term
open import Cubical.Categories.Limits.Terminal.More as Term

open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Free.CartesianCategory.Base as FCC
open import Cubical.Categories.Instances.Free.CartesianCategory.UncurriedElim as FCC
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Base as FCCC
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.UncurriedElim as FCCC
open import
  Cubical.Categories.Instances.Free.CartesianCategory.ProductQuiver
  hiding (_×_)
open import
  Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
  hiding (_×_)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Limits.CartesianV' as V'
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
import Cubical.Categories.Displayed.Instances.Terminal.Base as Unitᴰ
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base
open import Cubical.Categories.Displayed.Instances.Arrow.Base
open import Cubical.Categories.Displayed.Instances.Presheaf.Eq.Base as PshBase
  using (PRESHEAFᴰ; PSHAssoc; PSHIdL; PSHπ₁NatEq; PSH×aF-seq)
open import Cubical.Categories.Displayed.Instances.Presheaf.Eq.Cartesian
open import Cubical.Categories.Displayed.Instances.Presheaf.Eq.CartesianClosed
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianClosedV
  using (EqCCCⱽ→CCCⱽ)
open import Cubical.Categories.Displayed.Instances.PropertyOver
open import Cubical.Categories.Displayed.Instances.PropertyOver.Cartesian
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.StrictHom hiding (π₁; π₂)
open import Cubical.Categories.Presheaf.Nerve
open import Cubical.Categories.Presheaf.Constructions.BinProduct.Base using (_×Psh_)
open import Cubical.Categories.Limits.BinProduct.More

private
  variable ℓQ ℓQ' : Level

open Category
open Functor
open Categoryᴰ
open Section
open PshHomStrict
open PshHom

module _ (Q : Quiver ℓQ ℓQ') where
  private
    module Q = QuiverOver (Q .snd)
    ×Q = Quiver→×Quiver Q
    module ×Q = ×Quiver ×Q
    ×⇒Q = Quiver→×⇒Quiver Q
    module ×⇒Q = ×⇒Quiver ×⇒Q

  FREE-1,× : CartesianCategory _ _
  FREE-1,× = FreeCartesianCategory (Quiver→×Quiver Q)

  private
    module FREE-1,× = CartesianCategory FREE-1,×

  FREE-1,×,⇒ : CartesianClosedCategory _ _
  FREE-1,×,⇒ = FreeCartesianClosedCategory ×⇒Q

  private
    module FREE-1,×,⇒ = CartesianClosedCategory FREE-1,×,⇒
    ℓ = ℓ-max ℓQ ℓQ'

  ⊆ : Functor FREE-1,×.C FREE-1,×,⇒.C
  ⊆ = FCC.rec ×Q FREE-1,×,⇒.CC
    (mkInterpᴰ (λ o → CCCExpr.↑ o) (λ f → ↑ₑ f))

  extension : Functor FREE-1,×,⇒.C (PRESHEAF FREE-1,×.C _)
  extension = FCCC.rec ×⇒Q (CCC-PRESHEAF FREE-1,×.C (ℓ-max ℓQ ℓQ'))
    (interpᴰ (λ o → YOStrict ⟅ ProdExpr.↑ o ⟆)
             (λ f → YOStrict ⟪ ↑ₑ f ⟫))

  YO≅ext⊆ : NatIso YOStrict (extension ∘F ⊆)
  YO≅ext⊆ = FCC.FreeCartesianCatFunctor≅ ×Q
      (YOStrict , YOStrict-pres-bp FREE-1,×.bp)
      (extension ∘F ⊆ , ext-⊆-bp)
      yo-pres-terminal
      ext-⊆-pres-terminal
      (mkInterpᴰ (λ o → PRESHEAF FREE-1,×.C _ .Category.id , idCatIso .snd) (λ e → refl , tt))
    where
    PSH-bp = Cartesian-PRESHEAF FREE-1,×.C (ℓ-max ℓQ ℓQ') .CartesianCategory.bp

    ext-⊆-bp : preservesProvidedBinProducts (extension ∘F ⊆)
      FREE-1,×.bp
    ext-⊆-bp c c' =
      PSH-bp ((extension ∘F ⊆) .F-ob c , (extension ∘F ⊆) .F-ob c') .UniversalElement.universal

    FCC⊤ : Terminal FREE-1,×.C
    FCC⊤ = Terminal'ToTerminal (FreeCartesianCategory ×Q .CartesianCategory.term)

    yo-pres-terminal : preservesTerminal FREE-1,×.C (PRESHEAF FREE-1,×.C _) YOStrict
    yo-pres-terminal = preserveOnePreservesAll FREE-1,×.C (PRESHEAF FREE-1,×.C _) YOStrict FCC⊤
      λ P → theHom P , unique P
      where
      module FCC⊤ = TerminalNotation (terminalToUniversalElement FCC⊤)
      theHom : ∀ P → PshHomStrict P (YOStrict ⟅ FCC⊤ .fst ⟆)
      theHom P .N-ob c _ = FCC⊤.!t
      theHom P .N-hom c c' f p' p e = FCC⊤.𝟙extensionality
      unique : ∀ P → (f : PshHomStrict P (YOStrict ⟅ FCC⊤ .fst ⟆)) → theHom P ≡ f
      unique P f = makePshHomStrictPath (funExt₂ λ c p → FCC⊤.𝟙extensionality)

    ext-⊆-pres-terminal : preservesTerminal FREE-1,×.C (PRESHEAF FREE-1,×.C _) (extension ∘F ⊆)
    ext-⊆-pres-terminal = preserveOnePreservesAll FREE-1,×.C (PRESHEAF FREE-1,×.C _) (extension ∘F ⊆) FCC⊤
      λ P → theHom P , unique P
      where
      theHom : ∀ P → PshHomStrict P ((extension ∘F ⊆) ⟅ FCC⊤ .fst ⟆)
      theHom P .N-ob c _ = tt*
      theHom P .N-hom c c' f p' p e = refl
      unique : ∀ P → (f : PshHomStrict P ((extension ∘F ⊆) ⟅ FCC⊤ .fst ⟆)) → theHom P ≡ f
      unique P f = makePshHomStrictPath (funExt₂ λ c p → refl)

  ⊆-Faithful : isFaithful ⊆
  ⊆-Faithful =
    isFaithful-GF→isFaithful-F ⊆ extension (isFaithful≅ (symNatIso YO≅ext⊆) isFaithfulYOStrict)

  nerve : Functor FREE-1,×,⇒.C (PRESHEAF FREE-1,×.C ℓ)
  nerve = Nerve ⊆

  private
    FREE-1,×ᴰ : Categoryᴰ FREE-1,×.C ℓ-zero ℓ-zero
    FREE-1,×ᴰ = Unitᴰ.Unitᴰ FREE-1,×.C

    PSHᴰ = PRESHEAFᴰ FREE-1,×ᴰ ℓ ℓ

    module PSHᴰ = Categoryᴰ PSHᴰ

    PSH-CC : CartesianCategory (ℓ-max (ℓ-max ℓQ ℓQ') (ℓ-suc ℓ)) (ℓ-max (ℓ-max ℓQ ℓQ') ℓ)
    PSH-CC = Cartesian-PRESHEAF FREE-1,×.C ℓ

    PSHᴰCᴰ : Categoryᴰ (PRESHEAF FREE-1,×.C ℓ) _ _
    PSHᴰCᴰ = V'.CartesianCategoryⱽ.Cᴰ (EqCCⱽ→CCⱽ PSHAssoc PSHᴰ isCartesianⱽPSHᴰ)

    PSHᴰCartesianClosedⱽ : CartesianClosedCategoryⱽ PSH-CC
      (ℓ-max (ℓ-max ℓQ ℓQ') (ℓ-suc ℓ)) (ℓ-max (ℓ-max ℓQ ℓQ') ℓ)
    PSHᴰCartesianClosedⱽ = CCCⱽPSHᴰ {Cᴰ = FREE-1,×ᴰ}

    nerve-pres-bp : preservesProvidedBinProducts nerve (FREE-1,×,⇒.CC .CartesianCategory.bp)
    nerve-pres-bp = Nerve-pres-bp ⊆ (FREE-1,×,⇒.CC .CartesianCategory.bp)

  -- Displayed presheaf tracking fullness witnesses for base objects
  OB : (o : Q .fst) → PSHᴰ.ob[ nerve ⟅ ⊆ ⟅ ProdExpr.↑ o ⟆ ⟆ ]
  OB o .F-ob (o' , _ , f) =
    (Σ[ g ∈ FREE-1,×.C [ o' , ProdExpr.↑ o ] ] ⊆ ⟪ g ⟫ ≡ f) ,
    isSetΣ (FREE-1,×.C .isSetHom)
      (λ _ → isSet→isGroupoid (FREE-1,×,⇒.C .isSetHom) _ _)
  OB o .F-hom {x = o' , _ , f} {y = o'' , _ , f'} (h , _ , eq) (g , p) =
    h FREE-1,×.⋆ g ,
    ⊆ .F-seq h g ∙ cong (λ x → ⊆ ⟪ h ⟫ ⋆⟨ FREE-1,×,⇒.C ⟩ x) p ∙ Eq.eqToPath eq
  OB o .F-id = funExt λ (g , p) → ΣPathP (FREE-1,×.⋆IdL _ ,
    isSet→SquareP (λ _ _ → FREE-1,×,⇒.C .isSetHom) _ _ _ _)
  OB o .F-seq _ _ = funExt λ _ → ΣPathP (FREE-1,×.⋆Assoc _ _ _ ,
    isSet→SquareP (λ _ _ → FREE-1,×,⇒.C .isSetHom) _ _ _ _)

  HOM : (e : Q.mor) →
    PSHᴰ.Hom[ nerve ⟪ ⊆ ⟪ ↑ₑ e ⟫ ⟫ ][ OB (Q.dom e) , OB (Q.cod e) ]
  HOM e .N-ob (o , _ , f) (g , p) =
    (g FREE-1,×.⋆ (↑ₑ e)) ,
    ⊆ .F-seq g (↑ₑ e)
    ∙ cong (λ x → x FREE-1,×,⇒.⋆ ⊆ ⟪ ↑ₑ e ⟫) p
  HOM e .N-hom (o , _ , f) (o' , _ , f') (h , _ , eq) (g , p) =
    ΣPathP (FREE-1,×.⋆Assoc _ _ _ ,
      isSet→SquareP (λ _ _ → FREE-1,×,⇒.isSetHom) _ _ _ _)

  S : Section nerve PSHᴰCᴰ
  S = FCCC.elimLocal ×⇒Q (nerve , nerve-pres-bp) PSHᴰCartesianClosedⱽ
       (interpᴰ OB HOM)

  -- Helper: construct element of S .F-obᴰ for any expression at a point given by a CC morphism
  -- This is needed to handle product domains
  mkElem : (o Γ : ×Q.Expr) (g : FREE-1,×.C [ Γ , o ])
         → S .F-obᴰ (⊆ ⟅ o ⟆) .F-ob (Γ , tt , ⊆ ⟪ g ⟫) .fst
  mkElem (ProdExpr.↑ x) Γ g = g , refl
  mkElem ProdExpr.⊤ Γ g = tt*
  mkElem (l ProdExpr.× r) Γ g =
    mkElem l Γ (g FREE-1,×.⋆ π₁) , mkElem r Γ (g FREE-1,×.⋆ π₂)

  private
    RetrTy : ×Q.Expr → Type _
    RetrTy y =
      ∀ x → (f : FREE-1,×,⇒.C [ ⊆ ⟅ x ⟆ , ⊆ ⟅ y ⟆ ]) →
        Σ[ g ∈ FREE-1,×.C [ x , y ] ] ⊆ ⟪ g ⟫ ≡ f

    RetrTyCCᴰ : CartesianCategoryᴰ FREE-1,× _ _
    RetrTyCCᴰ = CartesianPropertyOver RetrTy
      retr⊤
      (retr× _ _)
      where
        retr⊤ : RetrTy FREE-1,×.𝟙ue.vertex
        retr⊤ o f = !ₑ , sym (⊤η f)
        retr× : (A B : FREE-1,×.ob) → RetrTy A → RetrTy B → RetrTy (FREE-1,×.×ue.vertex A B)
        retr× A B fullA fullB o f =
          ⟨ fullAf1 .fst , fullBf2 .fst ⟩
          , cong₂ ⟨_,_⟩ (fullAf1 .snd) (fullBf2 .snd) ∙ sym ×η
          where
            fullAf1 = fullA o (f FREE-1,×,⇒.⋆ π₁)
            fullBf2 = fullB o (f FREE-1,×,⇒.⋆ π₂)

    fullSection : GlobalSection (PropertyOver FREE-1,×.C RetrTy)
    fullSection = FCC.elim ×Q RetrTyCCᴰ
      (mkInterpᴰ baseFullness (λ _ → tt))
      where
      baseFullness : ∀ y → RetrTy (ProdExpr.↑ y)
      baseFullness y o f = (witness .fst) , (witness .snd ∙ FREE-1,×,⇒.⋆IdL _)
        where
        elem = mkElem o o FREE-1,×.id
        witness = S .F-homᴰ f .N-ob (o , tt , FREE-1,×,⇒.id) elem

  ⊆-Full : isFull ⊆
  ⊆-Full x y f = ∣ (fullSection .F-obᴰ y x f) ∣₁

  ⊆-FullyFaithful : isFullyFaithful ⊆
  ⊆-FullyFaithful = isFull+Faithful→isFullyFaithful {F = ⊆} ⊆-Full ⊆-Faithful
