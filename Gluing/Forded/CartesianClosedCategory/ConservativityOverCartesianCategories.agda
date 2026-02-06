{-# OPTIONS --lossy-unification #-}
module Gluing.Forded.CartesianClosedCategory.ConservativityOverCartesianCategories where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Quiver.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base

open import Cubical.Categories.Constructions.Free.Category.Forded as FC
open import Cubical.Categories.Constructions.Free.CartesianCategory.Forded as FCC
open import Cubical.Categories.Constructions.Free.CartesianClosedCategory.Forded as FCCC
open import
  Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
  hiding (_×_)
open import
  Cubical.Categories.Constructions.Free.CartesianClosedCategory.Quiver
  hiding (_×_)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Limits.CartesianV' as V'
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
import Cubical.Categories.Displayed.Instances.Terminal.Base as Unitᴰ
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base
  hiding (PRESHEAFᴰ)
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Presheaves.Base as PshBase
  using (PRESHEAFᴰ; PSHAssoc; PSHIdL; PSHπ₁NatEq; PSH×aF-seq)
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Presheaves.Cartesian
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Presheaves.CartesianClosed
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianClosedV
  using (EqCCCⱽ→CCCⱽ)
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.StrictHom
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

--   ı : FC.Interp Q FREE-1,×,⇒.C
--   ı .HetQG._$g_ = ↑_
--   ı .HetQG._<$g>_ = FCCC.↑ₑ ×⇒Q

  ⊆ : Functor FREE-1,×.C FREE-1,×,⇒.C
  ⊆ = FCC.rec ×Q FREE-1,×,⇒.CC
    (mkElimInterpᴰ (λ o → CCCExpr.↑ o) (λ f → FCCC.↑ₑ ×⇒Q f))

  extension : Functor FREE-1,×,⇒.C (PRESHEAF FREE-1,×.C _)
  extension = FCCC.rec ×⇒Q (CCC-PRESHEAF FREE-1,×.C (ℓ-max ℓQ ℓQ'))
    (mkElimInterpᴰ (λ o → YOStrict ⟅ ProdExpr.↑ o ⟆)
                   (λ f → YOStrict ⟪ FCC.↑ₑ ×Q f ⟫))

  -- Both YOStrict and extension ∘F ⊆ agree on generators by construction.
  -- We prove this using the uniqueness property of product-preserving functors
  -- out of the free cartesian category.
  --
  -- Key insight: Two product-preserving functors F, G : FreeCC → D are equal
  -- if they agree on base objects and base morphisms. This follows from the
  -- universal property of the free cartesian category.
  commutes : YOStrict ≡ extension ∘F ⊆
  commutes = Functor≡ F-ob≡ F-hom≡ where
    module PSH = Category (PRESHEAF FREE-1,×.C ℓ)

    -- Object equality by recursion on ProdExpr
    -- Both YOStrict and (extension ∘F ⊆) preserve products strictly
    F-ob≡ : ∀ o → YOStrict ⟅ o ⟆ ≡ extension ⟅ ⊆ ⟅ o ⟆ ⟆
    F-ob≡ (ProdExpr.↑ x) = refl  -- agree on generators by definition
    F-ob≡ ProdExpr.⊤ = refl      -- both preserve terminal
    F-ob≡ (l ProdExpr.× r) = cong₂ _×Psh_ (F-ob≡ l) (F-ob≡ r)  -- both preserve products

    -- Morphism equality by recursion on Exp
    -- Since hom-types are sets, use isSet→SquareP for HIT path constructors
    F-hom≡ : ∀ {A B} (f : FREE-1,×.C [ A , B ]) →
      PathP (λ i → PSH.Hom[ F-ob≡ A i , F-ob≡ B i ])
            (YOStrict ⟪ f ⟫) (extension ⟪ ⊆ ⟪ f ⟫ ⟫)
    -- Base case: generators
    F-hom≡ (genₑ t Eq.refl Eq.refl) = refl
    -- Category structure
    F-hom≡ (idₑ Eq.refl) = refl
    F-hom≡ (f ⋆ₑ g) =
      compPathP' {B = λ i → PSH.Hom[ F-ob≡ _ i , F-ob≡ _ i ]} (F-hom≡ f) (F-hom≡ g)
    F-hom≡ (⋆ₑIdL f i) = isSet→SquareP (λ _ _ → PSH.isSetHom) _ _ _ _ i
    F-hom≡ (⋆ₑIdR f i) = isSet→SquareP (λ _ _ → PSH.isSetHom) _ _ _ _ i
    F-hom≡ (⋆ₑAssoc f g h i) = isSet→SquareP (λ _ _ → PSH.isSetHom) _ _ _ _ i
    F-hom≡ (isSetExp f g p q i j) = isSet→SquareP
      (λ _ _ → isOfHLevelPathP' 2 PSH.isSetHom _ _)
      (λ k → F-hom≡ (p k)) (λ k → F-hom≡ (q k))
      (λ k → F-hom≡ f) (λ k → F-hom≡ g) i j
    -- Terminal structure
    F-hom≡ (!ₑ Eq.refl) = refl
    F-hom≡ (⊤η Eq.refl t i) = isSet→SquareP (λ _ _ → PSH.isSetHom) _ _ _ _ i
    -- Product structure
    F-hom≡ (π₁ Eq.refl Eq.refl) = refl
    F-hom≡ (π₂ Eq.refl Eq.refl) = refl
    F-hom≡ (⟨ f , g ⟩ Eq.refl) =
      cong₂ ×PshIntroStrict (F-hom≡ f) (F-hom≡ g)
    F-hom≡ (×β₁ i) = isSet→SquareP (λ _ _ → PSH.isSetHom) _ _ _ _ i
    F-hom≡ (×β₂ i) = isSet→SquareP (λ _ _ → PSH.isSetHom) _ _ _ _ i
    F-hom≡ (×η Eq.refl t i) = isSet→SquareP (λ _ _ → PSH.isSetHom) _ _ _ _ i

  comp-Faithful : isFaithful (extension ∘F ⊆)
  comp-Faithful = subst isFaithful commutes isFaithfulYOStrict

  -- TODO move this
  module _ {ℓA ℓA' ℓB ℓB' ℓC ℓC'}
    {A : Category ℓA ℓA'}{B : Category ℓB ℓB'}{C : Category ℓC ℓC'}
    (F : Functor A B)(G : Functor B C) where
    isFaithful-GF→isFaithful-F : isFaithful (G ∘F F) → isFaithful F
    isFaithful-GF→isFaithful-F faith x y f g p =
      faith x y f g (congS (λ Ff → G ⟪ Ff ⟫) p)

  ⊆-Faithful : isFaithful ⊆
  ⊆-Faithful = isFaithful-GF→isFaithful-F ⊆ extension comp-Faithful

  nerve : Functor FREE-1,×,⇒.C (PRESHEAF FREE-1,×.C ℓ)
  nerve = reindPshFStrict ⊆ ∘F YOStrict

  private
    FREE-1,×ᴰ : Categoryᴰ FREE-1,×.C ℓ-zero ℓ-zero
    FREE-1,×ᴰ = Unitᴰ.Unitᴰ FREE-1,×.C

    PSHᴰ = PRESHEAFᴰ FREE-1,×ᴰ ℓ ℓ

    module PSHᴰ = Categoryᴰ PSHᴰ

    PSH-CC : CartesianCategory (ℓ-max (ℓ-max ℓQ ℓQ') (ℓ-suc ℓ)) (ℓ-max (ℓ-max ℓQ ℓQ') ℓ)
    PSH-CC = Cartesian-PRESHEAF FREE-1,×.C ℓ

    PSHᴰCartesianⱽEq : isCartesianⱽ PSHAssoc PSHᴰ
    PSHᴰCartesianⱽEq = isCartesianⱽPSHᴰ

    PSHᴰCartesianⱽ : V'.CartesianCategoryⱽ (PRESHEAF FREE-1,×.C ℓ) _ _
    PSHᴰCartesianⱽ = EqCCⱽ→CCⱽ PSHAssoc PSHᴰ PSHᴰCartesianⱽEq

    PSHᴰCᴰ : Categoryᴰ (PRESHEAF FREE-1,×.C ℓ) _ _
    PSHᴰCᴰ = V'.CartesianCategoryⱽ.Cᴰ PSHᴰCartesianⱽ

    PSHᴰCartesianClosedⱽ : CartesianClosedCategoryⱽ PSH-CC
      (ℓ-max (ℓ-max ℓQ ℓQ') (ℓ-suc ℓ)) (ℓ-max (ℓ-max ℓQ ℓQ') ℓ)
    PSHᴰCartesianClosedⱽ = CCCⱽPSHᴰ {Cᴰ = FREE-1,×ᴰ}

    -- nerve preserves products because the universal property of products in
    -- FREE-1,×,⇒.C transfers pointwise to the presheaf category
    nerve-pres-bp : preservesProvidedBinProducts nerve (FREE-1,×,⇒.CC .CartesianCategory.bp)
    nerve-pres-bp A B Γ = isoToIsEquiv the-iso
      where
      open Iso
      module bp = BinProductNotation (FREE-1,×,⇒.CC .CartesianCategory.bp (A , B))
      pairHom : PshHomStrict Γ (nerve ⟅ A ⟆) → PshHomStrict Γ (nerve ⟅ B ⟆)
              → PshHomStrict Γ (nerve ⟅ bp.vert ⟆)
      pairHom α β .N-ob c x = α .N-ob c x bp.,p β .N-ob c x
      pairHom α β .N-hom c c' f x' x eq =
        sym (bp.,p≡
          (sym (α .N-hom c c' f x' x eq)
           ∙ cong (λ g → ⊆ ⟪ f ⟫ ⋆⟨ FREE-1,×,⇒.C ⟩ g) (sym bp.×β₁)
           ∙ sym (FREE-1,×,⇒.C .⋆Assoc _ _ _))
          (sym (β .N-hom c c' f x' x eq)
           ∙ cong (λ g → ⊆ ⟪ f ⟫ ⋆⟨ FREE-1,×,⇒.C ⟩ g) (sym bp.×β₂)
           ∙ sym (FREE-1,×,⇒.C .⋆Assoc _ _ _)))

      the-iso : Iso (PshHomStrict Γ (nerve ⟅ bp.vert ⟆))
                    (PshHomStrict Γ (nerve ⟅ A ⟆) × PshHomStrict Γ (nerve ⟅ B ⟆))
      the-iso .fun f = f ⋆PshHomStrict nerve ⟪ bp.π₁ ⟫ , f ⋆PshHomStrict nerve ⟪ bp.π₂ ⟫
      the-iso .inv (α , β) = pairHom α β
      the-iso .sec (α , β) = ΣPathP
        ( makePshHomStrictPath (funExt₂ λ c x → bp.×β₁)
        , makePshHomStrictPath (funExt₂ λ c x → bp.×β₂))
      the-iso .ret f = makePshHomStrictPath (funExt₂ λ c x →
        bp.,p-extensionality bp.×β₁ bp.×β₂)

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
    PSHᴰ.Hom[ nerve ⟪ ⊆ ⟪ FCC.↑ₑ ×Q e ⟫ ⟫ ][ OB (Q.dom e) , OB (Q.cod e) ]
  HOM e .N-ob (o , _ , f) (g , p) =
    (g FREE-1,×.⋆ genₑ e Eq.refl Eq.refl) ,
    ⊆ .F-seq g (genₑ e Eq.refl Eq.refl)
    ∙ cong (λ x → x FREE-1,×,⇒.⋆ ⊆ ⟪ genₑ e Eq.refl Eq.refl ⟫) p
  HOM e .N-hom (o , _ , f) (o' , _ , f') (h , _ , eq) (g , p) =
    ΣPathP (FREE-1,×.⋆Assoc _ _ _ ,
      isSet→SquareP (λ _ _ → FREE-1,×,⇒.isSetHom) _ _ _ _)

  S : Section nerve PSHᴰCᴰ
  S = FCCC.elimLocal ×⇒Q (nerve , nerve-pres-bp) PSHᴰCartesianClosedⱽ
       (mkElimInterpᴰ OB HOM)

  -- Identity elements in the displayed presheaf for each base object
  idElemOB : (x : Q .fst) → ⟨ OB x .F-ob (ProdExpr.↑ x , tt , FREE-1,×,⇒.id) ⟩
  idElemOB x = FREE-1,×.id , refl

  -- Helper: construct element of S .F-obᴰ for any expression at a point given by a CC morphism
  -- This is needed to handle product domains
  mkElem : (o Γ : ×Q.Expr) (g : FREE-1,×.C [ Γ , o ])
         → ⟨ S .F-obᴰ (⊆ ⟅ o ⟆) .F-ob (Γ , tt , ⊆ ⟪ g ⟫) ⟩
  mkElem (ProdExpr.↑ x) Γ g = g , refl
  mkElem ProdExpr.⊤ Γ g = tt*
  mkElem (l ProdExpr.× r) Γ g =
    mkElem l Γ (g FREE-1,×.⋆ FCC.π₁' ×Q) , mkElem r Γ (g FREE-1,×.⋆ FCC.π₂' ×Q)

  -- Fullness proof: recursion on the codomain structure
  -- Uses the FCC constructors which are parameterized by ×Q = Quiver→×Quiver Q
  ⊆-Full : isFull ⊆
  -- Codomain is terminal: unique morphism (by terminal η in the free CC)
  ⊆-Full o ProdExpr.⊤ f[o→o'] =
    ∣ ((!ₑ Eq.refl) , sym (FCCC.⊤η Eq.refl f[o→o'] )) ∣₁
  -- Codomain is base object
  ⊆-Full (ProdExpr.↑ x) (ProdExpr.↑ y) f[o→o'] =
    ∣ g , q ∙ FREE-1,×,⇒.C .⋆IdL _ ∣₁
    where
    witness : Σ[ g ∈ FREE-1,×.C [ ProdExpr.↑ x , ProdExpr.↑ y ] ]
                 ⊆ ⟪ g ⟫ ≡ FREE-1,×,⇒.id FREE-1,×,⇒.⋆ f[o→o']
    witness = S .F-homᴰ f[o→o'] .N-ob
                (ProdExpr.↑ x , tt , FREE-1,×,⇒.id) (idElemOB x)
    g = witness .fst
    q = witness .snd
  ⊆-Full ProdExpr.⊤ (ProdExpr.↑ y) f[o→o'] =
    ∣ g , q ∙ FREE-1,×,⇒.C .⋆IdL _ ∣₁
    where
    witness : Σ[ g ∈ FREE-1,×.C [ ProdExpr.⊤ , ProdExpr.↑ y ] ]
                 ⊆ ⟪ g ⟫ ≡ FREE-1,×,⇒.id FREE-1,×,⇒.⋆ f[o→o']
    witness = S .F-homᴰ f[o→o'] .N-ob
                (ProdExpr.⊤ , tt , FREE-1,×,⇒.id) tt*
    g = witness .fst
    q = witness .snd
  ⊆-Full (l ProdExpr.× r) (ProdExpr.↑ y) f[o→o'] =
    ∣ g , q ∙ FREE-1,×,⇒.C .⋆IdL _ ∣₁
    where
    elem : ⟨ S .F-obᴰ (⊆ ⟅ l ProdExpr.× r ⟆) .F-ob ((l ProdExpr.× r) , tt , FREE-1,×,⇒.id) ⟩
    elem = mkElem (l ProdExpr.× r) (l ProdExpr.× r) FREE-1,×.id

    witness : Σ[ g ∈ FREE-1,×.C [ l ProdExpr.× r , ProdExpr.↑ y ] ]
                 ⊆ ⟪ g ⟫ ≡ FREE-1,×,⇒.id FREE-1,×,⇒.⋆ f[o→o']
    witness = S .F-homᴰ f[o→o'] .N-ob ((l ProdExpr.× r) , tt , FREE-1,×,⇒.id) elem
    g = witness .fst
    q = witness .snd
  -- Codomain is product: decompose using projections and use η
  ⊆-Full o (o'₁ ProdExpr.× o'₂) f[o→o'] =
    rec2 squash₁
      (λ (g₁ , p₁) (g₂ , p₂) →
        ∣ (FCC.⟨_,_⟩' ×Q) g₁ g₂ ,
          cong₂ (FCCC.⟨_,_⟩' ×⇒Q) p₁ p₂
          ∙ sym (FCCC.×η Eq.refl f[o→o']) ∣₁)
      (⊆-Full o o'₁ (f[o→o'] FREE-1,×,⇒.⋆ FCCC.π₁' ×⇒Q))
      (⊆-Full o o'₂ (f[o→o'] FREE-1,×,⇒.⋆ FCCC.π₂' ×⇒Q))

  ⊆-FullyFaithful : isFullyFaithful ⊆
  ⊆-FullyFaithful = isFull+Faithful→isFullyFaithful {F = ⊆} ⊆-Full ⊆-Faithful
