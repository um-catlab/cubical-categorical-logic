{-# OPTIONS --lossy-unification #-}
module Gluing.Forded.CartesianClosedCategory.ConservativityOverCategories where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
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
open import Cubical.Categories.Constructions.Free.CartesianClosedCategory.Forded as FCCC
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
  using (PRESHEAFᴰ; PSHAssoc; PSHIdL; PSHπ₁NatEq; PSH×aF-seq; PSHBP)
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Presheaves.Cartesian
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Presheaves.CartesianClosed
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianClosedV
  using (EqCCCⱽ→CCCⱽ)
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.StrictHom
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
    ×⇒Q = Quiver→×⇒Quiver Q
    module ×⇒Q = ×⇒Quiver ×⇒Q

  FREE : Category _ _
  FREE = FreeCat Q

  private module FREE = Category FREE

  FREE-1,×,⇒ : CartesianClosedCategory _ _
  FREE-1,×,⇒ = FreeCartesianClosedCategory ×⇒Q

  private
    module FREE-1,×,⇒ = CartesianClosedCategory FREE-1,×,⇒
    ℓ = ℓ-max ℓQ ℓQ'

  ı : FC.Interp Q FREE-1,×,⇒.C
  ı .HetQG._$g_ = ↑_
  ı .HetQG._<$g>_ = FCCC.↑ₑ ×⇒Q

  ⊆ : Functor FREE FREE-1,×,⇒.C
  ⊆ = FC.rec Q ı

  extension : Functor FREE-1,×,⇒.C (PRESHEAF FREE _)
  extension = FCCC.rec ×⇒Q (CCC-PRESHEAF FREE (ℓ-max ℓQ ℓQ'))
    (mkElimInterpᴰ (YOStrict ⟅_⟆) λ f → YOStrict ⟪ ⇑ _ f ⟫)

  commutes : YOStrict ≡ extension ∘F ⊆
  commutes = FreeCatFunctor≡ Q _ _
    (record { _$gᴰ_ = λ _ → refl ; _<$g>ᴰ_ = λ _ → refl })

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

  nerve : Functor FREE-1,×,⇒.C (PRESHEAF FREE ℓ)
  nerve = reindPshFStrict ⊆ ∘F YOStrict

  private
    FREEᴰ : Categoryᴰ FREE ℓ-zero ℓ-zero
    FREEᴰ = Unitᴰ.Unitᴰ FREE

    PSHᴰ = PRESHEAFᴰ FREEᴰ ℓ ℓ

    module PSHᴰ = Categoryᴰ PSHᴰ

    PSH-CC : CartesianCategory (ℓ-max (ℓ-max ℓQ ℓQ') (ℓ-suc ℓ)) (ℓ-max (ℓ-max ℓQ ℓQ') ℓ)
    PSH-CC = Cartesian-PRESHEAF FREE ℓ


    RA : ReprEqAssoc (CartesianCategory.C PSH-CC)
    RA = {!!}

    IL : EqIdL (CartesianCategory.C PSH-CC)
    IL = {!!}

    ANE : Allπ₁NatEq (CartesianCategory.bp PSH-CC)
    ANE = {!!}

    AaFS : All×aF-seq (CartesianCategory.bp PSH-CC)
    AaFS = {!!}

    PSHᴰCartesianⱽEq : isCartesianⱽ {!!} PSHᴰ
    PSHᴰCartesianⱽEq = isCartesianⱽPSHᴰ

    PSHᴰCartesianⱽ : V'.CartesianCategoryⱽ (PRESHEAF FREE ℓ) _ _
    PSHᴰCartesianⱽ = EqCCⱽ→CCⱽ {!!} PSHᴰ PSHᴰCartesianⱽEq

    PSHᴰCᴰ : Categoryᴰ (PRESHEAF FREE ℓ) _ _
    PSHᴰCᴰ = V'.CartesianCategoryⱽ.Cᴰ PSHᴰCartesianⱽ


    isCCCPSHᴰ : isCartesianClosedⱽ {!!} PSHᴰ {!!} (CartesianCategory.bp PSH-CC) {!!} {!!}
    isCCCPSHᴰ .fst = PSHᴰCartesianⱽEq
    isCCCPSHᴰ .snd .fst = PSHᴰExponentials
    isCCCPSHᴰ .snd .snd = {!PSHᴰ∀!}

    -- Why is this slow?
    -- Something about the Eq assumptions not aligning with those from isCartesianClosedⱽPSHᴰ?
    PSHᴰCartesianClosedⱽ : CartesianClosedCategoryⱽ PSH-CC _ _
    PSHᴰCartesianClosedⱽ = EqCCCⱽ→CCCⱽ PSH-CC {!!} {!!} {!!} {!!} PSHᴰ isCCCPSHᴰ
      -- EqCCCⱽ→CCCⱽ PSH-CC PSHAssoc PSHIdL PSHπ₁NatEq PSH×aF-seq PSHᴰ isCartesianClosedⱽPSHᴰ

    -- nerve preserves products because the universal property of products in
    -- FREE-1,×,⇒.C transfers pointwise to the presheaf category
    nerve-pres-bp : preservesProvidedBinProducts nerve (FREE-1,×,⇒.CC .CartesianCategory.bp)
    nerve-pres-bp A B Γ = {!!}
    -- {!FREE-1,×,⇒.CC .CartesianCategory.bp (A , B) .UniversalElement.universal ?!}
      -- FREE-1,×,⇒.CC .CartesianCategory.bp (A , B) .UniversalElement.universal ?

  -- S : Section nerve PSHᴰCᴰ
  -- S = FCCC.elimLocal ×⇒Q (nerve , nerve-pres-bp) PSHᴰCartesianClosedⱽ
  --      (mkElimInterpᴰ OB HOM)
  --   where
  --   OB : (o : Q .fst) → PSHᴰ.ob[ nerve ⟅ ⊆ ⟅ o ⟆ ⟆ ]
  --   OB o .F-ob (o' , _ , f) =
  --     (Σ[ g ∈ FREE [ o' , o ] ] ⊆ ⟪ g ⟫ ≡ f) ,
  --     isSetΣ (FREE .isSetHom)
  --       (λ _ → isSet→isGroupoid (FREE-1,×,⇒.C .isSetHom) _ _)
  --   OB o .F-hom {x = o' , _ , f} {y = o'' , _ , f'} (h , _ , eq) (g , p) =
  --     h FREE.⋆ g ,
  --     ⊆ .F-seq h g ∙ cong (λ x → ⊆ ⟪ h ⟫ ⋆⟨ FREE-1,×,⇒.C ⟩ x) p ∙ Eq.eqToPath eq
  --   OB o .F-id = funExt λ (g , p) → ΣPathP (FREE .⋆IdL _ ,
  --     isSet→SquareP (λ _ _ → FREE-1,×,⇒.C .isSetHom) _ _ _ _)
  --   OB o .F-seq _ _ = funExt λ _ → ΣPathP (FREE .⋆Assoc _ _ _ ,
  --     isSet→SquareP (λ _ _ → FREE-1,×,⇒.C .isSetHom) _ _ _ _)

  --   HOM : (e : Q.mor) →
  --     PSHᴰ.Hom[ nerve ⟪ ⊆ ⟪ FC.⇑ Q e ⟫ ⟫ ][ OB (Q.dom e) , OB (Q.cod e) ]
  --   HOM e .N-ob (o , _ , f) (g , p) =
  --     FC.⇑ Q e ∘⟨ FREE ⟩ g ,
  --     ⊆ .F-seq g (FC.⇑ Q e) ∙ cong (λ x → x ⋆⟨ FREE-1,×,⇒.C ⟩ ⊆ ⟪ FC.⇑ Q e ⟫) p
  --   HOM e .N-hom (o , _ , f) (o' , _ , f') (h , _ , eq) (g , p) =
  --     ΣPathP (FREE .⋆Assoc _ _ _ ,
  --       isSet→SquareP (λ _ _ → FREE-1,×,⇒.C .isSetHom) _ _ _ _)

  -- ⊆-Full : isFull ⊆
  -- ⊆-Full o o' f[o→o'] = ∣ g , q ∙ FREE-1,×,⇒.C .⋆IdL _ ∣₁
  --   where
  --   witness : Σ[ g ∈ FREE [ o , o' ] ] ⊆ ⟪ g ⟫ ≡ FREE-1,×,⇒.C .id ⋆⟨ FREE-1,×,⇒.C ⟩ f[o→o']
  --   witness = (S .F-homᴰ f[o→o'] .N-ob (o , tt , FREE-1,×,⇒.C .id)) (FREE .id , refl)

  --   g : FREE [ o , o' ]
  --   g = witness .fst

  --   q : ⊆ ⟪ g ⟫ ≡ FREE-1,×,⇒.C .id ⋆⟨ FREE-1,×,⇒.C ⟩ f[o→o']
  --   q = witness .snd

  -- ⊆-FullyFaithful : isFullyFaithful ⊆
  -- ⊆-FullyFaithful = isFull+Faithful→isFullyFaithful {F = ⊆} ⊆-Full ⊆-Faithful
