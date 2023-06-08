{-# OPTIONS --safe #-}
module Cubical.Categories.Profunctor.Morphism where

open import Cubical.Foundations.Prelude hiding (Path)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Profunctor.General
open import Cubical.Data.Sigma
open import Cubical.Reflection.RecordEquiv

open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More

private
  variable
    ℓb ℓb' ℓc ℓc' ℓd ℓd' ℓe ℓe' ℓp ℓr : Level

open NatTrans
open Iso

-- Square in a double category of functors and profunctors
module _ {B : Category ℓb ℓb'}{C : Category ℓc ℓc'}
         {D : Category ℓd ℓd'}{E : Category ℓe ℓe'}
         (P : B o-[ ℓp ]-* C) (F : Functor B D)
         (G : Functor C E) (R : D o-[ ℓr ]-* E) where
  record ProfHom : Type ((ℓ-max (ℓ-max (ℓ-max (ℓ-max
                          (ℓ-max ℓb ℓb') ℓc) ℓc') ℓp) ℓr)) where
    field
      R-hom : ∀ b c → ⟨ P ⟅ b , c ⟆ ⟩ → ⟨ R ⟅ F ⟅ b ⟆ , G ⟅ c ⟆ ⟆ ⟩
      R-nat : ∀ b' b c c' → (f : B [ b' , b ])
              (p : ⟨ P ⟅ b , c ⟆ ⟩) (g : C [ c , c' ]) →
            R-hom _ _ ((P ⟪ f , g ⟫) p) ≡
              (R ⟪ F ⟪ f ⟫ , G ⟪ g ⟫ ⟫) (R-hom _ _ p)

    R-homI : ∀ {b c} → ⟨ P ⟅ b , c ⟆ ⟩ → ⟨ R ⟅ F ⟅ b ⟆ , G ⟅ c ⟆ ⟆ ⟩
    R-homI = R-hom _ _
    R-natI : ∀ {b' b c c'} →
      (f : B [ b' , b ]) (p : ⟨ P ⟅ b , c ⟆ ⟩) (g : C [ c , c' ]) →
            R-hom _ _ ((P ⟪ f , g ⟫) p) ≡
              (R ⟪ F ⟪ f ⟫ , G ⟪ g ⟫ ⟫) (R-hom _ _ p)
    R-natI = R-nat _ _ _ _

  open ProfHom
  unquoteDecl ProfHomIsoΣ = declareRecordIsoΣ ProfHomIsoΣ (quote ProfHom)
  ProfHom≡ : ∀ ph ph' → (ph .R-hom ≡ ph' .R-hom) → ph ≡ ph'
  ProfHom≡ ph ph' path =
    isoFunInjective ProfHomIsoΣ ph ph'
      (Σ≡Prop (λ f → isPropΠ6
        (λ a b c d e f' → isPropΠ λ g → (R ⟅ _ , _ ⟆) .snd _ _)) path)

  ProfHomNT : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓb ℓb') ℓc) ℓc') ℓp) ℓr)
  ProfHomNT =
    NatTrans (LiftF {ℓp} {ℓr} ∘F P) (LiftF {ℓr} {ℓp} ∘F R ∘F ((F ^opF) ×F G))

  ProfHom→NT : ProfHom → ProfHomNT
  ProfHom→NT ph .N-ob (b , c) f = lift (R-homI ph (f .lower))
  ProfHom→NT ph .N-hom f = funExt λ g → cong lift (R-natI ph _ _ _)

  NT→ProfHom : ProfHomNT → ProfHom
  NT→ProfHom α .R-hom _ _ p = α .N-ob _ (lift p) .lower
  NT→ProfHom α .R-nat _ _ _ _ f p g =
    cong lower (λ i → (α .N-hom (f , g) i) (lift p) )

  ProfHomIsoNT : Iso ProfHom ProfHomNT
  ProfHomIsoNT .fun = ProfHom→NT
  ProfHomIsoNT .inv = NT→ProfHom
  ProfHomIsoNT .leftInv ph = ProfHom≡ _ _ refl
  ProfHomIsoNT .rightInv α = makeNatTransPath refl
