module Cubical.Categories.LocallySmall.Displayed.SmallFibers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)
open import Cubical.Foundations.More
  using (isSet→Square)
  renaming (rectify to TypeRectify)

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.Constructions.BinProduct.Base

open import Cubical.Categories.LocallySmall.Displayed.Base
open import Cubical.Categories.LocallySmall.Displayed.Properties
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Weaken
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Total
open import Cubical.Categories.LocallySmall.Variables

open Functor
open Category
open Categoryᴰ
open Σω

module _
  {C : Category Cob CHom-ℓ}
  {Cᴰ-ℓ}{Cobᴰ}{CHom-ℓᴰ}
  (Cᴰ : SmallFibersCategoryᴰ C Cᴰ-ℓ Cobᴰ CHom-ℓᴰ)
  (D : Category Dob DHom-ℓ)
  (obᴰᴰ-ℓ : Cob → Dob → Level)
  (obᴰᴰ : ∀ ccᴰd → Type (obᴰᴰ-ℓ (ccᴰd .fst .fst) (ccᴰd .snd)))
  (Hom-ℓᴰᴰ : (c c' : Cob) → (d d' : Dob) → Level)
  where
  private
    module Cᴰ = CategoryᴰNotation Cᴰ

  SmallFibersᴰCategoryᴰ : Typeω
  SmallFibersᴰCategoryᴰ =
    SmallFibersCategoryᴰ (∫C (weaken (∫C Cᴰ) D)) _
      obᴰᴰ
      (λ ccᴰd ccᴰd' →
        Hom-ℓᴰᴰ (ccᴰd .fst .fst) (ccᴰd' .fst .fst)
                (ccᴰd .snd) (ccᴰd' .snd))

  private
    Cᴰ' = reindexEqSF (π₁ C D) Cᴰ Eq.refl (λ _ _ → Eq.refl)
    module Cᴰ' = CategoryᴰNotation Cᴰ'

  module _ (Cᴰᴰ : SmallFibersᴰCategoryᴰ) where
    private
      Cᴰᴰ' : SmallFibersCategoryᴰ (∫C Cᴰ') _ _ _
      Cᴰᴰ' = reindexEqSF F Cᴰᴰ Eq.refl (λ _ _ → Eq.refl)
        where
        F : Functor (∫C Cᴰ') (∫C (weaken (∫C Cᴰ) D))
        F .F-ob = λ z → (F-ob (π₁ C D) (z .fst) , z .snd) , z .fst .snd
        F .F-hom = λ z → (F-hom (π₁ C D) (z .fst) , z .snd) , z .fst .snd
        F .F-id = refl
        F .F-seq = λ _ _ → refl

      module Cᴰᴰ' = ∫CᴰSFNotation _ Cᴰᴰ'

      Cᴰᴰ'Over : (c : Cob) → (d : Dob) →
        Categoryᴰ Cᴰ.v[ c ]
          (λ cᴰ → Liftω (obᴰᴰ ((c , cᴰ) , d))) _
      Cᴰᴰ'Over c d = reindexEqSF F Cᴰᴰ'.vᴰ[ c , d ]SF Eq.refl (λ _ _ → Eq.refl)
        where
        F : Functor Cᴰ.v[ c ] Cᴰ'.v[ c , d ]
        F .F-ob = λ z → z
        F .F-hom = λ z → z
        F .F-id = refl
        F .F-seq = λ _ _ → refl

    SmallFibersᴰOver : (c : Cob) → (d : Dob) → SmallCategoryᴰ (_ , Cᴰ.v[ c ]) _ _
    SmallFibersᴰOver c d = _ , Cᴰᴰ'Over c d

module SmallFibersᴰCategoryᴰNotation
  {C : Category Cob CHom-ℓ}
  {Cᴰ-ℓ}{Cobᴰ}{CHom-ℓᴰ}
  {Cᴰ : SmallFibersCategoryᴰ C Cᴰ-ℓ Cobᴰ CHom-ℓᴰ}
  {D : Category Dob DHom-ℓ}
  {obᴰᴰ-ℓ : Cob → Dob → Level}
  {obᴰᴰ : ∀ ccᴰd → Type (obᴰᴰ-ℓ (ccᴰd .fst .fst) (ccᴰd .snd))}
  {Hom-ℓᴰᴰ : (c c' : Cob) → (d d' : Dob) → Level}
  (Cᴰᴰ : SmallFibersᴰCategoryᴰ Cᴰ D obᴰᴰ-ℓ obᴰᴰ Hom-ℓᴰᴰ)
  where
  open CategoryᴰNotation Cᴰᴰ public
  private
    module C = CategoryNotation C
    module D = CategoryNotation D
    module Cᴰ = CategoryᴰNotation Cᴰ
    module Cᴰᴰ = CategoryᴰNotation Cᴰᴰ

  -- The definition of SmallFibNatTransᴰ is parameterized by two
  -- displayed functor
  -- (Fᴰ : Functorᴰ F ⟨ Cᴰ ⟩smallcatᴰ ⟨ Dᴰᴰ.vᴰ[ d ][ e ] ⟩smallcatᴰ)
  -- (Gᴰ : Functorᴰ G ⟨ Cᴰ ⟩smallcatᴰ ⟨ Dᴰᴰ.vᴰ[ d' ][ e' ] ⟩smallcatᴰ)
  --
  -- If instead of mapping into vᴰ[_][_], we have Fᴰ/Gᴰ into vᴰ[_][_]'
  -- the resulting type SmallFibNatTransᴰ is large (at Typeω)
  vᴰ[_][_]' : (c : Cob) → (d : Dob) → SmallCategoryᴰ (_ , Cᴰ.v[ c ])
    (obᴰᴰ-ℓ c d)
    (Hom-ℓᴰᴰ c c d d)
  vᴰ[ c ][ d ]' = SmallFibersᴰOver _ _ _ _ _ Cᴰᴰ c d

  -- But using the following definiton results in it being small
  -- I'd like to avoid a new manual definition, but I can't make
  -- sense of why the one defined above causes this largeness
  vᴰ[_][_] : (c : Cob) → (d : Dob) → SmallCategoryᴰ (_ , Cᴰ.v[ c ])
    (obᴰᴰ-ℓ c d)
    (Hom-ℓᴰᴰ c c d d)
  vᴰ[ c ][ d ] .fst = liftω (λ cᴰ → obᴰᴰ ((c , liftω cᴰ) , d))
  vᴰ[ c ][ d ] .snd .Hom[_][_,_] fᴰ xᴰ yᴰ = Cᴰᴰ.Hom[ (C.id , fᴰ), D.id ][ xᴰ , yᴰ ]
  vᴰ[ c ][ d ] .snd .idᴰ = Cᴰᴰ.idᴰ
  vᴰ[ c ][ d ] .snd ._⋆ᴰ_ fᴰ gᴰ =
    Cᴰᴰ.reind (ΣPathP ((Cᴰ.reind-filler _ _) , (D.⋆IdL _))) $ fᴰ Cᴰᴰ.⋆ᴰ gᴰ
  vᴰ[ c ][ d ] .snd .⋆IdLᴰ fᴰ =
      ΣPathP (
        (Cᴰ.rectify $ Cᴰ.≡out $
          (sym $ Cᴰ.reind-filler _ _)
          ∙ Cᴰ.⋆IdLᴰ _) ,
        (Cᴰᴰ.rectify $ Cᴰᴰ.≡out $
          (sym $ Cᴰᴰ.reind-filler _ _)
          ∙ Cᴰᴰ.⋆IdLᴰ _))
  vᴰ[ c ][ d ] .snd .⋆IdRᴰ fᴰ =
      ΣPathP (
        (Cᴰ.rectify $ Cᴰ.≡out $
          (sym $ Cᴰ.reind-filler _ _)
          ∙ Cᴰ.⋆IdRᴰ _) ,
        (Cᴰᴰ.rectify $ Cᴰᴰ.≡out $
          (sym $ Cᴰᴰ.reind-filler _ _)
          ∙ Cᴰᴰ.⋆IdRᴰ _))
  vᴰ[ c ][ d ] .snd .⋆Assocᴰ fᴰ gᴰ hᴰ =
      ΣPathP (
        (Cᴰ.rectify $ Cᴰ.≡out $
          (sym $ Cᴰ.reind-filler _ _)
          ∙ Cᴰ.⟨ sym $ Cᴰ.reind-filler _ _ ⟩⋆⟨⟩
          ∙ Cᴰ.⋆Assocᴰ _ _ _
          ∙ Cᴰ.⟨⟩⋆⟨ Cᴰ.reind-filler _ _ ⟩
          ∙ Cᴰ.reind-filler _ _
          ),
        (Cᴰᴰ.rectify $ Cᴰᴰ.≡out $
          (sym $ Cᴰᴰ.reind-filler _ _)
          ∙ Cᴰᴰ.⟨ sym $ Cᴰᴰ.reind-filler _ _ ⟩⋆⟨⟩
          ∙ Cᴰᴰ.⋆Assocᴰ _ _ _
          ∙ Cᴰᴰ.⟨⟩⋆⟨ Cᴰᴰ.reind-filler _ _ ⟩
          ∙ Cᴰᴰ.reind-filler _ _
          ))
  vᴰ[ c ][ d ] .snd .isSetHomᴰ = Cᴰᴰ.isSetHomᴰ

  -- It's even more confusing because of these definitional equalities
  private
    module _ c d {x}{y} where
      u = vᴰ[ c ][ d ]'
      module u = CategoryᴰNotation ⟨ u ⟩smallcatᴰ
      v = vᴰ[ c ][ d ]
      module v = CategoryᴰNotation ⟨ v ⟩smallcatᴰ

      _ : ⟨ u ⟩small-obᴰ ≡ ⟨ v ⟩small-obᴰ
      _ = refl

      module _ (f : Cᴰ.Hom[ C.id ][ x , y ]) xᴰ yᴰ where
        _ : u.Hom[ f ][ xᴰ , yᴰ ] ≡ v.Hom[ f ][ xᴰ , yᴰ ]
        _ = refl
