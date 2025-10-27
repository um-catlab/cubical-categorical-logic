module Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

import Cubical.Categories.Category as Small
open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Functor

open import Cubical.Categories.LocallySmall.Displayed.Base
open import Cubical.Categories.LocallySmall.Displayed.Properties
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base

open Category
open Categoryᴰ
open Σω
open Liftω

module _
  {C : Category Cob CHom-ℓ}
  {D : Category Dob DHom-ℓ}
  (F : Functor C D)
  where
  private
    module C = CategoryNotation C
    module D = CategoryNotation D
    module F = FunctorNotation F

  module _ (Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ) where
    private
      module Dᴰ = Categoryᴰ Dᴰ
    reindex :
      Categoryᴰ C
        (λ c → Dobᴰ (F.F-ob c))
        λ c c' → DHom-ℓᴰ (F.F-ob c) (F.F-ob c')
    reindex .Hom[_][_,_] f xᴰ yᴰ = Dᴰ.Hom[ F.F-hom f ][ xᴰ , yᴰ ]
    reindex .idᴰ = Dᴰ.reind (sym F.F-id) Dᴰ.idᴰ
    reindex ._⋆ᴰ_ fᴰ gᴰ = Dᴰ.reind (sym $ F.F-seq _ _) (fᴰ Dᴰ.⋆ᴰ gᴰ)
    reindex .⋆IdLᴰ fᴰ =
      ΣPathP (
        (C.⋆IdL _) ,
        (Dᴰ.rectify $ Dᴰ.≡out $
          (sym $ Dᴰ.reind-filler _ _)
          ∙ Dᴰ.⟨ sym $ Dᴰ.reind-filler _ _ ⟩⋆⟨⟩
          ∙ Dᴰ.⋆IdLᴰ _))
    reindex .⋆IdRᴰ fᴰ =
      ΣPathP (
        (C.⋆IdR _) ,
        (Dᴰ.rectify $ Dᴰ.≡out $
          (sym $ Dᴰ.reind-filler _ _)
          ∙ Dᴰ.⟨⟩⋆⟨ sym $ Dᴰ.reind-filler _ _ ⟩
          ∙ Dᴰ.⋆IdRᴰ _))
    reindex .⋆Assocᴰ fᴰ gᴰ hᴰ =
      ΣPathP (
        (C.⋆Assoc _ _ _) ,
        (Dᴰ.rectify $ Dᴰ.≡out $
          (sym $ Dᴰ.reind-filler _ _)
          ∙ Dᴰ.⟨ sym $ Dᴰ.reind-filler _ _ ⟩⋆⟨⟩
          ∙ Dᴰ.⋆Assocᴰ _ _ _
          ∙ Dᴰ.⟨⟩⋆⟨ Dᴰ.reind-filler _ _ ⟩
          ∙ Dᴰ.reind-filler _ _
          ))
    reindex .isSetHomᴰ = Dᴰ.isSetHomᴰ

    open Functorᴰ
    π : Functorᴰ F reindex Dᴰ
    π .F-obᴰ = λ z → z
    π .F-homᴰ = λ fᴰ → fᴰ
    π .F-idᴰ =
      ΣPathP (
        F.F-id ,
        (Dᴰ.rectify $ Dᴰ.≡out $ sym $ Dᴰ.reind-filler _ _))
    π .F-seqᴰ _ _ =
      ΣPathP (
        F.F-seq _ _ ,
        (Dᴰ.rectify $ Dᴰ.≡out $ sym $ Dᴰ.reind-filler _ _))

  module _ {Dᴰ-ℓ Dobᴰ DHom-ℓᴰ}
    (Dᴰ : SmallFibersCategoryᴰ D Dᴰ-ℓ Dobᴰ DHom-ℓᴰ) where
    private
      module Dᴰ = Categoryᴰ Dᴰ
    reindexSF :
      SmallFibersCategoryᴰ C _
        (λ c → Dobᴰ (F.F-ob c))
        _
    reindexSF .Hom[_][_,_] f xᴰ yᴰ = Dᴰ.Hom[ F.F-hom f ][ xᴰ , yᴰ ]
    reindexSF .idᴰ = Dᴰ.reind (sym F.F-id) Dᴰ.idᴰ
    reindexSF ._⋆ᴰ_ fᴰ gᴰ = Dᴰ.reind (sym $ F.F-seq _ _) (fᴰ Dᴰ.⋆ᴰ gᴰ)
    reindexSF .⋆IdLᴰ fᴰ =
      ΣPathP (
        (C.⋆IdL _) ,
        (Dᴰ.rectify $ Dᴰ.≡out $
          (sym $ Dᴰ.reind-filler _ _)
          ∙ Dᴰ.⟨ sym $ Dᴰ.reind-filler _ _ ⟩⋆⟨⟩
          ∙ Dᴰ.⋆IdLᴰ _))
    reindexSF .⋆IdRᴰ fᴰ =
      ΣPathP (
        (C.⋆IdR _) ,
        (Dᴰ.rectify $ Dᴰ.≡out $
          (sym $ Dᴰ.reind-filler _ _)
          ∙ Dᴰ.⟨⟩⋆⟨ sym $ Dᴰ.reind-filler _ _ ⟩
          ∙ Dᴰ.⋆IdRᴰ _))
    reindexSF .⋆Assocᴰ fᴰ gᴰ hᴰ =
      ΣPathP (
        (C.⋆Assoc _ _ _) ,
        (Dᴰ.rectify $ Dᴰ.≡out $
          (sym $ Dᴰ.reind-filler _ _)
          ∙ Dᴰ.⟨ sym $ Dᴰ.reind-filler _ _ ⟩⋆⟨⟩
          ∙ Dᴰ.⋆Assocᴰ _ _ _
          ∙ Dᴰ.⟨⟩⋆⟨ Dᴰ.reind-filler _ _ ⟩
          ∙ Dᴰ.reind-filler _ _
          ))
    reindexSF .isSetHomᴰ = Dᴰ.isSetHomᴰ

    open Functorᴰ
    πSF : Functorᴰ F reindexSF Dᴰ
    πSF .F-obᴰ = λ z → z
    πSF .F-homᴰ = λ fᴰ → fᴰ
    πSF .F-idᴰ =
      ΣPathP (
        F.F-id ,
        (Dᴰ.rectify $ Dᴰ.≡out $ sym $ Dᴰ.reind-filler _ _))
    πSF .F-seqᴰ _ _ =
      ΣPathP (
        F.F-seq _ _ ,
        (Dᴰ.rectify $ Dᴰ.≡out $ sym $ Dᴰ.reind-filler _ _))

    module _
      (F-id' : {x : Cob} → D .id {x = F.F-ob x} Eq.≡ F.F-hom (C .id))
      (F-seq' : {x y z : Cob}
        (f : C.Hom[ x , y ]) (g : C.Hom[ y , z ]) →
        (F.F-hom f) D.⋆ (F.F-hom g) Eq.≡ F.F-hom (f C.⋆ g))
      where

      private
        -- todo: generalize upstream somewhere to Data.Equality?
        isPropEqHom : ∀ {a b : Dob} {f g : D.Hom[ a , b ]}
                    → isProp (f Eq.≡ g)
        isPropEqHom {f = f}{g} =
          subst isProp (Eq.PathPathEq {x = f}{y = g}) (D.isSetHom f g)

        reind' : {a b : Dob} {f g : D.Hom[ a , b ]} (p : f Eq.≡ g)
            {aᴰ : Dobᴰ a} {bᴰ : Dobᴰ  b }
          → Dᴰ.Hom[ f ][ liftω aᴰ , liftω bᴰ ]
          → Dᴰ.Hom[ g ][ liftω aᴰ , liftω bᴰ ]
        reind' p = Eq.transport Dᴰ.Hom[_][ _ , _ ] p

        reind≡reind' : ∀ {a b : Dob} {f g : D.Hom[ a , b ]}
          {p : f ≡ g} {e : f Eq.≡ g}
          {aᴰ : Dobᴰ a} {bᴰ : Dobᴰ b }
          → (fᴰ : Dᴰ.Hom[ f ][ liftω aᴰ , liftω bᴰ ])
          → Dᴰ.reind p fᴰ ≡ reind' e fᴰ
        reind≡reind' {p = p}{e} fᴰ =
          subst {x = Eq.pathToEq p}
            (λ e → Dᴰ.reind p fᴰ ≡ reind' e fᴰ)
            (isPropEqHom _ _)
            lem
          where
          lem : Dᴰ.reind p fᴰ ≡ reind' (Eq.pathToEq p) fᴰ
          lem =
            sym $ Eq.eqToPath $
              Eq.transportPathToEq→transportPath
                Dᴰ.Hom[_][ _ , _ ] p fᴰ

      reindexEqSF :
        SmallFibersCategoryᴰ C _
          (λ c → Dobᴰ (F.F-ob c))
          _
      reindexEqSF =
        redefine-idᴰ-⋆ᴰ reindexSF
          (λ {x}{xᴰ} →
            reind' F-id' Dᴰ.idᴰ ,
            (reind≡reind' Dᴰ.idᴰ))
          (λ fᴰ gᴰ →
            reind' (F-seq' _ _) (fᴰ Dᴰ.⋆ᴰ gᴰ) ,
            reind≡reind' (fᴰ Dᴰ.⋆ᴰ gᴰ))
