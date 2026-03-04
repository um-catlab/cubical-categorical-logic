{-# OPTIONS -W noUnsupportedIndexedMatch #-}
module Cubical.Categories.LocallySmall.Displayed.Instances.Reindex.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More
import Cubical.Data.Equality as Eq

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Instances.DisplayOverTerminal.Base
open import Cubical.Categories.LocallySmall.Instances.Unit
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Functor.Base

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base

open Category
open Categoryᴰ
open Σω
open Liftω

module _
  {C : Category Cob CHom-ℓ}
  (Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ) where
  private
    module C = CategoryNotation C
    module Cᴰ = Categoryᴰ Cᴰ

  module _
    (idᴰ' : ∀ {x : Cob} {xᴰ : Cobᴰ x} →
       Σ[ fᴰ ∈ Cᴰ.Hom[ C.id ][ xᴰ , xᴰ ] ] Cᴰ.idᴰ ≡ fᴰ)
    (⋆ᴰ' : ∀ {x y z : Cob}
       {f : C.Hom[ x , y ]} {g : C.Hom[ y , z ]}
       {xᴰ : Cobᴰ x} {yᴰ : Cobᴰ y} {zᴰ : Cobᴰ z} →
       (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ]) →
       (gᴰ : Cᴰ.Hom[ g ][ yᴰ , zᴰ ]) →
       Σ[ hᴰ ∈ Cᴰ.Hom[ f C.⋆ g ][ xᴰ , zᴰ ] ] (fᴰ Cᴰ.⋆ᴰ gᴰ) ≡ hᴰ)
    where

    redefine-idᴰ-⋆ᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ
    redefine-idᴰ-⋆ᴰ .Hom[_][_,_] = Cᴰ.Hom[_][_,_]
    redefine-idᴰ-⋆ᴰ .idᴰ = idᴰ' .fst
    redefine-idᴰ-⋆ᴰ ._⋆ᴰ_ fᴰ gᴰ = ⋆ᴰ' fᴰ gᴰ .fst
    redefine-idᴰ-⋆ᴰ .⋆IdLᴰ fᴰ =
      ΣPathP (
        (C.⋆IdL _) ,
        subst (λ gᴰ → gᴰ Cᴰ.≡[ C.⋆IdL _ ] fᴰ)
          (⋆ᴰ' Cᴰ.idᴰ fᴰ .snd
          ∙ cong₂ (λ u v → ⋆ᴰ' u v .fst) (idᴰ' .snd) refl)
          (Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdLᴰ _))
    redefine-idᴰ-⋆ᴰ .⋆IdRᴰ fᴰ =
      ΣPathP (
        (C.⋆IdR _) ,
        subst (λ gᴰ → gᴰ Cᴰ.≡[ C.⋆IdR _ ] fᴰ)
          (⋆ᴰ' fᴰ Cᴰ.idᴰ .snd
          ∙ cong₂ (λ u v → ⋆ᴰ' u v .fst) refl (idᴰ' .snd))
          (Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdRᴰ _))
    redefine-idᴰ-⋆ᴰ .⋆Assocᴰ fᴰ gᴰ hᴰ =
      ΣPathP (
        (C.⋆Assoc _ _ _) ,
        subst2
          (λ u v → u Cᴰ.≡[ C.⋆Assoc _ _ _ ] v)
          (⋆ᴰ' (fᴰ Cᴰ.⋆ᴰ gᴰ) hᴰ .snd
          ∙ cong (λ z → ⋆ᴰ' z hᴰ .fst) (⋆ᴰ' fᴰ gᴰ .snd))
          (⋆ᴰ' fᴰ (gᴰ Cᴰ.⋆ᴰ hᴰ) .snd
          ∙ cong (λ z → ⋆ᴰ' fᴰ z .fst) (⋆ᴰ' gᴰ hᴰ .snd))
          (Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆Assocᴰ _ _ _)
        )
    redefine-idᴰ-⋆ᴰ .isSetHomᴰ = Cᴰ.isSetHomᴰ

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
    -- This definition of reindexing is the most straightforward to
    -- define, but the use of reind on morphisms
    -- makes it sometimes inconvenient for defining
    -- constructions as a reindexing as a transport will
    -- be inserted at every composition
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

    module _
      (F-id' : {x : Cob} → D .id {x = F.F-ob x} Eq.≡ F.F-hom (C .id))
      (F-seq' : {x y z : Cob}
        (f : C.Hom[ x , y ]) (g : C.Hom[ y , z ]) →
        (F.F-hom f) D.⋆ (F.F-hom g) Eq.≡ F.F-hom (f C.⋆ g))
      where

      reindexEq : Categoryᴰ C (λ c → Dobᴰ (F.F-ob c)) _
      reindexEq =
        redefine-idᴰ-⋆ᴰ reindex
          (Dᴰ.reindEq F-id' Dᴰ.idᴰ , Dᴰ.reind≡reindEq Dᴰ.idᴰ)
          (λ fᴰ gᴰ → Dᴰ.reindEq (F-seq' _ _) (fᴰ Dᴰ.⋆ᴰ gᴰ) ,
                     Dᴰ.reind≡reindEq (fᴰ Dᴰ.⋆ᴰ gᴰ))

  module _ {Dᴰ-ℓ Dobᴰ DHom-ℓᴰ}
    (Dᴰ : SmallFibersCategoryᴰ D Dᴰ-ℓ Dobᴰ DHom-ℓᴰ) where
    private
      module Dᴰ = Categoryᴰ Dᴰ
    -- Reindexing preserves smallfiberedness
    reindexSF :
      SmallFibersCategoryᴰ C _
        (λ c → Dobᴰ (F.F-ob c))
        _
    reindexSF = reindex Dᴰ

    open Functorᴰ
    πSF : Functorᴰ F reindexSF Dᴰ
    πSF = π Dᴰ

    module _
      (F-id' : {x : Cob} → D .id {x = F.F-ob x} Eq.≡ F.F-hom (C .id))
      (F-seq' : {x y z : Cob}
        (f : C.Hom[ x , y ]) (g : C.Hom[ y , z ]) →
        (F.F-hom f) D.⋆ (F.F-hom g) Eq.≡ F.F-hom (f C.⋆ g))
      where

      reindexEqSF : SmallFibersCategoryᴰ C _ (λ c → Dobᴰ (F.F-ob c)) _
      reindexEqSF = reindexEq Dᴰ F-id' F-seq'

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

    -- Rather than acting with a reind on idᴰ and _⋆ᴰ_,
    -- this version of reindexing stores both of the terms
    -- that would have appeared as arguments to reind.
    -- That is, the path and the original (untransported)
    -- displayed hom are stored
    --
    -- Keeping both of these arguments around but not actually
    -- performing the transport lets us think of the morphisms
    -- in this displayed category as syntactic descriptions of
    -- a reind, rather than a semantic reind
    -- In this way, the morphisms here can be treated like deferred
    -- transorts, and we can maximally postpone the katabasis
    -- into transport hell
    reindex' : Categoryᴰ C (λ c → Dobᴰ (F.F-ob c)) _
    reindex' .Hom[_][_,_] f xᴰ yᴰ =
      Σ[ g ∈ D.Hom[ F.F-ob _ , F.F-ob _ ] ]
      Σ[ _ ∈ g ≡ F.F-hom f ]
      Dᴰ.Hom[ g ][ xᴰ , yᴰ ]
    reindex' .idᴰ = D.id , sym F.F-id , Dᴰ.idᴰ
    reindex' ._⋆ᴰ_ {f = f} {g = g} (Ff , p , fᴰ) (Fg , q , gᴰ) =
      Ff D.⋆ Fg , (D.⟨ p ⟩⋆⟨ q ⟩ ∙ (sym $ F.F-seq f g) , (fᴰ Dᴰ.⋆ᴰ gᴰ))
    reindex' .⋆IdLᴰ (Ff , p , fᴰ) =
      ΣPathP ((C.⋆IdL _) ,
        ΣPathP ((D.⋆IdL Ff) ,
          ΣPathP ((isSet→SquareP (λ _ _ → D.isSetHom) _ _ _ _) ,
            (Dᴰ.rectify $ Dᴰ.≡out $ Dᴰ.⋆IdLᴰ fᴰ))))
    reindex' .⋆IdRᴰ (Ff , p , fᴰ) =
      ΣPathP ((C.⋆IdR _) ,
        ΣPathP ((D.⋆IdR Ff) ,
          ΣPathP ((isSet→SquareP (λ _ _ → D.isSetHom) _ _ _ _) ,
            (Dᴰ.rectify $ Dᴰ.≡out $ Dᴰ.⋆IdRᴰ fᴰ))))
    reindex' .⋆Assocᴰ (Ff , p , fᴰ) (Fg , q , gᴰ) (Fh , r , hᴰ) =
      ΣPathP ((C.⋆Assoc _ _ _) ,
        ΣPathP ((D.⋆Assoc Ff Fg Fh) ,
          ΣPathP ((isSet→SquareP (λ _ _ → D.isSetHom) _ _ _ _) ,
            (Dᴰ.rectify $ Dᴰ.≡out $ Dᴰ.⋆Assocᴰ fᴰ gᴰ hᴰ))))
    reindex' .isSetHomᴰ =
      isSetΣ D.isSetHom (λ _ → isSetΣ (isProp→isSet (D.isSetHom _ _))
        (λ _ → Dᴰ.isSetHomᴰ))

    open Functorᴰ
    π' : Functorᴰ F reindex' Dᴰ
    π' .F-obᴰ = λ z → z
    π' .F-homᴰ (Ff , p , fᴰ) = Dᴰ.reind p fᴰ
    π' .F-idᴰ = sym $ Dᴰ.reind-filler _ _
    π' .F-seqᴰ _ _ =
      (sym $ Dᴰ.reind-filler _ _)
      ∙ Dᴰ.⟨ Dᴰ.reind-filler _ _ ⟩⋆⟨ Dᴰ.reind-filler _ _ ⟩

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

    module _
      (F-id' : {x : Cob} → D .id {x = F.F-ob x} Eq.≡ F.F-hom (C .id))
      (F-seq' : {x y z : Cob}
        (f : C.Hom[ x , y ]) (g : C.Hom[ y , z ]) →
        (F.F-hom f) D.⋆ (F.F-hom g) Eq.≡ F.F-hom (f C.⋆ g))
      where

      open Functorᴰ
      reindex→reindexEq :
        Functorⱽ (reindex F Dᴰ) (reindexEq F Dᴰ F-id' F-seq')
      reindex→reindexEq .F-obᴰ = λ z → z
      reindex→reindexEq .F-homᴰ = λ fᴰ → fᴰ
      reindex→reindexEq .F-idᴰ =
        ΣPathP (refl ,
          (Dᴰ.rectify $ Dᴰ.≡out $
            (sym $ Dᴰ.reind-filler _ _)
            ∙ Dᴰ.reindEq-pathFiller F-id' Dᴰ.idᴰ))
      reindex→reindexEq .F-seqᴰ {f = f}{g = g} fᴰ gᴰ =
        ΣPathP (refl ,
          (Dᴰ.rectify $ Dᴰ.≡out $
            (sym $ Dᴰ.reind-filler _ _)
            ∙ Dᴰ.reindEq-pathFiller _ _))

      reindexEq→reindex :
        Functorⱽ (reindexEq F Dᴰ F-id' F-seq') (reindex F Dᴰ)
      reindexEq→reindex .F-obᴰ = λ z → z
      reindexEq→reindex .F-homᴰ = λ fᴰ → fᴰ
      reindexEq→reindex .F-idᴰ =
        ΣPathP (refl ,
          (Dᴰ.rectify $ Dᴰ.≡out $
           (sym $ Dᴰ.reindEq-pathFiller _ _)
            ∙ Dᴰ.reind-filler _ _))
      reindexEq→reindex .F-seqᴰ {f = f}{g = g} fᴰ gᴰ =
        ΣPathP (refl ,
          (Dᴰ.rectify $ Dᴰ.≡out $
           (sym $ Dᴰ.reindEq-pathFiller _ _)
            ∙ Dᴰ.reind-filler _ _))

module _
  {C : Category Cob CHom-ℓ}
  (Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ)
  where
  private
    module C = CategoryNotation C

  module _ (C-⋆ : C.Id⋆Eq) where
    -- An alternative to v[_] for taking fiber categories
    -- For this construction to be well-behaved,
    -- C must have definitionally that C.id ⋆ C.id Eq.≡ C.id
    fibEq : (c : Cob) → Category _ _
    fibEq c = CatᴰOverUNIT→Cat (reindexEq (elimUNIT c) Cᴰ Eq.refl λ _ _ → C-⋆)

  fib' : (c : Cob) → Category _ _
  fib' c = CatᴰOverUNIT→Cat (reindex' (elimUNIT c) Cᴰ)

  fib : (c : Cob) → Category _ _
  fib c = CatᴰOverUNIT→Cat (reindex (elimUNIT c) Cᴰ)
