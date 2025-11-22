{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.LocallySmall.Displayed.NaturalTransformation.Fibered.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)

import Cubical.Data.Equality as Eq
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Reflection.RecordEquiv.More

import Cubical.Categories.Category as Small
import Cubical.Categories.Functor as SmallFunctor
import Cubical.Categories.Displayed.Functor as SmallFunctorᴰ

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Instances.Unit
open import Cubical.Categories.LocallySmall.Instances.Functor.Fibered
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.NaturalTransformation.Fibered
open import Cubical.Categories.LocallySmall.Instances.Indiscrete
open import Cubical.Categories.LocallySmall.Variables

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.SmallDisplayedFibers
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Functor.Properties
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Weaken
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.LocallySmall.Displayed.Constructions.BinProduct.Base

open Category
open Categoryᴰ

open Functorᴰ
-- open FibNatTrans
open Liftω
open Σω

module FiberedFunctorᴰDefs
  {C : SmallCategory ℓC ℓC'}
  {ℓCᴰ ℓCᴰ'}
  (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ')
  {D : Category Dob DHom-ℓ}
  {Dobᴰ DHom-ℓᴰ}
  (Dᴰ : GloballySmallCategoryᴰ D Dobᴰ DHom-ℓᴰ)
  {Eob-ℓᴰ Eobᴰ EHom-ℓᴰ}
  (Eᴰ : SmallFibersCategoryᴰ D Eob-ℓᴰ Eobᴰ EHom-ℓᴰ)
  {Dᴰᴰ-ℓ Dobᴰᴰ DHom-ℓᴰᴰ}
  (Dᴰᴰ : SmallFibersᴰCategoryᴰ Dᴰ Eᴰ Dᴰᴰ-ℓ Dobᴰᴰ DHom-ℓᴰᴰ)
  where
  private
    module C = SmallCategory C
    module Cᴰ = SmallCategoryᴰ Cᴰ
    module D = CategoryNotation D
    module Dᴰ = CategoryᴰNotation Dᴰ
    module Eᴰ = CategoryᴰNotation Eᴰ
    module Dᴰᴰ = SmallFibersᴰNotation Dᴰᴰ

  open FibNatTransDefs C Eᴰ public
  open SmallCategoryᴰ

  FiberedFunctorᴰ : {d : Dob} → (F : FiberedFunctor d) → (dᴰ : Dobᴰ d) → Typeω
  FiberedFunctorᴰ {d} F dᴰ = Functorᴰ F Cᴰ.catᴰ Dᴰᴰ.vᴰ[ d ][ dᴰ ]

  module FiberedFunctorᴰNotation
    {d : Dob} {dᴰ : Dobᴰ d} {F : FiberedFunctor d}
    (Fᴰ : FiberedFunctorᴰ F dᴰ) where
    open FunctorᴰNotation Fᴰ public


  module _
    (D-⋆ : ∀ {x} → D.id D.⋆ D.id Eq.≡ D.id {x = x})
    (F-seq' : ∀ {d dᴰ} →
     {x y z : Liftω (Eobᴰ d)} (f : Hom[ fibEq Eᴰ D-⋆ d , x ] y)
      (g : Hom[ fibEq Eᴰ D-⋆ d , y ] z) →
      (Categoryᴰ.∫C (Dᴰ ×ᴰ Eᴰ) ⋆
       Functor.F-hom (fibᴰEqF D Dᴰ Eᴰ Dᴰᴰ d dᴰ D-⋆) f)
      (Functor.F-hom (fibᴰEqF D Dᴰ Eᴰ Dᴰᴰ d dᴰ D-⋆) g)
      Eq.≡
      Functor.F-hom (fibᴰEqF D Dᴰ Eᴰ Dᴰᴰ d dᴰ D-⋆)
      ((fibEq Eᴰ D-⋆ d ⋆ f) g))
    where

    FiberedFunctorEqᴰ : {d : Dob} → (F : FiberedFunctorEq D-⋆ d) → (dᴰ : Dobᴰ d) → Typeω
    FiberedFunctorEqᴰ {d} F dᴰ =
      Functorᴰ F
        Cᴰ.catᴰ
        (fibᴰEq D Dᴰ Eᴰ Dᴰᴰ d dᴰ D-⋆ F-seq')

    FiberedFunctorᴰ→FiberedFunctorEqᴰ :
      {d : Dob} → {F : FiberedFunctor d} → {dᴰ : Dobᴰ d} →
      FiberedFunctorᴰ F dᴰ →
      FiberedFunctorEqᴰ (FiberedFunctor→FiberedFunctorEq D-⋆ d F) dᴰ
    FiberedFunctorᴰ→FiberedFunctorEqᴰ Fᴰ .F-obᴰ = F-obᴰ Fᴰ
    FiberedFunctorᴰ→FiberedFunctorEqᴰ Fᴰ .F-homᴰ = F-homᴰ Fᴰ
    FiberedFunctorᴰ→FiberedFunctorEqᴰ Fᴰ .F-idᴰ =
      F-idᴰ Fᴰ
      ∙ ΣPathP (fib→fibEq Eᴰ D-⋆ _ .Functor.F-id ,
        (Dᴰᴰ.rectify $ Dᴰᴰ.≡out $ sym $ Dᴰᴰ.reind-filler _ _))
    FiberedFunctorᴰ→FiberedFunctorEqᴰ Fᴰ .F-seqᴰ _ _ =
      F-seqᴰ Fᴰ _ _
      ∙ ΣPathP (fib→fibEq Eᴰ D-⋆ _ .Functor.F-seq _ _ ,
        (Dᴰᴰ.rectify $ Dᴰᴰ.≡out $
          (sym $ Dᴰᴰ.reind-filler _ _)
          ∙ Dᴰᴰ.reindEq-pathFiller _ _))

    FiberedFunctorEqᴰ→FiberedFunctorᴰ :
      {d : Dob} → {F : FiberedFunctorEq D-⋆ d} → {dᴰ : Dobᴰ d} →
      FiberedFunctorEqᴰ F dᴰ →
      FiberedFunctorᴰ (FiberedFunctorEq→FiberedFunctor D-⋆ d F) dᴰ
    FiberedFunctorEqᴰ→FiberedFunctorᴰ Fᴰ .F-obᴰ = F-obᴰ Fᴰ
    FiberedFunctorEqᴰ→FiberedFunctorᴰ Fᴰ .F-homᴰ = F-homᴰ Fᴰ
    FiberedFunctorEqᴰ→FiberedFunctorᴰ Fᴰ .F-idᴰ =
      F-idᴰ Fᴰ
      ∙ ΣPathP (fibEq→fib Eᴰ D-⋆ _ .Functor.F-id ,
        (Dᴰᴰ.rectify $ Dᴰᴰ.≡out $ Dᴰᴰ.reind-filler _ _))
    FiberedFunctorEqᴰ→FiberedFunctorᴰ Fᴰ .F-seqᴰ _ _ =
      F-seqᴰ Fᴰ _ _
      ∙ ΣPathP (fibEq→fib Eᴰ D-⋆ _ .Functor.F-seq _ _ ,
        (Dᴰᴰ.rectify $ Dᴰᴰ.≡out $
          (sym $ Dᴰᴰ.reindEq-pathFiller _ _)
          ∙ Dᴰᴰ.reind-filler _ _))

module FibNatTransᴰDefs
  {C : SmallCategory ℓC ℓC'}
  {ℓCᴰ ℓCᴰ'}
  (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ')
  {D : Category Dob DHom-ℓ}
  {Dobᴰ DHom-ℓᴰ}
  (Dᴰ : GloballySmallCategoryᴰ D Dobᴰ DHom-ℓᴰ)
  {Eob-ℓᴰ Eobᴰ EHom-ℓᴰ}
  (Eᴰ : SmallFibersCategoryᴰ D Eob-ℓᴰ Eobᴰ EHom-ℓᴰ)
  {Dᴰᴰ-ℓ Dobᴰᴰ DHom-ℓᴰᴰ}
  (Dᴰᴰ : SmallFibersᴰCategoryᴰ Dᴰ Eᴰ Dᴰᴰ-ℓ Dobᴰᴰ DHom-ℓᴰᴰ)
  where
  private
    module C = SmallCategory C
    module Cᴰ = SmallCategoryᴰ Cᴰ
    module D = CategoryNotation D
    module Dᴰ = CategoryᴰNotation Dᴰ
    module Eᴰ = CategoryᴰNotation Eᴰ
    module Dᴰᴰ = SmallFibersᴰNotation Dᴰᴰ
  open FiberedFunctorᴰDefs Cᴰ Dᴰ Eᴰ Dᴰᴰ public
  open FibNatTrans

  module _
    {d d' : Dob}
    {g : D.Hom[ d , d' ]}
    {dᴰ : Dobᴰ d}
    {dᴰ' : Dobᴰ d'}
    (gᴰ : Dᴰ.Hom[ g ][ dᴰ , dᴰ' ])
    {F : FiberedFunctor d}
    {G : FiberedFunctor d'}
    (α : FibNatTrans g F G)
    (Fᴰ : FiberedFunctorᴰ F dᴰ)
    (Gᴰ : FiberedFunctorᴰ G dᴰ')
    where
    private
      module F = FiberedFunctorNotation F
      module G = FiberedFunctorNotation G
      module Fᴰ = FiberedFunctorᴰNotation Fᴰ
      module Gᴰ = FiberedFunctorᴰNotation Gᴰ

    N-homᴰTy :
     (N-obᴰ :
        {x : C.small-ob} →
        (xᴰ : Cᴰ.small-obᴰ x) →
        Dᴰᴰ.Hom[ g , (gᴰ , α .N-ob x) ][ Fᴰ.F-obᴰ (liftω xᴰ) , Gᴰ.F-obᴰ (liftω xᴰ) ]) →
      ∀ {x y : C.small-ob}
        {xᴰ : Cᴰ.small-obᴰ x}
        {yᴰ : Cᴰ.small-obᴰ y}
        {f : C.Hom[ liftω x , liftω y ]}
        (fᴰ : Cᴰ.Hom[ f ][ liftω xᴰ , liftω yᴰ ]) →
        Type _
    N-homᴰTy N-obᴰ {xᴰ = xᴰ}{yᴰ = yᴰ} fᴰ =
      (Fᴰ.F-homᴰ fᴰ Dᴰᴰ.⋆ᴰ N-obᴰ yᴰ) Dᴰᴰ.∫≡
        (N-obᴰ xᴰ Dᴰᴰ.⋆ᴰ Gᴰ.F-homᴰ fᴰ)

    record FibNatTransᴰ :
      Type
        (ℓ-max (ℓ-max (DHom-ℓᴰᴰ d d' dᴰ dᴰ')
               (EHom-ℓᴰ d d'))
        (ℓ-max (ℓ-max DHom-ℓᴰ (ℓ-max ℓCᴰ' ℓCᴰ))
        (ℓ-max (DHom-ℓ d d') (ℓ-max ℓC' ℓC))))
      where
      no-eta-equality
      constructor natTransᴰ
      field
        N-obᴰ :
          {x : C.small-ob} →
          (xᴰ : Cᴰ.small-obᴰ x) →
          Dᴰᴰ.Hom[ g , (gᴰ , α .N-ob x) ][ Fᴰ.F-obᴰ (liftω xᴰ) , Gᴰ.F-obᴰ (liftω xᴰ) ]
        N-homᴰ :
          ∀ {x}{y}{xᴰ} {yᴰ}
            {f : C.Hom[ liftω x , liftω y ]}
            (fᴰ : Cᴰ.Hom[ f ][ liftω xᴰ , liftω yᴰ ]) →
            N-homᴰTy N-obᴰ fᴰ

    FibNatTransᴰIsoΣ :
      Iso FibNatTransᴰ
        (Σ[ N-obᴰ ∈
          (∀ {x : C.small-ob} → (xᴰ : Cᴰ.small-obᴰ x) →
             Dᴰᴰ.Hom[ g , (gᴰ , α .N-ob x) ][ Fᴰ.F-obᴰ (liftω xᴰ) ,
                                              Gᴰ.F-obᴰ (liftω xᴰ)  ])]
          (∀ {x y} {xᴰ} {yᴰ}
            {f : C.Hom[ liftω x , liftω y ]}
            (fᴰ : Cᴰ.Hom[ f ][ liftω xᴰ , liftω yᴰ ]) →
            N-homᴰTy N-obᴰ fᴰ))
    unquoteDef FibNatTransᴰIsoΣ =
      defineRecordIsoΣ FibNatTransᴰIsoΣ (quote FibNatTransᴰ)

    isSetFibNatTransᴰ : isSet FibNatTransᴰ
    isSetFibNatTransᴰ =
      isSetIso FibNatTransᴰIsoΣ
        (isSetΣSndProp
          (isSetImplicitΠ λ _ → isSetΠ λ _ → Dᴰᴰ.isSetHomᴰ)
          (λ _ → isPropImplicitΠ4 λ _ _ _ _ →
            isPropImplicitΠ λ _ → isPropΠ λ _ →
              ∫C Dᴰᴰ .isSetHom _ _))

  open FibNatTransᴰ

  module _
    {d : Dob}
    {dᴰ : Dobᴰ d}
    {F : FiberedFunctor d}
    (Fᴰ : FiberedFunctorᴰ F dᴰ)
    where

    idFibTransᴰ : FibNatTransᴰ Dᴰ.idᴰ (idFibTrans F) Fᴰ Fᴰ
    idFibTransᴰ .N-obᴰ = λ xᴰ → Dᴰᴰ.idᴰ
    idFibTransᴰ .N-homᴰ fᴰ = Dᴰᴰ.⋆IdRᴰ _ ∙ (sym $ Dᴰᴰ.⋆IdLᴰ _)

  module _
    {d d' d'' : Dob}
    {dᴰ : Dobᴰ d}
    {dᴰ' : Dobᴰ d'}
    {dᴰ'' : Dobᴰ d''}
    {g : D.Hom[ d , d' ]} {g' : D.Hom[ d' , d'' ]}
    {gᴰ : Dᴰ.Hom[ g ][ dᴰ , dᴰ' ]} {gᴰ' : Dᴰ.Hom[ g' ][ dᴰ' , dᴰ'' ]}
    {F : FiberedFunctor d}
    {G : FiberedFunctor d'}
    {H : FiberedFunctor d''}
    {Fᴰ : FiberedFunctorᴰ F dᴰ}
    {Gᴰ : FiberedFunctorᴰ G dᴰ'}
    {Hᴰ : FiberedFunctorᴰ H dᴰ''}
    {α : FibNatTrans g F G}
    {β : FibNatTrans g' G H}
    (αᴰ : FibNatTransᴰ gᴰ α Fᴰ Gᴰ)
    (βᴰ : FibNatTransᴰ gᴰ' β Gᴰ Hᴰ)
    where

    seqFibTransᴰ : FibNatTransᴰ (gᴰ Dᴰ.⋆ᴰ gᴰ') (seqFibTrans α β) Fᴰ Hᴰ
    seqFibTransᴰ .N-obᴰ xᴰ = αᴰ .N-obᴰ xᴰ Dᴰᴰ.⋆ᴰ βᴰ .N-obᴰ xᴰ
    seqFibTransᴰ .N-homᴰ fᴰ =
      (sym $ Dᴰᴰ.⋆Assocᴰ _ _ _)
      ∙ Dᴰᴰ.⟨ αᴰ .N-homᴰ fᴰ ⟩⋆⟨⟩
      ∙ Dᴰᴰ.⋆Assocᴰ _ _ _
      ∙ Dᴰᴰ.⟨⟩⋆⟨ βᴰ .N-homᴰ fᴰ ⟩
      ∙ (sym $ Dᴰᴰ.⋆Assocᴰ _ _ _)

  module _
    {d d' : Dob}
    {dᴰ : Dobᴰ d}
    {dᴰ' : Dobᴰ d'}
    {g g' : D.Hom[ d , d' ]}
    {gᴰ : Dᴰ.Hom[ g ][ dᴰ , dᴰ' ]}
    {gᴰ' : Dᴰ.Hom[ g' ][ dᴰ , dᴰ' ]}
    {F : FiberedFunctor d}
    {G : FiberedFunctor d'}
    {Fᴰ : FiberedFunctorᴰ F dᴰ}
    {Gᴰ : FiberedFunctorᴰ G dᴰ'}
    {α : FibNatTrans g F G}
    {β : FibNatTrans g' F G}
    (αᴰ : FibNatTransᴰ gᴰ α Fᴰ Gᴰ)
    (βᴰ : FibNatTransᴰ gᴰ' β Fᴰ Gᴰ)
    where
    private
      module F = FiberedFunctorNotation F
      module G = FiberedFunctorNotation G
      module Fᴰ = FiberedFunctorᴰNotation Fᴰ
      module Gᴰ = FiberedFunctorᴰNotation Gᴰ
      module ∫Dᴰᴰ = CategoryNotation (∫C Dᴰᴰ)

    makeFibNatTransᴰPathP :
      (gᴰ≡ : gᴰ Dᴰ.∫≡ gᴰ') →
      (α≡β : PathP (λ i → FibNatTrans (gᴰ≡ i .fst) F G) α β) →
      PathP (λ i → ∀ {x : C.small-ob} → (xᴰ : Cᴰ.small-obᴰ x) →
        Dᴰᴰ.Hom[ (gᴰ≡ i .fst) , ((gᴰ≡ i .snd) , (α≡β i .N-ob x)) ][
          Fᴰ.F-obᴰ (liftω xᴰ) , Gᴰ.F-obᴰ (liftω xᴰ) ])
        (αᴰ .N-obᴰ)
        (βᴰ .N-obᴰ) →
      PathP (λ i → FibNatTransᴰ (gᴰ≡ i .snd) (α≡β i) Fᴰ Gᴰ) αᴰ βᴰ
    makeFibNatTransᴰPathP gᴰ≡ α≡β p i .N-obᴰ xᴰ = p i xᴰ
    makeFibNatTransᴰPathP gᴰ≡ α≡β p i .N-homᴰ {xᴰ = xᴰ} {yᴰ = yᴰ} fᴰ =
      isSet→SquareP (λ i j → ∫Dᴰᴰ.isSetHom)
        (αᴰ .N-homᴰ fᴰ) (βᴰ .N-homᴰ fᴰ)
        (λ j → (_ , Fᴰ.F-homᴰ fᴰ) ∫Dᴰᴰ.⋆ (_ , (p j yᴰ)))
        (λ j → (_ , p j xᴰ) ∫Dᴰᴰ.⋆ (_ , Gᴰ.F-homᴰ fᴰ))
        i

  private
    C⇒Eᴰ : Categoryᴰ D FiberedFunctor _
    C⇒Eᴰ = FIBERED-FUNCTOR C Eᴰ

    Dᴰ×C⇒Eᴰ = Dᴰ ×ᴰ C⇒Eᴰ
    module Dᴰ×C⇒Eᴰ = CategoryᴰNotation Dᴰ×C⇒Eᴰ

  module _
    {d d' : Dob}
    {dᴰ : Dobᴰ d}
    {dᴰ' : Dobᴰ d'}
    {g g' : D.Hom[ d , d' ]}
    {gᴰ : Dᴰ.Hom[ g ][ dᴰ , dᴰ' ]}
    {gᴰ' : Dᴰ.Hom[ g' ][ dᴰ , dᴰ' ]}
    {F : FiberedFunctor d}
    {G : FiberedFunctor d'}
    {Fᴰ : FiberedFunctorᴰ F dᴰ}
    {Gᴰ : FiberedFunctorᴰ G dᴰ'}
    {α : FibNatTrans g F G}
    {β : FibNatTrans g' F G}
    {αᴰ : FibNatTransᴰ gᴰ α Fᴰ Gᴰ}
    {βᴰ : FibNatTransᴰ gᴰ' β Fᴰ Gᴰ}
    (gᴰα≡gᴰ'β : gᴰ , α Dᴰ×C⇒Eᴰ.∫≡ gᴰ' , β)
    (p : ∀ {x} (xᴰ : Cᴰ.small-obᴰ x) →
      αᴰ .N-obᴰ xᴰ Dᴰᴰ.∫≡ βᴰ .N-obᴰ xᴰ)
    where
    private
      module F = FiberedFunctorNotation F
      module G = FiberedFunctorNotation G
      module Fᴰ = FiberedFunctorᴰNotation Fᴰ
      module Gᴰ = FiberedFunctorᴰNotation Gᴰ
      module ∫Dᴰᴰ = CategoryNotation (∫C Dᴰᴰ)

    makeFibNatTransᴰPath :
      Path
        (Σ[ (g , gᴰ , γ) ∈
           Dᴰ×C⇒Eᴰ.∫Hom[ (d , dᴰ , F) , (d' , dᴰ' , G) ] ]
         FibNatTransᴰ gᴰ γ Fᴰ Gᴰ)
        (_ , αᴰ) (_ , βᴰ)
    makeFibNatTransᴰPath =
      ΣPathP
        (gᴰα≡gᴰ'β ,
        makeFibNatTransᴰPathP αᴰ βᴰ
          (λ i → (gᴰα≡gᴰ'β i .fst) , (gᴰα≡gᴰ'β i .snd .fst)) (λ i → gᴰα≡gᴰ'β i .snd .snd)
          (implicitFunExt λ {x} → funExt λ xᴰ → Dᴰᴰ.rectify $ Dᴰᴰ.≡out $ p xᴰ))
