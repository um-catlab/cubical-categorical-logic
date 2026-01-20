
module Cubical.Categories.LocallySmall.Displayed.NaturalTransformation.IntoFiberCategory.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)

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
open import Cubical.Categories.LocallySmall.Instances.Functor.IntoFiberCategory
import Cubical.Categories.LocallySmall.Functor.Base as LocallySmallF
open import Cubical.Categories.LocallySmall.NaturalTransformation.IntoFiberCategory
open import Cubical.Categories.LocallySmall.Instances.Indiscrete
open import Cubical.Categories.LocallySmall.Variables

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.SmallDisplayedFibers
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
import Cubical.Categories.LocallySmall.Displayed.Functor.Base as LocallySmallFᴰ
import Cubical.Categories.LocallySmall.Displayed.Functor.Properties as LocallySmallFᴰ
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Weaken
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.LocallySmall.Displayed.Constructions.BinProduct.Base

open Category
open Categoryᴰ

open LocallySmallF.Functor
open LocallySmallFᴰ.Functorᴰ
open Liftω
open Σω

module FunctorᴰDefs
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

  open NatTransDefs C Eᴰ public
  open SmallCategoryᴰ

  Functorᴰ : {d : Dob} → (F : Functor d) → (dᴰ : Dobᴰ d) → Typeω
  Functorᴰ {d} F dᴰ = LocallySmallFᴰ.Functorᴰ F Cᴰ.catᴰ Dᴰᴰ.vᴰ[ d ][ dᴰ ]

  module FunctorᴰNotation
    {d : Dob} {dᴰ : Dobᴰ d} {F : Functor d}
    (Fᴰ : Functorᴰ F dᴰ) where
    open LocallySmallFᴰ.FunctorᴰNotation Fᴰ public

module NatTransᴰDefs
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
  open FunctorᴰDefs Cᴰ Dᴰ Eᴰ Dᴰᴰ public
  open NatTrans

  module _
    {d d' : Dob}
    {g : D.Hom[ d , d' ]}
    {dᴰ : Dobᴰ d}
    {dᴰ' : Dobᴰ d'}
    (gᴰ : Dᴰ.Hom[ g ][ dᴰ , dᴰ' ])
    {F : Functor d}
    {G : Functor d'}
    (α : NatTrans g F G)
    (Fᴰ : Functorᴰ F dᴰ)
    (Gᴰ : Functorᴰ G dᴰ')
    where
    private
      module F = FunctorNotation F
      module G = FunctorNotation G
      module Fᴰ = FunctorᴰNotation Fᴰ
      module Gᴰ = FunctorᴰNotation Gᴰ

    N-homᴰTy :
     (N-obᴰ :
        {x : C.ob} →
        (xᴰ : Cᴰ.obᴰ x) →
        Dᴰᴰ.Hom[ g , (gᴰ , α .N-ob x) ][ Fᴰ.F-obᴰ (liftω xᴰ) , Gᴰ.F-obᴰ (liftω xᴰ) ]) →
      ∀ {x y : C.ob}
        {xᴰ : Cᴰ.obᴰ x}
        {yᴰ : Cᴰ.obᴰ y}
        {f : C.Hom[ liftω x , liftω y ]}
        (fᴰ : Cᴰ.Hom[ f ][ liftω xᴰ , liftω yᴰ ]) →
        Type _
    N-homᴰTy N-obᴰ {xᴰ = xᴰ}{yᴰ = yᴰ} fᴰ =
      (Fᴰ.F-homᴰ fᴰ Dᴰᴰ.⋆ᴰ N-obᴰ yᴰ) Dᴰᴰ.∫≡
        (N-obᴰ xᴰ Dᴰᴰ.⋆ᴰ Gᴰ.F-homᴰ fᴰ)

    record NatTransᴰ :
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
          {x : C.ob} →
          (xᴰ : Cᴰ.obᴰ x) →
          Dᴰᴰ.Hom[ g , (gᴰ , α .N-ob x) ][ Fᴰ.F-obᴰ (liftω xᴰ) , Gᴰ.F-obᴰ (liftω xᴰ) ]
        N-homᴰ :
          ∀ {x}{y}{xᴰ} {yᴰ}
            {f : C.Hom[ liftω x , liftω y ]}
            (fᴰ : Cᴰ.Hom[ f ][ liftω xᴰ , liftω yᴰ ]) →
            N-homᴰTy N-obᴰ fᴰ

    NatTransᴰIsoΣ :
      Iso NatTransᴰ
        (Σ[ N-obᴰ ∈
          (∀ {x : C.ob} → (xᴰ : Cᴰ.obᴰ x) →
             Dᴰᴰ.Hom[ g , (gᴰ , α .N-ob x) ][ Fᴰ.F-obᴰ (liftω xᴰ) ,
                                              Gᴰ.F-obᴰ (liftω xᴰ)  ])]
          (∀ {x y} {xᴰ} {yᴰ}
            {f : C.Hom[ liftω x , liftω y ]}
            (fᴰ : Cᴰ.Hom[ f ][ liftω xᴰ , liftω yᴰ ]) →
            N-homᴰTy N-obᴰ fᴰ))
    unquoteDef NatTransᴰIsoΣ =
      defineRecordIsoΣ NatTransᴰIsoΣ (quote NatTransᴰ)

    isSetNatTransᴰ : isSet NatTransᴰ
    isSetNatTransᴰ =
      isSetIso NatTransᴰIsoΣ
        (isSetΣSndProp
          (isSetImplicitΠ λ _ → isSetΠ λ _ → Dᴰᴰ.isSetHomᴰ)
          (λ _ → isPropImplicitΠ4 λ _ _ _ _ →
            isPropImplicitΠ λ _ → isPropΠ λ _ →
              ∫C Dᴰᴰ .isSetHom _ _))

  open NatTransᴰ

  module _
    {d : Dob}
    {dᴰ : Dobᴰ d}
    {F : Functor d}
    (Fᴰ : Functorᴰ F dᴰ)
    where

    idTransᴰ : NatTransᴰ Dᴰ.idᴰ (idTrans F) Fᴰ Fᴰ
    idTransᴰ .N-obᴰ = λ xᴰ → Dᴰᴰ.idᴰ
    idTransᴰ .N-homᴰ fᴰ = Dᴰᴰ.⋆IdRᴰ _ ∙ (sym $ Dᴰᴰ.⋆IdLᴰ _)

  module _
    {d d' d'' : Dob}
    {dᴰ : Dobᴰ d}
    {dᴰ' : Dobᴰ d'}
    {dᴰ'' : Dobᴰ d''}
    {g : D.Hom[ d , d' ]} {g' : D.Hom[ d' , d'' ]}
    {gᴰ : Dᴰ.Hom[ g ][ dᴰ , dᴰ' ]} {gᴰ' : Dᴰ.Hom[ g' ][ dᴰ' , dᴰ'' ]}
    {F : Functor d}
    {G : Functor d'}
    {H : Functor d''}
    {Fᴰ : Functorᴰ F dᴰ}
    {Gᴰ : Functorᴰ G dᴰ'}
    {Hᴰ : Functorᴰ H dᴰ''}
    {α : NatTrans g F G}
    {β : NatTrans g' G H}
    (αᴰ : NatTransᴰ gᴰ α Fᴰ Gᴰ)
    (βᴰ : NatTransᴰ gᴰ' β Gᴰ Hᴰ)
    where

    seqTransᴰ : NatTransᴰ (gᴰ Dᴰ.⋆ᴰ gᴰ') (seqTrans α β) Fᴰ Hᴰ
    seqTransᴰ .N-obᴰ xᴰ = αᴰ .N-obᴰ xᴰ Dᴰᴰ.⋆ᴰ βᴰ .N-obᴰ xᴰ
    seqTransᴰ .N-homᴰ fᴰ =
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
    {F : Functor d}
    {G : Functor d'}
    {Fᴰ : Functorᴰ F dᴰ}
    {Gᴰ : Functorᴰ G dᴰ'}
    {α : NatTrans g F G}
    {β : NatTrans g' F G}
    (αᴰ : NatTransᴰ gᴰ α Fᴰ Gᴰ)
    (βᴰ : NatTransᴰ gᴰ' β Fᴰ Gᴰ)
    where
    private
      module F = FunctorNotation F
      module G = FunctorNotation G
      module Fᴰ = FunctorᴰNotation Fᴰ
      module Gᴰ = FunctorᴰNotation Gᴰ
      module ∫Dᴰᴰ = CategoryNotation (∫C Dᴰᴰ)

    makeNatTransᴰPathP :
      (gᴰ≡ : gᴰ Dᴰ.∫≡ gᴰ') →
      (α≡β : PathP (λ i → NatTrans (gᴰ≡ i .fst) F G) α β) →
      PathP (λ i → ∀ {x : C.ob} → (xᴰ : Cᴰ.obᴰ x) →
        Dᴰᴰ.Hom[ (gᴰ≡ i .fst) , ((gᴰ≡ i .snd) , (α≡β i .N-ob x)) ][
          Fᴰ.F-obᴰ (liftω xᴰ) , Gᴰ.F-obᴰ (liftω xᴰ) ])
        (αᴰ .N-obᴰ)
        (βᴰ .N-obᴰ) →
      PathP (λ i → NatTransᴰ (gᴰ≡ i .snd) (α≡β i) Fᴰ Gᴰ) αᴰ βᴰ
    makeNatTransᴰPathP gᴰ≡ α≡β p i .N-obᴰ xᴰ = p i xᴰ
    makeNatTransᴰPathP gᴰ≡ α≡β p i .N-homᴰ {xᴰ = xᴰ} {yᴰ = yᴰ} fᴰ =
      isSet→SquareP (λ i j → ∫Dᴰᴰ.isSetHom)
        (αᴰ .N-homᴰ fᴰ) (βᴰ .N-homᴰ fᴰ)
        (λ j → (_ , Fᴰ.F-homᴰ fᴰ) ∫Dᴰᴰ.⋆ (_ , (p j yᴰ)))
        (λ j → (_ , p j xᴰ) ∫Dᴰᴰ.⋆ (_ , Gᴰ.F-homᴰ fᴰ))
        i

  private
    C⇒Eᴰ : Categoryᴰ D Functor _
    C⇒Eᴰ = FUNCTOR C Eᴰ

    Dᴰ×C⇒Eᴰ = Dᴰ ×ᴰ C⇒Eᴰ
    module Dᴰ×C⇒Eᴰ = CategoryᴰNotation Dᴰ×C⇒Eᴰ

  module _
    {d d' : Dob}
    {dᴰ : Dobᴰ d}
    {dᴰ' : Dobᴰ d'}
    {g g' : D.Hom[ d , d' ]}
    {gᴰ : Dᴰ.Hom[ g ][ dᴰ , dᴰ' ]}
    {gᴰ' : Dᴰ.Hom[ g' ][ dᴰ , dᴰ' ]}
    {F : Functor d}
    {G : Functor d'}
    {Fᴰ : Functorᴰ F dᴰ}
    {Gᴰ : Functorᴰ G dᴰ'}
    {α : NatTrans g F G}
    {β : NatTrans g' F G}
    {αᴰ : NatTransᴰ gᴰ α Fᴰ Gᴰ}
    {βᴰ : NatTransᴰ gᴰ' β Fᴰ Gᴰ}
    (gᴰα≡gᴰ'β : gᴰ , α Dᴰ×C⇒Eᴰ.∫≡ gᴰ' , β)
    (p : ∀ {x} (xᴰ : Cᴰ.obᴰ x) →
      αᴰ .N-obᴰ xᴰ Dᴰᴰ.∫≡ βᴰ .N-obᴰ xᴰ)
    where
    private
      module F = FunctorNotation F
      module G = FunctorNotation G
      module Fᴰ = FunctorᴰNotation Fᴰ
      module Gᴰ = FunctorᴰNotation Gᴰ
      module ∫Dᴰᴰ = CategoryNotation (∫C Dᴰᴰ)

    makeNatTransᴰPath :
      Path
        (Σ[ (g , gᴰ , γ) ∈
           Dᴰ×C⇒Eᴰ.∫Hom[ (d , dᴰ , F) , (d' , dᴰ' , G) ] ]
         NatTransᴰ gᴰ γ Fᴰ Gᴰ)
        (_ , αᴰ) (_ , βᴰ)
    makeNatTransᴰPath =
      ΣPathP
        (gᴰα≡gᴰ'β ,
        makeNatTransᴰPathP αᴰ βᴰ
          (λ i → (gᴰα≡gᴰ'β i .fst) , (gᴰα≡gᴰ'β i .snd .fst)) (λ i → gᴰα≡gᴰ'β i .snd .snd)
          (implicitFunExt λ {x} → funExt λ xᴰ → Dᴰᴰ.rectify $ Dᴰᴰ.≡out $ p xᴰ))
