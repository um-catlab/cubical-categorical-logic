module Cubical.Categories.LocallySmall.Displayed.NaturalTransformation.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)

open import Cubical.Data.Sigma

open import Cubical.Reflection.RecordEquiv.More

import Cubical.Categories.Category as Small
open import Cubical.Categories.LocallySmall.Base as LocallySmall
open import Cubical.Categories.LocallySmall.Instances.Unit
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.NaturalTransformation.Base
open import Cubical.Categories.LocallySmall.Variables

open import Cubical.Categories.LocallySmall.Displayed.Base
open import Cubical.Categories.LocallySmall.Displayed.Properties
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Weaken

open Category
open Categoryᴰ

record LargeNatTransᴰ
  {C-ob D-ob CHom-ℓ DHom-ℓ}
  {C : Category C-ob CHom-ℓ}
  {D : Category D-ob DHom-ℓ}
  {F G : Functor C D}
  {Cobᴰ Dobᴰ CHom-ℓᴰ DHom-ℓᴰ}
  {Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ}
  {Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ}
  (α : LargeNatTrans F G)
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  (Gᴰ : Functorᴰ G Cᴰ Dᴰ)
  : Typeω
  where
  no-eta-equality
  private
    module α = LargeNatTrans α
    module F = FunctorNotation F
    module Fᴰ = FunctorᴰNotation Fᴰ
    module G = FunctorNotation G
    module Gᴰ = FunctorᴰNotation Gᴰ
    module C =  CategoryNotation C
    module Cᴰ = CategoryᴰNotation Cᴰ
    module D =  CategoryNotation D
    module Dᴰ = CategoryᴰNotation Dᴰ
  field
    N-obᴰ : ∀ {x}(xᴰ : Cobᴰ x) → Dᴰ.Hom[ α.N-ob x ][ Fᴰ.F-obᴰ xᴰ , Gᴰ.F-obᴰ xᴰ ]
    N-homᴰ : ∀ {x y xᴰ yᴰ}{f : C.Hom[ x , y ]}
      (fᴰ  : Cᴰ.Hom[ f ][ xᴰ , yᴰ ])
      → (Fᴰ.F-homᴰ fᴰ Dᴰ.⋆ᴰ N-obᴰ yᴰ) Dᴰ.∫≡ (N-obᴰ xᴰ Dᴰ.⋆ᴰ Gᴰ.F-homᴰ fᴰ)

-- module _
--   {(Cob , C) : SmallCategory ℓC ℓC'}
--   {(Dob , D) : SmallCategory ℓD ℓD'}
--   {F G : Functor UNIT D} -- i.e., just an object
--   {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
--   {Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
--   (α : NatTrans F G) -- i.e., just a morphism
--   (Fᴰ : Functorᴰ F (weaken UNIT C) Dᴰ)
--   (Gᴰ : Functorᴰ G (weaken UNIT C) Dᴰ)
--   where

open Functorᴰ
open SmallFibNatTrans
open Liftω
open Σω
module SmallFibNatTransᴰDefs
  {(Cob , C) : SmallCategory ℓC ℓC'}
  {ℓCᴰ ℓCᴰ'}
  ((Cobᴰ , Cᴰ) : SmallCategoryᴰ ((Cob , C)) ℓCᴰ ℓCᴰ')
  {D : Category Dob DHom-ℓ}
  {Dob-ℓᴰ Dobᴰ DHom-ℓᴰ}
  (Dᴰ : SmallFibersCategoryᴰ D Dob-ℓᴰ Dobᴰ DHom-ℓᴰ)
  {Eob-ℓᴰ Eobᴰ}
  {EHom-ℓᴰ : Dob → Dob → Level}
  (Eᴰ : SmallFibersCategoryᴰ (∫C Dᴰ) Eob-ℓᴰ Eobᴰ λ u v → EHom-ℓᴰ (u .fst ) (v .fst))
  where
  private
    module C = CategoryNotation C
    module Cᴰ = CategoryᴰNotation Cᴰ
    module D = CategoryNotation D
    module Dᴰ = CategoryᴰNotation Dᴰ
    module Eᴰ = CategoryᴰOver∫SFNotation Eᴰ

  module _
    {d d' : Dob}
    {g : D.Hom[ d , d' ]}
    {F : Functor C Dᴰ.v[ d ]}
    {G : Functor C Dᴰ.v[ d' ]}
    (α : SmallFibNatTrans Dᴰ g F G)
    (Fᴰ : Functorᴰ F Cᴰ Eᴰ.vᴰ[ d ]SF)
    (Gᴰ : Functorᴰ G Cᴰ Eᴰ.vᴰ[ d' ]SF)
    where
    private
      module F = FunctorNotation F
      module G = FunctorNotation G
      module Fᴰ = FunctorᴰNotation Fᴰ
      module Gᴰ = FunctorᴰNotation Gᴰ

    record SmallFibNatTransᴰ :
      Type
        (ℓ-max
          (ℓ-max (ℓ-max ℓC ℓCᴰ) (EHom-ℓᴰ d d'))
          (ℓ-max (DHom-ℓᴰ d d') (ℓ-max (ℓ-max ℓC' ℓCᴰ') (DHom-ℓ d d'))))
      where
      no-eta-equality
      constructor natTransᴰ
      field
        N-obᴰ :
          {x : Cob .lowerω} →
          (xᴰ : Cobᴰ .lowerω x) →
          Eᴰ.Hom[ g , α .N-ob x ][
            Fᴰ .F-obᴰ (liftω xᴰ) ,
            Gᴰ .F-obᴰ (liftω xᴰ) ]
        N-homᴰ :
          ∀ {x y : Cob .lowerω}
            {xᴰ : Cobᴰ .lowerω x}
            {yᴰ : Cobᴰ .lowerω y}
            {f : C.Hom[ liftω x , liftω y ]}
            (fᴰ : Cᴰ.Hom[ f ][ liftω xᴰ , liftω yᴰ ]) →
            (Fᴰ.F-homᴰ fᴰ Eᴰ.⋆ᴰ N-obᴰ yᴰ)
              Eᴰ.∫≡ (N-obᴰ xᴰ Eᴰ.⋆ᴰ Gᴰ.F-homᴰ fᴰ)

  open SmallFibNatTransᴰ

  module _
    {d : Dob}
    {F : Functor C Dᴰ.v[ d ]}
    (Fᴰ : Functorᴰ F Cᴰ Eᴰ.vᴰ[ d ]SF)
    where

    idSFTransᴰ : SmallFibNatTransᴰ (idSFTrans F) Fᴰ Fᴰ
    idSFTransᴰ .N-obᴰ = λ xᴰ → Eᴰ.idᴰ
    idSFTransᴰ .N-homᴰ fᴰ = Eᴰ.⋆IdRᴰ _ ∙ (sym $ Eᴰ.⋆IdLᴰ _)

  module _
    {d d' d'' : Dob}
    {g : D.Hom[ d , d' ]} {h : D.Hom[ d' , d'' ]}
    {F : Functor C Dᴰ.v[ d ]}
    {G : Functor C Dᴰ.v[ d' ]}
    {H : Functor C Dᴰ.v[ d'' ]}
    {Fᴰ : Functorᴰ F Cᴰ Eᴰ.vᴰ[ d ]SF}
    {Gᴰ : Functorᴰ G Cᴰ Eᴰ.vᴰ[ d' ]SF}
    {Hᴰ : Functorᴰ H Cᴰ Eᴰ.vᴰ[ d'' ]SF}
    {α : SmallFibNatTrans Dᴰ g F G}
    {β : SmallFibNatTrans Dᴰ h G H}
    (αᴰ : SmallFibNatTransᴰ α Fᴰ Gᴰ)
    (βᴰ : SmallFibNatTransᴰ β Gᴰ Hᴰ)
    where

    seqSFTransᴰ : SmallFibNatTransᴰ (seqSFTrans α β) Fᴰ Hᴰ
    seqSFTransᴰ .N-obᴰ xᴰ = αᴰ .N-obᴰ xᴰ Eᴰ.⋆ᴰ βᴰ .N-obᴰ xᴰ
    seqSFTransᴰ .N-homᴰ fᴰ =
      (sym $ Eᴰ.⋆Assocᴰ _ _ _)
      ∙ Eᴰ.⟨ αᴰ .N-homᴰ fᴰ ⟩⋆⟨⟩
      ∙ Eᴰ.⋆Assocᴰ _ _ _
      ∙ Eᴰ.⟨⟩⋆⟨ βᴰ .N-homᴰ fᴰ ⟩
      ∙ (sym $ Eᴰ.⋆Assocᴰ _ _ _)

-- module _
--   {(Cob , C) : SmallCategory ℓC ℓC'}
--   {(Dob , D) : SmallCategory ℓD ℓD'}
--   {F G : Functor UNIT D} -- i.e., just an object
--   {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
--   {Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
--   (α : NatTrans F G) -- i.e., just a morphism
--   (Fᴰ : Functorᴰ F (weaken UNIT C) Dᴰ)
--   (Gᴰ : Functorᴰ G (weaken UNIT C) Dᴰ)
--   where
--   private
--     module α = NatTrans α
--     module F = FunctorNotation F
--     module Fᴰ = FunctorᴰNotation Fᴰ
--     module G = FunctorNotation G
--     module Gᴰ = FunctorᴰNotation Gᴰ
--     module C =  CategoryNotation C
--     module D =  CategoryNotation D
--     module Dᴰ = CategoryᴰNotation Dᴰ

--   record SmallFibNatTransᴰ : Type (ℓ-max (DHom-ℓᴰ (F.F-ob _) (G.F-ob _)) $ ℓ-max ℓD' $ ℓ-max ℓC' ℓC)
--     where
--     no-eta-equality
--     field
--       N-obᴰ : ∀ x →
--         Dᴰ.Hom[ α.N-ob _ ][ Fᴰ.F-obᴰ (liftω x) , Gᴰ.F-obᴰ (liftω x) ]
--       N-homᴰ : ∀ {x y}
--         (f  : C.Hom[ liftω x , liftω y ]) →
--         ({!!} Dᴰ.⋆ⱽᴰ {!!}) ≡ {!!}

--       -- N-homᴰ : ∀ {x y}
--       --   (f  : C.Hom[ liftω x , liftω y ])
--       --   → (Fᴰ.F-homᴰ f Dᴰ.⋆ᴰ N-obᴰ y) Dᴰ.∫≡ (N-obᴰ x Dᴰ.⋆ᴰ Gᴰ.F-homᴰ f)

-- open SmallFibNatTransᴰ

-- module _
--   {(Cob , C) : SmallCategory ℓC ℓC'}
--   {(Dob , D) : SmallCategory ℓD ℓD'}
--   {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
--   {Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
--   where
--   private
--     module C =  CategoryNotation C
--     module D =  CategoryNotation D
--     module Dᴰ = CategoryᴰNotation Dᴰ

--   idSFTransᴰ :
--     {F : Functor UNIT D} →
--     (Fᴰ : Functorᴰ F (weaken UNIT C) Dᴰ) →
--     SmallFibNatTransᴰ (idTrans F) Fᴰ Fᴰ
--   idSFTransᴰ Fᴰ .N-obᴰ _ = Dᴰ.idᴰ
--   idSFTransᴰ Fᴰ .N-homᴰ fᴰ =
--     {!!}
