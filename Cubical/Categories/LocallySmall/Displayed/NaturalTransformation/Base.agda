module Cubical.Categories.LocallySmall.Displayed.NaturalTransformation.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)

open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Reflection.RecordEquiv.More

import Cubical.Categories.Category as Small
open import Cubical.Categories.LocallySmall.Base as LocallySmall
open import Cubical.Categories.LocallySmall.Instances.Unit
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.NaturalTransformation.Base
open import Cubical.Categories.LocallySmall.Instances.Indiscrete
open import Cubical.Categories.LocallySmall.Instances.Functor.Base
open import Cubical.Categories.LocallySmall.Variables

open import Cubical.Categories.LocallySmall.Displayed.Base
open import Cubical.Categories.LocallySmall.Displayed.Properties
open import Cubical.Categories.LocallySmall.Displayed.SmallFibers
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

open Functorᴰ
open SmallFibNatTrans
open Liftω
open Σω
module SmallFibNatTransᴰDefs
  {C : SmallCategory ℓC ℓC'}
  {ℓCᴰ ℓCᴰ'}
  (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ')
  {D : Category Dob DHom-ℓ}
  {Dob-ℓᴰ Dobᴰ DHom-ℓᴰ}
  (Dᴰ : SmallFibersCategoryᴰ D Dob-ℓᴰ Dobᴰ DHom-ℓᴰ)
  {E : Category Eob EHom-ℓ}
  {Dᴰᴰ-ℓ Dobᴰᴰ DHom-ℓᴰᴰ}
  (Dᴰᴰ : SmallFibersᴰCategoryᴰ Dᴰ E Dᴰᴰ-ℓ Dobᴰᴰ DHom-ℓᴰᴰ)
  where
  private
    module C = CategoryNotation ⟨ C ⟩smallcat
    module Cᴰ = CategoryᴰNotation ⟨ Cᴰ ⟩smallcatᴰ
    module D = CategoryNotation D
    module Dᴰ = CategoryᴰNotation Dᴰ
    module Dᴰᴰ = SmallFibersᴰCategoryᴰNotation Dᴰᴰ
    module E = CategoryNotation E

    Dᴰ×E = weaken (∫C Dᴰ) E
    module Dᴰ×E = CategoryᴰNotation Dᴰ×E
    module ∫Dᴰ×E = CategoryNotation Dᴰ×E.∫C

    C⇒Dᴰ = FIBER-FUNCTOR C Dᴰ
    module C⇒Dᴰ = CategoryᴰNotation C⇒Dᴰ
    ∫C⇒Dᴰ = ∫C (FIBER-FUNCTOR C Dᴰ)
    module ∫C⇒Dᴰ = CategoryNotation ∫C⇒Dᴰ

    weaken∫C⇒Dᴰ : Categoryᴰ _ _ _
    weaken∫C⇒Dᴰ = weaken ∫C⇒Dᴰ E
    module weaken∫C⇒Dᴰ = Categoryᴰ weaken∫C⇒Dᴰ


  module _
    {d d' : Dob}
    {g : D.Hom[ d , d' ]}
    {e e' : Eob}
    (h : E.Hom[ e , e' ])
    {F : Functor ⟨ C ⟩smallcat Dᴰ.v[ d ]}
    {G : Functor ⟨ C ⟩smallcat Dᴰ.v[ d' ]}
    (α : SmallFibNatTrans Dᴰ g F G)
    (Fᴰ : Functorᴰ F ⟨ Cᴰ ⟩smallcatᴰ ⟨ Dᴰᴰ.vᴰ[ d ][ e ] ⟩smallcatᴰ)
    (Gᴰ : Functorᴰ G ⟨ Cᴰ ⟩smallcatᴰ ⟨ Dᴰᴰ.vᴰ[ d' ][ e' ] ⟩smallcatᴰ)
    where
    private
      module F = FunctorNotation F
      module G = FunctorNotation G
      module Fᴰ = FunctorᴰNotation Fᴰ
      module Gᴰ = FunctorᴰNotation Gᴰ

    record SmallFibNatTransᴰ :
      Type
        (ℓ-max
          (ℓ-max (ℓ-max (EHom-ℓ e e') (ℓ-max ℓC ℓCᴰ)) (DHom-ℓᴰᴰ d d' e e'))
          (ℓ-max (DHom-ℓᴰ d d') (ℓ-max (ℓ-max ℓC' ℓCᴰ') (DHom-ℓ d d'))))
      where
      no-eta-equality
      constructor natTransᴰ
      field
        N-obᴰ :
          {x : ⟨ C ⟩small-ob} →
          (xᴰ : ⟨ Cᴰ ⟩small-obᴰ x) →
          Dᴰᴰ.Hom[ (g , α .N-ob x) , h  ][ Fᴰ.F-obᴰ (liftω xᴰ) ,
                                           Gᴰ.F-obᴰ (liftω xᴰ) ]
        N-homᴰ :
          ∀ {x y : ⟨ C ⟩small-ob}
            {xᴰ : ⟨ Cᴰ ⟩small-obᴰ x}
            {yᴰ : ⟨ Cᴰ ⟩small-obᴰ y}
            {f : C.Hom[ liftω x , liftω y ]}
            (fᴰ : Cᴰ.Hom[ f ][ liftω xᴰ , liftω yᴰ ]) →
            (Fᴰ.F-homᴰ fᴰ Dᴰᴰ.⋆ᴰ N-obᴰ yᴰ)
              Dᴰᴰ.∫≡ (N-obᴰ xᴰ Dᴰᴰ.⋆ᴰ Gᴰ.F-homᴰ fᴰ)

    SFNatTransᴰIsoΣ :
      Iso SmallFibNatTransᴰ
        (Σ[ N-obᴰ ∈
          (∀ {x : ⟨ C ⟩small-ob} → (xᴰ : ⟨ Cᴰ ⟩small-obᴰ x) →
             Dᴰᴰ.Hom[ (g , α .N-ob x) , h ][ Fᴰ.F-obᴰ (liftω xᴰ) ,
                                             Gᴰ.F-obᴰ (liftω xᴰ)  ])]

          (∀ {x y : ⟨ C ⟩small-ob}
            {xᴰ : ⟨ Cᴰ ⟩small-obᴰ x}
            {yᴰ : ⟨ Cᴰ ⟩small-obᴰ y}
            {f : C.Hom[ liftω x , liftω y ]}
            (fᴰ : Cᴰ.Hom[ f ][ liftω xᴰ , liftω yᴰ ]) →
            (Fᴰ.F-homᴰ fᴰ Dᴰᴰ.⋆ᴰ N-obᴰ yᴰ)
              Dᴰᴰ.∫≡ (N-obᴰ xᴰ Dᴰᴰ.⋆ᴰ Gᴰ.F-homᴰ fᴰ)))
    unquoteDef SFNatTransᴰIsoΣ =
      defineRecordIsoΣ SFNatTransᴰIsoΣ (quote SmallFibNatTransᴰ)

    isSetSFNatTransᴰ : isSet SmallFibNatTransᴰ
    isSetSFNatTransᴰ =
      isSetIso SFNatTransᴰIsoΣ
        (isSetΣSndProp
          (isSetImplicitΠ λ _ → isSetΠ λ _ → Dᴰᴰ.isSetHomᴰ)
          (λ _ → isPropImplicitΠ4 λ _ _ _ _ →
            isPropImplicitΠ λ _ → isPropΠ λ _ →
              ∫C Dᴰᴰ .isSetHom _ _))

  open SmallFibNatTransᴰ

  module _
    {d : Dob} {e : Eob}
    {F : Functor ⟨ C ⟩smallcat Dᴰ.v[ d ]}
    (Fᴰ : Functorᴰ F ⟨ Cᴰ ⟩smallcatᴰ ⟨ Dᴰᴰ.vᴰ[ d ][ e ] ⟩smallcatᴰ)
    where

    idSFTransᴰ : SmallFibNatTransᴰ E.id (idSFTrans F) Fᴰ Fᴰ
    idSFTransᴰ .N-obᴰ = λ xᴰ → Dᴰᴰ.idᴰ
    idSFTransᴰ .N-homᴰ fᴰ = Dᴰᴰ.⋆IdRᴰ _ ∙ (sym $ Dᴰᴰ.⋆IdLᴰ _)

  module _
    {d d' d'' : Dob}
    {e e' e'' : Eob}
    {g : D.Hom[ d , d' ]} {g' : D.Hom[ d' , d'' ]}
    {h : E.Hom[ e , e' ]} {h' : E.Hom[ e' , e'' ]}
    {F : Functor ⟨ C ⟩smallcat Dᴰ.v[ d ]}
    {G : Functor ⟨ C ⟩smallcat Dᴰ.v[ d' ]}
    {H : Functor ⟨ C ⟩smallcat Dᴰ.v[ d'' ]}
    {Fᴰ : Functorᴰ F ⟨ Cᴰ ⟩smallcatᴰ ⟨ Dᴰᴰ.vᴰ[ d ][ e ] ⟩smallcatᴰ}
    {Gᴰ : Functorᴰ G ⟨ Cᴰ ⟩smallcatᴰ ⟨ Dᴰᴰ.vᴰ[ d' ][ e' ] ⟩smallcatᴰ}
    {Hᴰ : Functorᴰ H ⟨ Cᴰ ⟩smallcatᴰ ⟨ Dᴰᴰ.vᴰ[ d'' ][ e'' ] ⟩smallcatᴰ}
    {α : SmallFibNatTrans Dᴰ g F G}
    {β : SmallFibNatTrans Dᴰ g' G H}
    (αᴰ : SmallFibNatTransᴰ h α Fᴰ Gᴰ)
    (βᴰ : SmallFibNatTransᴰ h' β Gᴰ Hᴰ)
    where

    seqSFTransᴰ : SmallFibNatTransᴰ (h E.⋆ h') (seqSFTrans α β) Fᴰ Hᴰ
    seqSFTransᴰ .N-obᴰ xᴰ = αᴰ .N-obᴰ xᴰ Dᴰᴰ.⋆ᴰ βᴰ .N-obᴰ xᴰ
    seqSFTransᴰ .N-homᴰ fᴰ =
      (sym $ Dᴰᴰ.⋆Assocᴰ _ _ _)
      ∙ Dᴰᴰ.⟨ αᴰ .N-homᴰ fᴰ ⟩⋆⟨⟩
      ∙ Dᴰᴰ.⋆Assocᴰ _ _ _
      ∙ Dᴰᴰ.⟨⟩⋆⟨ βᴰ .N-homᴰ fᴰ ⟩
      ∙ (sym $ Dᴰᴰ.⋆Assocᴰ _ _ _)

  module _
    {d d' : Dob} {e e' : Eob}
    {g g' : D.Hom[ d , d' ]}
    {h h' : E.Hom[ e , e' ]}
    {F : Functor ⟨ C ⟩smallcat Dᴰ.v[ d ]}
    {G : Functor ⟨ C ⟩smallcat Dᴰ.v[ d' ]}
    {α : SmallFibNatTrans Dᴰ g F G}
    {β : SmallFibNatTrans Dᴰ g' F G}
    {Fᴰ : Functorᴰ F ⟨ Cᴰ ⟩smallcatᴰ ⟨ Dᴰᴰ.vᴰ[ d ][ e ] ⟩smallcatᴰ}
    {Gᴰ : Functorᴰ G ⟨ Cᴰ ⟩smallcatᴰ ⟨ Dᴰᴰ.vᴰ[ d' ][ e' ] ⟩smallcatᴰ}
    (αᴰ : SmallFibNatTransᴰ h α Fᴰ Gᴰ)
    (βᴰ : SmallFibNatTransᴰ h' β Fᴰ Gᴰ)
    where
    private
      module F = FunctorNotation F
      module G = FunctorNotation G
      module Fᴰ = FunctorᴰNotation Fᴰ
      module Gᴰ = FunctorᴰNotation Gᴰ
      module ∫Dᴰᴰ = CategoryNotation (∫C Dᴰᴰ)

    makeSFNatTransᴰPathP :
      (g≡g' : g ≡ g') →
      (h≡h' : h ≡ h') →
      (α≡β : PathP (λ i → SmallFibNatTrans Dᴰ (g≡g' i) F G) α β) →
      PathP (λ i → ∀ {x : ⟨ C ⟩small-ob} → (xᴰ : ⟨ Cᴰ ⟩small-obᴰ x) →
        Dᴰᴰ.Hom[ (g≡g' i , α≡β i .N-ob x) , h≡h' i ][ Fᴰ.F-obᴰ (liftω xᴰ) ,
                                                      Gᴰ.F-obᴰ (liftω xᴰ) ])
        (αᴰ .N-obᴰ)
        (βᴰ .N-obᴰ) →
      PathP (λ i → SmallFibNatTransᴰ (h≡h' i) (α≡β i) Fᴰ Gᴰ) αᴰ βᴰ
    makeSFNatTransᴰPathP g≡g' h≡h' α≡β p i .N-obᴰ xᴰ = p i xᴰ
    makeSFNatTransᴰPathP g≡g' h≡h' α≡β p i .N-homᴰ {xᴰ = xᴰ} {yᴰ = yᴰ} fᴰ =
      isSet→SquareP (λ i j → ∫Dᴰᴰ.isSetHom)
        (αᴰ .N-homᴰ fᴰ) (βᴰ .N-homᴰ fᴰ)
        (λ j → (_ , Fᴰ.F-homᴰ fᴰ) ∫Dᴰᴰ.⋆ (_ , p j yᴰ))
        (λ j → (_ , p j xᴰ) ∫Dᴰᴰ.⋆ (_ , Gᴰ.F-homᴰ fᴰ))
        i

  module _
    {d d' : Dob}
    {e e' : Eob}
    {g g' : D.Hom[ d , d' ]}
    {h h' : E.Hom[ e , e' ]}
    {F : Functor ⟨ C ⟩smallcat Dᴰ.v[ d ]}
    {G : Functor ⟨ C ⟩smallcat Dᴰ.v[ d' ]}
    {α : SmallFibNatTrans Dᴰ g F G}
    {β : SmallFibNatTrans Dᴰ g' F G}
    {Fᴰ : Functorᴰ F ⟨ Cᴰ ⟩smallcatᴰ ⟨ Dᴰᴰ.vᴰ[ d ][ e ] ⟩smallcatᴰ}
    {Gᴰ : Functorᴰ G ⟨ Cᴰ ⟩smallcatᴰ ⟨ Dᴰᴰ.vᴰ[ d' ][ e' ] ⟩smallcatᴰ}
    {αᴰ : SmallFibNatTransᴰ h α Fᴰ Gᴰ}
    {βᴰ : SmallFibNatTransᴰ h' β Fᴰ Gᴰ}
    (α≡β : Path (weaken∫C⇒Dᴰ.Hom[ ((d , F) , e) , ((d' , G) , e') ])
      ((g , α) , h) ((g' , β) , h'))
    (p : ∀ {x} (xᴰ : ⟨ Cᴰ ⟩small-obᴰ x) →
      αᴰ .N-obᴰ xᴰ Dᴰᴰ.∫≡ βᴰ .N-obᴰ xᴰ)
    where
    private
      module F = FunctorNotation F
      module G = FunctorNotation G
      module Fᴰ = FunctorᴰNotation Fᴰ
      module Gᴰ = FunctorᴰNotation Gᴰ
      module ∫Dᴰᴰ = CategoryNotation (∫C Dᴰᴰ)

    makeSFNatTransᴰPath :
      Path
        (Σ[ ((g , γ) , h) ∈
          weaken∫C⇒Dᴰ.Hom[ ((d , F) , e) , ((d' , G) , e') ] ]
            SmallFibNatTransᴰ h γ Fᴰ Gᴰ)
        (_ , αᴰ)
        (_ , βᴰ)
    makeSFNatTransᴰPath =
      ΣPathP
        (α≡β ,
        makeSFNatTransᴰPathP αᴰ βᴰ
          (λ i → α≡β i .fst .fst) (λ i → α≡β i .snd) (λ i → α≡β i .fst .snd)
          (implicitFunExt λ {x} → funExt λ xᴰ → Dᴰᴰ.rectify $ Dᴰᴰ.≡out $ p xᴰ))
