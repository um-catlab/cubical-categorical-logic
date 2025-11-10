module Cubical.Categories.LocallySmall.NaturalTransformation.SmallFibered where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Reflection.RecordEquiv.More

import Cubical.Categories.Category as Small
open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.Variables

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties

open Category
open Categoryᴰ

module _
  {C : SmallCategory ℓC ℓC'}
  {D : Category Dob DHom-ℓ}
  {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  (Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ)
  where
  private
    module C = SmallCategory C
    module D = CategoryNotation D
    module Dᴰ = CategoryᴰNotation Dᴰ
  module _
    {d d' : Dob} (g : D.Hom[ d , d' ])
    (F : Functor C.cat Dᴰ.v[ d ]) (G : Functor C.cat Dᴰ.v[ d' ])
    where
    private
      module F = FunctorNotation F
      module G = FunctorNotation G
    record SmallFibNatTrans : Type (ℓ-max (DHom-ℓᴰ d d') $ ℓ-max ℓC' ℓC)
      where
      no-eta-equality
      constructor natTrans
      field
        N-ob : ∀ x → Dᴰ.Hom[ g ][ F.F-ob (liftω x) , G.F-ob (liftω x) ]
        N-hom : ∀ {x y}
          (f  : C.Hom[ liftω x , liftω y ])
          → (F.F-hom f Dᴰ.⋆ⱽᴰ N-ob y) ≡ (N-ob x Dᴰ.⋆ᴰⱽ G.F-hom f)

      N-hom' : ∀ {x y}
          (f  : C.Hom[ liftω x , liftω y ])
          → (F.F-hom f Dᴰ.⋆ᴰ N-ob y) Dᴰ.∫≡ (N-ob x Dᴰ.⋆ᴰ G.F-hom f)
      N-hom' f = Dᴰ.reind-filler _ _ ∙ Dᴰ.≡in (N-hom f) ∙ (sym $ Dᴰ.reind-filler _ _)

    module _
      (N-ob : ∀ x → Dᴰ.Hom[ g ][ F.F-ob (liftω x) , G.F-ob (liftω x) ])
      where
      -- This is useful for establishing naturality when the goal has
      -- transports on the endpoints
      -- but the module structure for this definition is bonked so you
      -- need to provide many arguments manually
      N-hom'→N-hom : ∀ {x y}
          (f  : C.Hom[ liftω x , liftω y ])
          → (F.F-hom f Dᴰ.⋆ᴰ N-ob y) Dᴰ.∫≡ (N-ob x Dᴰ.⋆ᴰ G.F-hom f)
          → (F.F-hom f Dᴰ.⋆ⱽᴰ N-ob y) ≡ (N-ob x Dᴰ.⋆ᴰⱽ G.F-hom f)
      N-hom'→N-hom f p =
        Dᴰ.rectify $ Dᴰ.≡out $
          (sym $ Dᴰ.reind-filler _ _)
          ∙ p
          ∙ Dᴰ.reind-filler _ _

module _
  {C : SmallCategory ℓC ℓC'}
  {D : Category Dob DHom-ℓ}
  {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  {Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  where
  private
    module C =  SmallCategory C
    module D =  CategoryNotation D
    module Dᴰ = CategoryᴰNotation Dᴰ
  open SmallFibNatTrans
  idSFTrans : ∀ {d}(F : Functor C.cat Dᴰ.v[ d ])
    → SmallFibNatTrans Dᴰ D.id F F
  idSFTrans F .N-ob _ = Dᴰ.idᴰ
  idSFTrans F .N-hom f = Dᴰ.rectify $ Dᴰ.≡out $ Dᴰ.⋆IdRⱽᴰ _ ∙ (sym $ Dᴰ.⋆IdLᴰⱽ _)

  seqSFTrans : ∀ {d d' d''}
    {g : D.Hom[ d , d' ]}{g' : D.Hom[ d' , d'' ]}
    {F G H}
    (α : SmallFibNatTrans {_}{_}{_}{_}{C} Dᴰ g F G)
    (β : SmallFibNatTrans Dᴰ g' G H)
    → SmallFibNatTrans Dᴰ (g D.⋆ g') F H
  seqSFTrans α β .N-ob x = α .N-ob x Dᴰ.⋆ᴰ β .N-ob x
  seqSFTrans α β .N-hom f = Dᴰ.rectify $ Dᴰ.≡out $
    sym (Dᴰ.⋆Assocⱽᴰᴰ _ _ _)
    ∙ Dᴰ.⟨ Dᴰ.≡in $ α .N-hom f ⟩⋆⟨⟩
    ∙ Dᴰ.⋆Assocᴰⱽᴰ _ _ _
    ∙ Dᴰ.⟨⟩⋆⟨ Dᴰ.≡in $ β .N-hom f ⟩
    ∙ (sym $ Dᴰ.⋆Assocᴰᴰⱽ _ _ _)

  module _
    {d d'}
    (g : D.Hom[ d , d' ])
    (F : Functor C.cat Dᴰ.v[ d ])
    (G : Functor C.cat Dᴰ.v[ d' ])
    where
    private
      module F = Functor F
      module G = Functor G
    SFNatTransIsoΣ :
      Iso (SmallFibNatTrans Dᴰ g F G)
        (Σ[ N-ob ∈ (∀ x → Dᴰ.Hom[ g ][ F.F-ob (liftω x) , G.F-ob (liftω x) ])]
        (∀ {x y}
          (f  : C.Hom[ liftω x , liftω y ])
          → (F.F-hom f Dᴰ.⋆ⱽᴰ N-ob y) ≡ (N-ob x Dᴰ.⋆ᴰⱽ G.F-hom f)))
    unquoteDef SFNatTransIsoΣ = defineRecordIsoΣ SFNatTransIsoΣ (quote (SmallFibNatTrans))

    isSetSFNatTrans : isSet (SmallFibNatTrans Dᴰ g F G)
    isSetSFNatTrans =
      isSetRetract (Iso.fun SFNatTransIsoΣ ) (Iso.inv SFNatTransIsoΣ)
        (Iso.leftInv SFNatTransIsoΣ)
        (isSetΣSndProp
          (isSetΠ (λ _ → Dᴰ.isSetHomᴰ))
          (λ _ → isPropImplicitΠ2 (λ _ _ → isPropΠ (λ _ → Dᴰ.isSetHomᴰ _ _))))

  makeSFNatTransPathP : ∀ {d d'}
    {g g' : D.Hom[ d , d' ]}
    {F : Functor C.cat Dᴰ.v[ d ]}
    {G : Functor C.cat Dᴰ.v[ d' ]}
    {α : SmallFibNatTrans Dᴰ g F G}
    {β : SmallFibNatTrans Dᴰ g' F G}
    → (g≡g' : g ≡ g')
    → PathP
        (λ i → ∀ x →
          Dᴰ.Hom[ g≡g' i ][ Functor.F-ob F (liftω x),
                            Functor.F-ob G (liftω x) ])
        (α .N-ob)
        (β .N-ob)
    → PathP (λ i → SmallFibNatTrans Dᴰ (g≡g' i) F G) α β
  makeSFNatTransPathP g≡g' p i .N-ob x = p i x
  makeSFNatTransPathP {F = F} {G = G} {α = α} {β = β} g≡g' p i .N-hom {x = x} {y = y} f =
    isSet→SquareP (λ i j → Dᴰ.isSetHomᴰ)
      (α .N-hom f)
      (β .N-hom f)
      (λ j → Functor.F-hom F f Dᴰ.⋆ⱽᴰ p j y)
      (λ j → p j x Dᴰ.⋆ᴰⱽ Functor.F-hom G f)
      i

  module _
    {d d'} {g g' : D.Hom[ d , d' ]}
    {F : Functor C.cat Dᴰ.v[ d ]}
    {G : Functor C.cat Dᴰ.v[ d' ]}
    {α : SmallFibNatTrans Dᴰ g F G}
    {β : SmallFibNatTrans Dᴰ g' F G}
    (g≡g' : g ≡ g')
    (p : ∀ x → α .N-ob x Dᴰ.∫≡ β .N-ob x)
    where

    makeSFNatTransPath :
      Path (Σ[ h ∈ (D.Hom[ d , d' ]) ] SmallFibNatTrans Dᴰ h F G) ((_ , α)) ((_ , β))
    makeSFNatTransPath =
      ΣPathP
        (g≡g' ,
        makeSFNatTransPathP g≡g' (funExt λ x → Dᴰ.rectify (Dᴰ.≡out (p x))))
