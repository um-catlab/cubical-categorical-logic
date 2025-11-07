module Cubical.Categories.LocallySmall.NaturalTransformation.Base where

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

-- We want to define a category of presheaves of various universe
-- levels.
--
-- A Psh C ℓP should be a functor C^o → SET.v[ ℓP ].
-- this is equivalent to a displayed functor weaken C^op → SET.v[ ℓP ] over K ℓP : 1 → LEVEL
--
-- So the category of all Psh C is the total category of the category
-- of displayed functors weaken 1 C^op → SET

-- the type of natural transformations between functors of locally
-- small categories is large because while each D.Hom[_,_] is small,
-- they can each be in a different universe, the natural
-- transformations have to be in the universe ⨆_x Hom-ℓ (F x) (G x),
-- which is ω.

-- This means we do *not* get a locally small category of functors
-- between arbitrary locally small categories, only a large category.
record LargeNatTrans {C : Category Cob CHom-ℓ}{D : Category Dob DHom-ℓ}
  (F G : Functor C D) : Typeω
  where
  no-eta-equality
  constructor natTrans
  private
    module F = FunctorNotation F
    module G = FunctorNotation G
    module C = CategoryNotation C
    module D = CategoryNotation D
  field
    N-ob : ∀ x → D.Hom[ F.F-ob x , G.F-ob x ]
    N-hom : ∀ {x y}(f : C.Hom[ x , y ])
      → (F.F-hom f D.⋆ N-ob y) ≡ (N-ob x D.⋆ G.F-hom f)

-- To make a small type of natural transformations, we need
-- 1. C to have a small type of objects and a global universe level of all homs (i.e., a Small Category)
-- 2. D to have a global universe level
module _ {C : SmallCategory ℓC ℓC'} where
  private
    module C = SmallCategory C
  record NatTrans
    {D : GloballySmallCategory Dob ℓD'}
    (F G : Functor C.cat D)
    : Type (ℓ-max ℓC $ ℓ-max ℓC' $ ℓD')
    where
    no-eta-equality
    constructor natTrans
    private
      module F = FunctorNotation F
      module G = FunctorNotation G
      module D = CategoryNotation D
    field
      N-ob : ∀ x → D.Hom[ F.F-ob (liftω x) , G.F-ob (liftω x) ]
      N-hom : ∀ {x y}(f : C.Hom[ liftω x , liftω y ])
        → (F.F-hom f D.⋆ N-ob y) ≡ (N-ob x D.⋆ G.F-hom f)
-- open NatTrans

module _ {C : SmallCategory ℓC ℓC'}{D : GloballySmallCategory Dob ℓD'} where
  private
    module C = SmallCategory C
    module D = CategoryNotation D

  open NatTrans
  idTrans : (F : Functor C.cat D) → NatTrans F F
  idTrans F = natTrans (λ x → D.id) (λ f → D.⋆IdR _ ∙ (sym $ D.⋆IdL _))
    where module F = Functor F

  seqTrans :
    {F G H : Functor C.cat D}
    (α : NatTrans F G)
    (β : NatTrans G H)
    → NatTrans F H
  seqTrans α β = natTrans
    (λ x → α .N-ob x D.⋆ β .N-ob x)
    λ f → sym (D.⋆Assoc _ _ _)
      ∙ D.⟨ α .N-hom f ⟩⋆⟨⟩
      ∙ D.⋆Assoc _ _ _
      ∙ D.⟨⟩⋆⟨ β .N-hom f ⟩
      ∙ sym (D.⋆Assoc _ _ _)

  module _ (F G : Functor C.cat D) where
    private
      module F = Functor F
      module G = Functor G
    NatTransIsoΣ :
      Iso (NatTrans F G)
          (Σ[ N-ob ∈ (∀ x → D.Hom[ F.F-ob (liftω x) , G.F-ob (liftω x) ]) ]
            (∀ {x y}(f : C.Hom[ liftω x , liftω y ])
             → (F.F-hom f D.⋆ N-ob y) ≡ (N-ob x D.⋆ G.F-hom f)))
    unquoteDef NatTransIsoΣ = defineRecordIsoΣ NatTransIsoΣ (quote (NatTrans))

  makeNatTransPath : ∀ {F G : Functor C.cat D}
    {α β : NatTrans F G}
    → α .N-ob ≡ β .N-ob
    → α ≡ β
  makeNatTransPath {α = α}{β} α≡β = isoFunInjective (NatTransIsoΣ _ _) α β
    (ΣPathPProp (λ _ → isPropImplicitΠ2 (λ _ _ → isPropΠ (λ _ → D.isSetHom _ _)))
    α≡β)

module _ (C : SmallCategory ℓC ℓC')(D : GloballySmallCategory Dob ℓD') where
  private
    module C = SmallCategory C
    module D = CategoryNotation D
  FUNCTOR : GloballySmallCategory (Functor C.cat D) (ℓ-max (ℓ-max ℓC ℓC') ℓD')
  FUNCTOR .Hom[_,_] F G = NatTrans F G
  FUNCTOR .Category.id = idTrans _
  FUNCTOR .Category._⋆_ = seqTrans
  FUNCTOR .Category.⋆IdL α = makeNatTransPath $ funExt λ _ → D.⋆IdL _
  FUNCTOR .Category.⋆IdR α = makeNatTransPath $ funExt λ _ → D.⋆IdR _
  FUNCTOR .Category.⋆Assoc α β γ = makeNatTransPath $ funExt λ _ →
    D.⋆Assoc _ _ _
  FUNCTOR .Category.isSetHom = isSetIso (NatTransIsoΣ _ _)
    (isSetΣ
      (isSetΠ (λ _ → D.isSetHom))
      λ _ → isProp→isSet (isPropImplicitΠ2 (λ _ _ → isPropΠ (λ f → D.isSetHom _ _))))

-- Things that contribute to the size:
-- 1. x  -- need small Cob
-- 2. xᴰ -- need global bound on Cobᴰ
-- 3. Dᴰ.Hom -- need global bound on Dᴰ.Hom
-- 4. f  -- need global bound on C.Hom
-- 5. fᴰ -- need global bound on Cᴰ.Hom
-- 6. Dᴰ.∫≡ -- need global bound on Dᴰ.Hom and D.Hom

-- TODO: SmallNatTransᴰ
-- record SmallNatTransᴰ
--   {C-ob D-ob CHom-ℓ DHom-ℓ}
--   {C : Category C-ob CHom-ℓ}
--   {D : Category D-ob DHom-ℓ}
--   {F G : Functor C D}
--   {Cobᴰ Dobᴰ CHom-ℓᴰ DHom-ℓᴰ}
--   {Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ}
--   {Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ}
--   (α : SmallNatTrans F G)
--   (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
--   (Gᴰ : Functorᴰ G Cᴰ Dᴰ)
--   : Typeω
--   where
--   no-eta-equality
--   private
--     module α = LargeNatTrans α
--     module F = FunctorNotation F
--     module Fᴰ = FunctorᴰNotation Fᴰ
--     module G = FunctorNotation G
--     module Gᴰ = FunctorᴰNotation Gᴰ
--     module C =  CategoryNotation C
--     module Cᴰ = CategoryᴰNotation Cᴰ
--     module D =  CategoryNotation D
--     module Dᴰ = CategoryᴰNotation Dᴰ
--   field
--     N-obᴰ : ∀ {x}(xᴰ : Cobᴰ x) → Dᴰ.Hom[ α.N-ob x ][ Fᴰ.F-obᴰ xᴰ , Gᴰ.F-obᴰ xᴰ ]
--     N-homᴰ : ∀ {x y xᴰ yᴰ}{f : C.Hom[ x , y ]}
--       (fᴰ  : Cᴰ.Hom[ f ][ xᴰ , yᴰ ])
--       → (Fᴰ.F-homᴰ fᴰ Dᴰ.⋆ᴰ N-obᴰ yᴰ) Dᴰ.∫≡ (N-obᴰ xᴰ Dᴰ.⋆ᴰ Gᴰ.F-homᴰ fᴰ)

--
-- This works, but is unfortunately not satisfied by weaken C → SET so it isn't this simple...Everything holds except SET is not globally small, the Hom sets are of arbitrarily high universe level.

-- But it still works out that PshHom between presheaves is small
-- because the Functors are indexed only by an object and the size of
-- the displayed Homs is determined only by the objects of the base
-- (i.e., small fibers)
--

-- Let's generalize specifically the construction for Presheaves.
--
-- This is equivalent to a LargeNatTrans between
-- functors from weaken 1 C^o to SET
-- Let's try that directly first.
--
--
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
--     -- module Cᴰ = CategoryᴰNotation Cᴰ
--     module D =  CategoryNotation D
--     module Dᴰ = CategoryᴰNotation Dᴰ

--   record SmallFibNatTransᴰ : Type (ℓ-max (DHom-ℓᴰ (F.F-ob _) (G.F-ob _)) $ ℓ-max ℓD' $ ℓ-max ℓC' ℓC)
--     where
--     no-eta-equality
--     field
--       N-ob : ∀ x → Dᴰ.Hom[ α.N-ob _ ][ Fᴰ.F-obᴰ (liftω x) , Gᴰ.F-obᴰ (liftω x) ]
--       N-hom : ∀ {x y}
--         (f  : C.Hom[ liftω x , liftω y ])
--         → (Fᴰ.F-homᴰ f Dᴰ.⋆ᴰ N-ob y) Dᴰ.∫≡ (N-ob x Dᴰ.⋆ᴰ Gᴰ.F-homᴰ f)

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
