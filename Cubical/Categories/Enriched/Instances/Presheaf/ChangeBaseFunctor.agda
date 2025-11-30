{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Enriched.Instances.Presheaf.ChangeBaseFunctor where 

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf.Constructions.Lift
open import Cubical.Categories.Enriched.Functors.Base
open import Cubical.Categories.Enriched.Instances.Presheaf.ChangeBase
open import Cubical.Categories.Enriched.Instances.Presheaf.Self
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Monoidal.Instances.Presheaf
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Morphism.Alt hiding (_∘ˡ_)

open Category
open EnrichedCategory
open EnrichedFunctor
open Functor
open NatTrans

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS ℓS' ℓE ℓE' : Level
module _
  {C : Category ℓC ℓC'}
  {ℓS : Level}
  where
  
  private
    module PMC = PshMon C ℓS
    ℓm = PMC.ℓm
    V = PMC.𝓟Mon

  module _
    {EC : EnrichedCategory V ℓE}
    {EC' : EnrichedCategory V ℓE'}
    (EF : EnrichedFunctor V EC EC')
    (ℓS' : Level)
    where

    LiftEF : 
      EnrichedFunctor 
        (PshMon.𝓟Mon C (ℓ-max ℓm ℓS')) 
        (LiftE EC)
        (LiftE EC')
    LiftEF .F-ob = EF .F-ob
    LiftEF .F-hom = LiftF ∘ʳ EF .F-hom
    LiftEF .F-id = makeNatTransPath (funExt λ c → funExt λ _ → 
      cong lift (cong (λ h → h .N-ob c tt*) (EF .F-id)))
    LiftEF .F-seq = 
      makeNatTransPath (funExt λ c → funExt λ (lift f , lift g) → 
        cong lift (cong (λ h → h .N-ob c (f , g)) (EF .F-seq)) )
{-
  Given EF V C D 

  return EF V' LiftE C LiftE D
-}


module _ 
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  (F : Functor D C)
  {ℓS : Level}
  (ℓS' : Level) where
  
  private 
    module PMC = PshMon C ℓS 
    VC = PMC.𝓟Mon

    ℓmC = ℓ-max ℓC (ℓ-max ℓC' ℓS)
    ℓmD = ℓ-max ℓD (ℓ-max ℓD' ℓS')
    𝓛 = ℓ-max ℓmD ℓmC

    module LPMC = PshMon C 𝓛
    LVC = LPMC.𝓟Mon

    module LPMD = PshMon D 𝓛
    LVD = LPMD.𝓟Mon

  module _ 
    {EC : EnrichedCategory VC ℓE}
    {EC' : EnrichedCategory VC ℓE'}
    (EF : EnrichedFunctor VC EC EC') where 

    BaseChangeF : 
      EnrichedFunctor 
        LVD 
        (BaseChange F ℓmD _ EC) 
        (BaseChange F ℓmD _ EC') 
    BaseChangeF .F-ob = EF .F-ob
    BaseChangeF .F-hom = (LiftF ∘ʳ EF .F-hom) ∘ˡ (F ^opF)
    BaseChangeF .F-id = makeNatTransPath (funExt λ d → funExt λ tt* →  
      (cong (λ h → h .N-ob (F-ob F d) tt*) (LiftEF EF _ .F-id)) )
    BaseChangeF .F-seq = makeNatTransPath (funExt λ d → funExt λ (f , g) → 
      ((cong (λ h → h .N-ob (F-ob F d) (f , g)) (LiftEF EF _ .F-seq))))

  open PshHom
  open import Cubical.Data.Sigma
  BaseLiftSelf : 
    EnrichedFunctor LVD 
      (BaseChange F ℓmD ℓS (self C ℓS)) 
      (self D 𝓛) 
  BaseLiftSelf .F-ob P = (LiftF {ℓ' = ℓmD} ∘F P) ∘F (F ^opF)
  BaseLiftSelf .F-hom .N-ob d (lift f) .N-ob d' (g , lift FXd')= 
    lift (f .N-ob  (F .F-ob d') ((F .F-hom g) , FXd'))
  BaseLiftSelf .F-hom {X}{Y} .N-ob d (lift f) .N-hom d' d'' g (h , FXd'') = 
    cong lift 
      (cong (λ h → f .N-ob _ h) 
      (ΣPathP (F .F-seq _ _ , refl)) 
      ∙ f .N-hom (F .F-ob d') (F .F-ob d'') (F. F-hom g) 
      (F .F-hom h , FXd'' .lower))
  BaseLiftSelf .F-hom .N-hom f = funExt λ s → 
    makePshHomPath (funExt λ d' → funExt λ r → 
    cong lift (cong (λ h → s .lower .N-ob _ h) 
    (ΣPathP (sym (F .F-seq _ _) , refl))))
  BaseLiftSelf .F-id = makeNatTransPath (funExt λ d → funExt λ _ → 
    makePshHomPath (funExt λ d' → funExt λ (f , lift Fxd') → refl))
  BaseLiftSelf .F-seq = makeNatTransPath (funExt λ d → funExt λ n →
      makePshHomPath (funExt λ d' → funExt λ m → 
      cong lift (cong (λ h → n .snd .lower .N-ob _ h) 
      (ΣPathP 
      (cong (λ h → F .F-hom h) (D .⋆IdL _) ∙ sym (C .⋆IdL _) , 
      (cong (λ h → n .fst .lower .N-ob _ h) 
        (ΣPathP 
          (cong (λ h → F .F-hom h) (D .⋆IdL _) ∙ sym (C .⋆IdL _) , 
          refl))))))))
  
  -- note LiftEF and BaseChangeF 
  -- do not modify the objects of the enriched categories

module _ 
  {C : Category ℓC ℓC'}
  (ℓS ℓS' : Level) where 

  ℓm = ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓS ℓS')

  module LPMC = PshMon C ℓm
  LVC = LPMC.𝓟Mon

  open PshHom
  
  LiftSelf : 
    EnrichedFunctor LVC 
      (LiftE {ℓS' = ℓS' } (self C ℓS))
      (self C ℓm) 
  LiftSelf .F-ob = LiftF {ℓ' = ℓS'} ∘F_
  LiftSelf .F-hom .N-ob c (lift f) .N-ob c' (g , lift Fxc') = 
    lift (f . N-ob c' ((g , Fxc')))
  LiftSelf .F-hom .N-ob c (lift f) .N-hom c' c'' g (h , lift Fxc'')= 
    cong lift (f .N-hom c' c'' g (h , Fxc''))
  LiftSelf .F-hom .N-hom f = funExt λ (lift g) → 
    makePshHomPath (funExt λ c →  funExt λ (f , lift Fc) → refl)
  LiftSelf .F-id = makeNatTransPath (funExt λ c → funExt λ _ →
    makePshHomPath (funExt λ c' → funExt λ (f , lift Fxc') → cong lift refl) )
  LiftSelf .F-seq = makeNatTransPath (funExt λ c → funExt λ (f , g) → 
    makePshHomPath (funExt λ c' → funExt λ (f , x) → refl)) 

{-
  BaseChangeSelf : 
    EnrichedFunctor LVD 
      (BaseChange F ℓmD _ (self C ℓS)) 
      (LiftE {ℓS' = ℓmC } (self D ℓS'))
  BaseChangeSelf .F-ob = {!  !}
  BaseChangeSelf .F-hom = {! LiftOb _ (LiftE {ℓS' = 𝓛 } (self D ℓS')) ℓmC !}
  BaseChangeSelf .F-id = {!  LiftEC (LiftE {ℓS' = 𝓛 } (self D ℓS')) ℓmC !}
  BaseChangeSelf .F-seq = {!   !}
-}


{-


  BaseChangeSelf : EnrichedFunctor PMD.𝓟Mon (BaseChange F (self C _)) (self D _)
  BaseChangeSelf .F-ob = reindPsh F
  BaseChangeSelf .F-hom = distrib^ F (self C _)
  BaseChangeSelf .F-id =
    makeNatTransPath (funExt λ m → funExt λ {tt* →
    makePshHomPath (funExt λ n → funExt λ {(f , XFn) → refl})})
  BaseChangeSelf .F-seq =
    makeNatTransPath (funExt λ m → funExt λ{(f , x) →
    makePshHomPath (funExt λ n → funExt λ {(g , XFn) →
      cong (λ h → x . PshHom.N-ob _ h)
        (cong₂ _,_
          (cong (λ h → F .F-hom h) (D .⋆IdL _) ∙ sym (C .⋆IdL _))
          (cong (λ h → f .PshHom.N-ob _ (h , XFn))
          (cong (λ h → F .F-hom h) (D .⋆IdL _) ∙ sym (C .⋆IdL _))))})})
-}

  -- goal 
  -- EnrichedFunctor in presehaves on C but at the correct level

{-
module _ 
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  (F : Functor D C)
  (ℓS ℓS' : Level) where 

  private
    ℓmC = ℓ-max (ℓ-max ℓC ℓC') ℓS
    ℓmD = ℓ-max (ℓ-max ℓD ℓD') ℓS'
    ℓm = ℓ-max ℓmC ℓmD
    module PMC = PshMon C ℓm
    module PMD = PshMon D ℓm
    VC = PMC.𝓟Mon
    VD = PMD.𝓟Mon

    module MC = MonoidalCategory VC
    module MD = MonoidalCategory VD

  module _
    {EC EC' : EnrichedCategory VC ℓE}
    (EF : EnrichedFunctor VC EC EC')
    where

    BaseChangeF : 
      EnrichedFunctor 
        VD 
        (BaseChange F ℓS _ EC) 
        (BaseChange F ℓS _ EC') 
    BaseChangeF .F-ob = EF .F-ob
    BaseChangeF .F-hom = (LiftF ∘ʳ EF .F-hom) ∘ˡ (F ^opF)
    BaseChangeF .F-id = makeNatTransPath (funExt λ d → funExt λ tt* → 
      cong lift (cong (λ h → h .N-ob (F-ob F d) tt*) (EF .F-id)) )
    BaseChangeF .F-seq = 
      makeNatTransPath (funExt λ d → funExt λ (lift f , lift g) → 
        cong lift ((cong (λ h → h .N-ob (F-ob F d) (f , g)) (EF .F-seq))))

-}

