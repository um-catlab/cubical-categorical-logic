{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Enriched.Instances.Presheaf.ChangeBase where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf.Constructions.Lift
open import Cubical.Categories.Enriched.Functors.Base
open import Cubical.Categories.Enriched.Instances.Presheaf.Self
open import Cubical.Categories.Functor
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
    ℓ ℓ' ℓS ℓE : Level

module _
  {ℓC ℓC' ℓS ℓS' : Level}
  {C : Category ℓC ℓC'}
  (EC : EnrichedCategory (PshMon.𝓟Mon C ℓS) ℓE )
  where
  
  private 
    ℓm = ℓ-max (ℓ-max ℓC ℓC') ℓS
  open import Cubical.Categories.Instances.Sets
  open MonoidalCategory renaming (C to Cat)

  LiftE : EnrichedCategory (PshMon.𝓟Mon C (ℓ-max ℓm ℓS')) ℓE
  LiftE .ob = ob EC
  LiftE .Hom[_,_] X Y = LiftPsh (EC .Hom[_,_] X Y) ℓS'
  LiftE .id .N-ob c tt* = lift (EC .id .N-ob c tt*)
  LiftE .id .N-hom f i tt* = lift (EC .id .N-hom f i tt*)
  LiftE .seq x y z .N-ob c (lift f , lift g) = lift (EC .seq x y z .N-ob c (f , g))
  LiftE .seq x y z .N-hom f i (lift g , lift h) = lift (EC .seq x y z  .N-hom f i (g , h))
  LiftE .⋆IdL x y = makeNatTransPath (funExt λ c → funExt λ (tt* , lift f) → 
    cong lift (cong (λ h → h .N-ob c (tt* , f )) (EC .⋆IdL x y))) 
  LiftE .⋆IdR x y = makeNatTransPath (funExt λ c → funExt λ (lift f , tt*) → 
     cong lift (cong (λ h → h .N-ob c (f , tt*)) (EC .⋆IdR x y))) 
  LiftE .⋆Assoc x y z w = makeNatTransPath (funExt λ c → 
    funExt λ (lift f , (lift g , lift h)) → 
     cong lift (cong (λ h' → h' .N-ob c (f , (g , h))) (EC .⋆Assoc x y z w)) )

module _
  {ℓC ℓC' ℓD ℓD' : Level}
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  (F : Functor D C)
  (ℓS' ℓS : Level)
  (EC : EnrichedCategory (PshMon.𝓟Mon C ℓS) ℓE )
  where

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

  -- enriched in (ℓ-max ℓC ℓC' ℓD ℓD' ℓS' ℓS)
  LEC : EnrichedCategory VC ℓE 
  LEC = LiftE {ℓS' = ℓm} EC

  LEC[_,_] = LEC .Hom[_,_]

  const : PMD.𝓟 [ MD.unit , reindPsh F MC.unit ]
  const = natTrans (λ _ _ → tt*) λ _ → refl

  Eid : {x : ob LEC} → PMD.𝓟 [ MD.unit , reindPsh F LEC[ x , x ] ]
  Eid = const ●ᵛ (LEC .id ∘ˡ (F ^opF))

  distrib : {x y z : ob LEC} →
    PMD.𝓟 [ reindPsh F LEC[ x , y ] MD.⊗ reindPsh F LEC[ y , z ] ,
    reindPsh F (LEC[ x , y ] MC.⊗ LEC[ y , z ]) ]
  distrib = natTrans (λ _ x → x) λ _ → refl

  distrib^ : {X Y : MC.ob} →
    MD.Hom[ reindPsh F (Y PMC.^ X) , reindPsh F Y PMD.^ reindPsh F X ]
  distrib^ .N-ob d exp =
    pshhom
      (λ {d' (f , XFd') → exp .PshHom.N-ob (F .F-ob d') (F .F-hom f , XFd')})
      λ {d d' f (g , FXd') →
      cong (λ h → exp .PshHom.N-ob _ h) (cong₂ _,_ (F .F-seq _ _) refl)
      ∙ exp .PshHom.N-hom (F .F-ob d)(F .F-ob d')(F .F-hom f)
      (F .F-hom g , FXd')}
  distrib^ .N-hom {d}{d'} f = funExt λ p →
    makePshHomPath (funExt λ  d'' → funExt λ {(g , XFd'') →
      cong (λ h → p .PshHom.N-ob _ h) (cong₂ _,_ (sym ( F-seq F g f )) refl)})

  Eseq : {x y z : ob LEC} →
    PMD.𝓟 [ reindPsh F LEC[ x , y ] MD.⊗ reindPsh F LEC[ y , z ] ,
      reindPsh F LEC[ x , z ] ]
  Eseq {x}{y}{z} = distrib ●ᵛ (LEC .seq x y z ∘ˡ (F ^opF))

  BaseChange : EnrichedCategory VD ℓE 
  BaseChange .ob = ob EC
  BaseChange .Hom[_,_] c c' = reindPsh F (LEC .Hom[_,_] c c')
  BaseChange .id = Eid
  BaseChange .seq x y z = Eseq
  BaseChange .⋆IdL x y =
    makeNatTransPath (funExt λ d → funExt⁻
      (cong (N-ob) (LEC .⋆IdL x y)) (F-ob F d))
  BaseChange .⋆IdR x y =
    makeNatTransPath (funExt λ d → funExt⁻
      (cong (N-ob) (LEC .⋆IdR x y)) (F-ob F d))
  BaseChange .⋆Assoc x y z w =
    makeNatTransPath (funExt λ d → funExt⁻
      (cong N-ob (LEC .⋆Assoc x y z w)) (F-ob F d))
