{-# OPTIONS --lossy-unification #-}
-- {-# OPTIONS --show-implicit #-}
module Cubical.Categories.CBPV.Functor where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.CBPV.Base 
open import Cubical.Categories.Functor
open import Cubical.Categories.Enriched.Functors.Base 
open import Cubical.Categories.Enriched.Instances.Presheaf.ChangeBase
open import Cubical.Categories.Enriched.Instances.Presheaf.ChangeBaseFunctor
open import Cubical.Categories.Enriched.Instances.Presheaf.Self
open import Cubical.Categories.Enriched.NaturalTransformation.Base
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Monoidal.Instances.Presheaf
open import Cubical.Categories.WithFamilies.Simple.Functor
open import Cubical.Categories.WithFamilies.Simple.Base 

open CBPVModel hiding (V)

private
  variable
    ℓC ℓC' ℓVTy ℓVTm ℓCTy ℓCTm : Level
    ℓD ℓD' ℓVTy' ℓVTm' ℓCTy' ℓCTm' : Level

open import Cubical.Categories.Category
open Category
open EnrichedCategory
open import Cubical.Categories.Monoidal.Base

open MonoidalCategory renaming (C to Cat)
open Functor
open import Cubical.Foundations.HLevels

record CBPVFunctor
  (C : CBPVModel ℓC ℓC' ℓVTy ℓVTm ℓCTy ℓCTm)
  (D : CBPVModel ℓD ℓD' ℓVTy' ℓVTm' ℓCTy' ℓCTm') : Typeω
  where
  ctxC = C .Scwf .fst 
  ctxD = D .Scwf .fst
  ℓmC = PshMon.ℓm ctxC ℓCTm
  ℓmD = PshMon.ℓm ctxD ℓCTm'
  V = PshMon.𝓟Mon ctxC (ℓ-max ℓmC ℓmD)
  V' =  PshMon.𝓟Mon ctxC (ℓ-max ℓmC (ℓ-max ℓmD (ℓ-max ℓCTy ℓCTy')) )
  field
    PreF : PreFunctor (C .Scwf) (D .Scwf)

  {-
    We have two categories of stacks: 
    - C-Stacks : EnrichedCategory VC ℓCTy 
    - D-Stacks : EnrichedCategory VD ℓCTy'

    In order to define a mapping betwen them, 
    these categories need to have the same enrichment V.

    C-Stacks is enriched in Presheaf ctxC (ℓ-max (ℓC ℓC' ℓCTm)) 
    D-Stacks is enriched in Presheaf ctxD (ℓ-max (ℓD ℓD' ℓCTm'))

    We have a functor ctxFun : Functor ctxD ctxC

    So the shared enrichment will be presheaves on ctxC 
      if we reindex the presheaves on ctxD along ctxFun

    We then have to find the right levels for this to work out: 
      for this we choose ℓ-max (ℓC ℓC' ℓCTm ℓD ℓD' ℓCTm')

    We can reindex and lift both categories to be enriched in 
      Presheaf ctxC (ℓ-max (ℓC ℓC' ℓD ℓD' ℓCTm ℓCTm'))


      This works .. but is it the right level...
        ctxFun = PreF .fst

  C' : EnrichedCategory V ℓCTy 
  C' = LiftE (C .Stacks)

  D' : EnrichedCategory V ℓCTy'
  D' = BaseChange ctxFun ℓCTm _ (D .Stacks)

  field
    F-stacks : EnrichedFunctor V C' D' 
  -}
  ctxFun = PreF .fst
  C' : EnrichedCategory V ℓCTy 
  C' = LiftE (C .Stacks)
  
  D' : EnrichedCategory V ℓCTy'
  D' = BaseChange ctxFun ℓCTm ℓCTm'(D .Stacks)

  field
    F-stacks : EnrichedFunctor V C' D'

  LCTM : EnrichedFunctor V C' (self ctxC (ℓ-max ℓmC ℓmD))
  -- (LiftE ((self ctxC ℓCTm))) 
  LCTM = eseq V (LiftEF (C .CTm) ℓmD) (LiftSelf _ _)
    --LiftEF (C .CTm) ℓmD

  LDTM : 
    EnrichedFunctor V 
      D' 
      (BaseChange ctxFun ℓmC ℓCTm' (self ctxD ℓCTm'))
  LDTM = BaseChangeF ctxFun ℓCTm (D .CTm)

  Final : 
    EnrichedFunctor V 
      (BaseChange ctxFun ℓmC ℓCTm' (self ctxD ℓCTm'))
      (self ctxC (ℓ-max ℓmC ℓmD))
  Final = BaseLiftSelf ctxFun ℓmC

  field 
    F-comp : 
      EnrichedNatTrans 
        LCTM 
        (eseq V F-stacks (eseq V LDTM Final))




    -- BaseChangeF ctxFun {!   !} (D .CTm)
  
  {- big levels 
  ctxFun = PreF .fst


  C' : EnrichedCategory V' ℓCTy 
  C' = LiftE (C .Stacks)
  
  D' : EnrichedCategory V' ℓCTy'
  D' = BaseChange ctxFun (ℓ-max (ℓ-max ℓCTm ℓCTy) ℓCTy') ℓCTm'(D .Stacks)
  
  field
    F-stacks : EnrichedFunctor V' C' D' 
    
  LCTM : EnrichedFunctor V' C' (LiftE ((self ctxC ℓCTm))) 
  LCTM = LiftEF (C .CTm) (ℓ-max ℓmD (ℓ-max ℓCTy ℓCTy'))

  {-
      ℓC ℓC' ℓCTy ℓCTm : Level
    ℓD ℓD'  ℓCTy' ℓCTm' : Level 
  -}
  LDTM : 
    EnrichedFunctor V' 
      D' 
      (BaseChange ctxFun  {!   !} ℓCTm' ((self ctxD ℓCTm')))
  LDTM = BaseChangeF ctxFun {ℓS = ℓCTm'} {!   !} (D .CTm)


  Final : 
    EnrichedFunctor V' 
      (BaseChange ctxFun  {!   !} ℓCTm' ((self ctxD ℓCTm'))) 
      (LiftE ((self ctxC ℓCTm))) 
  Final = {!   !}

  field 
    F-comp : EnrichedNatTrans LCTM (eseq V' F-stacks (eseq V' LDTM Final))
-} 









    {-
  private 
    VC = PshMon.𝓟Mon ctxC ℓCTm
    VD = PshMon.𝓟Mon ctxD ℓCTm'

    CTM : EnrichedFunctor VC (C .Stacks) (self ctxC ℓCTm)
    CTM = C .CTm

    DTM : EnrichedFunctor VD (D .Stacks) (self ctxD ℓCTm')
    DTM = D .CTm

    LCTM : EnrichedFunctor V (LiftE (C .Stacks)) (LiftE ((self ctxC ℓCTm))) 
    LCTM = LiftEF CTM ℓmD


    LDTM : EnrichedFunctor V 
      (BaseChange ctxFun ℓCTm ℓCTm' (D .Stacks)) (BaseChange ctxFun ℓCTm ℓCTm' ((self ctxD ℓCTm'))) 
    LDTM = {! BaseChangeF  ?  ? ? ?  !}

    Final : EnrichedFunctor V (BaseChange ctxFun ℓCTm ℓCTm'((self ctxD ℓCTm'))) (LiftE ((self ctxC ℓCTm))) 
    Final = {!   !}

  field 
    F-Comp : EnrichedNatTrans LCTM (eseq V F-stacks (eseq V LDTM Final))
-}



  {-
    We have two enriched functors: 
      - C-CTm : EnrichedFunctor VC C-Stacks (self ctxC ℓCTm)
      - D-CTm : EnrichedFunctor VD D-Stacks (self ctxD ℓCTm')

    An enriched natural transformation is defined between functors 
      with the same enrichment (as well as same source and target categories)


    Ignoring enrichment and levels, we have 
    - C-CTm : EnrichedFunctor C-Stacks (self ctxC)
    - D-CTm : EnrichedFunctor D-Stacks (self ctxD)

    To define a natural transformation, we need the domain and codomain to align 
    we have 
    - F-Stacks : EnrichedFunctor C-Stacks D-Stacks
    - ctxFun : Functor ctxC ctxD
    so we can construct
    - D-Ctm' : EnrichedFunctor C-Stacks (self ctxC)
    - D-Ctm' := reindex ctxFun ∘ D-CTm ∘ F-Stacks 

    and define a natural transformation 
      F-Comp : C-CTm  ==> D-Ctm'
   
    However, we need to take care of enrichment and levels.
      F-stacks is enriched in Presheaf ctxC (ℓ-max (ℓC ℓC' ℓD ℓD' ℓCTm ℓCTm'))
      C-CTm is enriched in Presheaf ctxC (ℓ-max (ℓC ℓC' ℓCTm))
      D-CTm is enriched in Presheaf ctxD (ℓ-max (ℓD ℓD' ℓCTm'))

    we can lift C-CTm to be enriched in 
      Presheaf ctxC (ℓ-max (ℓC ℓC' ℓD ℓD' ℓCTm ℓCTm'))

    LCTM : EnrichedFunctor V (LiftE C-Stacks) (LiftE ((self ctxC ℓCTm))) 
    LCTM = LiftEF CTM ℓmD

    -F-Stacks : EnrichedFunctor V (LiftE C-Stacks) (BaseChange ctxFun (D-Stacks))

    we need to lift D-CTm to be enriched in 
      Presheaf ctxC (ℓ-max (ℓC ℓC' ℓD ℓD' ℓCTm ℓCTm'))
    LDTM : EnrichedFunctor V (BaseChange ctxFun (D-Stacks)) ? (LiftE (self ctxD ℓCTm'))


  -}







{-}
  F : EnrichedFunctor (PshMon.𝓟Mon catC ℓCTm) (C .Stacks) (self catC ℓCTm) 
  F = C .CTm

  F' : EnrichedFunctor V C' (self catC _)
  --(LiftE ((self catC ℓCTm)))
  F' = eseq V (LiftEF (C .CTm) _) {!   !}
    -- LiftEF F ℓmD
  G' : EnrichedFunctor V {!   !} {!   !} 
  G' = {! BaseChangeF ctxFun _ _  (LiftEF (D .Stacks) _) !}
  
  field 
    F-cmp : EnrichedNatTrans F' {! C .CTm  !} 

      -- (LiftE (BaseChange {!   !}  {! D .Stacks  !}))
    -- (BaseChange {!   !} {! D .Stacks  !}) 
    {-Fscwf : PreFunctor (C .Scwf) (D .Scwf)
    Fstacks : EnrichedFunctor (D .V) (C .Stacks) (D .Stacks)
    Fctm : NatTrans
      (EnrichedFunctorCompose (D .V) (C .Stacks) (self (D .Scwf) _) (Fstacks))
      (EnrichedFunctorCompose (D .V) (self (C .Scwf) _) (self (D .Scwf) _) Fscwf .fst)
      -}
      -}