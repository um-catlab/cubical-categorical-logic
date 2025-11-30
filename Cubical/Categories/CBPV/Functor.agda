{-# OPTIONS --lossy-unification #-}
-- {-# OPTIONS --show-implicit #-}
module Cubical.Categories.CBPV.Functor where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.CBPV.Base 
open import Cubical.Categories.Functor
open import Cubical.Categories.Enriched.Functors.Base 
open import Cubical.Categories.Enriched.Instances.Presheaf.ChangeBase
open import Cubical.Categories.Enriched.Instances.Presheaf.ChangeBaseFunctor
open import Cubical.Categories.Enriched.Instances.Presheaf.Self
open import Cubical.Categories.Enriched.NaturalTransformation.Base
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Monoidal.Instances.Presheaf
open import Cubical.Categories.WithFamilies.Simple.Functor
open import Cubical.Categories.WithFamilies.Simple.Base 

open Category
open EnrichedCategory
open Functor
open MonoidalCategory renaming (C to Cat)

-- this works.. but it is ungodly slow ..
-- unusably slow.. 
private
  variable
    ℓC ℓC' ℓVTy ℓVTm ℓCTy ℓCTm : Level
    ℓD ℓD' ℓVTy' ℓVTm' ℓCTy' ℓCTm' : Level

CBPVFunctor : 
  {ℓC ℓC' ℓVTy ℓVTm ℓCTy ℓCTm ℓD ℓD' ℓVTy' ℓVTm' ℓCTy' ℓCTm' : Level}→ 
  (C : CBPVModel ℓC ℓC' ℓVTy ℓVTm ℓCTy ℓCTm)
  (D : CBPVModel ℓD ℓD' ℓVTy' ℓVTm' ℓCTy' ℓCTm') → Type _ 
CBPVFunctor {ℓCTm = ℓCTm} {ℓCTm' = ℓCTm'} C D = 
  Σ[ PreF ∈ PreFunctor (C .fst) (D .fst) ]
  Σ[ F-Stacks ∈ EnrichedFunctor V (LiftE (C .snd .fst)) (BaseChange (PreF .fst) ℓCTm ℓCTm'(D .snd .fst)) ] 
  EnrichedNatTrans 
    (eseq V 
      (LiftEF (C .snd .snd) ℓmD) 
      (LiftSelf _ _)) 
    (eseq V 
      F-Stacks 
      (eseq V 
        (BaseChangeF (PreF .fst) ℓCTm (D .snd .snd))
        (BaseLiftSelf (PreF .fst) ℓmC))) where 
    ctxC = C .fst .fst 
    ctxD = D .fst .fst
    ℓmC = PshMon.ℓm ctxC ℓCTm
    ℓmD = PshMon.ℓm ctxD ℓCTm'
    V = PshMon.𝓟Mon ctxC (ℓ-max ℓmC ℓmD)
{-
record CBPVFunctor
  (C : CBPVModel ℓC ℓC' ℓVTy ℓVTm ℓCTy ℓCTm)
  (D : CBPVModel ℓD ℓD' ℓVTy' ℓVTm' ℓCTy' ℓCTm') : 
    Type 
      (ℓ-max (ℓ-suc (ℓ-suc ℓC)) 
      (ℓ-max (ℓ-suc (ℓ-suc ℓC')) 
      (ℓ-max (ℓ-suc (ℓ-suc ℓD))
      (ℓ-max (ℓ-suc (ℓ-suc ℓD'))
      (ℓ-max (ℓ-suc (ℓ-suc ℓCTm))
      (ℓ-max (ℓ-suc (ℓ-suc ℓCTm'))
      (ℓ-max (ℓ-suc ℓCTy)
      (ℓ-max (ℓ-suc ℓCTy')
      (ℓ-max ℓVTy 
      (ℓ-max ℓVTy'
      (ℓ-max ℓVTm ℓVTm')))))))))))
  where
  private
    ctxC = C .Scwf .fst 
    ctxD = D .Scwf .fst
    ℓmC = PshMon.ℓm ctxC ℓCTm
    ℓmD = PshMon.ℓm ctxD ℓCTm'
    V = PshMon.𝓟Mon ctxC (ℓ-max ℓmC ℓmD)
  field
    PreF : PreFunctor (C .Scwf) (D .Scwf)

  private
    ctxFun = PreF .fst
    C' : EnrichedCategory V ℓCTy 
    C' = LiftE (C .Stacks)
    
    D' : EnrichedCategory V ℓCTy'
    D' = BaseChange ctxFun ℓCTm ℓCTm'(D .Stacks)

  field
    F-stacks : EnrichedFunctor V C' D'

  private 
    LCTM : EnrichedFunctor V C' (self ctxC (ℓ-max ℓmC ℓmD))
    LCTM = eseq V (LiftEF (C .CTm) ℓmD) (LiftSelf _ _)

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
-}

{-
this is also ungodly slow ...
changing base may be the issue.. 

private
  variable
    ℓC ℓC' ℓVTy ℓVTm ℓCTy ℓCTm : Level
record CBPVFunctor
  (C D : CBPVModel ℓC ℓC' ℓVTy ℓVTm ℓCTy ℓCTm)
    : Type 
      (ℓ-max (ℓ-suc (ℓ-suc ℓC)) 
      (ℓ-max (ℓ-suc (ℓ-suc ℓC')) 
      (ℓ-max (ℓ-suc (ℓ-suc ℓCTm))
      (ℓ-max (ℓ-suc ℓCTy)
      (ℓ-max ℓVTy ℓVTm)))))
  where
  private
    ctxC = C .Scwf .fst 
    ctxD = D .Scwf .fst
    V = PshMon.𝓟Mon ctxC ℓCTm
  field
    PreF : PreFunctor (C .Scwf) (D .Scwf)

  private
    ctxFun = PreF .fst
  field
    F-stacks : 
      EnrichedFunctor V 
        (C .Stacks) 
        (BaseChange ctxFun ℓCTm ℓCTm (D .Stacks)) 
  
    F-Comp : EnrichedNatTrans ? ? 
-} 