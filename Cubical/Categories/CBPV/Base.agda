{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.CBPV.Base where
open import Cubical.Categories.Category
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt hiding (_∘ˡ_)
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Functor
open import Cubical.Foundations.Structure
open import Cubical.Categories.Instances.Sets
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.Monoidal.Instances.Presheaf
open import Cubical.Categories.Enriched.Functors.Base
open import Cubical.Categories.Enriched.NaturalTransformation.Base
open import Cubical.Categories.Enriched.Instances.Presheaf.Self
open import Cubical.Categories.WithFamilies.Simple.Functor
open import Cubical.Categories.Enriched.Instances.Presheaf.ChangeBase
open Category
open Functor
open NatTrans
open MonoidalCategory
open StrictMonCategory
open EnrichedCategory

private
  variable
    ℓC ℓC' ℓVTy ℓVTm ℓCTy ℓCTm : Level
    ℓD ℓD' ℓVTy' ℓVTm' ℓCTy' ℓCTm' : Level

CBPVModel : (ℓC ℓC' ℓVTy ℓVTm ℓCTy ℓCTm : Level) → Type _ 
CBPVModel ℓC ℓC' ℓVTy ℓVTm ℓCTy ℓCTm = 
  Σ[ Scwf ∈ SCwF ℓC ℓC' ℓVTy ℓVTm ] 
  Σ[ Stacks ∈ EnrichedCategory (𝓟Mon (Scwf .fst)) ℓCTy ] 
  EnrichedFunctor (𝓟Mon (Scwf .fst)) Stacks (self (Scwf .fst)) 
  where 
    open PshMon {ℓS = ℓCTm} 


-- universe levels are a terrible mess
module _ 
  (C : CBPVModel ℓC ℓC' ℓVTy ℓVTm ℓCTy ℓCTm)
  (D : CBPVModel ℓD ℓD' ℓVTy' ℓVTm' ℓCTy' ℓCTm') where

  record CBPVFunctor : Type _ where 
    private 
      ctxC = C .fst .fst 
      ctxD = D .fst .fst
      compCatC = C .snd .fst
      compCatD = D .snd .fst
      compTmC = C .snd .snd
      compTmD = D .snd .snd
      module PMC = PshMon {ℓS = ℓCTm} ctxC
      module PMD = PshMon {ℓS = ℓCTm} ctxD
    field 
      preFun : PreFunctor (C .fst) (D .fst)
      F-stack : EnrichedFunctor PMC.𝓟Mon compCatC {!   !} 
{-}      preFun : PreFunctor (C .fst) (D .fst)
      F-stack : EnrichedFunctor PMC.𝓟Mon compCatC (BaseChange (preFun .fst) compCatD)
    adjust : EnrichedFunctor PMC.𝓟Mon compCatC (self ctxC) 
    adjust = 
      eseq 
        PMC.𝓟Mon 
        F-stack 
        (eseq 
          PMC.𝓟Mon  
          (BaseChangeF {!   !} {! compTmD  !}) 
          {!   !})
    field 
      F-cty : EnrichedNatTrans compTmC adjust 
    {-}
-}
        ecomp
      mod𝓒.𝓟Mon
      stk
      (ecomp mod𝓒.𝓟Mon (BaseChangeF ctx N.cTm) (BaseChangeSelf ctx))
  CBPVFunctor = 
    Σ[ prefun ∈ PreFunctor (C .fst) (D .fst) ] 
    Σ[ F-stack ∈ 
      EnrichedFunctor 
        PMC.𝓟Mon 
        compCatC 
        (BaseChange (prefun .fst) compCatD) ] 
    EnrichedNatTrans compTmC {!   !} 
    where 
      ctxC = C .fst .fst 
      ctxD = D .fst .fst
      compCatC = C .snd .fst
      compCatD = D .snd .fst
      compTmC = C .snd .snd
      compTmD = D .snd .snd
      private 
        module PMC = PshMon {ℓS = ℓCTm} ctxC
        module PMD = PshMon {ℓS = ℓCTm} ctxD
      adjust : EnrichedFunctor PMC.𝓟Mon compCatC (self ctxC) 
      adjust = 
        eseq PMC.𝓟Mon {! F-stack  !} {!   !}
        -}
{-
record CBPVModelHom {ℓ ℓ' : Level} (M N : CBPVModel{ℓ}{ℓ'}) :
  Type (ℓ-suc (ℓ-suc (ℓ-max ℓ ℓ'))) where
  private module M = CBPVModel M
  private module N = CBPVModel N
  field
    ctx : Functor M.𝓒 N.𝓒
    ty : M.vTy → N.vTy
    tm : (A :  M.vTy  ) →
      NatTrans (M.vTm A) (N.vTm (ty A) ∘F (ctx ^opF))
  private module mod𝓒 = model M.𝓒
  private module mod𝓓 = model N.𝓒
  field
    stk : EnrichedFunctor mod𝓒.𝓟Mon M.𝓔 ((BaseChange ctx N.𝓔))

  adjust : EnrichedFunctor mod𝓒.𝓟Mon M.𝓔 mod𝓒.self
  adjust =
    ecomp
      mod𝓒.𝓟Mon
      stk
      (ecomp mod𝓒.𝓟Mon (BaseChangeF ctx N.cTm) (BaseChangeSelf ctx))
  field
    cmp : EnrichedNatTrans M.cTm adjust
-}