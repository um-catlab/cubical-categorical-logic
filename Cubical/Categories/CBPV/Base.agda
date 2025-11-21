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
    open import Cubical.Categories.Enriched.Presheaf
    open import Cubical.Categories.Monoidal.Enriched
    open import Cubical.Categories.Enriched.More

    open Category
    open Functor
    open NatTrans
    open MonoidalCategory
    open StrictMonCategory
    open EnrichedCategory

    record CBPVModel {ℓ ℓ' ℓS ℓE : Level} :
      Type (ℓ-suc (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓS ℓE))))) where
        field
            𝓒 : Category ℓ ℓ'
        open model 𝓒 {ℓS} using (self ; 𝓟Mon)
        -- 𝓟Mon : MonoidalCategory (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) ℓm
        field
            𝓔 : EnrichedCategory 𝓟Mon ℓE
            vTy : Type ℓ
            vTm :  vTy  → Presheaf 𝓒 ℓ'
            cTm : EnrichedFunctor 𝓟Mon 𝓔 self
            emp : Terminal 𝓒
            _×c_ : ob 𝓒 → vTy  → ob 𝓒
            up×c : (Γ : ob 𝓒)(A : vTy ) →
              𝓒 [-, (Γ ×c A) ] ≅ᶜ (𝓒 [-, Γ ]) ×Psh vTm A

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
        adjust = ecomp
                  mod𝓒.𝓟Mon
                  stk
                  (ecomp mod𝓒.𝓟Mon (BaseChangeF ctx N.cTm) (BaseChangeSelf ctx))
        field
            cmp : EnrichedNatTrans M.cTm adjust
