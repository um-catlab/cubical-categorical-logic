{-# OPTIONS --lossy-unification #-}
module Gluing.CBPV.Model where
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
    open import Cubical.Categories.Monoidal.Enriched.Presheaf
    open import Cubical.Categories.Monoidal.Enriched
    open import Cubical.Categories.Monoidal.Enriched.More

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

    module InitialModel {ℓ : Level} where
        open EnrichedFunctor
        open import Syntax.CBPV
        open import Cubical.Data.List hiding (init)
        open CBPVModel {ℓ}
        open Syn {ℓ}

        SCat : Category _ _
        SCat .ob = Ctx
        SCat .Hom[_,_] = Sub[_,_]
        SCat .id = ids
        SCat ._⋆_ f g = g ∘s f
        SCat .⋆IdL _ = ∘sIdR
        SCat .⋆IdR _ = ∘sIdL
        SCat .⋆Assoc _ _ _ = ∘sAssoc
        SCat .isSetHom = isSetSub

        open model SCat {ℓ}

        Ehom : CTy  → CTy  → ob 𝓟
        Ehom B B' .F-ob Γ = Γ ◂ B ⊢k B' , isSetStack
        Ehom B B' .F-hom γ k = k [ γ ]k
        Ehom B B' .F-id = funExt λ _ → subIdK
        Ehom B B' .F-seq γ δ = funExt λ k → subAssocK

        E : EnrichedCategory 𝓟Mon _
        E .ob = CTy
        E .Hom[_,_] = Ehom
        E .id = natTrans (λ _ _ → ∙k) λ _ → funExt λ _ → sym plugDist
        E .seq _ _ _ =
          natTrans (λ{x₁ (k , k') → k' ∘k k}) λ _ → funExt λ _ →  sym substDist
        E .⋆IdL _ _ = makeNatTransPath (funExt λ _ → funExt λ _  → sym ∘kIdR)
        E .⋆IdR _ _ = makeNatTransPath (funExt λ _ → funExt λ _  → sym ∘kIdL)
        E .⋆Assoc _ _ _ _ =
          makeNatTransPath  (funExt λ _ → funExt λ _ →  ∘kAssoc)

        vtm : VTy → Functor (SCat ^op) (SET ℓ)
        vtm A .F-ob Γ = (Γ ⊢v A) , isSetVal
        vtm A .F-hom γ v = v [ γ ]v
        vtm A .F-id = funExt λ _ → subIdV
        vtm A .F-seq _ _ = funExt λ _ → subAssocV

        ctm' : E .ob → ob self
        ctm' B .F-ob Γ = (Γ ⊢c B) , isSetComp
        ctm' B .F-hom γ m = m [ γ ]c
        ctm' B .F-id = funExt λ _ → subIdC
        ctm' B .F-seq _ _ = funExt λ _ →  subAssocC

        𝓟[_,_] = 𝓟 .Hom[_,_]
        E[_,_] = E .Hom[_,_]
        self[_,_]  = self .Hom[_,_]

        plug : (B B' : ob E) → 𝓟[ E[ B , B' ] , self[ ctm' B , ctm' B' ] ]
        plug B B' .N-ob Γ k  =
          pshhom
            (λ Δ (γ , m) → (k [ γ ]k) [ m ]∙)
            λ Δ Θ γ (δ , m) → subPlugComp
        plug B B' .N-hom γ = funExt λ k →
          makePshHomPath (funExt λ Θ → funExt λ (δ , m) →
            cong (λ h → h [ m ]∙ ) (sym subAssocK))

        ctm : EnrichedFunctor 𝓟Mon E self
        ctm .F₀ = ctm'
        ctm .F₁ {B} {B'}= plug B B'
        ctm .Fid {B} =
          makeNatTransPath (funExt λ Γ → funExt λ tt* →
            makePshHomPath (funExt λ Δ → funExt λ (γ , m) →
            cong (λ h → h [ m ]∙) plugDist ∙ plugId ))
        ctm .Fseq =
          makeNatTransPath (funExt λ Γ → funExt λ (k , k') →
            makePshHomPath (funExt λ Δ → funExt λ (γ , m) →
               cong₂
                (λ h1 h2 → ((k' [ h1 ]k) [ (k [ h2 ]k) [ m ]∙ ]∙))
                ∘sIdR ∘sIdR
               ∙ sym plugAssoc
               ∙ cong (λ h → ( h [ m ]∙)) (sym substDist)))

        open NatIso
        up : (Γ : Ctx) (A : VTy) →
          SCat [-, (A ∷ Γ) ] ≅ᶜ ((SCat [-, Γ ]) ×Psh vtm A)
        up Γ A .trans = goal where
          goal : NatTrans (SCat [-, A ∷ Γ ]) ((SCat [-, Γ ]) ×Psh vtm A)
          goal .N-ob Δ γ = (wk ∘s γ) , (var [ γ ]v)
          goal .N-hom γ = funExt λ δ → ΣPathP (∘sAssoc , subAssocV)
        up Γ A .nIso Δ .isIso.inv (γ , m) = γ ,s m
        up Γ A .nIso Δ .isIso.sec = funExt λ (γ , m) → ΣPathP (wkβ , varβ)
        up Γ A .nIso Δ .isIso.ret = funExt λ γ → sym ,sη

        init : CBPVModel
        init .𝓒 = SCat
        init .𝓔 = E
        init .vTy = VTy
        init .vTm = vtm
        init .cTm = ctm
        init .emp = ⊘ , λ Γ → !s , λ _ → sym ⊘η
        init ._×c_ Γ A = A ∷ Γ
        init .up×c = up

