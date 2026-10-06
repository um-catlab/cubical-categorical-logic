{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category

module Cubical.Categories.Enriched.Enrichment.Instances.Presheaf.StrictHom.Limits
  {ℓ ℓ' : Level} (A : Category ℓ ℓ') (ℓS : Level) where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Bifunctor using (appL)
open import Cubical.Categories.Limits.Terminal using (isTerminal)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.StrictHom.CartesianClosed
open import Cubical.Categories.Presheaf.Constructions.Reindex using (becomesUniversal)
open import Cubical.Categories.Limits.BinProduct.More using (preservesBinProdCones)
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Enriched.Enrichment.HomFunctor
open import Cubical.Categories.Enriched.Enrichment.Limits.BinProduct
open import Cubical.Categories.Enriched.Enrichment.Instances.Presheaf.StrictHom.Self A ℓS
import Cubical.Categories.Enriched.Enrichment.Functor.Base as FE
open import Cubical.Categories.Enriched.Enrichment.Instances.Presheaf.StrictHom.Product A ℓS using (_×ᴱ_)

open Functor
open NatTrans
open PshHomStrict
open PshMon A ℓS using (𝓟Mon ; 𝓟 ; ℓm ; 𝟙)

private
  module A = Category A

𝟙-terminal : isTerminal 𝓟 𝟙
𝟙-terminal P .fst .N-ob _ _ = tt*
𝟙-terminal P .fst .N-hom _ _ _ _ _ _ = refl
𝟙-terminal P .snd h = makePshHomStrictPath refl

module _ (Γ : Presheaf A ℓm) where
  Γ×- : Functor 𝓟 𝓟
  Γ×- = appL PshProdStrict Γ

  π₁Γ : NatTrans Γ×- (Constant 𝓟 𝓟 Γ)
  π₁Γ .N-ob X = π₁ Γ X
  π₁Γ .N-hom f = makePshHomStrictPath refl

  π₂Γ : NatTrans Γ×- Id
  π₂Γ .N-ob X = π₂ Γ X
  π₂Γ .N-hom f = makePshHomStrictPath refl

  ×-univ : ∀ X W → becomesUniversal (preservesBinProdCones (Hom[_,-] selfEnrichment W) Γ X)
                      (Γ×- ⟅ X ⟆) (π₁Γ ⟦ X ⟧ , π₂Γ ⟦ X ⟧)
  ×-univ X W Z = isoToIsEquiv (iso _ pair
    (λ (a , b) → ΣPathP
      ( makePshHomStrictPath (funExt λ c → funExt λ z → makePshHomStrictPath
          (funExt λ d → funExt λ (g , w) → cong (λ k → a .N-ob c z .N-ob d (k , w)) (A.⋆IdL g)))
      , makePshHomStrictPath (funExt λ c → funExt λ z → makePshHomStrictPath
          (funExt λ d → funExt λ (g , w) → cong (λ k → b .N-ob c z .N-ob d (k , w)) (A.⋆IdL g)))))
    (λ h → makePshHomStrictPath (funExt λ c → funExt λ z → makePshHomStrictPath
          (funExt λ d → funExt λ (g , w) → cong (λ k → h .N-ob c z .N-ob d (k , w)) (A.⋆IdL g)))))
    where
    H = Hom[_,-] selfEnrichment W
    pair : 𝓟 [ Z , H ⟅ Γ ⟆ ] × 𝓟 [ Z , H ⟅ X ⟆ ] → 𝓟 [ Z , H ⟅ Γ×- ⟅ X ⟆ ⟆ ]
    pair (a , b) .N-ob c z .N-ob d gw = a .N-ob c z .N-ob d gw , b .N-ob c z .N-ob d gw
    pair (a , b) .N-ob c z .N-hom d' d k gw gw' eq =
      ΣPathP (a .N-ob c z .N-hom d' d k gw gw' eq , b .N-ob c z .N-hom d' d k gw gw' eq)
    pair (a , b) .N-hom c' c k z z' eq = makePshHomStrictPath (funExt λ d → funExt λ gw →
      ΣPathP ( (λ i → a .N-hom c' c k z z' eq i .N-ob d gw)
             , (λ i → b .N-hom c' c k z z' eq i .N-ob d gw)))

  ×-Enr : FE.Enrichment 𝓟Mon selfEnrichment selfEnrichment Γ×-
  ×-Enr = ×-Enrichment selfEnrichment 𝟙-terminal Γ Γ×- π₁Γ π₂Γ ×-univ

⨂-Enr : FE.Enrichment 𝓟Mon (selfEnrichment ×ᴱ selfEnrichment) selfEnrichment PshProd'Strict
⨂-Enr .FE.Enrichment.F[_,_] _ _ .N-ob c (α , β) .N-ob d (g , (x₁ , x₂)) =
  α .N-ob d (g , x₁) , β .N-ob d (g , x₂)
⨂-Enr .FE.Enrichment.F[_,_] _ _ .N-ob c (α , β) .N-hom d' d k (g , (x₁ , x₂)) (g' , (x₁' , x₂')) e =
  ΣPathP ( α .N-hom d' d k (g , x₁) (g' , x₁') (ΣPathP ((λ i → e i .fst) , (λ i → e i .snd .fst)))
         , β .N-hom d' d k (g , x₂) (g' , x₂') (ΣPathP ((λ i → e i .fst) , (λ i → e i .snd .snd))))
⨂-Enr .FE.Enrichment.F[_,_] _ _ .N-hom c' c f (α' , β') (α , β) e =
  makePshHomStrictPath (funExt λ d → funExt λ (g , (x₁ , x₂)) →
    ΣPathP ((λ i → e i .fst .N-ob d (g , x₁)) , (λ i → e i .snd .N-ob d (g , x₂))))
⨂-Enr .FE.Enrichment.F-id = makePshHomStrictPath (funExt λ c → funExt λ _ → makePshHomStrictPath refl)
⨂-Enr .FE.Enrichment.F-seq = makePshHomStrictPath (funExt λ c → funExt λ _ → makePshHomStrictPath refl)
⨂-Enr .FE.Enrichment.agree f = makePshHomStrictPath (funExt λ c → funExt λ _ → makePshHomStrictPath refl)
