

module Cubical.Categories.Instances.Functors.Redundant.Bifunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Instances.Functors.Redundant
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Data.Sigma

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓ ℓ' : Level

open Category
open Functor
open NatTrans
open BifunctorParAx
open Bifunctor

-- Universal Bifunctor
εBif : {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
     → Bifunctor (FUNCTOR C D) C D
εBif {C = C}{D = D} = mkBifunctorParAx ε' where

  ε' : BifunctorParAx (FUNCTOR C D) C D
  ε' .Bif-ob F c = F ⟅ c ⟆
  ε' .Bif-homL α d = α .fst ⟦ d ⟧
  ε' .Bif-homR F f = F ⟪ f ⟫
  ε' .Bif-hom× α f = α .snd .fst f
  ε' .Bif-×-id {c = F} = F .F-id
  ε' .Bif-×-seq {c'' = F''} α α' f f' =
    seq' (FUNCTOR C D) α α' .snd .snd _
    ∙ D .⋆Assoc _ _ _
    ∙ cong₂ (seq' D) refl
      (cong₂ (seq' D) refl (F'' .F-seq f f')
      ∙ sym (D .⋆Assoc _ _ _)
      ∙ cong₂ (comp' D) refl (sym (α' .fst .N-hom _))
      ∙ D .⋆Assoc _ _ _)
    ∙ sym (D .⋆Assoc _ _ _)
    ∙ cong₂ (seq' D) (sym (α .snd .snd f)) (sym (α' .snd .snd f'))
  ε' .Bif-L×-agree {c' = F'} (α , ϕ)= (sym (D .⋆IdR _)
    ∙ cong₂ (seq' D) refl (sym (F' .F-id))) ∙ sym (ϕ .snd _)
  ε' .Bif-R×-agree f = refl

curry : {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}{E : Category ℓE ℓE'}
      → Bifunctor C D E → Functor C (FUNCTOR D E)
curry F .F-ob c .F-ob d = F ⟅ c , d ⟆b
curry F .F-ob c .F-hom g = F ⟪ g ⟫r
curry F .F-ob c .F-id = F .Bif-R-id
curry F .F-ob c .F-seq g g' = F .Bif-R-seq g g'
curry F .F-hom f .fst .N-ob d = F ⟪ f ⟫l
curry F .F-hom f .fst .N-hom g = Bif-RL-commute F f g
curry F .F-hom f .snd .fst g = F ⟪ f , g ⟫×
curry F .F-hom f .snd .snd g = sym (F .Bif-LR-fuse f g)
curry F .F-id = RedundNatTrans≡ (funExt λ d → F .Bif-L-id)
curry F .F-seq f f' = RedundNatTrans≡ (funExt λ d → F .Bif-L-seq f f')

uncurry : {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}{E : Category ℓE ℓE'}
       → Functor C (FUNCTOR D E) → Bifunctor C D E
uncurry = compL εBif
