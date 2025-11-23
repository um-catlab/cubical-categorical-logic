module Cubical.Categories.Enriched.Instances.Presheaf.Lifting where 
open import Cubical.Categories.Monoidal.Instances.Presheaf
open import Cubical.Categories.Category
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation 
open import Cubical.Data.Unit
open EnrichedCategory
open NatTrans
open Functor

module _   
  {ℓ ℓ' ℓS ℓE ℓS' : Level}
  {C : Category ℓ ℓ'}
  {EC : EnrichedCategory (PshMon.𝓟Mon {ℓS = ℓS} C) ℓE} where 

  ℓm = ℓ-max ℓ (ℓ-max ℓ' ℓS)
  V = PshMon.𝓟Mon {ℓS = ℓ-max ℓm ℓS'} C

  EC[_,_] = EC .Hom[_,_]

  LiftE : EnrichedCategory V ℓE 
  LiftE .ob = ob EC
  LiftE .Hom[_,_] x y = LiftF {ℓm}{ℓ-max ℓm ℓS'} ∘F  EC[ x , y ]
  LiftE .id = {! ? ∘ʳ ? !}
  LiftE .seq = {!   !}
  LiftE .⋆IdL = {!   !}
  LiftE .⋆IdR = {!   !}
  LiftE .⋆Assoc = {!   !}
  {-}.ob = EC .ob 
  LiftE .Hom[_,_] x y = LiftF {ℓm}{ℓ-max ℓm ℓS'} ∘F  EC[ x , y ]
  LiftE .id {x} .N-ob y z = lift (EC .id {x} .N-ob y (lift _))
  LiftE .id {x} .N-hom f = funExt λ _ → cong lift (funExt⁻ (EC .id {x} .N-hom f) _)
  LiftE .seq x y z .N-ob q r = lift (EC .seq x y z .N-ob q ((r .fst .lower) , r .snd .lower))
  LiftE .seq x y z .N-hom f = funExt λ (p , q) → cong lift (funExt⁻ (EC .seq x y z .N-hom f) _)
  LiftE .⋆IdL x y i = {! EC .⋆IdL x y i  !}
    --natTrans (λ p q → lift (EC .⋆IdL x y i .N-ob p (tt* , q .snd .lower))) λ f → funExt λ (r , s) → cong lift {! funExt⁻ (EC .⋆IdL x y i .N-hom f) i ?   !}
    --makeNatTransPath (funExt λ c → funExt λ (f , g) → cong lift {! EC .⋆IdL x y   !})
  LiftE .⋆IdR = {!   !} 
  LiftE .⋆Assoc = {!   !} -}