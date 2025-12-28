module Cubical.Categories.Monoidal.Enriched.More where 

open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Foundations.Prelude

module _ 
  {ℓV ℓV' ℓE : Level} 
  {V : MonoidalCategory ℓV ℓV'}
  (EC : EnrichedCategory V ℓE)
  (ℓE' : Level) where 

  open EnrichedCategory

  LiftEC : EnrichedCategory V (ℓ-max ℓE ℓE')
  LiftEC .ob = Lift {j = ℓE'} (EC .ob)
  LiftEC .Hom[_,_] (lift X)(lift Y) = EC .Hom[_,_] X Y
  LiftEC .id = EC .id
  LiftEC .seq (lift X)(lift Y)(lift Z)= EC .seq X Y Z
  LiftEC .⋆IdL (lift X)(lift Y)= EC .⋆IdL X Y
  LiftEC .⋆IdR (lift X)(lift Y)= EC .⋆IdR X Y
  LiftEC .⋆Assoc (lift X)(lift Y)(lift Z)(lift W)= EC .⋆Assoc X Y Z W