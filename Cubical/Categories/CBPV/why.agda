module Cubical.Categories.CBPV.why where 

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monoidal.Instances.Presheaf


module test1 (ℓ : Level) where 
  V = PshMon.𝓟Mon (SET ℓ) ℓ 
  
_ : test1.V ℓ-zero ≡ PshMon.𝓟Mon (SET ℓ-zero) ℓ-zero  
_ = refl -- instantaneous!

module test2 (ℓ : Level) where 
  set = SET ℓ 
  V  = PshMon.𝓟Mon set ℓ 

_ : test2.V  ℓ-zero ≡ PshMon.𝓟Mon (SET ℓ-zero) ℓ-zero 
_ = {!   !} -- takes about 2.5 minutes to check

{-
  annotating set as 
    set : Category (ℓ-suc ℓ) ℓ 
  and annotation V as 
    V : MonoidalCategory (ℓ-suc (PshMon.ℓm set ℓ)) (PshMon.ℓm set ℓ)

  still yield a 2.5+ minute wait


  Note, normalizing the goal in either hole is intantaneous and yields 
  PshMon.𝓟Mon (SET ℓ-zero) ℓ-zero ≡ PshMon.𝓟Mon (SET ℓ-zero) ℓ-zero
-}
