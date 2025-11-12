module Cubical.Categories.LocallySmall.Category.Small where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma.More

import Cubical.Categories.Category as Small
open import Cubical.Categories.LocallySmall.Variables.Base
open import Cubical.Categories.LocallySmall.Category.Base

open Σω
open Liftω

open Category

-- A (LS) Category with a small type of objects
SmallObjectsCategory : ∀ {ℓC}(ob : Type ℓC)(C-ℓ : ob → ob → Level) → Typeω
SmallObjectsCategory ob C-ℓ = Category (Liftω ob) λ (liftω x) (liftω y) → C-ℓ x y

-- A (LS) Category such that all hom sets are at the *same* universe level
GloballySmallCategory : (Cob : Typeω)(ℓC' : Level) → Typeω
GloballySmallCategory Cob ℓC' = Category Cob λ _ _ → ℓC'

record SmallCategory (ℓC ℓC' : Level) : Typeω where
  constructor smallcat
  field
    small-ob : Type ℓC
    cat : GloballySmallCategory (Liftω small-ob) ℓC'
  open CategoryNotation cat public

open SmallCategory

_^opsmall : ∀ {ℓC ℓC'} → SmallCategory ℓC ℓC' → SmallCategory ℓC ℓC'
(C ^opsmall) .small-ob = C .small-ob
(C ^opsmall) .cat = (C .cat) ^op

module _ (C : Small.Category ℓC ℓC') where
  private
    module C = Small.Category C
  |mkSmallCategory| : GloballySmallCategory (Liftω C.ob) ℓC'
  |mkSmallCategory| .Hom[_,_] (liftω x) (liftω y) = C.Hom[ x , y ]
  |mkSmallCategory| .id = C.id
  |mkSmallCategory| ._⋆_ = C._⋆_
  |mkSmallCategory| .⋆IdL = C.⋆IdL
  |mkSmallCategory| .⋆IdR = C.⋆IdR
  |mkSmallCategory| .⋆Assoc = C.⋆Assoc
  |mkSmallCategory| .isSetHom = C.isSetHom

  mkSmallCategory : SmallCategory ℓC ℓC'
  mkSmallCategory = smallcat C.ob |mkSmallCategory|

module _ (C : SmallCategory ℓC ℓC') where
  open Small.Category
  private
    module C = SmallCategory C
  SmallLocallySmallCategory→SmallCategory : Small.Category ℓC ℓC'
  SmallLocallySmallCategory→SmallCategory .ob = C.small-ob
  SmallLocallySmallCategory→SmallCategory .Hom[_,_] x y = C.Hom[ liftω x , liftω y ]
  SmallLocallySmallCategory→SmallCategory .id = C.id
  SmallLocallySmallCategory→SmallCategory ._⋆_ = C._⋆_
  SmallLocallySmallCategory→SmallCategory .⋆IdL = C.⋆IdL
  SmallLocallySmallCategory→SmallCategory .⋆IdR = C.⋆IdR
  SmallLocallySmallCategory→SmallCategory .⋆Assoc = C.⋆Assoc
  SmallLocallySmallCategory→SmallCategory .isSetHom = C.isSetHom
