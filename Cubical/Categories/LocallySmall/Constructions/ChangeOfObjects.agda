module Cubical.Categories.LocallySmall.Constructions.ChangeOfObjects where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Functor.Base

open import Cubical.Categories.LocallySmall.Displayed.Category.Base

open Category

module _ where
  open CategoryVariables
  module _ {X : Typeω}
    (C : Category Cob CHom-ℓ)(F : X → Cob) where
    private
      module C = CategoryNotation C
    ChangeOfObjects : Category X _
    ChangeOfObjects .Hom[_,_] = λ x y → C.Hom[ F x , F y ]
    ChangeOfObjects .id = C.id
    ChangeOfObjects ._⋆_ = C._⋆_
    ChangeOfObjects .⋆IdL = C.⋆IdL
    ChangeOfObjects .⋆IdR = C.⋆IdR
    ChangeOfObjects .⋆Assoc = C.⋆Assoc
    ChangeOfObjects .isSetHom = C.isSetHom

    open Functor
    π : Functor ChangeOfObjects C
    π .F-ob = λ z → F z
    π .F-hom = λ z → z
    π .F-id = refl
    π .F-seq _ _ = refl
