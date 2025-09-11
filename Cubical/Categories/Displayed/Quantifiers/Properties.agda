module Cubical.Categories.Displayed.Quantifiers.Properties where

open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.More
-- open import Cubical.Foundations.Function
-- open import Cubical.Foundations.Structure
-- open import Cubical.Functions.FunExtEquiv
-- open import Cubical.Foundations.Isomorphism
-- open import Cubical.Data.Sigma
-- import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
-- open import Cubical.Categories.Profunctor.General
-- open import Cubical.Categories.Yoneda
-- open import Cubical.Categories.Constructions.Fiber
-- open import Cubical.Categories.Limits.BinProduct.More
-- open import Cubical.Categories.Presheaf.Base
-- open import Cubical.Categories.Presheaf.Morphism.Alt
-- open import Cubical.Categories.Presheaf.Representable
-- open import Cubical.Categories.Presheaf.More
-- open import Cubical.Categories.Presheaf.Constructions
-- open import Cubical.Categories.Instances.Sets
-- open import Cubical.Categories.NaturalTransformation
-- open import Cubical.Categories.FunctorComprehension

open import Cubical.Categories.Displayed.Base
-- open import Cubical.Categories.Displayed.Instances.Sets.Base
-- open import Cubical.Categories.Displayed.Instances.Functor.Base
-- open import Cubical.Categories.Displayed.Functor
-- open import Cubical.Categories.Displayed.Profunctor
-- open import Cubical.Categories.Displayed.NaturalTransformation
-- open import Cubical.Categories.Displayed.Functor.More
-- open import Cubical.Categories.Displayed.Adjoint.More
-- open import Cubical.Categories.Displayed.Constructions.Reindex.Base
-- open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Presheaf
-- open import Cubical.Categories.Displayed.FunctorComprehension
-- import Cubical.Categories.Displayed.Presheaf.CartesianLift as PshᴰCL
-- open import Cubical.Categories.Displayed.FunctorComprehension
open import Cubical.Categories.Displayed.Quantifiers.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓ ℓ' ℓP ℓPᴰ ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
