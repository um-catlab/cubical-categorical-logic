{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Arrow.Displayed.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Data.Unit
import      Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Morphism
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Instances.BinProduct.More as BPᴰ
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.HLevels.More
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Section.More
open import Cubical.Categories.Displayed.Instances.Arrow.Base
open import Cubical.Categories.Displayed.Instances.Graph
open import Cubical.Categories.Displayed.Instances.PropertyOver
open import Cubical.Categories.Displayed.Instances.StructureOver
open import Cubical.Categories.Displayed.Instances.TotalCategory
open import Cubical.Categories.Displayed.Instances.Reindex.Eq
open import Cubical.Categories.Displayed.Instances.Weaken.Base
open import Cubical.Categories.Displayed.Instances.Weaken.Properties
open import Cubical.Categories.Instances.TotalCategory as ∫C
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions

open import Cubical.Categories.Displayed.Instances.Arrow.Displayed.Base

private
  variable
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓS ℓR : Level

open Section
open Functor
open Categoryᴰ
open UniversalElement
open isIsoOver

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  module _ (term : Terminal' C) (termᴰ : Terminalᴰ Cᴰ term) where
    private
      module term = TerminalNotation term
      module termᴰ = TerminalᴰNotation Cᴰ {term = term} termᴰ
      module Cᴰ = Fibers Cᴰ
    -- Manual for now
    term-IsoᴰBase : Terminal' (IsoᴰBase Cᴰ)
    term-IsoᴰBase .vertex = (term .vertex , term .vertex) , idCatIso , termᴰ .fst , termᴰ .fst
    term-IsoᴰBase .element = _
    term-IsoᴰBase .universal ((x , y) , f , xᴰ , yᴰ) = isIsoToIsEquiv
      ((λ _ → _ , (term.𝟙extensionality , tt) , termᴰ.introᴰ _ , termᴰ.introᴰ _)
      , (λ _ → refl)
      , λ _ → IsoᴰBaseHom≡ Cᴰ ((≡-× term.𝟙extensionality term.𝟙extensionality) , (ΣPathP ((Cᴰ.rectifyOut (termᴰ.∫extensionalityᴰ refl)) , (Cᴰ.rectifyOut (termᴰ.∫extensionalityᴰ refl))))))

    Terminalᴰ-Isoᴰ : Terminalᴰ (Isoᴰ Cᴰ) term-IsoᴰBase
    Terminalᴰ-Isoᴰ = UEᴰProp→UEᴰ _ _ _ term-IsoᴰBase (hasPropHomsIsoᴰ Cᴰ) isPropUnit
      ( idᴰCatIsoᴰ Cᴰ
      , _
      , (λ _ _ → Cᴰ.rectifyOut (termᴰ.∫extensionalityᴰ refl)))
