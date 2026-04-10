{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Equiv.Dependent.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.HLevels.More

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.More
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.Terminal as Unitᴰ
import Cubical.Categories.Displayed.Instances.Sets.Base as Setᴰ
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.BinProduct.More
open import Cubical.Categories.Displayed.Instances.Graph.Presheaf
open import Cubical.Categories.Displayed.Instances.Reindex.Eq

import Cubical.Categories.Displayed.Presheaf.Base as Curried
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base

import Cubical.Categories.Displayed.Limits.CartesianV' as Path
import Cubical.Categories.Displayed.Presheaf.Uncurried.Base as Path
import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable as Path
import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions as Path
import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration as Path
import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties as Path

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.Base

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓE ℓE' ℓEᴰ ℓEᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level


module _ {C : Category ℓC ℓC'} {P : Presheaf C ℓP} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module P = PresheafNotation P
    module Cᴰ = Fibers Cᴰ

  EqUnitⱽ≅PathUnitⱽ : Path.PshIsoⱽ (EqPresheafᴰ→PathPresheafᴰ P Cᴰ UnitⱽPsh) Path.UnitPshᴰ
  EqUnitⱽ≅PathUnitⱽ = reindPsh-Unit (Path/→Eq/ P Cᴰ)

  -- reindPsh F (Pᴰ ×ⱽPsh Qᴰ) ≅ reindPsh F Pᴰ ×ⱽPsh reindPsh F Qᴰ
  Eq×ⱽ≅Path×ⱽ : ∀ {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}
    → Path.PshIsoⱽ (EqPresheafᴰ→PathPresheafᴰ P Cᴰ (Pᴰ ×ⱽPsh Qᴰ))
                   (EqPresheafᴰ→PathPresheafᴰ P Cᴰ Pᴰ Path.×ⱽPsh EqPresheafᴰ→PathPresheafᴰ P Cᴰ Qᴰ)
  Eq×ⱽ≅Path×ⱽ = reindPsh× (Path/→Eq/ P Cᴰ) _ _

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  fibrationNatIso : ∀ {Γ x} (⋆AssocC : ReprEqAssoc C) (f : C [ Γ , x ])
    → NatIso {C = Cᴰ Path./ (C [-, Γ ])}{D = Cᴰ / (C [-, x ])}
             (((Idᴰ /Fⱽ yoRecEq (C [-, x ]) (⋆AssocC x) f) ∘F Path/→Eq/ (C [-, Γ ]) Cᴰ))
             ((Path/→Eq/ (C [-, x ]) Cᴰ ∘F (Idᴰ Path./Fⱽ yoRec (C [-, x ]) f)))
  fibrationNatIso {Γ}{x} ⋆AssocC f = isosToNatIso
    (λ obPath/@(Δ , Δᴰ , g) → idCatIso)
    λ Θ3 Δ3 morPath@(δ , δᴰ , δg≡h) → Hom/≡ $ Cᴰ.⋆IdR _ ∙ sym (Cᴰ.⋆IdL _)

module _ {C : Category ℓC ℓC'} (⋆AssocC : ReprEqAssoc C)(Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  EqTerminalsⱽ→Terminalsⱽ : Terminalsⱽ Cᴰ → Path.Terminalsⱽ Cᴰ
  EqTerminalsⱽ→Terminalsⱽ termsⱽ x =
    EqReprⱽ→PathReprⱽ UnitⱽPsh (termsⱽ x)
    Path.◁PshIsoⱽ EqUnitⱽ≅PathUnitⱽ Cᴰ

  EqFibration→Fibration : Fibration Cᴰ ⋆AssocC → Path.isFibration Cᴰ
  EqFibration→Fibration isFib {x} xᴰ Γ f = EqReprⱽ→PathReprⱽ _ (isFib f xᴰ)
    Path.◁PshIsoⱽ reindPsh-square (Path/→Eq/ (C [-, Γ ]) Cᴰ) (Idᴰ /Fⱽ yoRecEq (C [-, x ]) (⋆AssocC x) f) (Idᴰ Path./Fⱽ yoRec (C [-, x ]) f) (Path/→Eq/ (C [-, x ]) Cᴰ) (Cᴰ [-][-, xᴰ ]) (fibrationNatIso Cᴰ ⋆AssocC f)
    Path.⋆PshIsoⱽ reindPshIso (Idᴰ Path./Fⱽ yoRec (C [-, x ]) f) Representable≅


  EqCCⱽ→CCⱽ : isCartesianⱽ ⋆AssocC Cᴰ → Path.CartesianCategoryⱽ C ℓCᴰ ℓCᴰ'
  EqCCⱽ→CCⱽ cartⱽCᴰ .Path.CartesianCategoryⱽ.Cᴰ = Cᴰ
  EqCCⱽ→CCⱽ cartⱽCᴰ .Path.CartesianCategoryⱽ.termⱽ = EqTerminalsⱽ→Terminalsⱽ (cartⱽCᴰ .fst)
  EqCCⱽ→CCⱽ cartⱽCᴰ .Path.CartesianCategoryⱽ.bpⱽ xᴰ yᴰ =
    EqReprⱽ→PathReprⱽ ((Cᴰ [-][-, xᴰ ]) ×ⱽPsh (Cᴰ [-][-, yᴰ ])) (cartⱽCᴰ .snd .fst xᴰ yᴰ)
    Path.◁PshIsoⱽ Eq×ⱽ≅Path×ⱽ Cᴰ
    Path.⋆PshIsoⱽ ×PshIso Representable≅ Representable≅
  EqCCⱽ→CCⱽ cartⱽCᴰ .Path.CartesianCategoryⱽ.cartesianLifts {x = x} xᴰ Γ f =
    EqFibration→Fibration (cartⱽCᴰ .snd .snd) xᴰ Γ f
