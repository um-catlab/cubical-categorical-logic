{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Presheaves where
-- TODO still need better name

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport hiding (pathToIso)

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.HITs.PathEq
open import Cubical.HITs.Join

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Constructions.Lift
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory.Base
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation hiding (_∘ˡ_; _∘ˡⁱ_)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Properties renaming (PshIso to PshIsoLift)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.BinProduct hiding (π₁ ; π₂)
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Yoneda

open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Isomorphism.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
-- open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base
open import Cubical.Categories.Presheaf.StrictHom


open Functor
open Iso
open NatIso
open NatTrans
open Categoryᴰ
open PshHomStrict
open PshHom

private
  variable
    ℓ ℓ' ℓP ℓQ ℓR ℓS ℓS' ℓS'' : Level
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓPᴰ ℓQᴰ ℓRᴰ : Level

module _ {C : Category ℓC ℓC'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshHomStrict P Q)
  where

  -- Yikes but...who cares?
  PshHomStrict→Eq : PshHomEq P Q
  PshHomStrict→Eq .PshHomEq.N-ob c x = α .N-ob c x
  PshHomStrict→Eq .PshHomEq.N-hom c c' f p' p x =
    Eq.pathToEq (α .N-hom c c' f p' p (Eq.eqToPath x))
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  where
  _*Strict_ : (α : PshHomStrict P Q) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) → Presheafᴰ P Cᴰ ℓQᴰ
  α *Strict Qᴰ = reindPsh (Idᴰ /Fⱽ PshHomStrict→Eq α) Qᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  {Pᴰ : Presheafᴰ Q Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where
  _*StrictF_ : (α : PshHomStrict P Q) (β : PshHom Pᴰ Qᴰ) → PshHom (α *Strict Pᴰ) (α *Strict Qᴰ)
  α *StrictF β = reindPshHom (Idᴰ /Fⱽ PshHomStrict→Eq α) β

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshHomStrict P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
  PshHomᴰ : Type _
  PshHomᴰ = PshHom Pᴰ (α *Strict Qᴰ)

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
  -- (idPshHom *Strict) has a universal property:
  -- PshHom Pᴰ (idPshHom *Strict Qᴰ) ≅ PshHom Pᴰ Qᴰ

  idPshHomᴰ : PshHomᴰ idPshHomStrict Pᴰ Pᴰ
  idPshHomᴰ .N-ob = λ c z → z
  idPshHomᴰ .N-hom c c' f p = Pᴰ.rectifyOut $ sym (Pᴰ.⋆ᴰ-reind _) ∙ Pᴰ.⋆ᴰ-reind _

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  {R : Presheaf C ℓR}
  {Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ}
  (α : PshHomStrict P Q)
  β
  where
  private
    module Rᴰ = PresheafᴰNotation Rᴰ
  *Strict-seq : PshHom (α *Strict (β *Strict Rᴰ)) ((α ⋆PshHomStrict β) *Strict Rᴰ)
  *Strict-seq .N-ob = λ c z → z
  *Strict-seq .N-hom c c' (γ , γᴰ , Eq.refl) p = Rᴰ.rectifyOut $
    sym (Rᴰ.⋆ᴰ-reind _) ∙ Rᴰ.⋆ᴰ-reind _

  *Strict-seq⁻ : PshHom ((α ⋆PshHomStrict β) *Strict Rᴰ) (α *Strict (β *Strict Rᴰ))
  *Strict-seq⁻ .N-ob = λ c z → z
  *Strict-seq⁻ .N-hom c c' (γ , γᴰ , Eq.refl) p = Rᴰ.rectifyOut $
    sym (Rᴰ.⋆ᴰ-reind _) ∙ Rᴰ.⋆ᴰ-reind _

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  {R : Presheaf C ℓR}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  {Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ}
  {α : PshHomStrict P Q}
  {β : PshHomStrict Q R}
  where
  _⋆PshHomᴰ_ : (αᴰ : PshHomᴰ α Pᴰ Qᴰ) (βᴰ : PshHomᴰ β Qᴰ Rᴰ)
    → PshHomᴰ (α ⋆PshHomStrict β) Pᴰ Rᴰ
  αᴰ ⋆PshHomᴰ βᴰ = αᴰ ⋆PshHom (α *StrictF βᴰ) ⋆PshHom *Strict-seq α β

module _
  {C : Category ℓC ℓC'}
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (ℓP : Level)
  (ℓPᴰ : Level)
  where
  private
    PSH = PRESHEAF C ℓP
    module PSH = Category PSH
    module Cᴰ = Fibers Cᴰ
  -- This is very slow without the annotations to refl.
  -- Think on that
  PRESHEAFᴰ : Categoryᴰ (PRESHEAF C ℓP) _ _
  PRESHEAFᴰ .ob[_] P = Presheaf (Cᴰ / P) ℓPᴰ
  PRESHEAFᴰ .Hom[_][_,_] α P Q = PshHom P (α *Strict Q)
  PRESHEAFᴰ .idᴰ = idPshHomᴰ
  PRESHEAFᴰ ._⋆ᴰ_ {f = α}{g = β} αᴰ βᴰ = αᴰ ⋆PshHomᴰ βᴰ
  PRESHEAFᴰ .⋆IdLᴰ {x = P}{xᴰ = Pᴰ}αᴰ = makePshHomPath (refl {x = αᴰ .N-ob})
  PRESHEAFᴰ .⋆IdRᴰ αᴰ = makePshHomPath (refl {x = αᴰ .N-ob})
  PRESHEAFᴰ .⋆Assocᴰ αᴰ βᴰ γᴰ = makePshHomPath
    (refl {x = ((αᴰ ⋆PshHomᴰ βᴰ) ⋆PshHomᴰ γᴰ) .N-ob})
  PRESHEAFᴰ .isSetHomᴰ = isSetPshHom _ _
