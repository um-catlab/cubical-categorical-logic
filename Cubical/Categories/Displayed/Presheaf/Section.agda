-- (global) sections of displayed presheaves generalize presheaf
-- homomorphisms in the same way that global sections of displayed
-- categories generalize functors.

-- That is, given a presheaf Pᴰ on Cᴰ over P on C, a section of Pᴰ is
-- a kind of "homomorphism from P to Pᴰ". This doesn't quite make
-- sense unless we are provided a global section F of Cᴰ.

-- In terms of total categories, a global section F of Cᴰ is a section
-- of the projection functor ∫ Cᴰ → C. A global section α of Pᴰ along
-- F is similarly a section of the natural transformation (∫ Pᴰ ∘ F) ⇒
-- P
module Cubical.Categories.Displayed.Presheaf.Section where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Terminal as Terminal
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.Unit.Base
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Section

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓP ℓPᴰ ℓQ ℓQᴰ : Level

open PshHomᴰ
open Section

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} (F : GlobalSection Cᴰ) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ
  -- N.B. this is a *global* section.
  record PshSection : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓP) ℓPᴰ) where
    no-eta-equality
    field
      N-ob  : ∀ {x}(p : P.p[ x ]) → Pᴰ.p[ p ][ F .F-obᴰ x ]
      N-hom :
        ∀ {x y}(f : C [ x , y ])(p : P.p[ y ])
        → N-ob (f P.⋆ p) ≡ (F .F-homᴰ f Pᴰ.⋆ᴰ N-ob p)

  open PshSection
  PshSection→PshHomⱽ : PshSection → PshHomⱽ {Cᴰ = Unitᴰ C} (UnitPshᴰ {P = P}) (Pᴰ ∘Fᴰⱽ (Terminal.recᴰ F ^opFⱽ))
  PshSection→PshHomⱽ α .N-obᴰ {_} {_} {p} _ = α .N-ob p
  PshSection→PshHomⱽ α .N-homᴰ = α .N-hom _ _

  PshHomⱽ→PshSection : PshHomⱽ {Cᴰ = Unitᴰ C} (UnitPshᴰ {P = P}) (Pᴰ ∘Fᴰⱽ (Terminal.recᴰ F ^opFⱽ)) → PshSection
  PshHomⱽ→PshSection α .N-ob = λ p → α .N-obᴰ tt
  PshHomⱽ→PshSection α .N-hom = λ f p → α .N-homᴰ

open PshSection
module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (F : GlobalSection Cᴰ) c
  where
  Section→PshSection : PshSection F (Cᴰ [-][-, F .F-obᴰ c ])
  Section→PshSection .N-ob = F .F-homᴰ
  Section→PshSection .N-hom = F .F-seqᴰ

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  (F : GlobalSection Cᴰ)(α : PshSection F Pᴰ)
  (ue : UniversalElement C P)
  where
  open UniversalElement
  open UniversalElementᴰ
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Cᴰ = Categoryᴰ Cᴰ
    elementOverUE = (Σ[ v ∈ Cᴰ.ob[ ue .vertex ] ] Pᴰ.p[ ue .element ][ v ])
  -- Strict preservation is when vertex ↦ vertexᴰ and element ↦ elementᴰ
  strictlyPreservesUE : (ueᴰ : UniversalElementᴰ Cᴰ ue Pᴰ) → Type _
  strictlyPreservesUE ueᴰ =
    Path elementOverUE
      (_ , (α .N-ob (ue .element)))
      (_ , ueᴰ .elementᴰ)

  -- weak preservation doesn't require the a priori existence of ueᴰ
  preservesUE : Type _
  preservesUE =
    isUniversalᴰ Cᴰ ue Pᴰ (F .F-obᴰ $ ue .vertex) (α .N-ob $ ue .element)

  strictlyPreservesUE→preservesUE :
    (ueᴰ : UniversalElementᴰ Cᴰ ue Pᴰ)
    → strictlyPreservesUE ueᴰ → preservesUE
  strictlyPreservesUE→preservesUE ueᴰ ue↦ueᴰ =
    subst isUniversalᴰ' (sym ue↦ueᴰ) (ueᴰ .universalᴰ)
    where
      isUniversalᴰ' : elementOverUE → Type _
      isUniversalᴰ' (vᴰ , eᴰ) = isUniversalᴰ Cᴰ ue Pᴰ vᴰ eᴰ
