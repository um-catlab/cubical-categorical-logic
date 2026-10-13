module Cubical.Categories.Displayed.HLevels.PropValuedPresheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.HLevels

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Categoryᴰ
open isIsoOver
open UniversalElementNotation
open PshIso
open PshHom

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  open Category
  private
    module Cᴰ = Categoryᴰ Cᴰ
  module _ (hasContrHom : hasContrHoms Cᴰ) {v} (vᴰ : Cᴰ.ob[ v ]) where
    hasContrHoms→Reprᴰ≅1 : PshIso (UnitPshᴰ {P = C [-, v ]}) (Cᴰ [-][-, vᴰ ])
    hasContrHoms→Reprᴰ≅1 =
      Isos→PshIso (λ _ → isContr→Iso isContrUnit (hasContrHom _ _ _))
        (λ _ _ _ _ → isContr→isProp (hasContrHom _ _ _) _ _)

  module _ (hasContrHom : hasContrHoms Cᴰ)
      {P : Presheaf C ℓP} {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ} where
    private
      module Pᴰ = PresheafᴰNotation Cᴰ P Pᴰ
    module _
        (isPropPshᴰ : ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) → ∀ {e}
          → isProp (Pᴰ.p[ e ][ Γᴰ ]))
        (ue : UniversalElement C P) {vᴰ}
        (eᴰ : Pᴰ.p[ ue .element ][ vᴰ ]) where
       hasContrHoms→isUniversalᴰ : isUniversalᴰ Cᴰ P Pᴰ ue eᴰ
       hasContrHoms→isUniversalᴰ Γ Γᴰ .inv p pᴰ =
         hasContrHom _ Γᴰ vᴰ .fst
       hasContrHoms→isUniversalᴰ Γ Γᴰ .rightInv p pᴰ =
         isProp→PathP (λ _ → isPropPshᴰ Γᴰ) _ pᴰ
       hasContrHoms→isUniversalᴰ Γ Γᴰ .leftInv f fᴰ =
         isProp→PathP (λ _ → isContr→isProp (hasContrHom _ Γᴰ vᴰ)) _ fᴰ

       hasContrHoms+propValuedPshᴰ→UEᴰ : UniversalElementᴰ Cᴰ P Pᴰ ue
       hasContrHoms+propValuedPshᴰ→UEᴰ .fst = vᴰ
       hasContrHoms+propValuedPshᴰ→UEᴰ .snd .fst = eᴰ
       hasContrHoms+propValuedPshᴰ→UEᴰ .snd .snd = hasContrHoms→isUniversalᴰ
