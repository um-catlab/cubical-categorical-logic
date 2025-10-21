-- This is for the notion of reindexing a presheaf Qᴰ over Q along a
-- homomorphism α : P ⇒ Q to be over P, i.e., the "fibration"
-- structure of presheaves.
--
-- For reindexing along a functor, see Cubical.Categories.Displayed.Presheaf.Constructions.ReindexFunctor
module Cubical.Categories.Displayed.Presheaf.Constructions.Reindex.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
  renaming (π to Reindexπ; reindex to CatReindex)

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Bifunctorᴰ
open Functorᴰ

open PshHom
open PshIso

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
           (α : PshHom P Q) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
           where
    private
      module Qᴰ = PresheafᴰNotation Qᴰ
    open Functorᴰ
    reind : Presheafᴰ P Cᴰ ℓQᴰ
    reind .F-obᴰ {x} xᴰ p = Qᴰ .F-obᴰ xᴰ (α .N-ob x p)
    reind .F-homᴰ {y} {x} {f} {yᴰ} {xᴰ} fᴰ p qᴰ =
      Qᴰ.reind (sym $ α .N-hom _ _ _ _) (fᴰ Qᴰ.⋆ᴰ qᴰ)
    reind .F-idᴰ = funExt λ p → funExt λ qᴰ → Qᴰ.rectify $ Qᴰ.≡out $
      (sym $ Qᴰ.reind-filler _ _)
      ∙ Qᴰ.⋆IdL _
    reind .F-seqᴰ fᴰ gᴰ = funExt λ p → funExt λ qᴰ → Qᴰ.rectify $ Qᴰ.≡out $
      (sym $ Qᴰ.reind-filler _ _)
      ∙ Qᴰ.⋆Assoc _ _ _
      ∙ Qᴰ.⟨ refl ⟩⋆⟨ Qᴰ.reind-filler _ _ ⟩
      ∙ Qᴰ.reind-filler _ _

  module _ {Q : Presheaf C ℓQ} where
    private
      module Q = PresheafNotation Q
    module _ {c : C.ob} (q : Q.p[ c ]) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where
      private
        module Qᴰ = PresheafᴰNotation Qᴰ
        open Functorᴰ
      reindYo : Presheafⱽ c Cᴰ ℓQᴰ
      reindYo = reind (yoRec Q q) Qᴰ
