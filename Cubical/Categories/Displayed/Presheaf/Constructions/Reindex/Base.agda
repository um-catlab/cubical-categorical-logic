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

  -- Reindexing presheaves
  -- There are 3 different notions of reindexing a presheaf we consider here.
  -- 1. Reindexing a presheaf Qᴰ over Q along a homomorphism α : P ⇒ Q to be over P
  -- 2. Reindexing a presheaf Qᴰ over Q along a functor F to be over (Q ∘ F^op)
  -- 3. The combination of those two, reindexing a presheaf Qᴰ over Q along a heteromorphism α : P =[ F ]=> Q to be over P.
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

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {Q : Presheaf D ℓQ}
  (F : Functor C D) (Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ)
  where
  reindFunc : Presheafᴰ (Q ∘F (F ^opF)) (CatReindex Dᴰ F) ℓQᴰ
  reindFunc = Qᴰ ∘Fᴰ (Reindexπ _ _ ^opFᴰ)

open Category
module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  {P : Presheaf C ℓP}{Q : Presheaf D ℓQ}
  (α : PshHet F P Q)(Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ)
  where
  reindHet : Presheafᴰ P (CatReindex Dᴰ F) ℓQᴰ
  reindHet = reind α $ reindFunc F Qᴰ

module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  {P : Presheaf C ℓP}{Q : Presheaf D ℓQ}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ}
  (α : PshHet F P Q)
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  where
  reindHet' : Presheafᴰ P Cᴰ ℓQᴰ
  reindHet' = reind α $ (Qᴰ ∘Fᴰ (Fᴰ ^opFᴰ)) -- reind α $ reindFunc F Qᴰ

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {x : C .ob}
  (F : Functor C D) (Qᴰ : Presheafⱽ (F ⟅ x ⟆) Dᴰ ℓQᴰ)
  where
  reindⱽFunc : Presheafⱽ x (CatReindex Dᴰ F) ℓQᴰ
  reindⱽFunc = reindHet (Functor→PshHet F x) Qᴰ
