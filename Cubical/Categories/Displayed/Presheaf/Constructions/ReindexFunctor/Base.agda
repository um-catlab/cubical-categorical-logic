-- reindexing a displayed presheaf Qᴰ over Q on Cᴰ over C by a Functorᴰ Fᴰ over F
module Cubical.Categories.Displayed.Presheaf.Constructions.ReindexFunctor.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Structure

open import Cubical.Reflection.RecordEquiv.More

import Cubical.Data.Equality as Eq
open import Cubical.Data.Prod.Base hiding (_×_)
open import Cubical.Data.Sigma

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
  using (NatTrans ; NatIso ; idTrans)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.LocallySmall as LocallySmall

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Presheaf.Base hiding (PRESHEAFᴰ)
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Representable

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓP ℓPᴰ ℓQ ℓQᴰ ℓR ℓRᴰ ℓS ℓSᴰ : Level

open Functor
open Functorᴰ
open isIsoᴰ
open PshHomᴰ
open PshIsoᴰ

module _
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'} where
  reindPshᴰFunctor : {F : Functor C D} {Q : Presheaf D ℓQ}
    (Fᴰ : Functorᴰ F Cᴰ Dᴰ) (Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ)
    → Presheafᴰ (reindPsh F Q) Cᴰ ℓQᴰ
  reindPshᴰFunctor Fᴰ Qᴰ = Qᴰ ∘Fᴰ (Fᴰ ^opFᴰ)

  reindPshᴰPshHomᴰ :
    {F : Functor C D} {P : Presheaf D ℓP}{Q : Presheaf D ℓQ}
    {α : PshHom P Q}
    {Pᴰ : Presheafᴰ P Dᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ}
    (Fᴰ : Functorᴰ F Cᴰ Dᴰ)(αᴰ : PshHomᴰ α Pᴰ Qᴰ)
    → PshHomᴰ (reindPshHom F α) (reindPshᴰFunctor Fᴰ Pᴰ) (reindPshᴰFunctor Fᴰ Qᴰ)
  reindPshᴰPshHomᴰ Fᴰ αᴰ .N-obᴰ = αᴰ .N-obᴰ
  reindPshᴰPshHomᴰ Fᴰ αᴰ .N-homᴰ = αᴰ .N-homᴰ

  reindPshᴰPshIsoᴰ :
    {F : Functor C D} {P : Presheaf D ℓP}{Q : Presheaf D ℓQ}
    {α : PshIso P Q}
    {Pᴰ : Presheafᴰ P Dᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ}
    (Fᴰ : Functorᴰ F Cᴰ Dᴰ)(αᴰ : PshIsoᴰ α Pᴰ Qᴰ)
    → PshIsoᴰ (reindPshIso F α) (reindPshᴰFunctor Fᴰ Pᴰ) (reindPshᴰFunctor Fᴰ Qᴰ)
  reindPshᴰPshIsoᴰ Fᴰ αᴰ .transᴰ = reindPshᴰPshHomᴰ Fᴰ (αᴰ .transᴰ)
  reindPshᴰPshIsoᴰ Fᴰ αᴰ .nIsoᴰ .fst = reindPshᴰPshHomᴰ Fᴰ (invPshIsoᴰ αᴰ .transᴰ) .N-obᴰ
  reindPshᴰPshIsoᴰ Fᴰ αᴰ .nIsoᴰ .snd .fst = αᴰ .nIsoᴰ .snd .fst
  reindPshᴰPshIsoᴰ Fᴰ αᴰ .nIsoᴰ .snd .snd = αᴰ .nIsoᴰ .snd .snd

  -- A displayed "heteromorphism" is a kind of morphism between
  -- displayed presheaves on different categories.

  -- We can't make this into a displayed category because PshHetᴰ is
  -- displayed over Functorᴰs, which do not form an hSet. Would need
  -- displayed 2-categories.
  module _ {F : Functor C D} {P : Presheaf C ℓP}{Q : Presheaf D ℓQ} where
    PshHetᴰ : (α : PshHet F P Q) (Fᴰ : Functorᴰ F Cᴰ Dᴰ) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ)
      → Type _
    PshHetᴰ α Fᴰ Pᴰ Qᴰ = PshHomᴰ α Pᴰ (reindPshᴰFunctor Fᴰ Qᴰ)

  Functorᴰ→PshHetᴰ :
    ∀ {F : Functor C D} {x} (Fᴰ : Functorᴰ F Cᴰ Dᴰ) xᴰ →
      PshHetᴰ (Functor→PshHet F x) Fᴰ (Cᴰ [-][-, xᴰ ]) (Dᴰ [-][-, Fᴰ .F-obᴰ xᴰ ])
  Functorᴰ→PshHetᴰ Fᴰ xᴰ .N-obᴰ = Fᴰ .F-homᴰ
  Functorᴰ→PshHetᴰ Fᴰ xᴰ .N-homᴰ = Fᴰ .F-seqᴰ _ _

-- A "vertical" heteromorphism is between objects
module _
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {x}
  {F : Functor C D}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  (Pⱽ : Presheafⱽ x Cᴰ ℓPᴰ)
  (Qⱽ : Presheafⱽ (F ⟅ x ⟆) Dᴰ ℓQᴰ) where

  PshHetⱽ : Type _
  PshHetⱽ = PshHetᴰ (Functor→PshHet F x) Fᴰ Pⱽ Qⱽ

reindPshᴰIdᴰ≅ : {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}(Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) → PshIsoᴰ (reindPshId≅ P) Pᴰ (reindPshᴰFunctor Idᴰ Pᴰ)
reindPshᴰIdᴰ≅ Pᴰ .transᴰ .N-obᴰ = λ z → z
reindPshᴰIdᴰ≅ Pᴰ .transᴰ .N-homᴰ = refl
reindPshᴰIdᴰ≅ Pᴰ .nIsoᴰ .fst = λ z → z
reindPshᴰIdᴰ≅ Pᴰ .nIsoᴰ .snd .fst = λ _ → refl
reindPshᴰIdᴰ≅ Pᴰ .nIsoᴰ .snd .snd = λ _ → refl

-- -- TODO
-- reindPshᴰ∘Fᴰ≅
-- TODO: stuff about preserving universal elements goes in the PshHetᴰ file ReindexFunctor

module _
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {P : Presheaf C ℓP} {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Q : Presheaf D ℓQ} {Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ}
  {F : Functor C D}{Fᴰ : Functorᴰ F Cᴰ Dᴰ}
  {α : PshHet F P Q}
  (αᴰ : PshHetᴰ α Fᴰ Pᴰ Qᴰ)
  where

  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Cᴰ = Fibers Cᴰ

  becomesUniversalᴰ : ∀ {v}{e} →
    becomesUniversal α v e →
    (vᴰ : Cᴰ.ob[ v ])(eᴰ : Pᴰ.p[ e ][ vᴰ ]) → Type _
  becomesUniversalᴰ becomesUE vᴰ eᴰ =
    isUniversalᴰ Dᴰ (becomesUniversal→UniversalElement α becomesUE)
      Qᴰ (Fᴰ .F-obᴰ vᴰ) (αᴰ .N-obᴰ eᴰ)

  becomesUniversalᴰ→UEᴰ : ∀ {v}{e}
    {becomesUE : becomesUniversal α v e} →
    {vᴰ : Cᴰ.ob[ v ]}{eᴰ : Pᴰ.p[ e ][ vᴰ ]} →
    becomesUniversalᴰ becomesUE vᴰ eᴰ →
    UniversalElementᴰ Dᴰ
      (becomesUniversal→UniversalElement α becomesUE) Qᴰ
  becomesUniversalᴰ→UEᴰ = univeltᴰ _ _

module _
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {P : Presheaf C ℓP} {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Q : Presheaf D ℓQ} {Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ}
  {F : Functor C D}{Fᴰ : Functorᴰ F Cᴰ Dᴰ}
  {α : PshHet F P Q}
  {ue : UniversalElement C P}
  (α-presUE : preservesUniversalElement {F = F}{P = P} α ue)
  (αᴰ : PshHetᴰ α Fᴰ Pᴰ Qᴰ)
  where
  module _ (ueᴰ : UniversalElementᴰ Cᴰ ue Pᴰ) where
    private
      module ueᴰ = UniversalElementᴰ ueᴰ
    preservesUEᴰ : Type _
    preservesUEᴰ =
      becomesUniversalᴰ αᴰ α-presUE ueᴰ.vertexᴰ ueᴰ.elementᴰ

  module _
    (ueᴰ : UniversalElementᴰ Cᴰ ue Pᴰ)
    (presUEᴰ : preservesUEᴰ ueᴰ)
    where
    preservesUEᴰ→UEᴰ :
      UniversalElementᴰ Dᴰ
        (becomesUniversal→UniversalElement α α-presUE) Qᴰ
    preservesUEᴰ→UEᴰ = becomesUniversalᴰ→UEᴰ αᴰ presUEᴰ

-- module _
--   {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
--   {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
--   {F : Functor C D}{Fᴰ : Functorᴰ F Cᴰ Dᴰ}
--   {c}
--   {Pⱽ : Presheafⱽ c Cᴰ ℓPᴰ}
--   {Qⱽ : Presheafⱽ (F ⟅ c ⟆) Dᴰ ℓQᴰ}
--   (αⱽ : PshHetⱽ Fᴰ Pⱽ Qⱽ)
--   where

--   private
--     module Pⱽ = PresheafⱽNotation Pⱽ
--     module Qⱽ = PresheafⱽNotation Qⱽ
--     module C = Category C
--     module Cᴰ = Fibers Cᴰ

--   becomesUniversalⱽ :
--     (cᴰ : Cᴰ.ob[ c ])(eⱽ : Pⱽ.p[ C.id ][ cᴰ ]) → Type _
--   becomesUniversalⱽ cᴰ eⱽ = isUniversalᴰ Dᴰ (F⟨selfUnivElt⟩ F c) Qⱽ _
--     (αⱽ .N-obᴰ eⱽ)

    -- isUniversalⱽ Dᴰ (F ⟅ c ⟆) Qⱽ (Fᴰ .F-obᴰ cᴰ)
    --   -- TODO: define this as N-obⱽ?
    --   (Qⱽ.reind (F .F-id) $ αⱽ .N-obᴰ eⱽ)

-- --   becomesUniversalⱽ→UEⱽ :
-- --     ∀ {cᴰ}{eⱽ} →
-- --     becomesUniversalⱽ cᴰ eⱽ →
-- --     UniversalElementⱽ Dᴰ (F ⟅ c ⟆) Qⱽ
-- --   becomesUniversalⱽ→UEⱽ becomesUEⱽ .UniversalElementⱽ.vertexⱽ = _
-- --   becomesUniversalⱽ→UEⱽ becomesUEⱽ .UniversalElementⱽ.elementⱽ = _
-- --   becomesUniversalⱽ→UEⱽ becomesUEⱽ .UniversalElementⱽ.universalⱽ = becomesUEⱽ

-- -- module _
-- --   {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
-- --   {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
-- --   {F : Functor C D}
-- --   {x}
-- --   {Fᴰ : Functorᴰ F Cᴰ Dᴰ}
-- --   {Pⱽ : Presheafⱽ x Cᴰ ℓPᴰ}
-- --   {Qⱽ : Presheafⱽ (F ⟅ x ⟆) Dᴰ ℓQᴰ}
-- --   (αⱽ : PshHetⱽ Fᴰ Pⱽ Qⱽ)
-- --   (ueⱽ : UniversalElementⱽ Cᴰ x Pⱽ)
-- --   where
-- --   private
-- --     module Qⱽ = PresheafⱽNotation Qⱽ
-- --     module ueⱽ = UniversalElementⱽ ueⱽ
-- --   preservesUEⱽ : Type _
-- --   preservesUEⱽ = becomesUniversalⱽ αⱽ ueⱽ.vertexⱽ ueⱽ.elementⱽ

-- --   preservesUEⱽ→UEⱽ : preservesUEⱽ → UniversalElementⱽ Dᴰ (F ⟅ x ⟆) Qⱽ
-- --   preservesUEⱽ→UEⱽ = becomesUniversalⱽ→UEⱽ αⱽ
