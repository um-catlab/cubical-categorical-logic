{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions.Reindex.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Equiv.Dependent

open import Cubical.Functions.FunExtEquiv

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
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.ReindexFunctor.Base
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
  renaming (π to Reindexπ; reindex to CatReindex)
-- TODO make CatReindex use hSetReasoning

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Bifunctorᴰ
open Functorᴰ

open isIsoOver

open PshHomᴰ
open PshHom
open PshIso

open Category
open Functor

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α β : PshHom P Q} {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where
  private
    module Qᴰ = PresheafᴰNotation Qᴰ
    module P = PresheafNotation P
    module Q = PresheafNotation Q

  module _ (α≡β : α ≡ β) where
    reindPathIsoⱽ : PshIsoⱽ (reind α Qᴰ) (reind β Qᴰ)
    reindPathIsoⱽ .fst .PshHomᴰ.N-obᴰ = Qᴰ.reind {e = funExt⁻ (funExt⁻ (cong N-ob α≡β) _) _}
    reindPathIsoⱽ .fst .PshHomᴰ.N-homᴰ =
      Qᴰ.rectify $ Qᴰ.≡out $
        (sym (Qᴰ.reind-filler)
        ∙ sym (Qᴰ.reind-filler)
        ∙ Qᴰ.⟨⟩⋆⟨ Qᴰ.reind-filler ⟩)
        ∙ Qᴰ.reind-filler
    reindPathIsoⱽ .snd .isIsoOver.inv q =
      Qᴰ.reind {e = funExt⁻ (funExt⁻ (cong N-ob (sym α≡β)) _) _}
    reindPathIsoⱽ .snd .isIsoOver.rightInv q qᴰ =
      Qᴰ.rectify $ Qᴰ.≡out $ sym $ Qᴰ.reind-filler ∙ Qᴰ.reind-filler
    reindPathIsoⱽ .snd .isIsoOver.leftInv q qᴰ =
      Qᴰ.rectify $ Qᴰ.≡out $ sym $ Qᴰ.reind-filler ∙ Qᴰ.reind-filler


module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α : PshHom P Q}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where
  private
    module Qᴰ = PresheafᴰNotation Qᴰ
  reind-π : PshHomᴰ α (reind α Qᴰ) Qᴰ
  reind-π .N-obᴰ = λ z → z
  reind-π .N-homᴰ = Qᴰ.rectify $ Qᴰ.≡out $ sym $ Qᴰ.reind-filler

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α : PshHom P Q}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where
  private
    module Q = PresheafNotation Q
    module Qᴰ = PresheafᴰNotation Qᴰ
  reind-introⱽ :
    PshHomᴰ α Pᴰ Qᴰ
    → PshHomⱽ Pᴰ (reind α Qᴰ)
  reind-introⱽ α .N-obᴰ = α .N-obᴰ
  reind-introⱽ α .N-homᴰ =
    Qᴰ.rectify $ Qᴰ.≡out $ (Qᴰ.≡in $ α .N-homᴰ) ∙ Qᴰ.reind-filler

  opaque
    reind-βⱽ :
      (αᴰ : PshHomᴰ α Pᴰ Qᴰ) →
      PshHomᴰPathP (reind-introⱽ αᴰ ⋆PshHomᴰ reind-π) αᴰ
        id⋆α≡α
    reind-βⱽ αᴰ =
      makePshHomᴰPathP _ _ _ λ {x}{xᴰ}{p} →
        funExt λ pᴰ → Qᴰ.rectify {e = refl} refl

    reind-βⱽ' :
      (αᴰ : PshHomᴰ α Pᴰ Qᴰ) →
      reind-introⱽ αᴰ ⋆PshHomⱽᴰ reind-π ≡ αᴰ
    reind-βⱽ' αᴰ = makePshHomᴰPath refl

    reind-ηⱽ :
      (αⱽ : PshHomⱽ Pᴰ (reind α Qᴰ)) →
      reind-introⱽ (αⱽ ⋆PshHomⱽᴰ reind-π) ≡ αⱽ
    reind-ηⱽ αⱽ = makePshHomᴰPath refl

  reind-UMPⱽ : Iso (PshHomᴰ α Pᴰ Qᴰ) (PshHomⱽ Pᴰ (reind α Qᴰ))
  reind-UMPⱽ .Iso.fun = reind-introⱽ
  reind-UMPⱽ .Iso.inv = _⋆PshHomⱽᴰ reind-π
  reind-UMPⱽ .Iso.sec = reind-ηⱽ
  reind-UMPⱽ .Iso.ret = reind-βⱽ'

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}{R : Presheaf C ℓR}
  {α : PshHom P Q} {β : PshHom Q R}
  {Pᴰ : Presheafᴰ Q Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  {Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ}
  (αᴰ : PshHomⱽ Pᴰ Qᴰ)
  (βᴰ : PshHomᴰ β Qᴰ Rᴰ)
  where
  private
    module Q = PresheafNotation Q
    module Qᴰ = PresheafᴰNotation Qᴰ
  reind-introⱽ-natural :
    αᴰ ⋆PshHomⱽ reind-introⱽ βᴰ ≡ reind-introⱽ (αᴰ ⋆PshHomⱽᴰ βᴰ)
  reind-introⱽ-natural = makePshHomᴰPath refl

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}{R : Presheaf C ℓR}
  {α : PshHom P Q}
  {β : PshHom Q R}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ}
  where
  private
    module Rᴰ = PresheafᴰNotation Rᴰ
  reind-introᴰ :
    PshHomᴰ (α ⋆PshHom β) Pᴰ Rᴰ
    → PshHomᴰ α Pᴰ (reind β Rᴰ)
  reind-introᴰ αβᴰ .N-obᴰ = αβᴰ .N-obᴰ
  reind-introᴰ αβᴰ .N-homᴰ = Rᴰ.rectify $ Rᴰ.≡out $
    (∫PshHom αβᴰ .N-hom _ _ _ _) ∙ Rᴰ.reind-filler

  opaque
    reind-βᴰ :
      (αᴰ : PshHomᴰ (α ⋆PshHom β) Pᴰ Rᴰ) →
      reind-introᴰ αᴰ ⋆PshHomᴰ reind-π ≡ αᴰ
    reind-βᴰ αᴰ = makePshHomᴰPath refl

    reind-ηᴰ :
      (αᴰ : PshHomᴰ α Pᴰ (reind β Rᴰ)) →
      reind-introᴰ (αᴰ ⋆PshHomᴰ reind-π) ≡ αᴰ
    reind-ηᴰ αᴰ = makePshHomᴰPath refl

  reind-UMP : Iso (PshHomᴰ (α ⋆PshHom β) Pᴰ Rᴰ) (PshHomᴰ α Pᴰ (reind β Rᴰ))
  reind-UMP .Iso.fun = reind-introᴰ
  reind-UMP .Iso.inv = _⋆PshHomᴰ reind-π
  reind-UMP .Iso.sec = reind-ηᴰ
  reind-UMP .Iso.ret = reind-βᴰ

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α : PshHom P Q}
  {α⁻ : PshHom Q P}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  {αᴰ : PshHomᴰ α Pᴰ Qᴰ}
  {αᴰ⁻ : PshHomᴰ α⁻ Qᴰ Pᴰ}
  (ret : α ⋆PshHom α⁻ ≡ idPshHom)
  (sec : α⁻ ⋆PshHom α ≡ idPshHom)
  (retᴰ : PshHomᴰPathP (αᴰ ⋆PshHomᴰ αᴰ⁻) idPshHomᴰ ret)
  (secᴰ : PshHomᴰPathP (αᴰ⁻ ⋆PshHomᴰ αᴰ) idPshHomᴰ sec)
  where

  makePshIsoᴰ' : PshIsoᴰ (makePshIso ret sec) Pᴰ Qᴰ
  makePshIsoᴰ' .fst = αᴰ
  makePshIsoᴰ' .snd .inv _ = αᴰ⁻ .N-obᴰ
  makePshIsoᴰ' .snd .isIsoOver.rightInv q qᴰ = congP (λ i z → z .N-obᴰ qᴰ) secᴰ
  makePshIsoᴰ' .snd .isIsoOver.leftInv p pᴰ = congP (λ i z → z .N-obᴰ pᴰ) retᴰ

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α : PshIso P Q}
  where

  module _
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
    {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
    {αᴰ : PshHomᴰ (α .trans) Pᴰ Qᴰ}
    {αᴰ⁻ : PshHomᴰ (invPshIso α .trans) Qᴰ Pᴰ}
    (retᴰ : PshHomᴰPathP (αᴰ ⋆PshHomᴰ αᴰ⁻) idPshHomᴰ (PshIso→ret α))
    (secᴰ : PshHomᴰPathP (αᴰ⁻ ⋆PshHomᴰ αᴰ) idPshHomᴰ (PshIso→sec α))
    where

    private
      module Qᴰ = PresheafᴰNotation Qᴰ
      module Pᴰ = PresheafᴰNotation Pᴰ

    makePshIsoᴰ : PshIsoᴰ α Pᴰ Qᴰ
    makePshIsoᴰ .fst = αᴰ
    makePshIsoᴰ .snd .inv _ = αᴰ⁻ .N-obᴰ
    makePshIsoᴰ .snd .isIsoOver.rightInv q qᴰ =
      Qᴰ.rectify $ congP (λ i z → z .N-obᴰ qᴰ) secᴰ
    makePshIsoᴰ .snd .isIsoOver.leftInv p pᴰ =
      Pᴰ.rectify $ congP (λ i z → z .N-obᴰ pᴰ) retᴰ

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α : PshIso P Q}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where
  open isIsoOver
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ

  -- TODO Finish porting reind-introIsoⱽ using β/η
  -- reind-introIsoⱽ' :
  --   PshIsoᴰ α Pᴰ Qᴰ →
  --   PshIsoᴰ (makePshIso _ _) Pᴰ (reind (α .trans) Qᴰ)
  -- reind-introIsoⱽ' αᴰ =
  --   makePshIsoᴰ'
  --     {αᴰ = reind-introⱽ (αᴰ .fst)}
  --     -- {αᴰ⁻ = reind-π ⋆PshHomᴰ invPshIsoᴰ αᴰ .fst}
  --     {αᴰ⁻ = reind-introⱽ (reind-π ⋆PshHomᴰ invPshIsoᴰ αᴰ .fst) ⋆PshHomⱽᴰ reind-π}
  --     (makePshHomPath (funExt₂ λ c p → α .nIso _ .snd .snd (idPshHom {C = C} {P = P} .N-ob c p)))
  --     (makePshHomPath (funExt₂ λ c p → α .nIso _ .snd .snd p))
  --     -- First is compPshHomᴰPathP' because it uses a rectify to be agnostic
  --     -- to the path between PshHoms requested by the goal
  --     (compPshHomᴰPathP' (congP₂ (λ _ → _⋆PshHomᴰ_) refl (reind-βⱽ' _)) $
  --       compPshHomᴰPathP (symP $ ⋆PshHomᴰAssoc _ _ _) $
  --       compPshHomᴰPathP (congP₂ (λ _ → _⋆PshHomᴰ_) (reind-βⱽ _) refl) $
  --       PshIsoᴰ→retᴰ αᴰ)
  --     -- TODO ⟨_⟩⋆PshHomᴰ⟨_⟩
  --     -- TODO use reind-introⱽ-natural for this goal
  --     (compPshHomᴰPathP' {!reind-introⱽ-natural!} $ {!!})

  reind-introIsoⱽ : PshIsoᴰ α Pᴰ Qᴰ → PshIsoⱽ Pᴰ (reind (α .trans) Qᴰ)
  reind-introIsoⱽ αᴰ .fst = reind-introⱽ (αᴰ .fst)
  reind-introIsoⱽ αᴰ .snd =
    isisoover
      (λ a qᴰ → Pᴰ.reind {e = α .nIso _ .snd .snd a} $ αᴰ⁻ .fst .N-obᴰ qᴰ)
      (λ a p →
        Qᴰ.rectify $ Qᴰ.≡out $
          Qᴰ.≡in (congP (λ i → αᴰ .fst .N-obᴰ) (Pᴰ.≡out $ sym $ Pᴰ.reind-filler))
          ∙ (Qᴰ.≡in (αᴰ .snd .rightInv _ _)))
      (λ b q →
        Pᴰ.rectify $ Pᴰ.≡out $
          (sym $ Pᴰ.reind-filler)
          ∙ Pᴰ.≡in (αᴰ .snd .leftInv _ q))
    where
    αᴰ⁻ = invPshIsoᴰ αᴰ

module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf D ℓQ}{R : Presheaf D ℓR}
  {F : Functor C D}
  {Fᴰ : Functorᴰ F Cᴰ Dᴰ}
  {α : PshHet F P Q}
  {β : PshHom Q R}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Rᴰ : Presheafᴰ R Dᴰ ℓRᴰ}
  where
  private
    module Rᴰ = PresheafᴰNotation Rᴰ
  reind-introHet
    : PshHetᴰ (α ⋆PshHom (β ∘ˡ F)) Fᴰ Pᴰ Rᴰ
    → PshHetᴰ α Fᴰ Pᴰ (reind β Rᴰ)
  reind-introHet αβᴰ .N-obᴰ = αβᴰ .N-obᴰ
  reind-introHet αβᴰ .N-homᴰ = Rᴰ.rectify $ Rᴰ.≡out $
    ∫PshHom αβᴰ .N-hom _ _ _ _ ∙ Rᴰ.reind-filler

module _{C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ Q Cᴰ ℓRᴰ} (α : PshHom P Q)
  where
  private
    module Qᴰ = PresheafᴰNotation Qᴰ
    module Rᴰ = PresheafᴰNotation Rᴰ
  reindPshHomⱽ : PshHomⱽ Qᴰ Rᴰ → PshHomⱽ (reind α Qᴰ) (reind α Rᴰ)
  reindPshHomⱽ βⱽ = reind-introⱽ (reind-π ⋆PshHomᴰⱽ βⱽ)

  reindPshIsoⱽ : PshIsoⱽ Qᴰ Rᴰ → PshIsoⱽ (reind α Qᴰ) (reind α Rᴰ)
  reindPshIsoⱽ βⱽ .fst = reindPshHomⱽ (βⱽ .fst)
  reindPshIsoⱽ βⱽ .snd .inv _ x = reind-βⱽ'' .N-obᴰ x
    where
      reind-βⱽ'' : PshHomⱽ (reind α Rᴰ) (reind α Qᴰ)
      reind-βⱽ'' = reind-introⱽ (reind-π ⋆PshHomᴰⱽ invPshIsoⱽ βⱽ .fst)
  reindPshIsoⱽ βⱽ .snd .rightInv _ _ = βⱽ .snd .rightInv _ _
  reindPshIsoⱽ βⱽ .snd .leftInv _ _ = βⱽ .snd .leftInv _ _

-- Reindexing is compositional:
module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}{R : Presheaf C ℓR}
  (α : PshHom P Q)(β : PshHom Q R) (Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ)
  where
  private
    module Rᴰ = PresheafᴰNotation Rᴰ
  opaque
    unfolding hSetReasoning.reind
    reind-seq-path :
      {x y : ob C} {f : (C ^op) [ x , y ]}
      {xᴰ : Categoryᴰ.ob[ Cᴰ ^opᴰ ] x} {yᴰ : Categoryᴰ.ob[ Cᴰ ^opᴰ ] y}
      (fᴰ : (Cᴰ ^opᴰ) [ f ][ xᴰ , yᴰ ]) →
      F-homᴰ (reind α (reind β Rᴰ)) fᴰ ≡
      (λ p qᴰ →
         hSetReasoning.reind {e = R .F-ob y} Rᴰ.p[_][ yᴰ ]
         (λ i →
            ((λ i₁ → β .N-ob y (α .N-hom y x f p i₁)) ∙
             β .N-hom y x f (α .N-ob x p))
            (~ i))
         (fᴰ Rᴰ.⋆ᴰ qᴰ))
    reind-seq-path fᴰ =
        funExt λ p → funExt λ rᴰ →
        Rᴰ.rectify $ Rᴰ.≡out $
            sym (Rᴰ.reind-filler ∙ Rᴰ.reind-filler)
            ∙ Rᴰ.reind-filler


  reind-seq : reind α (reind β Rᴰ) ≡ reind (α ⋆PshHom β) Rᴰ
  reind-seq = Functorᴰ≡ (λ _ → refl) reind-seq-path

  reind-seqIsoⱽ : PshIsoⱽ (reind α (reind β Rᴰ)) (reind (α ⋆PshHom β) Rᴰ)
  reind-seqIsoⱽ .fst .PshHomᴰ.N-obᴰ = λ z → z
  reind-seqIsoⱽ .fst .PshHomᴰ.N-homᴰ {f = f}{p = p}{fᴰ = fᴰ}{pᴰ = pᴰ} = opq
    where
    opaque
      unfolding hSetReasoning.reind
      opq :
        (reind (α ⋆PshHom β) Rᴰ PresheafᴰNotation.≡[
         (reind α (reind β Rᴰ) PresheafᴰNotation.⋆ᴰ fᴰ) pᴰ ]
         (λ _ → (P PresheafNotation.⋆ f) p))
        ((reind (α ⋆PshHom β) Rᴰ PresheafᴰNotation.⋆ᴰ fᴰ) pᴰ)
      opq = Rᴰ.rectify $ Rᴰ.≡out $
        sym (Rᴰ.reind-filler ∙ Rᴰ.reind-filler) ∙ Rᴰ.reind-filler
  reind-seqIsoⱽ .snd .isIsoOver.inv = λ a z → z
  reind-seqIsoⱽ .snd .isIsoOver.rightInv b q = refl
  reind-seqIsoⱽ .snd .isIsoOver.leftInv a p = refl

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}(Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
  reind-id : Pᴰ ≡ reind (idPshHom {P = P}) Pᴰ
  reind-id = Functorᴰ≡ (λ _ → refl)
    (λ _ → funExt λ _ → funExt λ _ → Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.reind-filler)

  reind-idIsoⱽ : PshIsoⱽ Pᴰ (reind (idPshHom {P = P}) Pᴰ)
  reind-idIsoⱽ .fst .PshHomᴰ.N-obᴰ = λ z → z
  reind-idIsoⱽ .fst .PshHomᴰ.N-homᴰ = Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.reind-filler
  reind-idIsoⱽ .snd .isIsoOver.inv = λ a z → z
  reind-idIsoⱽ .snd .isIsoOver.rightInv b q = refl
  reind-idIsoⱽ .snd .isIsoOver.leftInv a p = refl

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  (α : PshHom P Q) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
  private
    module P = PresheafNotation P
    module Qᴰ = PresheafᴰNotation Qᴰ
  module _ {c}(p : P.p[ c ]) where
    -- TODO This is really slow
    reindYo-seq : reindYo p (reind α Qᴰ) ≡ reindYo (α .N-ob _ p) Qᴰ
    reindYo-seq =
      reind-seq (yoRec P p) α Qᴰ
      ∙ cong₂ reind (yoRec-natural P Q α) refl

    reindYo-seqIsoⱽ : PshIsoⱽ (reindYo p (reind α Qᴰ)) (reindYo (α .N-ob c p) Qᴰ)
    reindYo-seqIsoⱽ =
      reind-seqIsoⱽ _ _ _ ⋆PshIsoⱽ reindPathIsoⱽ (yoRec-natural _ _ _)

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  (α : PshIso P Q) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
  private
    module Qᴰ = PresheafᴰNotation Qᴰ
  -- is this the universal property of reind?
  reindPshIsoPshIsoᴰ : PshIsoᴰ α (reind (α .trans) Qᴰ) Qᴰ
  reindPshIsoPshIsoᴰ = mkPshIsoᴰEquivOver α (reind (α .trans) Qᴰ) Qᴰ
    (record { N-obᴰ = λ z → z
            ; N-homᴰ = Qᴰ.rectify $ Qᴰ.≡out $ sym $ Qᴰ.reind-filler
            })
    (λ a → record { equiv-proof = strictContrFibers _ })

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}

  where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    motive : ∀ ℓQᴰ → (Q : Presheaf C ℓP) (α : P ≡ Q) → Type _
    motive ℓQᴰ Q α = ∀ (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
      → PathP (λ i → Presheafᴰ (α i) Cᴰ ℓQᴰ) (reind (pathToPshIso {P = P} {Q = Q} α .trans) Qᴰ) Qᴰ
  reindPathToPshIsoPathP :
    ∀ {Q : Presheaf C ℓP} (α : P ≡ Q)
    → (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
    -- TODO: give this kind of PathP a name? it's the analogue of PshIsoᴰ for paths
    → PathP (λ i → Presheafᴰ (α i) Cᴰ ℓQᴰ) (reind (pathToPshIso {P = P} {Q = Q} α .trans) Qᴰ) Qᴰ
  -- If we have prove pathToPshIso is an Iso then we could apply reindPshIsoPshIsoᴰ here
  reindPathToPshIsoPathP =
    J (motive _) λ Qᴰ →
      subst (λ α → reind (α .trans) Qᴰ ≡ Qᴰ)
        (sym $ pathToPshIsoRefl {C = C})
        (sym $ reind-id Qᴰ)

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  where
  private
    module Dᴰ = Categoryᴰ Dᴰ
  reindⱽFuncRepr :
    ∀ {x}{xᴰ : Dᴰ.ob[ F ⟅ x ⟆ ]} →
    PshIsoⱽ (reindⱽFunc F (Dᴰ [-][-, xᴰ ]))
            (CatReindex Dᴰ F [-][-, xᴰ ])
  reindⱽFuncRepr .fst .N-obᴰ = λ z → z
  -- This would be refl (with no unfolding) if CatReindex used hSetReasoning
  reindⱽFuncRepr {x = x}{xᴰ = xᴰ} .fst .N-homᴰ {x = y}{xᴰ = yᴰ}{f = f}{p = p}{fᴰ = fᴰ}{pᴰ = pᴰ} = opq
    where
    opaque
      unfolding hSetReasoning.reind
      opq :
        hSetReasoning.reind {e = Hom[ D , F-ob F y ] (F-ob F x) , D .isSetHom}
        Dᴰ.Hom[_][ yᴰ , xᴰ ] (λ i → F .F-seq f p (~ i)) (fᴰ Dᴰ.⋆ᴰ pᴰ)
        ≡
        transp (λ i → Dᴰ.Hom[ F-seq F f p (~ i) ][ yᴰ , xᴰ ]) i0
        (fᴰ Dᴰ.⋆ᴰ pᴰ)
      opq = refl
  reindⱽFuncRepr .snd .inv = λ a z → z
  reindⱽFuncRepr .snd .rightInv _ _ = refl
  reindⱽFuncRepr .snd .leftInv _ _ = refl

-- Whiskering a UniversalElementⱽ
module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {x : C .ob}
  {F : Functor C D}
  {Pⱽ : Presheafⱽ (F ⟅ x ⟆) Dᴰ ℓPᴰ}
  where
  open UniversalElementⱽ
  private
    module Pⱽ = PresheafⱽNotation Pⱽ

  -- manual for now but I feel like this should "just" be whiskering...
  reindUEⱽ : (ueⱽ : UniversalElementⱽ Dᴰ (F ⟅ x ⟆) Pⱽ)
    → UniversalElementⱽ (CatReindex Dᴰ F) x (reindⱽFunc F Pⱽ)
  reindUEⱽ ueⱽ .vertexⱽ = vertexⱽ ueⱽ
  reindUEⱽ ueⱽ .elementⱽ = Pⱽ.reind {e = sym $ F .F-id} (elementⱽ ueⱽ)
  reindUEⱽ ueⱽ .universalⱽ .fst = universalⱽ ueⱽ .fst
  reindUEⱽ ueⱽ .universalⱽ .snd .fst pᴰ = opq
    where
    opaque
      unfolding hSetReasoning.reind
      opq :
        (reindⱽFunc F Pⱽ PresheafⱽNotation.⋆ᴰⱽ
          universalⱽ ueⱽ .fst pᴰ)
         (hSetReasoning.reind {e = D [ F .F-ob x , F-ob F x ]} , D .isSetHom
          Pⱽ.p[_][ vertexⱽ ueⱽ ] (λ i → F .F-id (~ i)) (elementⱽ ueⱽ))
         ≡ pᴰ
      opq =
        (Pⱽ.rectify $ Pⱽ.≡out $
        (sym (Pⱽ.reind-filler) ∙ sym (Pⱽ.reind-filler)
        ∙ Pⱽ.⟨⟩⋆⟨ sym $ Pⱽ.reind-filler ⟩ ∙ Pⱽ.reind-filler))
        ∙ βⱽ ueⱽ
  reindUEⱽ ueⱽ .universalⱽ .snd .snd fᴰ = opq
    where
    opaque
      unfolding hSetReasoning.reind
      opq :
        universalⱽ ueⱽ .fst
        ((reindⱽFunc F Pⱽ PresheafⱽNotation.⋆ᴰⱽ fᴰ)
        (hSetReasoning.reind {e = D [ F .F-ob x , F-ob F x ]} , D .isSetHom
        Pⱽ.p[_][ vertexⱽ ueⱽ ] (λ i → F .F-id (~ i)) (elementⱽ ueⱽ)))
        ≡ fᴰ
      opq =
        cong (introᴰ ueⱽ) (Pⱽ.rectify $ Pⱽ.≡out $ sym (Pⱽ.reind-filler) ∙ sym (Pⱽ.reind-filler) ∙ Pⱽ.⟨⟩⋆⟨ sym $ Pⱽ.reind-filler ⟩ ∙ Pⱽ.reind-filler)
        ∙ (sym $ ηⱽ ueⱽ)

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  where
  module _ {P : Presheaf D ℓP}{Q : Presheaf D ℓQ} {Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ}
           {α : PshHom P Q}
           where
    reindFuncReind :
      PshIsoⱽ (reindFunc F $ reind α Qᴰ)
              (reind (α ∘ˡ F) $ reindFunc F Qᴰ)
    reindFuncReind = eqToPshIsoⱽ foo where
      foo : PresheafᴰEq (reindFunc F $ reind α Qᴰ) (reind (α ∘ˡ F) $ reindFunc F Qᴰ)
      foo = (Eq.refl , Eq.refl)

  module _ {x y}{f : C [ x , y ]}{Qⱽ : Presheafⱽ (F ⟅ y ⟆) Dᴰ ℓQ} where
    reindYoReindFunc :
      PshIsoⱽ (reindYo f $ reindⱽFunc F Qⱽ)
              (reindⱽFunc F (reindYo (F ⟪ f ⟫) Qⱽ))
    reindYoReindFunc =
      reindYo-seqIsoⱽ _ _ _
      -- TODO: turn this yoRec≡ ... into a lemma?
      ⋆PshIsoⱽ reindPathIsoⱽ (yoRec≡ _ ((sym $ D .⋆IdL _) ∙ cong₂ (seq' D) (sym $ F .F-id) refl))
      ⋆PshIsoⱽ (invPshIsoⱽ $ reind-seqIsoⱽ _ _ _)
      ⋆PshIsoⱽ reindPshIsoⱽ (Functor→PshHet F x) (invPshIsoⱽ reindFuncReind)

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  {Fᴰ : Functorᴰ F Cᴰ Dᴰ}
  {P : Presheaf D ℓP}
  {Q : Presheaf D ℓP}
  {Qᴰ : Presheafᴰ Q Dᴰ ℓPᴰ}
  {α : PshHom P Q}
  where

  reindFuncCompIsoⱽ :
    PshIsoⱽ
      (reind α Qᴰ ∘Fᴰ (Fᴰ ^opFᴰ))
      (reind (α ∘ˡ F) (Qᴰ ∘Fᴰ (Fᴰ ^opFᴰ)))
  reindFuncCompIsoⱽ = eqToPshIsoⱽ foo
      where
      foo :
        PresheafᴰEq
          (reind α Qᴰ ∘Fᴰ (Fᴰ ^opFᴰ))
          (reind (α ∘ˡ F) (Qᴰ ∘Fᴰ (Fᴰ ^opFᴰ)))
      foo = (Eq.refl , Eq.refl)
