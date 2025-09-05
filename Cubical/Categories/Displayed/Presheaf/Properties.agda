{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Equiv.Dependent

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
  renaming (π to Reindexπ; reindex to CatReindex)
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Representable

open Bifunctor
open Bifunctorᴰ
open Category
open Functor
open Functorᴰ
open isIsoOver
open PshHomᴰ
private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open PshHom
open PshIso

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α β : PshHom P Q}(α≡β : α ≡ β) {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where
  private
    module Qᴰ = PresheafᴰNotation Qᴰ
  reindPathIsoⱽ : PshIsoⱽ (reind α Qᴰ) (reind β Qᴰ)
  reindPathIsoⱽ .fst .PshHomᴰ.N-obᴰ = Qᴰ.reind (funExt⁻ (funExt⁻ (cong N-ob α≡β) _) _)
  reindPathIsoⱽ .fst .PshHomᴰ.N-homᴰ =
    Qᴰ.rectify $ Qᴰ.≡out $
      (sym (Qᴰ.reind-filler _ _)
      ∙ sym (Qᴰ.reind-filler _ _)
      ∙ Qᴰ.⟨⟩⋆⟨ Qᴰ.reind-filler _ _ ⟩)
      ∙ Qᴰ.reind-filler _ _
  reindPathIsoⱽ .snd .isIsoOver.inv q =
    Qᴰ.reind ((funExt⁻ (funExt⁻ (cong N-ob (sym α≡β)) _) _))
  reindPathIsoⱽ .snd .isIsoOver.rightInv q qᴰ =
    Qᴰ.rectify $ Qᴰ.≡out $ sym $ Qᴰ.reind-filler _ _ ∙ Qᴰ.reind-filler _ _
  reindPathIsoⱽ .snd .isIsoOver.leftInv q qᴰ =
    Qᴰ.rectify $ Qᴰ.≡out $ sym $ Qᴰ.reind-filler _ _ ∙ Qᴰ.reind-filler _ _


module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α : PshHom P Q}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where
  private
    module Qᴰ = PresheafᴰNotation Qᴰ
  reind-π : PshHomᴰ α (reind α Qᴰ) Qᴰ
  reind-π .N-obᴰ = λ z → z
  reind-π .N-homᴰ = Qᴰ.rectify $ Qᴰ.≡out $ sym $ Qᴰ.reind-filler _ _

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α : PshHom P Q}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where
  private
    module Qᴰ = PresheafᴰNotation Qᴰ
  reind-introⱽ :
    PshHomᴰ α Pᴰ Qᴰ
    → PshHomⱽ Pᴰ (reind α Qᴰ)
  reind-introⱽ α .N-obᴰ = α .N-obᴰ
  reind-introⱽ α .N-homᴰ =
    Qᴰ.rectify $ Qᴰ.≡out $ (Qᴰ.≡in $ α .N-homᴰ) ∙ Qᴰ.reind-filler _ _

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
    (Rᴰ.≡in $ αβᴰ .N-homᴰ) ∙ Rᴰ.reind-filler _ _

module _{C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α : PshHom P Q} {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ Q Cᴰ ℓRᴰ}
  where
  private
    module Qᴰ = PresheafᴰNotation Qᴰ
    module Rᴰ = PresheafᴰNotation Rᴰ
  reindPshHomⱽ : PshHomⱽ Qᴰ Rᴰ → PshHomⱽ (reind α Qᴰ) (reind α Rᴰ)
  reindPshHomⱽ βⱽ = reind-introⱽ (reind-π ⋆PshHomᴰⱽ βⱽ)

  reindPshIsoⱽ : PshIsoⱽ Qᴰ Rᴰ → PshIsoⱽ (reind α Qᴰ) (reind α Rᴰ)
  reindPshIsoⱽ βⱽ .fst = reindPshHomⱽ (βⱽ .fst)
  reindPshIsoⱽ βⱽ .snd .inv _ x = reind-βⱽ .N-obᴰ x
    where
      reind-βⱽ : PshHomⱽ (reind α Rᴰ) (reind α Qᴰ)
      reind-βⱽ = reind-introⱽ (reind-π ⋆PshHomᴰⱽ invPshIsoⱽ βⱽ .fst)
  reindPshIsoⱽ βⱽ .snd .rightInv _ _ = βⱽ .snd .rightInv _ _
  reindPshIsoⱽ βⱽ .snd .leftInv _ _ = βⱽ .snd .leftInv _ _

-- Reindexing is compositional:
module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}{R : Presheaf C ℓR}
  (α : PshHom P Q)(β : PshHom Q R) (Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ)
  where
  private
    module Rᴰ = PresheafᴰNotation Rᴰ
  reind-seq : reind α (reind β Rᴰ) ≡ reind (α ⋆PshHom β) Rᴰ
  reind-seq = Functorᴰ≡ (λ _ → refl) λ fᴰ → funExt λ p → funExt λ rᴰ →
    Rᴰ.rectify $ Rᴰ.≡out $
      sym (Rᴰ.reind-filler _ _ ∙ Rᴰ.reind-filler _ _)
      ∙ Rᴰ.reind-filler _ _

  reind-seqIsoⱽ : PshIsoⱽ (reind α (reind β Rᴰ)) (reind (α ⋆PshHom β) Rᴰ)
  reind-seqIsoⱽ .fst .PshHomᴰ.N-obᴰ = λ z → z
  reind-seqIsoⱽ .fst .PshHomᴰ.N-homᴰ = Rᴰ.rectify $ Rᴰ.≡out $
    sym (Rᴰ.reind-filler _ _ ∙ Rᴰ.reind-filler _ _) ∙ Rᴰ.reind-filler _ _
  reind-seqIsoⱽ .snd .isIsoOver.inv = λ a z → z
  reind-seqIsoⱽ .snd .isIsoOver.rightInv b q = refl
  reind-seqIsoⱽ .snd .isIsoOver.leftInv a p = refl

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}(Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
  reind-id : Pᴰ ≡ reind idPshHom Pᴰ
  reind-id = Functorᴰ≡ (λ _ → refl)
    (λ _ → funExt λ _ → funExt λ _ → Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.reind-filler _ _)

  reind-idIsoⱽ : PshIsoⱽ Pᴰ (reind idPshHom Pᴰ)
  reind-idIsoⱽ .fst .PshHomᴰ.N-obᴰ = λ z → z
  reind-idIsoⱽ .fst .PshHomᴰ.N-homᴰ = Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.reind-filler _ _
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
    reindYo-seq : reindYo p (reind α Qᴰ) ≡ reindYo (α .N-ob _ p) Qᴰ
    reindYo-seq = reind-seq _ _ _
      ∙ cong₂ reind (yoRec-natural _ _ _) refl

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
            ; N-homᴰ = Qᴰ.rectify $ Qᴰ.≡out $ sym $ Qᴰ.reind-filler _ _
            })
    (λ a → record { equiv-proof = strictContrFibers _ })

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}

  where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    motive : ∀ ℓQᴰ → (Q : Presheaf C ℓP) (α : P ≡ Q) → Type _
    motive ℓQᴰ Q α = ∀ (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
      → PathP (λ i → Presheafᴰ (α i) Cᴰ ℓQᴰ) (reind (pathToPshIso α .trans) Qᴰ) Qᴰ
  reindPathToPshIsoPathP :
    ∀ {Q : Presheaf C ℓP} (α : P ≡ Q)
    → (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
    -- TODO: give this kind of PathP a name? it's the analogue of PshIsoᴰ for paths
    → PathP (λ i → Presheafᴰ (α i) Cᴰ ℓQᴰ) (reind (pathToPshIso α .trans) Qᴰ) Qᴰ
  -- If we have prove pathToPshIso is an Iso then we could apply reindPshIsoPshIsoᴰ here
  reindPathToPshIsoPathP =
    J (motive _) λ Qᴰ →
      subst (λ α → reind (α .trans) Qᴰ ≡ Qᴰ)
        (sym pathToPshIsoRefl)
        (sym $ reind-id _)

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
  reindⱽFuncRepr .fst .N-homᴰ = refl
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
  reindUEⱽ ueⱽ .elementⱽ = Pⱽ.reind (sym $ F .F-id) (elementⱽ ueⱽ)
  reindUEⱽ ueⱽ .universalⱽ .fst = universalⱽ ueⱽ .fst
  reindUEⱽ ueⱽ .universalⱽ .snd .fst pᴰ = (Pⱽ.rectify $ Pⱽ.≡out $
    (sym (Pⱽ.reind-filler _ _) ∙ sym (Pⱽ.reind-filler _ _)
      ∙ Pⱽ.⟨⟩⋆⟨ sym $ Pⱽ.reind-filler _ _ ⟩ ∙ Pⱽ.reind-filler _ _))
    ∙ βⱽ ueⱽ
  reindUEⱽ ueⱽ .universalⱽ .snd .snd fᴰ =
    cong (introᴰ ueⱽ) (Pⱽ.rectify $ Pⱽ.≡out $ sym (Pⱽ.reind-filler _ _) ∙ sym (Pⱽ.reind-filler _ _) ∙ Pⱽ.⟨⟩⋆⟨ sym $ Pⱽ.reind-filler _ _ ⟩ ∙ Pⱽ.reind-filler _ _)
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
      ⋆PshIsoⱽ reindPshIsoⱽ (invPshIsoⱽ reindFuncReind)


-- Lift
module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
  LiftHomⱽ : ∀ {ℓ'} → PshHomⱽ Pᴰ (LiftPshᴰ Pᴰ ℓ')
  LiftHomⱽ .N-obᴰ = λ z → lift z
  LiftHomⱽ .N-homᴰ = refl

  LiftIsoⱽ : ∀ {ℓ'} → PshIsoⱽ Pᴰ (LiftPshᴰ Pᴰ ℓ')
  LiftIsoⱽ .fst = LiftHomⱽ
  LiftIsoⱽ .snd .inv = λ a z → z .lower
  LiftIsoⱽ .snd .rightInv b q = refl
  LiftIsoⱽ .snd .leftInv a p = refl

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Q : Presheaf C ℓP} {Qᴰ : Presheafᴰ Q Cᴰ ℓPᴰ}
  {α : P ≡ Q}
  where
  Lift-Path :
    ∀ (αᴰ : PathP (λ i → Presheafᴰ (α i) Cᴰ ℓPᴰ) Pᴰ Qᴰ)
    → PathP (λ i → Presheafᴰ (α i) Cᴰ (ℓ-max ℓPᴰ ℓ'))
        (LiftPshᴰ Pᴰ ℓ')
        (LiftPshᴰ Qᴰ ℓ')
  Lift-Path αᴰ i = LiftPshᴰ (αᴰ i) _
module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Q : Presheaf C ℓQ} {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
  -- TODO: naming...
  Lift-F-Homᴰ : ∀ {α : PshHom P Q} (αᴰ : PshHomᴰ α Pᴰ Qᴰ) → PshHomᴰ α (LiftPshᴰ Pᴰ ℓ) (LiftPshᴰ Qᴰ ℓ')
  Lift-F-Homᴰ αᴰ .N-obᴰ pᴰ = lift (αᴰ .N-obᴰ (pᴰ .lower))
  Lift-F-Homᴰ αᴰ .N-homᴰ {fᴰ = fᴰ}{pᴰ = pᴰ} i =
    lift (αᴰ .N-homᴰ {fᴰ = fᴰ}{pᴰ = pᴰ .lower} i)

  Lift-F-Isoᴰ : ∀ {α : PshIso P Q} (αᴰ : PshIsoᴰ α Pᴰ Qᴰ) → PshIsoᴰ α (LiftPshᴰ Pᴰ ℓ) (LiftPshᴰ Qᴰ ℓ')
  Lift-F-Isoᴰ αᴰ .fst = Lift-F-Homᴰ (αᴰ .fst)
  Lift-F-Isoᴰ αᴰ .snd .inv _ qᴰ = lift (αᴰ .snd .inv _ (qᴰ .lower))
  Lift-F-Isoᴰ αᴰ .snd .rightInv p pᴰ i =
    lift (αᴰ .snd .rightInv p (pᴰ .lower) i)
  Lift-F-Isoᴰ αᴰ .snd .leftInv q qᴰ i =
    lift (αᴰ .snd .leftInv q (qᴰ .lower) i)

module _{C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α : PshHom P Q} {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where
  reindLiftEq : PresheafᴰEq (reind α (LiftPshᴰ Qᴰ ℓ')) (LiftPshᴰ (reind α Qᴰ) ℓ')
  reindLiftEq = Eq.refl , Eq.refl

  reindLift : reind α (LiftPshᴰ Qᴰ ℓ') ≡ LiftPshᴰ (reind α Qᴰ) ℓ'
  reindLift = Functorᴰ≡ (λ xᴰ → refl) (λ _ → refl)

  reindLiftIsoⱽ : PshIsoⱽ (reind α (LiftPshᴰ Qᴰ ℓ')) (LiftPshᴰ (reind α Qᴰ) ℓ')
  reindLiftIsoⱽ = eqToPshIsoⱽ reindLiftEq

-- Unit

module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α : PshHom P Q}
  where
  reindUnitEq : PresheafᴰEq (reind α (UnitPshᴰ {Cᴰ = Cᴰ})) UnitPshᴰ
  reindUnitEq = Eq.refl , Eq.refl

  reindUnit : reind α (UnitPshᴰ {Cᴰ = Cᴰ}) ≡ UnitPshᴰ
  reindUnit =
    Functorᴰ≡ (λ _ → funExt λ _ → Σ≡Prop (λ _ → isPropIsSet) refl)
    λ fᴰ → refl

  reindUnitIsoⱽ : PshIsoⱽ (reind α (UnitPshᴰ {Cᴰ = Cᴰ})) UnitPshᴰ
  reindUnitIsoⱽ = eqToPshIsoⱽ reindUnitEq

module _ {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  {Q : Presheaf D ℓQ}
  where
  -- for some reason this can't be inlined. Is this an Agda bug?
  reindFuncUnitEq : PresheafᴰEq (reindFunc F (UnitPshᴰ {Cᴰ = Dᴰ}{P = Q})) UnitPshᴰ
  reindFuncUnitEq = (Eq.refl , Eq.refl)

  reindFuncUnitIsoⱽ : PshIsoⱽ (reindFunc F (UnitPshᴰ {Cᴰ = Dᴰ}{P = Q})) UnitPshᴰ
  reindFuncUnitIsoⱽ = eqToPshIsoⱽ reindFuncUnitEq

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α : PshIso P Q}
  where
  UnitPshᴰ≅UnitPshᴰ : PshIsoᴰ {Cᴰ = Cᴰ} α (UnitPshᴰ {P = P}) (UnitPshᴰ {P = Q})
  UnitPshᴰ≅UnitPshᴰ =
    invPshIsoⱽ reindUnitIsoⱽ
    ⋆PshIsoⱽᴰ reindPshIsoPshIsoᴰ α (UnitPshᴰ {P = Q})
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓP}
  {α : P ≡ Q}
  where
  UnitPshᴰ≡UnitPshᴰ :
    PathP
      (λ i → Presheafᴰ (α i) Cᴰ ℓ-zero)
      (UnitPshᴰ {P = P})
      (UnitPshᴰ {P = Q})
  UnitPshᴰ≡UnitPshᴰ = sym reindUnit ◁ reindPathToPshIsoPathP α UnitPshᴰ

-- Product
module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
  where
  module _ {P : Presheaf C ℓP}{Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ P Cᴰ ℓRᴰ}
    where
    ×ⱽ-introⱽ :
      PshHomⱽ Pᴰ Qᴰ
      → PshHomⱽ Pᴰ Rᴰ
      → PshHomⱽ Pᴰ (Qᴰ ×ⱽPsh Rᴰ)
    ×ⱽ-introⱽ αⱽ βⱽ .N-obᴰ = λ z → αⱽ .N-obᴰ z , βⱽ .N-obᴰ z
    ×ⱽ-introⱽ αⱽ βⱽ .N-homᴰ = ΣPathP ((αⱽ .N-homᴰ) , (βⱽ .N-homᴰ))

  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
    {α : PshHom P Q}
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ Q Cᴰ ℓRᴰ}
    where
    ×ⱽ-introᴰ :
      PshHomᴰ α Pᴰ Qᴰ
      → PshHomᴰ α Pᴰ Rᴰ
      → PshHomᴰ α Pᴰ (Qᴰ ×ⱽPsh Rᴰ)
    ×ⱽ-introᴰ αᴰ βᴰ .N-obᴰ = λ z → αᴰ .N-obᴰ z , βᴰ .N-obᴰ z
    ×ⱽ-introᴰ αᴰ βᴰ .N-homᴰ = ΣPathP ((αᴰ .N-homᴰ) , (βᴰ .N-homᴰ))

  module _ {P : Presheaf C ℓP}{Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}
    where
    ×ⱽ-π₁ : PshHomⱽ (Pᴰ ×ⱽPsh Qᴰ) Pᴰ
    ×ⱽ-π₁ .N-obᴰ = fst
    ×ⱽ-π₁ .N-homᴰ = refl

    ×ⱽ-π₂ : PshHomⱽ (Pᴰ ×ⱽPsh Qᴰ) Qᴰ
    ×ⱽ-π₂ .N-obᴰ = snd
    ×ⱽ-π₂ .N-homᴰ = refl

  -- This is like PshProdⱽ .F-hom but for homomorphisms/isomorphisms
  -- between presheaves of different levels
  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
    {Pᴰ' : Presheafᴰ P Cᴰ ℓPᴰ'}
    {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
    {Qᴰ' : Presheafᴰ Q Cᴰ ℓQᴰ'}
    where
    module _ {α : PshHom P Q} where
      _×ⱽHom_ : (αᴰ : PshHomᴰ α Pᴰ Qᴰ) (βᴰ : PshHomᴰ α Pᴰ' Qᴰ')
        → PshHomᴰ α (Pᴰ ×ⱽPsh Pᴰ') (Qᴰ ×ⱽPsh Qᴰ')
      (αᴰ ×ⱽHom βᴰ) = ×ⱽ-introᴰ (×ⱽ-π₁ ⋆PshHomⱽᴰ αᴰ) (×ⱽ-π₂ ⋆PshHomⱽᴰ βᴰ)

    module _ {α : PshIso P Q} where
      _×ⱽIso_ : (αᴰ : PshIsoᴰ α Pᴰ Qᴰ) (βᴰ : PshIsoᴰ α Pᴰ' Qᴰ')
        → PshIsoᴰ α (Pᴰ ×ⱽPsh Pᴰ') (Qᴰ ×ⱽPsh Qᴰ')
      (αᴰ ×ⱽIso βᴰ) .fst = (αᴰ .fst) ×ⱽHom (βᴰ .fst)
      (αᴰ ×ⱽIso βᴰ) .snd .inv _ = invers .N-obᴰ where
        invers : PshHomᴰ (invPshIso α .trans) (Qᴰ ×ⱽPsh Qᴰ') (Pᴰ ×ⱽPsh Pᴰ')
        invers = ×ⱽ-introᴰ (×ⱽ-π₁ ⋆PshHomⱽᴰ (invPshIsoᴰ αᴰ .fst)) (×ⱽ-π₂ ⋆PshHomⱽᴰ (invPshIsoᴰ βᴰ .fst))
      (αᴰ ×ⱽIso βᴰ) .snd .rightInv _ _ = ΣPathP ((αᴰ .snd .rightInv _ _) , (βᴰ .snd .rightInv _ _))
      (αᴰ ×ⱽIso βᴰ) .snd .leftInv _ _ = ΣPathP ((αᴰ .snd .leftInv _ _) , (βᴰ .snd .leftInv _ _))

module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)(Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
  PshProdⱽ≡ᴰ :
    Pᴰ ×ᴰPsh Qᴰ ≡ reind (π₁ P Q) Pᴰ ×ⱽPsh reind (π₂ P Q) Qᴰ
  PshProdⱽ≡ᴰ = Functorᴰ≡
    (λ Aᴰ → funExt λ (p , q) → ΣPathPProp (λ _ → isPropIsSet) refl)
    λ fᴰ → funExt λ (p , q) → funExt λ (pᴰ , qᴰ) → ΣPathP $
      (Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.reind-filler _ _)
      , (Qᴰ.rectify $ Qᴰ.≡out $ Qᴰ.reind-filler _ _)

  -- This one is only Eq.refl on objects, would need a corresponding eqToPshIsoⱽ' like reindF''
  PshProdⱽ≅ᴰ :
    PshIsoⱽ (Pᴰ ×ᴰPsh Qᴰ) (reind (π₁ P Q) Pᴰ ×ⱽPsh reind (π₂ P Q) Qᴰ)
  PshProdⱽ≅ᴰ .fst .N-obᴰ x = x
  PshProdⱽ≅ᴰ .fst .N-homᴰ =
    ΣPathP ( (Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.reind-filler _ _)
           , (Qᴰ.rectify $ Qᴰ.≡out $ Qᴰ.reind-filler _ _))
  PshProdⱽ≅ᴰ .snd .inv _ x = x
  PshProdⱽ≅ᴰ .snd .rightInv _ _ = refl
  PshProdⱽ≅ᴰ .snd .leftInv _ _ = refl

module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {Pᴰ : Presheafᴰ Q Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  {α : PshHom P Q}
  where
  reind×ⱽIsoⱽ : PshIsoⱽ (reind α (Pᴰ ×ⱽPsh Qᴰ)) (reind α Pᴰ ×ⱽPsh reind α Qᴰ)
  reind×ⱽIsoⱽ .fst = ×ⱽ-introⱽ (reind-introⱽ (reind-π ⋆PshHomᴰⱽ ×ⱽ-π₁)) (reind-introⱽ (reind-π ⋆PshHomᴰⱽ ×ⱽ-π₂))
  reind×ⱽIsoⱽ .snd .inv p = invers .N-obᴰ
    where
      invers : PshHomⱽ (reind α Pᴰ ×ⱽPsh reind α Qᴰ) (reind α (Pᴰ ×ⱽPsh Qᴰ))
      invers = reind-introⱽ (×ⱽ-introᴰ (×ⱽ-π₁ ⋆PshHomⱽᴰ reind-π) (×ⱽ-π₂ ⋆PshHomⱽᴰ reind-π))
  reind×ⱽIsoⱽ .snd .rightInv _ _ = refl
  reind×ⱽIsoⱽ .snd .leftInv _ _ = refl

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {P : Presheaf D ℓP}
  {Pᴰ : Presheafᴰ P Dᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Dᴰ ℓQᴰ}
  {F : Functor C D}
  where
  reindFunc×ⱽIsoⱽ :
    PshIsoⱽ (reindFunc F (Pᴰ ×ⱽPsh Qᴰ))
            (reindFunc F Pᴰ ×ⱽPsh reindFunc F Qᴰ)
  reindFunc×ⱽIsoⱽ = eqToPshIsoⱽ the-eq where
    the-eq : PresheafᴰEq (reindFunc F (Pᴰ ×ⱽPsh Qᴰ)) (reindFunc F Pᴰ ×ⱽPsh reindFunc F Qᴰ)
    the-eq = (Eq.refl , Eq.refl)

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {x}
  {F : Functor C D}
  {Pᴰ : Presheafⱽ (F ⟅ x ⟆) Dᴰ ℓPᴰ}{Qᴰ : Presheafⱽ (F ⟅ x ⟆) Dᴰ ℓQᴰ}
  where
  reindⱽFunc×ⱽIsoⱽ :
    PshIsoⱽ (reindⱽFunc F (Pᴰ ×ⱽPsh Qᴰ))
            (reindⱽFunc F Pᴰ ×ⱽPsh reindⱽFunc F Qᴰ)
  reindⱽFunc×ⱽIsoⱽ =
    reindPshIsoⱽ reindFunc×ⱽIsoⱽ
    ⋆PshIsoⱽ reind×ⱽIsoⱽ
