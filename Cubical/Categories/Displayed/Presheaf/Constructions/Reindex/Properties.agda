{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions.Reindex.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Equiv.Dependent

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
    (∫PshHom αβᴰ .N-hom _ _ _ _) ∙ Rᴰ.reind-filler _ _

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
    ∫PshHom αβᴰ .N-hom _ _ _ _ ∙ Rᴰ.reind-filler _ _

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
  reind-id : Pᴰ ≡ reind (idPshHom {P = P}) Pᴰ
  reind-id = Functorᴰ≡ (λ _ → refl)
    (λ _ → funExt λ _ → funExt λ _ → Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.reind-filler _ _)

  reind-idIsoⱽ : PshIsoⱽ Pᴰ (reind (idPshHom {P = P}) Pᴰ)
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
            ; N-homᴰ = Qᴰ.rectify $ Qᴰ.≡out $ sym $ Qᴰ.reind-filler _ _
            })
    (λ a → record { equiv-proof = strictContrFibers _ })

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α : PshIso P Q}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  (αᴰ : PshIsoᴰ α Pᴰ Qᴰ)
  where

  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ

  PshIsoᴰ→PshIsoⱽ : PshIsoⱽ Pᴰ (reind (α .trans) Qᴰ)
  PshIsoᴰ→PshIsoⱽ = invPshIsoⱽ (
    (PshHomPathPshHomᴰ (makePshHomPath {C = C} (λ i c x → α .nIso c .snd .snd x i)) $
      reind-π ⋆PshHomᴰ invPshIsoᴰ αᴰ .fst) ,
    isisoover
      (λ a pᴰ → αᴰ .fst .N-obᴰ pᴰ)
      (λ b q →
        Pᴰ.rectify $ Pᴰ.≡out $
          (sym $ Pᴰ.reind-filler _ _)
          ∙ Pᴰ.≡in (αᴰ .snd .isIsoOver.leftInv _ q)
      )
      (λ a p →
        Qᴰ.rectify $ Qᴰ.≡out $
          Qᴰ.≡in (congP (λ i → αᴰ .fst .N-obᴰ) (Pᴰ.≡out $ sym $ Pᴰ.reind-filler _ _))
          ∙ (Qᴰ.≡in (αᴰ .snd .isIsoOver.rightInv _ _))
      ))

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
