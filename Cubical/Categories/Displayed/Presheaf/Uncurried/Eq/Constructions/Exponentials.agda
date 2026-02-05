{-

  Uncurried Presheaves using EqElement
-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS -W noUnsupportedIndexedMatch #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Constructions.Exponentials where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Equiv.Dependent.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.HLevels.More
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.More
open import Cubical.Categories.HLevels
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Props
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions hiding (π₁Strict ; π₂Strict)
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.StrictHom renaming (π₁ to π₁Strict ; π₂ to π₂Strict)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.Terminal as Unitᴰ
import Cubical.Categories.Displayed.Instances.Sets.Base as Setᴰ
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf
open import Cubical.Categories.Displayed.Constructions.Reindex.Eq
import Cubical.Categories.Displayed.Presheaf.Base as Curried

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Constructions.Eq
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Constructions.Push
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Constructions.BinProduct

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓE ℓE' ℓEᴰ ℓEᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Category
open Categoryᴰ
open Functor
open Functorᴰ
open isIsoOver
open NatTrans
open NatTransᴰ
open NatIso
open NatIsoᴰ
open PshHomEq
open PshIso

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  module _ {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
    (α : PshHomStrict P Q) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) (Rᴰ : Presheafᴰ Q Cᴰ ℓRᴰ)
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
    where
    *↑-⇒-commute :
      Iso (PshHomEq Pᴰ (α *↑ (Qᴰ ⇒PshLargeEq Rᴰ)))
          (PshHomEq Pᴰ ((α *↑ Qᴰ) ⇒PshLargeEq (α *↑ Rᴰ)))
    *↑-⇒-commute =
      PshHomEq Pᴰ (α *↑ (Qᴰ ⇒PshLargeEq Rᴰ))
        Iso⟨ invIso $ *↓-UMP α ⟩
      PshHomEq (α *↓ Pᴰ) (Qᴰ ⇒PshLargeEq Rᴰ)
        Iso⟨ ⇒PshLargeEq-UMP Qᴰ Rᴰ ⟩
      PshHomEq ((α *↓ Pᴰ) ×ⱽPsh Qᴰ) Rᴰ
        Iso⟨ precompPshIsoEq (FrobeniusReciprocity α Pᴰ Qᴰ) ⟩
      PshHomEq (α *↓ (Pᴰ ×ⱽPsh (α *↑ Qᴰ))) Rᴰ
        Iso⟨ *↓-UMP α ⟩
      PshHomEq (Pᴰ ×ⱽPsh (α *↑ Qᴰ)) (α *↑ Rᴰ)
        Iso⟨ invIso (⇒PshLargeEq-UMP (α *↑ Qᴰ) (α *↑ Rᴰ)) ⟩
      PshHomEq Pᴰ ((α *↑ Qᴰ) ⇒PshLargeEq (α *↑ Rᴰ))
      ∎Iso


-- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- --   (C : Category ℓC ℓC')
-- -- -- -- -- -- -- --   (ℓP : Level)
-- -- -- -- -- -- -- --   (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
-- -- -- -- -- -- -- --   (ℓPᴰ : Level)
-- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- --   private
-- -- -- -- -- -- -- --      the-ℓ = ℓC ⊔ℓ ℓC' ⊔ℓ ℓP
-- -- -- -- -- -- -- --      the-ℓᴰ = the-ℓ ⊔ℓ ℓCᴰ ⊔ℓ ℓCᴰ' ⊔ℓ ℓPᴰ
-- -- -- -- -- -- -- --      PSHᴰ = PRESHEAFᴰ C the-ℓ Cᴰ the-ℓᴰ
-- -- -- -- -- -- -- --      module PSHᴰ = Fibers PSHᴰ
-- -- -- -- -- -- -- --   module _ {P : Presheaf C the-ℓ} (Pᴰ : Presheafᴰ P Cᴰ the-ℓᴰ) where
-- -- -- -- -- -- -- --     private
-- -- -- -- -- -- -- --       module Pᴰ = PresheafᴰNotation Pᴰ

-- -- -- -- -- -- -- --     PSHᴰLRⱽ : LRⱽ PSHᴰ (λ {w} {x} {y} {z} f g h → Eq.refl) Pᴰ
-- -- -- -- -- -- -- --     PSHᴰLRⱽ {Γ = Q} Qᴰ α = UEⱽ→Reprⱽ _ (λ {x} {y} f → Eq.refl) lrⱽue
-- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- --         module Qᴰ = PresheafᴰNotation Qᴰ

-- -- -- -- -- -- -- --         lrⱽue : UEⱽ
-- -- -- -- -- -- -- --                  ((PSHᴰ [-][-, Qᴰ ]) ×ⱽPsh
-- -- -- -- -- -- -- --                   reindᴰRedundPshHom
-- -- -- -- -- -- -- --                   (yoRecHom PSHᴰ (λ {w} {x} {y} {z} f g h → Eq.refl) α)
-- -- -- -- -- -- -- --                   (PSHᴰ [-][-, Pᴰ ]))
-- -- -- -- -- -- -- --                  (λ {x} {y} f → Eq.refl)
-- -- -- -- -- -- -- --         lrⱽue .UEⱽ.v = Qᴰ ×ⱽPsh (α *Strict Pᴰ)
-- -- -- -- -- -- -- --         lrⱽue .UEⱽ.e .fst = π₁ _ _ ⋆PshHomStrict *StrictIdIntro Qᴰ
-- -- -- -- -- -- -- --         lrⱽue .UEⱽ.e .snd = π₂ _ _
-- -- -- -- -- -- -- --         lrⱽue .UEⱽ.universal .isPshIso'.nIso c .fst (αᴰ , βᴰ) =
-- -- -- -- -- -- -- --           ×PshIntroStrict αᴰ βᴰ
-- -- -- -- -- -- -- --           ⋆PshHomStrict ×PshIntroStrict (π₁ _ _) (π₂ _ _ ⋆PshHomStrict *StrictSeqIntro⁻)
-- -- -- -- -- -- -- --           ⋆PshHomStrict ×ⱽ*Strict→*Strict×ⱽ (c .snd .snd) Qᴰ (α *Strict Pᴰ)
-- -- -- -- -- -- -- --         lrⱽue .UEⱽ.universal .isPshIso'.nIso c .snd .fst _ =
-- -- -- -- -- -- -- --           ΣPathP (makePshHomStrictPath refl , makePshHomStrictPath refl)
-- -- -- -- -- -- -- --         lrⱽue .UEⱽ.universal .isPshIso'.nIso c .snd .snd _ =
-- -- -- -- -- -- -- --           makePshHomStrictPath refl

-- -- -- -- -- -- -- --     -- PSHᴰExpsⱽ : Exponentialsⱽ PSHᴰ
-- -- -- -- -- -- -- --     --   (λ {w} {x} {y} {z} f g h → Eq.refl) (λ {x} {y} f → Eq.refl) Pᴰ PSHᴰLRⱽ
-- -- -- -- -- -- -- --     -- PSHᴰExpsⱽ Qᴰ =
-- -- -- -- -- -- -- --     --   ?
-- -- -- -- -- -- -- --       -- UEⱽ→Reprⱽ _ (λ {x} {y} f → Eq.refl) (expUE Qᴰ)
-- -- -- -- -- -- -- --       -- where
-- -- -- -- -- -- -- --       -- expUE : ExponentialsⱽUE PSHᴰ
-- -- -- -- -- -- -- --       --   (λ {w} {x} {y} {z} f g h → Eq.refl) (λ {x} {y} f → Eq.refl)
-- -- -- -- -- -- -- --       --   Pᴰ PSHᴰLRⱽ (λ {x} {y} f → Eq.refl)
-- -- -- -- -- -- -- --       -- expUE Qᴰ .UEⱽ.v = Pᴰ ⇒PshLargeStrict Qᴰ
-- -- -- -- -- -- -- --       -- -- Pᴰ⇒Qᴰ × Id*Pᴰ → Id*Qᴰ
-- -- -- -- -- -- -- --       -- expUE Qᴰ .UEⱽ.e =
-- -- -- -- -- -- -- --       --   {!!}
-- -- -- -- -- -- -- --       --   -- ×PshIntroStrict (π₁ _ _) (π₂ _ _ ⋆PshHomStrict *StrictIdIntro⁻ Pᴰ)
-- -- -- -- -- -- -- --       --   -- ⋆PshHomStrict appPshHomStrict Pᴰ Qᴰ
-- -- -- -- -- -- -- --       --   -- ⋆PshHomStrict *StrictIdIntro Qᴰ
-- -- -- -- -- -- -- --       -- expUE Qᴰ .UEⱽ.universal .isPshIso'.nIso (R , Rᴰ , α) .fst αᴰ =
-- -- -- -- -- -- -- --       --   {!!}
-- -- -- -- -- -- -- --       --   -- λPshHomStrict (α *Strict Pᴰ) (α *Strict Qᴰ) αᴰ
-- -- -- -- -- -- -- --       --   -- ⋆PshHomStrict ⇒ⱽ*Strict→*Strict⇒ⱽ α Pᴰ Qᴰ
-- -- -- -- -- -- -- --       -- expUE Qᴰ .UEⱽ.universal .isPshIso'.nIso (R , Rᴰ , α) .snd .fst αᴰ =
-- -- -- -- -- -- -- --       --   {!!}
-- -- -- -- -- -- -- --       --   -- makePshHomStrictPath (funExt₂ λ u v →
-- -- -- -- -- -- -- --       --   --   Qᴰ.rectifyOut $ {!!} ∙ {!!})
-- -- -- -- -- -- -- --       --   -- where module Qᴰ = PresheafᴰNotation Qᴰ
-- -- -- -- -- -- -- --       -- expUE Qᴰ .UEⱽ.universal .isPshIso'.nIso (R , Rᴰ , α) .snd .snd αᴰ =
-- -- -- -- -- -- -- --       --   {!!}
-- -- -- -- -- -- -- --       --   -- makePshHomStrictPath {!!}
-- -- -- -- -- -- -- --       --   -- where module Qᴰ = PresheafᴰNotation Qᴰ
