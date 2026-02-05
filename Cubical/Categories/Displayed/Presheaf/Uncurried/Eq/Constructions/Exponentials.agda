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
  module _
    {P : Presheaf C ℓP}
    {Q : Presheaf C ℓQ}
    (α : PshHomStrict P Q)
    (Pᴰ : Presheafᴰ Q Cᴰ ℓPᴰ)
    (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
    where

    private
      module C = Category C
      module P = PresheafNotation P
      module Q = PresheafNotation Q
      module Pᴰ = PresheafᴰNotation Pᴰ
      module Qᴰ = PresheafᴰNotation Qᴰ
      module Cᴰ = Fibers Cᴰ
      F : Functor ((Cᴰ / P) ^op) ((Cᴰ / Q) ^op)
      F = (Idᴰ /FⱽStrict α) ^opF

    *↑-⇒-commute' : PshIsoEq (α *↑ (Pᴰ ⇒PshLargeEq Qᴰ)) ((α *↑ Pᴰ) ⇒PshLargeEq (α *↑ Qᴰ))
    *↑-⇒-commute' .PshIsoEq.isos x@(c , cᴰ , p) .Iso.fun f .N-ob d (γ@(h , hᴰ , e) , pᴰ) =
      f .N-ob (F ⟅ d ⟆) (F ⟪ γ ⟫ , pᴰ)
    *↑-⇒-commute' .PshIsoEq.isos x@(c , cᴰ , p) .Iso.fun f
      .PshHomEq.N-hom _ _ (δ , δᴰ , Eq.refl)
        ((_ , _ , Eq.refl) , pᴰ') (γ , pᴰ) Eq.refl =
      f .N-hom _ _ (F-hom F (δ , δᴰ , Eq.refl)) _ _
        (Eq.pathToEq (ΣPathP ((ΣPathP (refl ,
          (ΣPathP (refl , isProp→PathP (λ _ → Eq.isSet→isSetEq Q.isSetPsh) _ _)))) , refl)))
    *↑-⇒-commute' .PshIsoEq.isos x@(c , cᴰ , p) .Iso.inv g .N-ob
      (d , dᴰ , q') (γ'@(h , hᴰ , e') , pᴰ') =
      Qᴰ.reindEq (Eq.sym (Eq.pathToEq (α .PshHomStrict.N-hom d c h p (h P.⋆ p) refl)) Eq.∙ e')
        (g .N-ob (d , dᴰ , h P.⋆ p) ((h , hᴰ , Eq.refl) ,
          Pᴰ.reindEq (Eq.sym e' Eq.∙ Eq.pathToEq (α .PshHomStrict.N-hom d c h p (h P.⋆ p) refl)) pᴰ'))
    *↑-⇒-commute' .PshIsoEq.isos x@(c , cᴰ , p) .Iso.inv g .PshHomEq.N-hom d' (d , dᴰ , q') (δ , δᴰ , Eq.refl) (γ''@(h' , h'ᴰ , Eq.refl) , pᴰ'') (γ'@(h , hᴰ , e') , pᴰ') Eq.refl =
      Eq.pathToEq $ Qᴰ.rectifyOut $
        ?
    *↑-⇒-commute' .PshIsoEq.isos x@(c , cᴰ , p) .Iso.sec g =
      {!!}
    *↑-⇒-commute' .PshIsoEq.isos x@(c , cᴰ , p) .Iso.ret f =
      {!!}
    *↑-⇒-commute' .PshIsoEq.nat _ _ (_ , _ , Eq.refl) f' f Eq.refl =
      {!!}

    -- *↑-×-commute' : PshIsoEq (α *↑ (Pᴰ ×ⱽPsh Qᴰ)) ((α *↑ Pᴰ) ×ⱽPsh (α *↑ Qᴰ))
    -- *↑-×-commute' .PshIsoEq.isos (c , cᴰ , p) = idIso
    -- *↑-×-commute' .PshIsoEq.nat = λ c c' f p' p z → z

-- -- -- -- -- -- -- --   *Strict⇒ⱽ→⇒ⱽ*Strict :
-- -- -- -- -- -- -- --     PshHomStrict
-- -- -- -- -- -- -- --       (α *Strict (Qᴰ ⇒PshLargeStrict Rᴰ))
-- -- -- -- -- -- -- --       ((α *Strict Qᴰ) ⇒PshLargeStrict (α *Strict Rᴰ))
-- -- -- -- -- -- -- --   *Strict⇒ⱽ→⇒ⱽ*Strict .N-ob c f .N-ob c' (γ , qᴰ) =
-- -- -- -- -- -- -- --     f .N-ob (F ⟅ c' ⟆) (F ⟪ γ ⟫ , qᴰ)
-- -- -- -- -- -- -- --   *Strict⇒ⱽ→⇒ⱽ*Strict .N-ob c f .N-hom c'' c' e (γ' , qᴰ') (γ , qᴰ) eq =
-- -- -- -- -- -- -- --     f .N-hom (F ⟅ c'' ⟆) (F ⟅ c' ⟆) (F ⟪ e ⟫) (F ⟪ γ' ⟫ , qᴰ') (F ⟪ γ ⟫ , qᴰ)
-- -- -- -- -- -- -- --       (ΣPathP (sym (F .F-seq e γ') ∙ cong (F .F-hom) (cong fst eq) , cong snd eq))
-- -- -- -- -- -- -- --   *Strict⇒ⱽ→⇒ⱽ*Strict .N-hom c c' h f' f eq =
-- -- -- -- -- -- -- --     makePshHomStrictPath (funExt₂ λ d (γ , qᴰ) →
-- -- -- -- -- -- -- --       cong (λ δ → f' .N-ob (F ⟅ d ⟆) (δ , qᴰ)) (F .F-seq γ h)
-- -- -- -- -- -- -- --       ∙ funExt⁻ (funExt⁻ (cong N-ob eq) (F ⟅ d ⟆)) (F ⟪ γ ⟫ , qᴰ))

-- -- -- -- -- -- -- --   private
-- -- -- -- -- -- -- --     module P = PresheafNotation P
-- -- -- -- -- -- -- --     module Q = PresheafNotation Q
-- -- -- -- -- -- -- --     module Qᴰ = PresheafᴰNotation Qᴰ
-- -- -- -- -- -- -- --     module Rᴰ = PresheafᴰNotation Rᴰ

-- -- -- -- -- -- -- --   ⇒ⱽ*Strict→*Strict⇒ⱽ :
-- -- -- -- -- -- -- --     PshHomStrict
-- -- -- -- -- -- -- --       ((α *Strict Qᴰ) ⇒PshLargeStrict (α *Strict Rᴰ))
-- -- -- -- -- -- -- --       (α *Strict (Qᴰ ⇒PshLargeStrict Rᴰ))
-- -- -- -- -- -- -- --   ⇒ⱽ*Strict→*Strict⇒ⱽ =
-- -- -- -- -- -- -- --     push-UMP α ((α *Strict Qᴰ) ⇒PshLargeStrict (α *Strict Rᴰ)) (Qᴰ ⇒PshLargeStrict Rᴰ) .Iso.fun
-- -- -- -- -- -- -- --       (λPshHomStrict Qᴰ Rᴰ
-- -- -- -- -- -- -- --         (invPshIsoStrict
-- -- -- -- -- -- -- --           (FrobeniusReciprocityStrict α
-- -- -- -- -- -- -- --            ((α *Strict Qᴰ) ⇒PshLargeStrict (α *Strict Rᴰ)) Qᴰ)
-- -- -- -- -- -- -- --              .PshIsoStrict.trans
-- -- -- -- -- -- -- --           ⋆PshHomStrict push-UMP α (((α *Strict Qᴰ) ⇒PshLargeStrict (α *Strict Rᴰ)) ×Psh
-- -- -- -- -- -- -- --                                      (α *Strict Qᴰ)) Rᴰ .inv
-- -- -- -- -- -- -- --                         (appPshHomStrict (α *Strict Qᴰ) (α *Strict Rᴰ))))

-- -- -- -- -- -- -- -- module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
-- -- -- -- -- -- -- --   {P : Presheaf C ℓP}
-- -- -- -- -- -- -- --   {Q : Presheaf C ℓQ}
-- -- -- -- -- -- -- --   {R : Presheaf C ℓR}
-- -- -- -- -- -- -- --   {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
-- -- -- -- -- -- -- --   {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
-- -- -- -- -- -- -- --   {Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ}
-- -- -- -- -- -- -- --   {α : PshHomStrict P Q}
-- -- -- -- -- -- -- --   {β : PshHomStrict Q R}
-- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- --   private
-- -- -- -- -- -- -- --     module Pᴰ = PresheafᴰNotation Pᴰ
-- -- -- -- -- -- -- --     module Qᴰ = PresheafᴰNotation Qᴰ
-- -- -- -- -- -- -- --     module Rᴰ = PresheafᴰNotation Rᴰ

-- -- -- -- -- -- -- --   _⋆PshHomᴰStrict_ :
-- -- -- -- -- -- -- --     (αᴰ : PshHomᴰStrict α Pᴰ Qᴰ)
-- -- -- -- -- -- -- --     (βᴰ : PshHomᴰStrict β Qᴰ Rᴰ) →
-- -- -- -- -- -- -- --     PshHomᴰStrict (α ⋆PshHomStrict β) Pᴰ Rᴰ
-- -- -- -- -- -- -- --   αᴰ ⋆PshHomᴰStrict βᴰ =
-- -- -- -- -- -- -- --     αᴰ
-- -- -- -- -- -- -- --     ⋆PshHomStrict (α *StrictF βᴰ)
-- -- -- -- -- -- -- --     ⋆PshHomStrict *StrictSeqIntro

-- -- -- -- -- -- -- --   infixr 9 _⋆PshHomᴰStrict_

-- -- -- -- -- -- -- -- module _
-- -- -- -- -- -- -- --   (C : Category ℓC ℓC')
-- -- -- -- -- -- -- --   (ℓP : Level)
-- -- -- -- -- -- -- --   (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
-- -- -- -- -- -- -- --   (ℓPᴰ : Level)
-- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- --   private
-- -- -- -- -- -- -- --     PSH = PRESHEAF C ℓP
-- -- -- -- -- -- -- --     module PSH = Category PSH
-- -- -- -- -- -- -- --     module Cᴰ = Fibers Cᴰ
-- -- -- -- -- -- -- --   PRESHEAFᴰ : Categoryᴰ (PRESHEAF C ℓP) _ _
-- -- -- -- -- -- -- --   PRESHEAFᴰ .ob[_] P = Presheafᴰ P Cᴰ ℓPᴰ
-- -- -- -- -- -- -- --   PRESHEAFᴰ .Hom[_][_,_] = PshHomᴰStrict
-- -- -- -- -- -- -- --   PRESHEAFᴰ .idᴰ = idPshHomᴰStrict
-- -- -- -- -- -- -- --   PRESHEAFᴰ ._⋆ᴰ_ = _⋆PshHomᴰStrict_
-- -- -- -- -- -- -- --   PRESHEAFᴰ .⋆IdLᴰ _ = makePshHomStrictPath refl
-- -- -- -- -- -- -- --   PRESHEAFᴰ .⋆IdRᴰ _ = makePshHomStrictPath refl
-- -- -- -- -- -- -- --   PRESHEAFᴰ .⋆Assocᴰ _ _ _ = makePshHomStrictPath refl
-- -- -- -- -- -- -- --   PRESHEAFᴰ .isSetHomᴰ = isSetPshHomStrict _ _
-- -- -- -- -- -- -- --   private
-- -- -- -- -- -- -- --     module PSHᴰ = Fibers PRESHEAFᴰ

-- -- -- -- -- -- -- --   PSHᴰTerminalsⱽ : Terminalsⱽ PRESHEAFᴰ
-- -- -- -- -- -- -- --   PSHᴰTerminalsⱽ P .fst = Unit*Psh
-- -- -- -- -- -- -- --   PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .fun αᴰ = tt
-- -- -- -- -- -- -- --   PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .inv _ .N-ob = λ c _ → tt*
-- -- -- -- -- -- -- --   PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .inv _ .N-hom = λ _ _ _ _ _ _ → refl
-- -- -- -- -- -- -- --   PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .sec _ = refl
-- -- -- -- -- -- -- --   PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .ret _ = makePshHomStrictPath refl
-- -- -- -- -- -- -- --   PSHᴰTerminalsⱽ P .snd .PshIso'.nat _ _ _ _ = inr Eq.refl

-- -- -- -- -- -- -- --   -- Slow, broke
-- -- -- -- -- -- -- --   -- Something about using the record constructor inline vs hiding behind coprojections?
-- -- -- -- -- -- -- --   -- Or is it about more annotations?
-- -- -- -- -- -- -- --   -- PSHᴰFibration : Fibration PRESHEAFᴰ λ f g h → Eq.refl
-- -- -- -- -- -- -- --   -- PSHᴰFibration α Pᴰ = UEⱽ→Reprⱽ _ (λ {x = x₁} {y = y₁} f → Eq.refl)
-- -- -- -- -- -- -- --   --   (record {
-- -- -- -- -- -- -- --   --     v = α *Strict Pᴰ
-- -- -- -- -- -- -- --   --   ; e = idPshHomStrict
-- -- -- -- -- -- -- --   --   ; universal = {!!} })

-- -- -- -- -- -- -- --   -- Fast, woke
-- -- -- -- -- -- -- --   PSHᴰFibrationUE : FibrationUE PRESHEAFᴰ (λ f g h → Eq.refl) λ {x} {y} f → Eq.refl
-- -- -- -- -- -- -- --   PSHᴰFibrationUE α Pᴰ .UEⱽ.v = α *Strict Pᴰ
-- -- -- -- -- -- -- --   PSHᴰFibrationUE α Pᴰ .UEⱽ.e = idPshHomStrict
-- -- -- -- -- -- -- --   PSHᴰFibrationUE α Pᴰ .UEⱽ.universal .isPshIso'.nIso _ .fst βᴰ =
-- -- -- -- -- -- -- --     βᴰ ⋆PshHomStrict *StrictSeqIntro⁻
-- -- -- -- -- -- -- --   PSHᴰFibrationUE α Pᴰ .UEⱽ.universal .isPshIso'.nIso _ .snd .fst _ =
-- -- -- -- -- -- -- --     makePshHomStrictPath refl
-- -- -- -- -- -- -- --   PSHᴰFibrationUE α Pᴰ .UEⱽ.universal .isPshIso'.nIso _ .snd .snd _ =
-- -- -- -- -- -- -- --     makePshHomStrictPath refl

-- -- -- -- -- -- -- --   PSHᴰFibration : Fibration PRESHEAFᴰ (λ f g h → Eq.refl)
-- -- -- -- -- -- -- --   PSHᴰFibration α Pᴰ = UEⱽ→Reprⱽ _ (λ {x = x₁} {y = y₁} f → Eq.refl) (PSHᴰFibrationUE α Pᴰ)

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
