{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Redundant.Curried where
-- TODO still need better name

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport hiding (pathToIso)
open import Cubical.Functions.FunExtEquiv

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq

open import Cubical.HITs.PathEq
open import Cubical.HITs.Join

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Constructions.Lift
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory.Base
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.HLevels
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Props
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Exponentials
open import Cubical.Categories.NaturalTransformation hiding (_∘ˡ_; _∘ˡⁱ_)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt using
  (isPshIso' ; PshIso' ; PshHom ; _⋆NatTransPshHom_ ; _⋆PshHom_)
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Properties renaming (PshIso to PshIsoLift)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.Exponential
open import Cubical.Categories.Presheaf.Constructions.BinProduct hiding (π₁ ; π₂)
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Yoneda

open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Isomorphism.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions renaming
--   (push to pushPsh)
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
-- open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf

-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Redundant.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom

open Category
open Categoryᴰ
open Functor
open Iso
open NatIso
open NatTrans
open PshHomStrict

private
  variable
    ℓ ℓ' ℓs ℓr ℓc ℓc' ℓp ℓq ℓP ℓQ ℓR ℓS ℓS' ℓS'' : Level
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓPᴰ ℓQᴰ ℓRᴰ : Level

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshHomStrict P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where

  private
    module Cᴰ = Categoryᴰ Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ

  record PshHomᴰ : Type (ℓ-max ℓQᴰ $ ℓ-max ℓPᴰ $ ℓ-max ℓP $ ℓ-max ℓCᴰ' $ ℓ-max ℓCᴰ $ ℓ-max ℓC' $ ℓ-max ℓC $ ℓ-max ℓQᴰ $ ℓ-max ℓPᴰ $ ℓ-max ℓP $ ℓ-max ℓCᴰ $ ℓC) where
    field
      N-obᴰ  : ∀ {x}{xᴰ : Cᴰ.ob[ x ]}{p : P.p[ x ]} → Pᴰ.p[ p ][ xᴰ ] → Qᴰ.p[ α .N-ob x p ][ xᴰ ]
      -- Do I want this to be forded?
      N-homᴰ :
        ∀ {x y}(xᴰ : Cᴰ.ob[ x ])(yᴰ : Cᴰ.ob[ y ])
        → {f : C [ x , y ]}{p' : P.p[ y ]}{p : P.p[ x ]}
        → {fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]}
        → (pᴰ : Pᴰ.p[ p' ][ yᴰ ])
        → (pᴰ' : Pᴰ.p[ p ][ xᴰ ])
        → (e : (f P.⋆ p') ≡ p)
        → fᴰ Pᴰ.⋆ᴰ pᴰ Pᴰ.≡[ e ] pᴰ'
        → (fᴰ Qᴰ.⋆ᴰ N-obᴰ pᴰ) Qᴰ.≡[ α .N-hom x y f p' p e ] N-obᴰ pᴰ'

    ∫PshHomStrict : PshHomStrict (∫P Pᴰ) (∫P Qᴰ)
    ∫PshHomStrict .PshHomStrict.N-ob (x , xᴰ) (p , pᴰ) = (α .N-ob _ p) , (N-obᴰ pᴰ)
    ∫PshHomStrict .PshHomStrict.N-hom _ _ (f , fᴰ) (p , pᴰ) (p' , pᴰ') e =
        ΣPathP ((α .N-hom _ _ _ _ _ (cong fst e)) ,
          (Qᴰ.rectifyOut $
            Qᴰ.≡in (N-homᴰ _ _ _ _ refl refl)
            ∙ Qᴰ.≡in λ i → N-obᴰ (e i .snd)))

-- --     private
-- --       module ∫Pᴰ = PresheafNotation (∫P Pᴰ)
-- --       module ∫Qᴰ = PresheafNotation (∫P Qᴰ)

-- --     N-obᴰ⟨_⟩ :
-- --       ∀ {xxᴰ}{ppᴰ ppᴰ'}
-- --       → Path ∫Pᴰ.p[ xxᴰ ] ppᴰ ppᴰ'
-- --       → Path ∫Qᴰ.p[ xxᴰ ] (_ , N-obᴰ (ppᴰ .snd)) (_ , N-obᴰ (ppᴰ' .snd))
-- --     N-obᴰ⟨_⟩ = cong (∫PshHom .N-ob _)

-- --     open PshHom ∫PshHom public

-- --   isPshIsoᴰ : PshHomᴰ → isPshIso {P = P}{Q = Q} α → Type _
-- --   isPshIsoᴰ αᴰ αIsIso = ∀ {x}{xᴰ : Cᴰ.ob[ x ]}
-- --       → isIsoOver (isIsoToIso (αIsIso x)) Pᴰ.p[_][ xᴰ ] Qᴰ.p[_][ xᴰ ]
-- --           (λ _ → αᴰ .PshHomᴰ.N-obᴰ)

-- --   isPshEquivOver : PshHomᴰ → Type _
-- --   isPshEquivOver αᴰ = ∀ {x}{xᴰ : Cᴰ.ob[ x ]}
-- --     → isEquivOver {P = Pᴰ.p[_][ xᴰ ]}{Q = Qᴰ.p[_][ xᴰ ]}{f = α .N-ob x}
-- --         λ _ → αᴰ .PshHomᴰ.N-obᴰ

-- --   PshHomᴰΣ : Type _
-- --   PshHomᴰΣ =
-- --     Σ[ N-obᴰ ∈
-- --          (∀ {x}{xᴰ : Cᴰ.ob[ x ]}{p : P.p[ x ]} → Pᴰ.p[ p ][ xᴰ ] → Qᴰ.p[ α .N-ob x p ][ xᴰ ]) ]
-- --     (∀ {x y}{xᴰ : Cᴰ.ob[ x ]}{yᴰ : Cᴰ.ob[ y ]}
-- --         → {f : C [ x , y ]}{p : P.p[ y ]}
-- --         → {fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]}{pᴰ : Pᴰ.p[ p ][ yᴰ ]}
-- --         → N-obᴰ (fᴰ Pᴰ.⋆ᴰ pᴰ)
-- --             Qᴰ.≡[ α .N-hom x y f p ]
-- --           (fᴰ Qᴰ.⋆ᴰ N-obᴰ pᴰ))

-- --   isPropN-homᴰ :
-- --     ∀ (N-obᴰ : ∀ {x}{xᴰ : Cᴰ.ob[ x ]}
-- --          {p : P.p[ x ]} → Pᴰ.p[ p ][ xᴰ ] → Qᴰ.p[ α .N-ob x p ][ xᴰ ]) →
-- --     isProp (∀ {x y}{xᴰ : Cᴰ.ob[ x ]}{yᴰ : Cᴰ.ob[ y ]}
-- --         → {f : C [ x , y ]}{p : P.p[ y ]}
-- --         → {fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]}{pᴰ : Pᴰ.p[ p ][ yᴰ ]}
-- --         → N-obᴰ (fᴰ Pᴰ.⋆ᴰ pᴰ)
-- --             Qᴰ.≡[ α .N-hom x y f p ]
-- --           (fᴰ Qᴰ.⋆ᴰ N-obᴰ pᴰ))
-- --   isPropN-homᴰ =
-- --     λ _ → isPropImplicitΠ4 λ _ _ _ _ → isPropImplicitΠ4 λ _ _ _ _ →
-- --       λ _ _ → isSet→SquareP (λ i j → F-obᴰ Qᴰ _ (α .N-hom _ _ _ _ j) .snd) _ _ _ _

-- --   isSetPshHomᴰΣ : isSet PshHomᴰΣ
-- --   isSetPshHomᴰΣ =
-- --     isSetΣ
-- --       (isSetImplicitΠ3 (λ c cᴰ p → isSetΠ (λ pᴰ → Qᴰ.isSetPshᴰ)))
-- --       λ _ → isProp→isSet (isPropN-homᴰ _)

-- --   PshHomᴰΣIso : Iso PshHomᴰ PshHomᴰΣ
-- --   unquoteDef PshHomᴰΣIso = defineRecordIsoΣ PshHomᴰΣIso (quote (PshHomᴰ))

-- --   isSetPshHomᴰ : isSet PshHomᴰ
-- --   isSetPshHomᴰ = isOfHLevelRetractFromIso 2 PshHomᴰΣIso isSetPshHomᴰΣ


open PshHomᴰ

module _
  (C : Category ℓC ℓC')
  (ℓP : Level)
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (ℓPᴰ : Level)
  where
  private
    PSH = PRESHEAF C ℓP
    module PSH = Category PSH
    module Cᴰ = Fibers Cᴰ
  PRESHEAFᴰ' : Categoryᴰ (PRESHEAF C ℓP) _ _
  PRESHEAFᴰ' .ob[_] P = Presheafᴰ P Cᴰ ℓPᴰ
  PRESHEAFᴰ' .Hom[_][_,_] = PshHomᴰ
  PRESHEAFᴰ' .idᴰ .PshHomᴰ.N-obᴰ = λ z → z
  PRESHEAFᴰ' .idᴰ .PshHomᴰ.N-homᴰ _ _ _ _ _ z = z
  PRESHEAFᴰ' ._⋆ᴰ_ αᴰ βᴰ .PshHomᴰ.N-obᴰ = λ z₁ → βᴰ .PshHomᴰ.N-obᴰ (αᴰ .PshHomᴰ.N-obᴰ z₁)
  PRESHEAFᴰ' ._⋆ᴰ_ {f = γ} {zᴰ = Pᴰ} αᴰ βᴰ .PshHomᴰ.N-homᴰ _ _ _ _ _ e =
    βᴰ .N-homᴰ _ _ (αᴰ .N-obᴰ _) (αᴰ .N-obᴰ _) (γ .N-hom _ _ _ _ _ _)
     (αᴰ .N-homᴰ _ _ _ _ _ e)
  PRESHEAFᴰ' .⋆IdLᴰ _ = refl
  PRESHEAFᴰ' .⋆IdRᴰ _ = refl
  PRESHEAFᴰ' .⋆Assocᴰ _ _ _ = refl
  PRESHEAFᴰ' .isSetHomᴰ = {!!}

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} {R : Presheaf C ℓR}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ)
  (α : PshHomStrict R P)
  where

-- -- --   PRESHEAFᴰ .ob[_] P = Presheafᴰ P Cᴰ ℓPᴰ
-- -- --   PRESHEAFᴰ .Hom[_][_,_] = PshHomᴰStrict
-- -- --   PRESHEAFᴰ .idᴰ = idPshHomᴰStrict
-- -- --   PRESHEAFᴰ ._⋆ᴰ_ = _⋆PshHomᴰStrict_
-- -- --   PRESHEAFᴰ .⋆IdLᴰ _ = makePshHomStrictPath refl
-- -- --   PRESHEAFᴰ .⋆IdRᴰ _ = makePshHomStrictPath refl
-- -- --   PRESHEAFᴰ .⋆Assocᴰ _ _ _ = makePshHomStrictPath refl
-- -- --   PRESHEAFᴰ .isSetHomᴰ = isSetPshHomStrict _ _
-- -- --   private
-- -- --     module PSHᴰ = Fibers PRESHEAFᴰ

-- -- --   PSHᴰTerminalsⱽ : Terminalsⱽ PRESHEAFᴰ
-- -- --   PSHᴰTerminalsⱽ P .fst = Unit*Psh
-- -- --   PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .fun αᴰ = tt
-- -- --   PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .inv _ .N-ob = λ c _ → tt*
-- -- --   PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .inv _ .N-hom = λ _ _ _ _ _ _ → refl
-- -- --   PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .sec _ = refl
-- -- --   PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .ret _ = makePshHomStrictPath refl
-- -- --   PSHᴰTerminalsⱽ P .snd .PshIso'.nat _ _ _ _ = inr Eq.refl

-- -- --   PSHᴰBPⱽ : BinProductsⱽ PRESHEAFᴰ
-- -- --   PSHᴰBPⱽ Pᴰ Qᴰ =
-- -- --     UEⱽ→Reprⱽ _ (λ {x = x₁} {y} f → Eq.refl) (record {
-- -- --         v = Pᴰ ×ⱽPsh Qᴰ
-- -- --       ; e = π₁ _ _ ⋆PshHomStrict *StrictIdIntro Pᴰ ,
-- -- --             π₂ _ _ ⋆PshHomStrict *StrictIdIntro Qᴰ
-- -- --       ; universal = record {
-- -- --         nIso = λ c →
-- -- --           (λ (αᴰ , βᴰ) → ×PshIntroStrict αᴰ βᴰ ⋆PshHomStrict ×ⱽ*Strict→*Strict×ⱽ (c .snd .snd) Pᴰ Qᴰ) ,
-- -- --           (λ _ → ΣPathP (makePshHomStrictPath refl , makePshHomStrictPath refl)) ,
-- -- --           λ _ → makePshHomStrictPath refl
-- -- --           } })

-- -- --   -- Slow, broke
-- -- --   -- Something about using the record constructor inline vs hiding behind coprojections?
-- -- --   -- Or is it about more annotations?
-- -- --   -- PSHᴰFibration : Fibration PRESHEAFᴰ λ f g h → Eq.refl
-- -- --   -- PSHᴰFibration α Pᴰ = UEⱽ→Reprⱽ _ (λ {x = x₁} {y = y₁} f → Eq.refl)
-- -- --   --   (record {
-- -- --   --     v = α *Strict Pᴰ
-- -- --   --   ; e = idPshHomStrict
-- -- --   --   ; universal = {!!} })

-- -- --   -- Fast, woke
-- -- --   PSHᴰFibrationUE : FibrationUE PRESHEAFᴰ (λ f g h → Eq.refl) λ {x} {y} f → Eq.refl
-- -- --   PSHᴰFibrationUE α Pᴰ .UEⱽ.v = α *Strict Pᴰ
-- -- --   PSHᴰFibrationUE α Pᴰ .UEⱽ.e = idPshHomStrict
-- -- --   PSHᴰFibrationUE α Pᴰ .UEⱽ.universal .isPshIso'.nIso _ .fst βᴰ =
-- -- --     βᴰ ⋆PshHomStrict *StrictSeqIntro⁻
-- -- --   PSHᴰFibrationUE α Pᴰ .UEⱽ.universal .isPshIso'.nIso _ .snd .fst _ =
-- -- --     makePshHomStrictPath refl
-- -- --   PSHᴰFibrationUE α Pᴰ .UEⱽ.universal .isPshIso'.nIso _ .snd .snd _ =
-- -- --     makePshHomStrictPath refl

-- -- --   PSHᴰFibration : Fibration PRESHEAFᴰ (λ f g h → Eq.refl)
-- -- --   PSHᴰFibration α Pᴰ = UEⱽ→Reprⱽ _ (λ {x = x₁} {y = y₁} f → Eq.refl) (PSHᴰFibrationUE α Pᴰ)

-- -- -- module _
-- -- --   (C : Category ℓC ℓC')
-- -- --   (ℓP : Level)
-- -- --   (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
-- -- --   (ℓPᴰ : Level)
-- -- --   where
-- -- --   private
-- -- --      the-ℓ = ℓC ⊔ℓ ℓC' ⊔ℓ ℓP
-- -- --      the-ℓᴰ = the-ℓ ⊔ℓ ℓCᴰ ⊔ℓ ℓCᴰ' ⊔ℓ ℓPᴰ
-- -- --      PSHᴰ = PRESHEAFᴰ C the-ℓ Cᴰ the-ℓᴰ
-- -- --      module PSHᴰ = Fibers PSHᴰ
-- -- --   module _ {P : Presheaf C the-ℓ} (Pᴰ : Presheafᴰ P Cᴰ the-ℓᴰ) where
-- -- --     private
-- -- --       module Pᴰ = PresheafᴰNotation Pᴰ

-- -- --     PSHᴰLRⱽ : LRⱽ PSHᴰ (λ {w} {x} {y} {z} f g h → Eq.refl) Pᴰ
-- -- --     PSHᴰLRⱽ {Γ = Q} Qᴰ α = UEⱽ→Reprⱽ _ (λ {x} {y} f → Eq.refl) lrⱽue
-- -- --       where
-- -- --         module Qᴰ = PresheafᴰNotation Qᴰ

-- -- --         lrⱽue : UEⱽ
-- -- --                  ((PSHᴰ [-][-, Qᴰ ]) ×ⱽPsh
-- -- --                   reindᴰRedundPshHom
-- -- --                   (yoRecHom PSHᴰ (λ {w} {x} {y} {z} f g h → Eq.refl) α)
-- -- --                   (PSHᴰ [-][-, Pᴰ ]))
-- -- --                  (λ {x} {y} f → Eq.refl)
-- -- --         lrⱽue .UEⱽ.v = Qᴰ ×ⱽPsh (α *Strict Pᴰ)
-- -- --         lrⱽue .UEⱽ.e .fst = π₁ _ _ ⋆PshHomStrict *StrictIdIntro Qᴰ
-- -- --         lrⱽue .UEⱽ.e .snd = π₂ _ _
-- -- --         lrⱽue .UEⱽ.universal .isPshIso'.nIso c .fst (αᴰ , βᴰ) =
-- -- --           ×PshIntroStrict αᴰ βᴰ
-- -- --           ⋆PshHomStrict ×PshIntroStrict (π₁ _ _) (π₂ _ _ ⋆PshHomStrict *StrictSeqIntro⁻)
-- -- --           ⋆PshHomStrict ×ⱽ*Strict→*Strict×ⱽ (c .snd .snd) Qᴰ (α *Strict Pᴰ)
-- -- --         lrⱽue .UEⱽ.universal .isPshIso'.nIso c .snd .fst _ =
-- -- --           ΣPathP (makePshHomStrictPath refl , makePshHomStrictPath refl)
-- -- --         lrⱽue .UEⱽ.universal .isPshIso'.nIso c .snd .snd _ =
-- -- --           makePshHomStrictPath refl

-- -- --     PSHᴰExpsⱽ : Exponentialsⱽ PSHᴰ
-- -- --       (λ {w} {x} {y} {z} f g h → Eq.refl) (λ {x} {y} f → Eq.refl) Pᴰ PSHᴰLRⱽ
-- -- --     PSHᴰExpsⱽ Qᴰ = {!!}
-- -- --       -- UEⱽ→Reprⱽ _ (λ {x} {y} f → Eq.refl) (expUE Qᴰ)
-- -- --       -- where
-- -- --       -- expUE : ExponentialsⱽUE PSHᴰ
-- -- --       --   (λ {w} {x} {y} {z} f g h → Eq.refl) (λ {x} {y} f → Eq.refl)
-- -- --       --   Pᴰ PSHᴰLRⱽ (λ {x} {y} f → Eq.refl)
-- -- --       -- expUE Qᴰ .UEⱽ.v = Pᴰ ⇒PshLargeStrict Qᴰ
-- -- --       -- -- Pᴰ⇒Qᴰ × Id*Pᴰ → Id*Qᴰ
-- -- --       -- expUE Qᴰ .UEⱽ.e =
-- -- --       --   ×PshIntroStrict (π₁ _ _) (π₂ _ _ ⋆PshHomStrict *StrictIdIntro⁻ Pᴰ)
-- -- --       --   ⋆PshHomStrict appPshHomStrict Pᴰ Qᴰ
-- -- --       --   ⋆PshHomStrict *StrictIdIntro Qᴰ
-- -- --       -- expUE Qᴰ .UEⱽ.universal .isPshIso'.nIso (R , Rᴰ , α) .fst αᴰ =
-- -- --       --   λPshHomStrict (α *Strict Pᴰ) (α *Strict Qᴰ) αᴰ
-- -- --       --   ⋆PshHomStrict ⇒ⱽ*Strict→*Strict⇒ⱽ α Pᴰ Qᴰ
-- -- --       -- expUE Qᴰ .UEⱽ.universal .isPshIso'.nIso (R , Rᴰ , α) .snd .fst αᴰ =
-- -- --       --   makePshHomStrictPath (funExt₂ λ u v →
-- -- --       --     Qᴰ.rectifyOut $ {!!} ∙ {!!})
-- -- --       --   where module Qᴰ = PresheafᴰNotation Qᴰ
-- -- --       -- expUE Qᴰ .UEⱽ.universal .isPshIso'.nIso (R , Rᴰ , α) .snd .snd αᴰ =
-- -- --       --   makePshHomStrictPath {!!}
-- -- --       --   where module Qᴰ = PresheafᴰNotation Qᴰ
