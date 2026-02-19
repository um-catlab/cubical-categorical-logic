{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Redundant.PresheafStrictHom.Exponentials where
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
--   (push to pushPsh)
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Redundant.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Redundant.PresheafStrictHom.Base
open import Cubical.Categories.Presheaf.StrictHom

open Category
open Categoryᴰ
open Functor
open Iso
open NatIso
open NatTrans
open PshHomStrict
open PshIsoStrict

private
  variable
    ℓ ℓ' ℓs ℓr ℓc ℓc' ℓp ℓq ℓP ℓQ ℓR ℓS ℓS' ℓS'' : Level
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓPᴰ ℓQᴰ ℓRᴰ : Level

-- Helper: precomposing with a PshIsoStrict gives an Iso on hom sets
-- For iso P ≅ Q, we get Iso (Hom Q R) (Hom P R) by precomposition
module _ {C : Category ℓC ℓC'}
  {P : Presheaf C ℓP} {Q : Presheaf C ℓQ} {R : Presheaf C ℓR}
  (isoᴾᴼ : PshIsoStrict P Q)
  where
  private
    -- f : P → Q, g : Q → P, with f ∘ g = id_Q (sec) and g ∘ f = id_P (ret)
    f = isoᴾᴼ .trans
    g = invPshIsoStrict isoᴾᴼ .trans
    sec' : ∀ c q → f .N-ob c (g .N-ob c q) ≡ q
    sec' c = isoᴾᴼ .nIso c .snd .fst
    ret' : ∀ c p → g .N-ob c (f .N-ob c p) ≡ p
    ret' c = isoᴾᴼ .nIso c .snd .snd

  precompPshIsoStrict : Iso (PshHomStrict Q R) (PshHomStrict P R)
  precompPshIsoStrict .fun β = f ⋆PshHomStrict β
  precompPshIsoStrict .inv γ = g ⋆PshHomStrict γ
  -- sec: fun (inv γ) = f ⋆ (g ⋆ γ), at p: γ(g(f(p))) = γ(ret'(p)) ≡ γ(p)
  precompPshIsoStrict .sec γ = makePshHomStrictPath
    (funExt₂ λ c p → cong (γ .N-ob c) (ret' c p))
  -- ret: inv (fun β) = g ⋆ (f ⋆ β), at q: β(f(g(q))) = β(sec'(q)) ≡ β(q)
  precompPshIsoStrict .ret β = makePshHomStrictPath
    (funExt₂ λ c q → cong (β .N-ob c) (sec' c q))

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
  (α : PshHomStrict P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) (Rᴰ : Presheafᴰ Q Cᴰ ℓRᴰ)
  where
  private
    F : Functor (Cᴰ / P) (Cᴰ / Q)
    F = Idᴰ /FⱽStrict α

  *Strict-⇒ⱽ-commute :
    Iso (PshHomStrict Pᴰ ((α *Strict Qᴰ) ⇒PshLargeStrict (α *Strict Rᴰ)))
        (PshHomStrict Pᴰ (α *Strict (Qᴰ ⇒PshLargeStrict Rᴰ)))
  *Strict-⇒ⱽ-commute =
    PshHomStrict Pᴰ ((α *Strict Qᴰ) ⇒PshLargeStrict (α *Strict Rᴰ))
     Iso⟨ ⇒PshLargeStrict-UMP (α *Strict Qᴰ) (α *Strict Rᴰ) ⟩
    PshHomStrict (Pᴰ ×Psh (α *Strict Qᴰ)) (α *Strict Rᴰ)
     Iso⟨ invIso $ push-UMP α (Pᴰ ×Psh (α *Strict Qᴰ)) Rᴰ ⟩
    PshHomStrict (PushPsh α (Pᴰ ×Psh (α *Strict Qᴰ))) Rᴰ
     Iso⟨ invIso $ precompPshIsoStrict (FrobeniusReciprocityStrict α Pᴰ Qᴰ) ⟩
    PshHomStrict ((PushPsh α Pᴰ) ×Psh Qᴰ) Rᴰ
     Iso⟨ invIso $ ⇒PshLargeStrict-UMP Qᴰ Rᴰ ⟩
    PshHomStrict (PushPsh α Pᴰ) (Qᴰ ⇒PshLargeStrict Rᴰ)
     Iso⟨ push-UMP α Pᴰ (Qᴰ ⇒PshLargeStrict Rᴰ) ⟩
    PshHomStrict Pᴰ (α *Strict (Qᴰ ⇒PshLargeStrict Rᴰ))
    ∎Iso

module _
  (C : Category ℓC ℓC')
  (ℓP : Level)
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (ℓPᴰ : Level)
  where
  private
     the-ℓ = ℓC ⊔ℓ ℓC' ⊔ℓ ℓP
     the-ℓᴰ = the-ℓ ⊔ℓ ℓCᴰ ⊔ℓ ℓCᴰ' ⊔ℓ ℓPᴰ
     PSHᴰ = PRESHEAFᴰ C the-ℓ Cᴰ the-ℓᴰ
     module PSHᴰ = Fibers PSHᴰ
  module _ {P : Presheaf C the-ℓ} (Pᴰ : Presheafᴰ P Cᴰ the-ℓᴰ) where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ

    PSHᴰLRⱽ : LRⱽ PSHᴰ (λ {w} {x} {y} {z} f g h → Eq.refl) Pᴰ
    PSHᴰLRⱽ {Γ = Q} Qᴰ α = UEⱽ→Reprⱽ _ (λ {x} {y} f → Eq.refl) lrⱽue
      where
        module Qᴰ = PresheafᴰNotation Qᴰ

        lrⱽue : UEⱽ
                 ((PSHᴰ [-][-, Qᴰ ]) ×ⱽPsh
                  reindᴰRedundPshHom
                  (yoRecHom PSHᴰ (λ {w} {x} {y} {z} f g h → Eq.refl) α)
                  (PSHᴰ [-][-, Pᴰ ]))
                 (λ {x} {y} f → Eq.refl)
        lrⱽue .UEⱽ.v = Qᴰ ×ⱽPsh (α *Strict Pᴰ)
        lrⱽue .UEⱽ.e .fst = π₁ _ _ ⋆PshHomStrict *StrictIdIntro Qᴰ
        lrⱽue .UEⱽ.e .snd = π₂ _ _
        lrⱽue .UEⱽ.universal .isPshIso'.nIso c .fst (αᴰ , βᴰ) =
          ×PshIntroStrict αᴰ βᴰ
          ⋆PshHomStrict ×PshIntroStrict (π₁ _ _) (π₂ _ _ ⋆PshHomStrict *StrictSeqIntro⁻)
          ⋆PshHomStrict ×ⱽ*Strict→*Strict×ⱽ (c .snd .snd) Qᴰ (α *Strict Pᴰ)
        lrⱽue .UEⱽ.universal .isPshIso'.nIso c .snd .fst _ =
          ΣPathP (makePshHomStrictPath refl , makePshHomStrictPath refl)
        lrⱽue .UEⱽ.universal .isPshIso'.nIso c .snd .snd _ =
          makePshHomStrictPath refl

    PSHᴰExpsⱽ : Exponentialsⱽ PSHᴰ
      (λ {w} {x} {y} {z} f g h → Eq.refl) (λ {x} {y} f → Eq.refl) Pᴰ PSHᴰLRⱽ
    PSHᴰExpsⱽ Qᴰ .fst = Pᴰ ⇒PshLargeStrict Qᴰ
    PSHᴰExpsⱽ Qᴰ .snd .PshIso'.isos (R , Rᴰ , α) =
      PshHomStrict Rᴰ (α *Strict (Pᴰ ⇒PshLargeStrict Qᴰ))
        Iso⟨ invIso (push-UMP α Rᴰ (Pᴰ ⇒PshLargeStrict Qᴰ)) ⟩
      PshHomStrict (PushPsh α Rᴰ) (Pᴰ ⇒PshLargeStrict Qᴰ)
        Iso⟨ ⇒PshLargeStrict-UMP Pᴰ Qᴰ ⟩
      PshHomStrict ((PushPsh α Rᴰ) ×Psh Pᴰ) Qᴰ
        Iso⟨ precompPshIsoStrict (FrobeniusReciprocityStrict α Rᴰ Pᴰ) ⟩
      PshHomStrict (PushPsh α (Rᴰ ×Psh (α *Strict Pᴰ))) Qᴰ
        Iso⟨ push-UMP α (Rᴰ ×Psh (α *Strict Pᴰ)) Qᴰ ⟩
      PshHomStrict (Rᴰ ×Psh (α *Strict Pᴰ)) (α *Strict Qᴰ)
      ∎Iso
    PSHᴰExpsⱽ Qᴰ .snd .PshIso'.nat (S , Sᴰ , β) (R , Rᴰ , α) =
      Hom/-elim (λ γ γᴰ → elimPropEq (PRESHEAF C _ .isSetHom)
        (λ _ → isPropΠ λ _ → isPropPathEq (isSetPshHomStrict _ _))
        λ {Eq.refl p → inl (makePshHomStrictPath
          (funExt₂ λ _ _ → Qᴰ.rectifyOut $ refl))})
          where module Qᴰ = PresheafᴰNotation Qᴰ
