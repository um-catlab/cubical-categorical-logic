{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Presheaves.CartesianClosed where
-- TODO still need better name

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport hiding (pathToIso)
open import Cubical.Functions.FunExtEquiv

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
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation hiding (_∘ˡ_; _∘ˡⁱ_)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Properties renaming (PshIso to PshIsoLift)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.BinProduct as BP hiding (π₁ ; π₂)
open import Cubical.Categories.Presheaf.Constructions.Exponential
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Yoneda

open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Isomorphism.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
import Cubical.Categories.Displayed.Limits.CartesianV' as Path
import Cubical.Categories.Displayed.Limits.CartesianClosedV as Path
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Presheaves.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Presheaves.Cartesian
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianClosedV
open import Cubical.Categories.Presheaf.StrictHom

open Category
open Functor
open Iso
open NatIso
open NatTrans
open Categoryᴰ
open PshHomStrict
open PshHom
open PshIso

private
  variable
    ℓ ℓ' ℓP ℓQ ℓR ℓS ℓS' ℓS'' : Level
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓPᴰ ℓQᴰ ℓRᴰ : Level

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  ℓPSHᴰ = ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ')
  PSHᴰExponentials : Exponentialsⱽ (PRESHEAFᴰ Cᴰ ℓPSHᴰ ℓPSHᴰ) PSHAssoc PSHIdL (BPⱽ+Fibration→AllLRⱽ (PRESHEAFᴰ Cᴰ ℓPSHᴰ ℓPSHᴰ) PSHAssoc PSHᴰBPⱽ PSHᴰFibration)
  PSHᴰExponentials {x = P} Pᴰ Qᴰ .fst = Pᴰ ⇒PshLarge Qᴰ
  PSHᴰExponentials {x = P} Pᴰ Qᴰ .snd .PshIsoEq.isos R3@(R , Rᴰ , α) =
    PshHom Rᴰ (α *Strict (Pᴰ ⇒PshLarge Qᴰ))
      Iso⟨ Push⊣* (PshHomStrict→Eq α) Rᴰ (Pᴰ ⇒PshLarge Qᴰ) ⟩
    PshHom (α PushStrict Rᴰ) (Pᴰ ⇒PshLarge Qᴰ)
      Iso⟨ ⇒PshLarge-UMP Pᴰ Qᴰ ⟩
    PshHom (((α PushStrict Rᴰ)) ×Psh Pᴰ) Qᴰ
      Iso⟨ precomp⋆PshHom-Iso (FrobeniusReciprocity (PshHomStrict→Eq α) Rᴰ Pᴰ) ⟩
    PshHom (α PushStrict (Rᴰ ×Psh (α *Strict Pᴰ))) Qᴰ
      Iso⟨ invIso (Push⊣* (PshHomStrict→Eq α) (Rᴰ ×Psh (α *Strict Pᴰ)) Qᴰ) ⟩
    PshHom (Rᴰ ×Psh (α *Strict Pᴰ)) (α *Strict Qᴰ)
      ∎Iso
  PSHᴰExponentials {x = P} Pᴰ Qᴰ .snd .PshIsoEq.nat
    S3@(S , Sᴰ , .(α ⋆PshHomStrict β)) R3@(R , Rᴰ , β) α3@(α , αᴰ , Eq.refl) p ._ Eq.refl =
    Eq.pathToEq (makePshHomPath refl) -- this refl could use an annotation

  module _ {P : Presheaf C ℓPSHᴰ}{Q : Presheaf C ℓPSHᴰ} where
    private
      module P = PresheafNotation P
    -- This is less universe polymorphic than it could be because of the use of
    -- PRESHEAF (Cᴰ / (P ×Psh Q)) _ [-, Pᴰ ]
    ∀Pshᴰ : (Pᴰ : Presheafᴰ (P ×Psh Q) Cᴰ ℓPSHᴰ) → Presheafᴰ P Cᴰ ℓPSHᴰ
    ∀Pshᴰ Pᴰ =
      reindPsh (reindPshFStrict (Idᴰ /Fⱽ π₁Eq P Q) ∘F YOStrict) ((PRESHEAF (Cᴰ / (P ×Psh Q)) _ [-, Pᴰ ]))

    private
      module _ (Pᴰ : Presheafᴰ (P ×Psh Q) Cᴰ ℓPSHᴰ) (Γ3@(Γ , Γᴰ , p) : (Cᴰ / P) .ob) where
        module ∀Pᴰ = PresheafᴰNotation (∀Pshᴰ Pᴰ)
        ∀PshᴰOb : ∀Pᴰ.p[ p ][ Γᴰ ] ≡ PshHomStrict (reindPsh ((Idᴰ /Fⱽ π₁Eq P Q)) ((Cᴰ / P) [-, Γ3 ])) Pᴰ
        ∀PshᴰOb = refl

    ∀Pshᴰ-app : (Pᴰ : Presheafᴰ (P ×Psh Q) Cᴰ ℓPSHᴰ) → PshHom (π₁ P Q *Strict (∀Pshᴰ Pᴰ)) Pᴰ
    ∀Pshᴰ-app Pᴰ .N-ob (Γ , Γᴰ , p , q) pᴰ = pᴰ .N-ob (Γ , Γᴰ , p , q) (C.id , Cᴰ.idᴰ , (Eq.pathToEq (P.⋆IdL p)))
    ∀Pshᴰ-app Pᴰ .N-hom c c' (u , v , e) α =
      (sym $ α .N-hom _ _ _ _ _ (ΣPathP (C.⋆IdR u ∙ sym (C.⋆IdL u) ,
            ΣPathPProp (λ _ → Eq.isSet→isSetEq P.isSetPsh)
              (Cᴰ.rectifyOut $ Cᴰ.⋆IdR (u , v) ∙ sym (Cᴰ.⋆IdL (u , v))))))

    module _ {Rᴰ : Presheafᴰ P Cᴰ ℓRᴰ} (Pᴰ : Presheafᴰ (P ×Psh Q) Cᴰ ℓPSHᴰ) where
      private
        module Rᴰ = PresheafᴰNotation Rᴰ
      ∀Pshᴰ-Λ-N-ob : (α : PshHom (π₁ P Q *Strict Rᴰ) Pᴰ)
        → (Γ3@(Γ , Γᴰ , p) : (Cᴰ / P) .ob)
        → (rᴰ : Rᴰ.p[ p ][ Γᴰ ])
        → PshHomStrict (reindPsh ((Idᴰ /Fⱽ π₁Eq P Q)) ((Cᴰ / P) [-, Γ3 ])) Pᴰ
      ∀Pshᴰ-Λ-N-ob α Γ3@(Γ , Γᴰ , p) rᴰ .N-ob (Δ , Δᴰ , p' , q) (γ , γᴰ , p'γ≡p) =
        -- Need a Pᴰ.p[ Δᴰ ][ (p , q) ]
        α .N-ob _ (Rᴰ.reindEq p'γ≡p $ (γᴰ Rᴰ.⋆ᴰ rᴰ))
      ∀Pshᴰ-Λ-N-ob α Γ3 rᴰ .N-hom c c' (_ , _ , Eq.refl)  (_ , _ , Eq.refl)
        (_ , _ , e) p =
        Pᴰ.rectifyOut $
          Pᴰ.≡in (sym $ α .N-hom _ _ _ _)
          ∙ (Pᴰ.≡in $ cong (α .N-ob _)
              (Rᴰ.rectifyOut $ (sym (Rᴰ.⋆ᴰ-reind _)
                ∙ sym (Rᴰ.⋆Assoc _ _ _)
                ∙ Rᴰ.⟨ ΣPathP ((cong fst p) , (λ i → p i .snd .fst)) ⟩⋆⟨⟩) ∙ Rᴰ.reindEq-filler e))
        where module Pᴰ = PresheafᴰNotation Pᴰ

      ∀Pshᴰ-Λ : PshHom (π₁ P Q *Strict Rᴰ) Pᴰ → PshHom Rᴰ (∀Pshᴰ Pᴰ)
      ∀Pshᴰ-Λ α .N-ob (Γ , Γᴰ , p) rᴰ = ∀Pshᴰ-Λ-N-ob α (Γ , Γᴰ , p) rᴰ
      -- .N-ob (Δ , Δᴰ , _ , q) (γ , γᴰ , Eq.refl) = {!!}
      -- ∀Pshᴰ-Λ α .N-ob (Γ , Γᴰ , p) rᴰ .N-hom = {!!}
      ∀Pshᴰ-Λ α .N-hom c c' f rᴰ =
        makePshHomStrictPath (funExt₂ λ _ _ → cong (α .N-ob _)
          (Rᴰ.rectifyOut $ Rᴰ.reindEq-filler⁻ _
            ∙ Rᴰ.⟨⟩⋆⟨ sym $ Rᴰ.⋆ᴰ-reind _ ⟩
            ∙ sym (Rᴰ.⋆Assoc _ _ _)
            ∙ Rᴰ.reindEq-filler _))

      ∀Pshᴰ-UMP : Iso (PshHom Rᴰ (∀Pshᴰ Pᴰ)) (PshHom (π₁ P Q *Strict Rᴰ) Pᴰ)
      ∀Pshᴰ-UMP = {!!}
      -- ∀Pshᴰ-UMP .fun α∀ = (π₁ P Q *StrictF α∀) ⋆PshHom ∀Pshᴰ-app Pᴰ
      -- ∀Pshᴰ-UMP .inv = ∀Pshᴰ-Λ
      -- ∀Pshᴰ-UMP .sec α = {!!}
      --   -- makePshHomPath (funExt₂ λ { (Γ , Γᴰ , p , q) rᴰ →
      --   --   cong (α .N-ob _) (Rᴰ.rectifyOut (Rᴰ.reindEq-filler⁻ _ ∙ Rᴰ.⋆IdLᴰ))
      --   --   })
      -- ∀Pshᴰ-UMP .ret α∀ = {!!}
      --   -- makePshHomPath (funExt₂ λ { (Γ , Γᴰ , p) rᴰ →
      --   -- makePshHomStrictPath (funExt₂ λ { (Δ , Δᴰ , p' , q) (γ , γᴰ , Eq.refl) →
      --   --   {!!}
      --   --   }) })

  -- PSHᴰ∀ : UniversalQuantifiers (PRESHEAFᴰ Cᴰ ℓPSHᴰ ℓPSHᴰ) PSHIdL PSHAssoc PSHᴰFibration
  --   (PSHBP C ℓPSHᴰ)
  --   PSHπ₁NatEq PSH×aF-seq
  -- -- Pᴰ : Pshᴰ (P × Q)
  -- -- -----------------
  -- -- (∀Q Pᴰ) (Γ , Γᴰ , p) = PshHom ? Pᴰ
  -- PSHᴰ∀ Q {P} Pᴰ .fst = ∀Pshᴰ Pᴰ

  -- PSHᴰ∀ Q {P} Pᴰ .snd .PshIsoEq.isos (R , Rᴰ , α) =
  --   PshHom Rᴰ (α *Strict ∀Pshᴰ Pᴰ)
  --     Iso⟨ Push⊣* (PshHomStrict→Eq α) Rᴰ (∀Pshᴰ Pᴰ) ⟩
  --   PshHom (α PushStrict Rᴰ) (∀Pshᴰ Pᴰ)
  --     Iso⟨ ∀Pshᴰ-UMP Pᴰ ⟩
  --   PshHom (π₁ P Q *Strict α PushStrict Rᴰ) Pᴰ
  --     -- Beck Chevalley
  --     Iso⟨ precomp⋆PshHom-Iso (BeckChevalley α Rᴰ) ⟩
  --   PshHom (×PshIntroStrict (π₁ R Q ⋆PshHomStrict α) (π₂ R Q) PushStrict (π₁ R Q) *Strict Rᴰ) Pᴰ
  --     Iso⟨ invIso $ Push⊣* _ _ _ ⟩
  --   PshHom (π₁ R Q *Strict Rᴰ) (×PshIntroStrict (π₁ R Q ⋆PshHomStrict α) (π₂ R Q) *Strict Pᴰ)
  --     ∎Iso
  -- PSHᴰ∀ Q {P} Pᴰ .snd .PshIsoEq.nat S3@(S , Sᴰ , _) R3@(R , Rᴰ , β)
  --   (α , αᴰ , Eq.refl) p _ Eq.refl =
  --   Eq.pathToEq (makePshHomPath (funExt₂ λ (Γ , Γᴰ , (s , q)) sᴰ → refl))

  -- isCartesianClosedⱽPSHᴰ : isCartesianClosedⱽ PSHAssoc (PRESHEAFᴰ Cᴰ ℓPSHᴰ ℓPSHᴰ) PSHIdL
  --   (PSHBP C ℓPSHᴰ) PSHπ₁NatEq PSH×aF-seq
  -- isCartesianClosedⱽPSHᴰ .fst = isCartesianⱽPSHᴰ
  -- isCartesianClosedⱽPSHᴰ .snd .fst = PSHᴰExponentials
  -- isCartesianClosedⱽPSHᴰ .snd .snd = PSHᴰ∀

  -- CCCⱽPSHᴰ : Path.CartesianClosedCategoryⱽ (Cartesian-PRESHEAF C ℓPSHᴰ) _ _
  -- CCCⱽPSHᴰ = EqCCCⱽ→CCCⱽ (Cartesian-PRESHEAF C ℓPSHᴰ) PSHAssoc PSHIdL PSHπ₁NatEq PSH×aF-seq
  --   (PRESHEAFᴰ Cᴰ ℓPSHᴰ ℓPSHᴰ) isCartesianClosedⱽPSHᴰ
