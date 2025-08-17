{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Bifunctor
import Cubical.Categories.Displayed.Constructions.Reindex.Base as Categoryᴰ
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Presheaf

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓQᴰ ℓRᴰ : Level

module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
  where
  -- External product: (Pᴰ ×ᴰ Qᴰ) over (P × Q)
  PshProd'ᴰ :
    Functorᴰ PshProd' (PRESHEAFᴰ Cᴰ ℓA ℓAᴰ ×Cᴰ PRESHEAFᴰ Cᴰ ℓB ℓBᴰ)
                      (PRESHEAFᴰ Cᴰ (ℓ-max ℓA ℓB) (ℓ-max ℓAᴰ ℓBᴰ))
  PshProd'ᴰ = postcomposeFᴰ (C ^op) (Cᴰ ^opᴰ) ×Setsᴰ ∘Fᴰ ,Fᴰ-functorᴰ

  PshProdᴰ :
    Bifunctorᴰ PshProd (PRESHEAFᴰ Cᴰ ℓA ℓAᴰ) (PRESHEAFᴰ Cᴰ ℓB ℓBᴰ)
                       (PRESHEAFᴰ Cᴰ (ℓ-max ℓA ℓB) (ℓ-max ℓAᴰ ℓBᴰ))
  PshProdᴰ = ParFunctorᴰToBifunctorᴰ PshProd'ᴰ

module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
  where
  -- Internal product: Pᴰ ×ⱽ Qᴰ over P
  PshProdⱽ :
    Functorⱽ (PRESHEAFᴰ Cᴰ ℓA ℓAᴰ ×ᴰ PRESHEAFᴰ Cᴰ ℓA ℓBᴰ)
             (PRESHEAFᴰ Cᴰ ℓA (ℓ-max ℓAᴰ ℓBᴰ))
  PshProdⱽ = postcomposeFⱽ (C ^op) (Cᴰ ^opᴰ) ×Setsⱽ ∘Fⱽ ,Fⱽ-functorⱽ

  -- module _ {P : Presheaf C ℓ}
  -- PshProdⱽ-ue :

-- Reindexing presheaves
-- There are 3 different notions of reindexing a presheaf we consider here.
-- 1. Reindexing a presheaf Qᴰ over Q along a homomorphism α : P ⇒ Q to be over P
-- 2. Reindexing a presheaf Qᴰ over Q along a functor F to be over (Q ∘ F^op)
-- 3. The combination of those two, reindexing a presheaf Qᴰ over Q along a heteromorphism α : P =[ F ]=> Q to be over P.
module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  (α : PshHom P Q) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
  private
    module Qᴰ = PresheafᴰNotation Qᴰ
  open Functorᴰ
  reind : Presheafᴰ P Cᴰ ℓQᴰ
  reind .F-obᴰ {x} xᴰ p = Qᴰ .F-obᴰ xᴰ (α .fst x p)
  reind .F-homᴰ {y} {x} {f} {yᴰ} {xᴰ} fᴰ p qᴰ =
    Qᴰ.reind (sym $ α .snd _ _ _ _) (fᴰ Qᴰ.⋆ᴰ qᴰ)
  reind .F-idᴰ = funExt λ p → funExt λ qᴰ → Qᴰ.rectify $ Qᴰ.≡out $
    (sym $ Qᴰ.reind-filler _ _)
    ∙ Qᴰ.⋆IdL _
  reind .F-seqᴰ fᴰ gᴰ = funExt λ p → funExt λ qᴰ → Qᴰ.rectify $ Qᴰ.≡out $
    (sym $ Qᴰ.reind-filler _ _)
    ∙ Qᴰ.⋆Assoc _ _ _
    ∙ Qᴰ.⟨ refl ⟩⋆⟨ Qᴰ.reind-filler _ _ ⟩
    ∙ Qᴰ.reind-filler _ _

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {Q : Presheaf D ℓQ}
  (F : Functor C D) (Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ)
  where
  reindFunc : Presheafᴰ (Q ∘F (F ^opF)) (Categoryᴰ.reindex Dᴰ F) ℓQᴰ
  reindFunc = Qᴰ ∘Fᴰ (Categoryᴰ.π _ _ ^opFᴰ)

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  {P : Presheaf C ℓP}{Q : Presheaf D ℓQ}
  (α : PshHet F P Q)(Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ)
  where
  reindHet : Presheafᴰ P (Categoryᴰ.reindex Dᴰ F) ℓQᴰ
  reindHet = reind α $ reindFunc F Qᴰ

  -- Theorem
  -- if cᴰ represents Pⱽ and dᴰ represents Qⱽ
  -- and cᴰ×ⱽdᴰ represents Cᴰ[-][-, cᴰ ] ×ⱽ Cᴰ[-][-, dᴰ ],
  -- then cᴰ×ⱽdᴰ represents Pⱽ ×ⱽ Qⱽ
  --
  -- this is trivial if we use univalence...
  --   Cᴰ[-][-, cᴰ ] ×ⱽ Cᴰ[-][-, dᴰ ],
  --   ≡ Pᴰ ×ⱽ Qᴰ
  --   ≡ Cᴰ[-][-, cᴰ×ⱽdᴰ ]
-- module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
--   {c}
--   (Pᴰ : Presheafⱽ c Cᴰ ℓPᴰ)(Pᴰ' : Presheafⱽ c Cᴰ ℓQᴰ)
--   where
--   open Functorᴰ
--   open Bifunctor
--   open Bifunctorᴰ

--   module _
--     {ueᴰ : UniversalElementⱽ _ _ Pᴰ}
--     {ueᴰ' : UniversalElementⱽ _ _ Pᴰ'}
--     where
--     private
--       module C = Category C
--       module ueᴰ = UniversalElementⱽ ueᴰ
--       module ueᴰ' = UniversalElementⱽ ueᴰ'
--       module Pᴰ = PresheafⱽNotation Pᴰ
--       module Pᴰ' = PresheafⱽNotation Pᴰ'
--       Pᴰ×Pᴰ' = PshProdⱽ .F-obᴰ (Pᴰ , Pᴰ')
--       module Pᴰ×Pᴰ' = PresheafⱽNotation (PshProdⱽ .F-obᴰ (Pᴰ , Pᴰ'))

--       ueᴰ×ueᴰ' = PshProdⱽ .F-obᴰ (Cᴰ [-][-, ueᴰ.vertexⱽ ] , Cᴰ [-][-, ueᴰ'.vertexⱽ ])
--       module ueᴰ×ueᴰ' = PresheafⱽNotation ueᴰ×ueᴰ'

--     open UniversalElementⱽ
    -- This should follow from the general principle that PshProdⱽ preserves PshHoms, PshIso
    --   PshProdⱽUE : UniversalElementⱽ _ c Pᴰ×Pᴰ'

module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
  (P : Presheaf C ℓP)(Q : Presheaf C ℓQ)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)(Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
  open Functorᴰ
  open Bifunctor
  open Bifunctorᴰ
  π₁ : PshHom (PshProd .Bif-ob P Q) P
  π₁ .fst _ = fst
  π₁ .snd _ _ _ _ = refl

  π₂ : PshHom (PshProd .Bif-ob P Q) Q
  π₂ .fst _ = snd
  π₂ .snd _ _ _ _ = refl

  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
  PshProdⱽ→ᴰ :
    PshProdᴰ .Bif-obᴰ Pᴰ Qᴰ ≡ PshProdⱽ .F-obᴰ (reind π₁ Pᴰ , reind π₂ Qᴰ)
  PshProdⱽ→ᴰ = Functorᴰ≡
    (λ Aᴰ → funExt λ (p , q) → ΣPathPProp (λ _ → isPropIsSet) refl)
    λ fᴰ → funExt λ (p , q) → funExt λ (pᴰ , qᴰ) → ΣPathP $
      (Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.reind-filler _ _)
      , (Qᴰ.rectify $ Qᴰ.≡out $ Qᴰ.reind-filler _ _)


module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{Q : Presheaf C ℓQ} where
  private
    module C = Category C
    module Q = PresheafNotation Q
  module _ {c : C.ob} (q : Q.p[ c ]) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where
    private
      module Qᴰ = PresheafᴰNotation Qᴰ
      open Functorᴰ
    reindYo : Presheafⱽ c Cᴰ ℓQᴰ
    reindYo = reind (yoRec Q q) Qᴰ

-- Reindexing is compositional:
module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}{R : Presheaf C ℓR}
  (α : PshHom P Q)(β : PshHom Q R) (Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ)
  where
  private
    module Rᴰ = PresheafᴰNotation Rᴰ
  reind-seq : reind α (reind β Rᴰ) ≡ reind (seqPshHom α β) Rᴰ
  reind-seq = Functorᴰ≡ (λ _ → refl) λ fᴰ → funExt λ p → funExt λ rᴰ →
    Rᴰ.rectify $ Rᴰ.≡out $
      sym (Rᴰ.reind-filler _ _ ∙ Rᴰ.reind-filler _ _)
      ∙ Rᴰ.reind-filler _ _

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  (α : PshHom P Q) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
  private
    module P = PresheafNotation P
    module Qᴰ = PresheafᴰNotation Qᴰ
  module _ {c}(p : P.p[ c ]) where
    reindYo-seq : reindYo p (reind α Qᴰ) ≡ reindYo (α .fst _ p) Qᴰ
    reindYo-seq = reind-seq _ _ _
      ∙ cong₂ reind (yoRec-natural _ _ _) refl
