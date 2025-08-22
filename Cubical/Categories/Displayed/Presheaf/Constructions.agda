{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Equiv.Dependent
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
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
  renaming (π to Reindexπ; reindex to CatReindex)
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Morphism

open Bifunctorᴰ
open Functorᴰ
private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

-- TODO: Terminal presheafᴰ here.

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

  _×ᴰPsh_ : ∀ {P : Presheaf C ℓA}{Q : Presheaf C ℓB}
            → (Pᴰ : Presheafᴰ P Cᴰ ℓAᴰ)(Qᴰ : Presheafᴰ Q Cᴰ ℓBᴰ)
            → Presheafᴰ (P ×Psh Q) Cᴰ _
  _×ᴰPsh_ = PshProdᴰ .Bif-obᴰ

module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
  where
  -- Internal product: Pᴰ ×ⱽ Qᴰ over P
  PshProdⱽ :
    Functorⱽ (PRESHEAFᴰ Cᴰ ℓA ℓAᴰ ×ᴰ PRESHEAFᴰ Cᴰ ℓA ℓBᴰ)
             (PRESHEAFᴰ Cᴰ ℓA (ℓ-max ℓAᴰ ℓBᴰ))
  PshProdⱽ = postcomposeFⱽ (C ^op) (Cᴰ ^opᴰ) ×Setsⱽ ∘Fⱽ ,Fⱽ-functorⱽ

  _×ⱽPsh_ : ∀ {P : Presheaf C ℓA}
            → (Pᴰ : Presheafᴰ P Cᴰ ℓAᴰ)(Qᴰ : Presheafᴰ P Cᴰ ℓBᴰ)
            → Presheafᴰ P Cᴰ _
  Pᴰ ×ⱽPsh Qᴰ = PshProdⱽ .F-obᴰ (Pᴰ , Qᴰ)

  -- This is like PshProdⱽ .F-hom but for homomorphisms/isomorphisms
  -- between presheaves of different levels
  --
  -- We should see if we can get this for free using Lift
  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
    {Pᴰ' : Presheafᴰ P Cᴰ ℓPᴰ'}
    {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
    {Qᴰ' : Presheafᴰ Q Cᴰ ℓQᴰ'}
    where
    module _ {α : PshHom P Q} where
      open PshHomᴰ
      _×ⱽHom_ : (αᴰ : PshHomᴰ α Pᴰ Qᴰ) (βᴰ : PshHomᴰ α Pᴰ' Qᴰ')
        → PshHomᴰ α (Pᴰ ×ⱽPsh Pᴰ') (Qᴰ ×ⱽPsh Qᴰ')
      (αᴰ ×ⱽHom βᴰ) .N-obᴰ (p , p') = (αᴰ .N-obᴰ p) , (βᴰ .N-obᴰ p')
      (αᴰ ×ⱽHom βᴰ) .N-homᴰ = ΣPathP ((αᴰ .N-homᴰ) , (βᴰ .N-homᴰ))

    module _ {α : PshIso P Q} where
      open isIsoOver
      _×ⱽIso_ : (αᴰ : PshIsoᴰ α Pᴰ Qᴰ) (βᴰ : PshIsoᴰ α Pᴰ' Qᴰ')
        → PshIsoᴰ α (Pᴰ ×ⱽPsh Pᴰ') (Qᴰ ×ⱽPsh Qᴰ')
      (αᴰ ×ⱽIso βᴰ) .fst = (αᴰ .fst) ×ⱽHom (βᴰ .fst)
      (αᴰ ×ⱽIso βᴰ) .snd .inv _ (q , q') = (αᴰ .snd .inv _ q) , (βᴰ .snd .inv _ q')
      (αᴰ ×ⱽIso βᴰ) .snd .rightInv _ _ = ΣPathP ((αᴰ .snd .rightInv _ _) , (βᴰ .snd .rightInv _ _))
      (αᴰ ×ⱽIso βᴰ) .snd .leftInv _ _ = ΣPathP ((αᴰ .snd .leftInv _ _) , (βᴰ .snd .leftInv _ _))

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
  reindFunc : Presheafᴰ (Q ∘F (F ^opF)) (CatReindex Dᴰ F) ℓQᴰ
  reindFunc = Qᴰ ∘Fᴰ (Reindexπ _ _ ^opFᴰ)

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  {P : Presheaf C ℓP}{Q : Presheaf D ℓQ}
  (α : PshHet F P Q)(Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ)
  where
  reindHet : Presheafᴰ P (CatReindex Dᴰ F) ℓQᴰ
  reindHet = reind α $ reindFunc F Qᴰ

module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)(Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
  open Functorᴰ
  open Bifunctor
  open Bifunctorᴰ
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

  open PshHomᴰ
  open isIsoOver
  PshProdⱽ≅ᴰ :
    PshIsoⱽ (Pᴰ ×ᴰPsh Qᴰ) (reind (π₁ P Q) Pᴰ ×ⱽPsh reind (π₂ P Q) Qᴰ)
  PshProdⱽ≅ᴰ .fst .N-obᴰ x = x
  PshProdⱽ≅ᴰ .fst .N-homᴰ =
    ΣPathP ( (Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.reind-filler _ _)
           , (Qᴰ.rectify $ Qᴰ.≡out $ Qᴰ.reind-filler _ _))
  PshProdⱽ≅ᴰ .snd .inv _ x = x
  PshProdⱽ≅ᴰ .snd .rightInv _ _ = refl
  PshProdⱽ≅ᴰ .snd .leftInv _ _ = refl

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α β : PshHom P Q}(α≡β : α ≡ β) {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where
  private
    module Qᴰ = PresheafᴰNotation Qᴰ
  reindPathIsoⱽ : PshIsoⱽ (reind α Qᴰ) (reind β Qᴰ)
  reindPathIsoⱽ .fst .PshHomᴰ.N-obᴰ = Qᴰ.reind (funExt⁻ (funExt⁻ (cong fst α≡β) _) _)
  reindPathIsoⱽ .fst .PshHomᴰ.N-homᴰ =
    Qᴰ.rectify $ Qᴰ.≡out $
      (sym (Qᴰ.reind-filler _ _)
      ∙ sym (Qᴰ.reind-filler _ _)
      ∙ Qᴰ.⟨⟩⋆⟨ Qᴰ.reind-filler _ _ ⟩)
      ∙ Qᴰ.reind-filler _ _
  reindPathIsoⱽ .snd .isIsoOver.inv q =
    Qᴰ.reind ((funExt⁻ (funExt⁻ (cong fst (sym α≡β)) _) _))
  reindPathIsoⱽ .snd .isIsoOver.rightInv q qᴰ =
    Qᴰ.rectify $ Qᴰ.≡out $ sym $ Qᴰ.reind-filler _ _ ∙ Qᴰ.reind-filler _ _
  reindPathIsoⱽ .snd .isIsoOver.leftInv q qᴰ =
    Qᴰ.rectify $ Qᴰ.≡out $ sym $ Qᴰ.reind-filler _ _ ∙ Qᴰ.reind-filler _ _

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
    reindYo-seq : reindYo p (reind α Qᴰ) ≡ reindYo (α .fst _ p) Qᴰ
    reindYo-seq = reind-seq _ _ _
      ∙ cong₂ reind (yoRec-natural _ _ _) refl

    reindYo-seqIsoⱽ : PshIsoⱽ (reindYo p (reind α Qᴰ)) (reindYo (α .fst c p) Qᴰ)
    reindYo-seqIsoⱽ =
      reind-seqIsoⱽ _ _ _ ⋆PshIsoⱽ reindPathIsoⱽ (yoRec-natural _ _ _)

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  (α : PshIso P Q) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
  private
    module Qᴰ = PresheafᴰNotation Qᴰ
  -- is this the universal property of reind?
  reindPshIsoPshIsoᴰ : PshIsoᴰ α (reind (α .fst) Qᴰ) Qᴰ
  reindPshIsoPshIsoᴰ = mkPshIsoᴰEquivOver α (reind (α .fst) Qᴰ) Qᴰ
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
      → PathP (λ i → Presheafᴰ (α i) Cᴰ ℓQᴰ) (reind (pathToPshIso α .fst) Qᴰ) Qᴰ
  reindPathToPshIsoPathP :
    ∀ {Q : Presheaf C ℓP} (α : P ≡ Q)
    → (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
    -- TODO: give this kind of PathP a name? it's the analogue of PshIsoᴰ for paths
    → PathP (λ i → Presheafᴰ (α i) Cᴰ ℓQᴰ) (reind (pathToPshIso α .fst) Qᴰ) Qᴰ
  -- If we have prove pathToPshIso is an Iso then we could apply reindPshIsoPshIsoᴰ here
  reindPathToPshIsoPathP =
    J (motive _) λ Qᴰ →
      subst (λ α → reind (α .fst) Qᴰ ≡ Qᴰ)
        (sym pathToPshIsoRefl)
        (sym $ reind-id _)
