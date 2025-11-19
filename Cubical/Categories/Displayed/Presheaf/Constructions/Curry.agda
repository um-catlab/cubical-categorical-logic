{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions.Curry where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.HLevels.More

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Morphism
import Cubical.Categories.Displayed.Presheaf.Uncurried.Base as Uncurried
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
  renaming (π to Reindexπ; reindex to CatReindex)
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Category
open Functor
open Functorᴰ
open Iso
open PshHom
open PshHomᴰ

module _ {C : Category ℓC ℓC'} (P : Presheaf C ℓP)(Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module P = PresheafNotation P
  module _ (Pᴰ' : Uncurried.Presheafᴰ P Cᴰ ℓPᴰ) where
    private
      module Pᴰ' = Uncurried.PresheafᴰNotation Cᴰ P Pᴰ'
    CurryPshᴰ : Presheafᴰ P Cᴰ ℓPᴰ
    CurryPshᴰ .F-obᴰ {x} xᴰ p = Pᴰ' .F-ob (x , xᴰ , p)
    CurryPshᴰ .F-homᴰ {f = f} fᴰ p pᴰ = fᴰ Pᴰ'.⋆ᴰ pᴰ
    CurryPshᴰ .F-idᴰ = funExt (λ p → funExt λ pᴰ → Pᴰ'.rectify $ Pᴰ'.≡out $ Pᴰ'.⋆IdLᴰ pᴰ)
    CurryPshᴰ .F-seqᴰ fᴰ gᴰ = funExt λ p → funExt λ pᴰ → Pᴰ'.rectify $ Pᴰ'.≡out $ Pᴰ'.⋆Assocᴰ gᴰ fᴰ pᴰ

  module _ (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ
    UncurryPshᴰ : Uncurried.Presheafᴰ P Cᴰ ℓPᴰ
    UncurryPshᴰ .F-ob (x , xᴰ , p) = Pᴰ .F-obᴰ xᴰ p
    UncurryPshᴰ .F-hom {x = (x , xᴰ , p)}{y = (y , yᴰ , q)} (f , fᴰ , f⋆p≡q) pᴰ =
      Pᴰ.reind f⋆p≡q (fᴰ Pᴰ.⋆ᴰ pᴰ)
    UncurryPshᴰ .F-id = funExt (λ pᴰ → Pᴰ.rectify $ Pᴰ.≡out $
      sym (Pᴰ.reind-filler _ _) ∙ Pᴰ.⋆IdL _)
    UncurryPshᴰ .F-seq (f , fᴰ , f⋆p≡q) (g , gᴰ , g⋆q≡r) = funExt λ pᴰ → Pᴰ.rectify $ Pᴰ.≡out $
      sym (Pᴰ.reind-filler _ _)
      ∙ Pᴰ.⋆Assoc _ _ _
      ∙ Pᴰ.⟨⟩⋆⟨ Pᴰ.reind-filler _ _ ⟩
      ∙ Pᴰ.reind-filler _ _

  CurryPshᴰIso : Iso (Uncurried.Presheafᴰ P Cᴰ ℓPᴰ) (Presheafᴰ P Cᴰ ℓPᴰ)
  CurryPshᴰIso .fun = CurryPshᴰ
  CurryPshᴰIso .inv = UncurryPshᴰ
  CurryPshᴰIso .rightInv Pᴰ = Functorᴰ≡ (λ _ → refl)
    λ fᴰ → funExt λ p → funExt λ pᴰ → Pᴰ.rectify $ Pᴰ.≡out $
      sym $ Pᴰ.reind-filler _ _
    where module Pᴰ = PresheafᴰNotation Pᴰ
  CurryPshᴰIso .leftInv Pᴰ' = Functor≡ (λ _ → refl) λ (f , fᴰ , f⋆p≡q) → funExt λ pᴰ →
    Pᴰ'.rectify $ Pᴰ'.≡out $
      sym (Pᴰ.reind-filler _ _)
      ∙ (Pᴰ'.≡in $ λ i → Pᴰ' .F-hom (f , fᴰ , λ j → f⋆p≡q (i ∧ j)) pᴰ)
    where module Pᴰ = PresheafᴰNotation (CurryPshᴰ Pᴰ')
          module Pᴰ' = Uncurried.PresheafᴰNotation Cᴰ P Pᴰ'

module _ {C : Category ℓC ℓC'} {x : C .ob} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  CurryPshⱽ : Uncurried.Presheafⱽ x Cᴰ ℓPᴰ → Presheafⱽ x Cᴰ ℓPᴰ
  CurryPshⱽ = CurryPshᴰ _ Cᴰ

module _ {C : Category ℓC ℓC'} {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ' : Uncurried.Presheafᴰ Q Cᴰ ℓQᴰ)
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ' = Uncurried.PresheafᴰNotation Cᴰ Q Qᴰ'

  Uncurry-recᴰ : {α : PshHom P Q} → PshHomᴰ α Pᴰ (CurryPshᴰ Q Cᴰ Qᴰ') → Uncurried.PshHomᴰ α (UncurryPshᴰ P Cᴰ Pᴰ) Qᴰ'
  Uncurry-recᴰ αᴰ .N-ob = λ c → N-obᴰ αᴰ
  Uncurry-recᴰ αᴰ .N-hom (Δ , Δᴰ , q) (Γ , Γᴰ , p) (γ , γᴰ , γ⋆p≡q) pᴰ = Qᴰ'.rectify $ Qᴰ'.≡out $
    αᴰ.N-obᴰ⟨ sym $ Pᴰ.reind-filler _ _ ⟩
    ∙ αᴰ.N-hom _ _ _ _
    ∙ (sym $ Qᴰ'.∫⋆ᴰ-reind _ _ _)
    where module αᴰ = PshHomᴰ αᴰ

module _ {C : Category ℓC ℓC'} {P : Presheaf C ℓP}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ' : Uncurried.Presheafᴰ P Cᴰ ℓQᴰ)
  where
  private
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ' = Uncurried.PresheafᴰNotation Cᴰ P Qᴰ'
  Uncurry-recⱽ : PshHomⱽ Pᴰ (CurryPshᴰ P Cᴰ Qᴰ') → Uncurried.PshHomⱽ (UncurryPshᴰ P Cᴰ Pᴰ) Qᴰ'
  Uncurry-recⱽ αⱽ .N-ob = λ c → N-obᴰ αⱽ
  Uncurry-recⱽ αⱽ .N-hom (Δ , Δᴰ , q) (Γ , Γᴰ , p) (γ , γᴰ , γ⋆p≡q) pᴰ = Qᴰ'.rectify $ Qᴰ'.≡out $
    cong (αⱽ.N-ob _) (sym $ Pᴰ.reind-filler _ _)
    ∙ αⱽ.N-hom (Δ , Δᴰ) (Γ , Γᴰ) (γ , γᴰ) (p , pᴰ)
    ∙ (sym $ Qᴰ'.∫⋆ᴰ-reind _ _ _)
    where module αⱽ = PshHomᴰ αⱽ

  Curry-introⱽ : Uncurried.PshHomⱽ (UncurryPshᴰ P Cᴰ Pᴰ) Qᴰ' → PshHomⱽ Pᴰ (CurryPshᴰ P Cᴰ Qᴰ')
  Curry-introⱽ αⱽ .N-obᴰ {x} {xᴰ} {p} pᴰ = αⱽ .N-ob (x , xᴰ , p) pᴰ
  Curry-introⱽ αⱽ .N-homᴰ {x} {y} {xᴰ} {yᴰ} {f} {p} {fᴰ} {pᴰ} =
    cong (αⱽ .N-ob (x , xᴰ , (f P.⋆ p))) (sym $ transportRefl (fᴰ Pᴰ.⋆ᴰ pᴰ))
    ∙ αⱽ .N-hom (x , xᴰ , f P.⋆ p) (y , yᴰ , p) (f , fᴰ , refl) pᴰ

  Uncurry-recⱽ-Iso :
    Iso (Uncurried.PshHomⱽ (UncurryPshᴰ P Cᴰ Pᴰ) Qᴰ') (PshHomⱽ Pᴰ (CurryPshᴰ P Cᴰ Qᴰ'))
  Uncurry-recⱽ-Iso = iso Curry-introⱽ Uncurry-recⱽ
    (λ α → makePshHomᴰPathP (Curry-introⱽ (Uncurry-recⱽ α)) α refl refl)
    λ αⱽ → makePshHomPath refl

module _ {C : Category ℓC ℓC'} {P : Presheaf C ℓP}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (Pᴰ' : Uncurried.Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ' : Uncurried.Presheafᴰ P Cᴰ ℓQᴰ)
  where
  private
    module Pᴰ' = Uncurried.PresheafᴰNotation Cᴰ P Pᴰ'
    module Qᴰ' = Uncurried.PresheafᴰNotation Cᴰ P Qᴰ'
  CurryPshHom : PshHom Pᴰ' Qᴰ' → PshHomⱽ (CurryPshᴰ P Cᴰ Pᴰ') (CurryPshᴰ P Cᴰ Qᴰ')
  CurryPshHom α .PshHomᴰ.N-obᴰ = α .PshHom.N-ob _
  CurryPshHom α .PshHomᴰ.N-homᴰ =
    α .PshHom.N-hom (_ , _ , P .F-hom _ _) (_ , _ , _) (_ , _ , (λ _ → P .F-hom _ _)) _

  CurryPshHom⁻ : PshHomⱽ (CurryPshᴰ P Cᴰ Pᴰ') (CurryPshᴰ P Cᴰ Qᴰ') → PshHom Pᴰ' Qᴰ'
  CurryPshHom⁻ α .PshHom.N-ob = λ c → α .PshHomᴰ.N-obᴰ
  CurryPshHom⁻ α .PshHom.N-hom c c' (f , fᴰ , f⋆p≡q) pᴰ = Qᴰ'.rectify $ Qᴰ'.≡out $
    α.N-obᴰ⟨ Pᴰ'.≡in (Pᴰ'.⋆ᴰ-reind _ _ _) ∙ (sym $ Pᴰ'.reind-filler _) ⟩
    ∙ (Qᴰ'.≡in $ α .PshHomᴰ.N-homᴰ {fᴰ = fᴰ}{pᴰ = pᴰ})
    ∙ Qᴰ'.reind-filler f⋆p≡q ∙ (Qᴰ'.≡in $ sym $ Qᴰ'.⋆ᴰ-reind _ _ _)
    where module α = PshHomᴰ α

  CurryPshHom-FF-Iso : Iso (PshHom Pᴰ' Qᴰ') (PshHomⱽ (CurryPshᴰ P Cᴰ Pᴰ') (CurryPshᴰ P Cᴰ Qᴰ'))
  CurryPshHom-FF-Iso .fun = CurryPshHom
  CurryPshHom-FF-Iso .inv = CurryPshHom⁻
  CurryPshHom-FF-Iso .rightInv = λ αⱽ → makePshHomᴰPath refl
  CurryPshHom-FF-Iso .leftInv = λ α → makePshHomPath refl


module _ {C : Category ℓC ℓC'} {P : Presheaf C ℓP}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ)
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ

  UncurryPshHomⱽ : PshHomⱽ Pᴰ Qᴰ → PshHom (UncurryPshᴰ P Cᴰ Pᴰ) (UncurryPshᴰ P Cᴰ Qᴰ)
  UncurryPshHomⱽ α .N-ob _ = α .N-obᴰ
  UncurryPshHomⱽ α .N-hom (x , xᴰ , f) (y , yᴰ , g) (h , hᴰ , h⋆g≡f) pᴰ = Qᴰ.rectify $ Qᴰ.≡out $
    N-obᴰ⟨ α ⟩ (sym $ Pᴰ.reind-filler _ _)
    ∙ Qᴰ.≡in (α .N-homᴰ)
    ∙ Qᴰ.reind-filler _ _

  -- UncurryPshHomⱽ⁻ : PshHom (UncurryPshᴰ P Cᴰ Pᴰ) (UncurryPshᴰ P Cᴰ Qᴰ) → PshHomⱽ Pᴰ Qᴰ
  -- UncurryPshHomⱽ⁻ α .N-obᴰ = α .N-ob (_ , _ , _)
  -- UncurryPshHomⱽ⁻ α .N-homᴰ = {!α .N-hom _ _ _ _ ∙ ?!}

  -- UncurryPshHomⱽ-FF-Iso : Iso (PshHomⱽ Pᴰ Qᴰ) (PshHom (UncurryPshᴰ P Cᴰ Pᴰ) (UncurryPshᴰ P Cᴰ Qᴰ))
  -- UncurryPshHomⱽ-FF-Iso .fun = UncurryPshHomⱽ
  -- UncurryPshHomⱽ-FF-Iso .inv = {!!}
  -- UncurryPshHomⱽ-FF-Iso .rightInv = {!!}
  -- UncurryPshHomⱽ-FF-Iso .leftInv = {!!}
