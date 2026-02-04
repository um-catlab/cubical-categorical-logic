{-

  Uncurried Presheaves using EqElement
-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Constructions.Push where

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
    (α : PshHomStrict P Q) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where

    private
      module P = PresheafNotation P
      module Q = PresheafNotation Q
      module Pᴰ = PresheafᴰNotation Pᴰ


    _*↓_ : Presheafᴰ Q Cᴰ (ℓP ⊔ℓ ℓPᴰ ⊔ℓ ℓQ)
    _*↓_ = ΣPshEq ((π₂Strict Q P *↑ Pᴰ) ×Psh
                   ((idPshHomStrict ×PshHomStrict α) *↑ EqPsh Q))

  module _ {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
    (α : PshHomStrict P Q) {Pᴰ : Presheafᴰ P Cᴰ ℓRᴰ} where

    private
      module Q = PresheafNotation Q
      module Pᴰ = PresheafᴰNotation Pᴰ
      module α*↑α*↓Pᴰ = PresheafᴰNotation (α *↑ (α *↓ Pᴰ))

    *↓-σ : PshHomᴰ α Pᴰ (α *↓ Pᴰ)
    *↓-σ .N-ob = λ c z → snd (c .snd) , z , Eq.refl
    *↓-σ .N-hom (c , cᴰ , p) (c' , cᴰ' , p') (f , fᴰ , Eq.refl) pᴰ' pᴰ Eq.refl =
      Eq.pathToEq (ΣPathP (refl ,
        ΣPathPProp (λ _ → Eq.isSet→isSetEq Q.isSetPsh) (Pᴰ.rectifyOut $
          -- Can't use reindEq-filler⁻ here
          Pᴰ.reind-revealed-filler⁻ _ ∙ Pᴰ.reind-revealed-filler⁻ _ ∙ (sym $ Pᴰ.⋆ᴰ-reind _))))

    module _ {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ} where
      private
        module Qᴰ = PresheafᴰNotation Qᴰ
        module Cᴰ = Fibers Cᴰ
        module C = Category C

      *↓-rec : PshHomᴰ α Pᴰ Qᴰ → PshHomEq (α *↓ Pᴰ) Qᴰ
      *↓-rec αᴰ .N-ob (Γ , Γᴰ , q) (p , pᴰ , q≡αp) =
        Qᴰ.reindEq (Eq.sym q≡αp) (αᴰ .N-ob (Γ , Γᴰ , p) pᴰ)
      *↓-rec αᴰ .N-hom (Δ , Δᴰ , q) (Γ , Γᴰ , q') (γ , γᴰ , Eq.refl)
        (p , pᴰ , Eq.refl) (p' , pᴰ' , e) e' =
          Eq.pathToEq $ Qᴰ.rectifyOut $
          Qᴰ.⋆ᴰ-reind _
          ∙ Qᴰ.≡in (Eq.eqToPath (αᴰ .N-hom _ _ (γ , γᴰ , Eq.pathToEq (cong fst (Eq.eqToPath e'))) _ _
              (Eq.pathToEq (Pᴰ.rectifyOut $
                (sym $ Pᴰ.⋆ᴰ-reind _)
                ∙ Pᴰ.⋆ᴰ-reind _
                ∙ Pᴰ.reind-revealed-filler _
                ∙ Pᴰ.reind-revealed-filler _
                ∙ Pᴰ.≡in (cong (λ z → z .snd .fst) (Eq.eqToPath e'))))))
          ∙ Qᴰ.reindEq-filler (Eq.sym e)

      *↓-UMP : Iso (PshHomEq (α *↓ Pᴰ) Qᴰ) (PshHomᴰ α Pᴰ Qᴰ)
      *↓-UMP .Iso.fun βⱽ = *↓-σ ⋆PshHomEq (α *↑F βⱽ)
      *↓-UMP .Iso.inv = *↓-rec
      *↓-UMP .Iso.sec βⱽ = makePshHomEqPath refl
      *↓-UMP .Iso.ret βⱽ = makePshHomEqPath (funExt₂ λ {_ (_ , _ , Eq.refl) → refl })

  module _
    {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
    (α : PshHomStrict P Q)
    (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
    (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
    where
    private
      module C = Category C
      module P = PresheafNotation P
      module Q = PresheafNotation Q
      module Pᴰ = PresheafᴰNotation Pᴰ
      module Qᴰ = PresheafᴰNotation Qᴰ
      module Cᴰ = Fibers Cᴰ

    -- Frobenius Reciprocity: ∃α (Pᴰ × α*Qᴰ) ≅ (∃α Pᴰ) × Qᴰ
    FrobeniusReciprocity-ptwise : ∀ ((Γ , Γᴰ , q) : (Cᴰ / Q) .Category.ob) →
      Iso (Σ[ p ∈ P.p[ Γ ] ] (Pᴰ.p[ p ][ Γᴰ ] × Qᴰ.p[ α .PshHomStrict.N-ob Γ p ][ Γᴰ ]) × (q Eq.≡ α .PshHomStrict.N-ob Γ p))
          ((Σ[ p ∈ P.p[ Γ ] ] Pᴰ.p[ p ][ Γᴰ ] × (q Eq.≡ α .PshHomStrict.N-ob Γ p)) × Qᴰ.p[ q ][ Γᴰ ])
    FrobeniusReciprocity-ptwise (Γ , Γᴰ , q) .Iso.fun (p , (pᴰ , qᴰ) , q≡αp) =
      (p , pᴰ , q≡αp) , Qᴰ.reindEq (Eq.sym q≡αp) qᴰ
    FrobeniusReciprocity-ptwise (Γ , Γᴰ , q) .Iso.inv ((p , pᴰ , q≡αp) , qᴰ) =
      p , (pᴰ , Qᴰ.reindEq q≡αp qᴰ) , q≡αp
    FrobeniusReciprocity-ptwise (Γ , Γᴰ , q) .Iso.sec ((p , pᴰ , q≡αp) , qᴰ) =
      ΣPathP (refl , (Qᴰ.rectifyOut $ Qᴰ.reindEq-filler⁻ _ ∙ Qᴰ.reindEq-filler⁻ _))
    FrobeniusReciprocity-ptwise (Γ , Γᴰ , q) .Iso.ret (p , (pᴰ , qᴰ) , q≡αp) =
      ΣPathP (refl , ΣPathP (ΣPathP (refl , (Qᴰ.rectifyOut $ Qᴰ.reindEq-filler⁻ _ ∙ Qᴰ.reindEq-filler⁻ _)) , refl))

    private
      -- ∃α (Pᴰ × α*Qᴰ)
      LHS : Presheafᴰ Q Cᴰ _
      LHS = α *↓ (Pᴰ ×Psh (α *↑ Qᴰ))

      -- (∃α Pᴰ) × Qᴰ
      RHS : Presheafᴰ Q Cᴰ _
      RHS = (α *↓ Pᴰ) ×Psh Qᴰ

      module LHSMod = PresheafᴰNotation LHS
      module RHSMod = PresheafᴰNotation RHS

    -- Naturality condition: for f : (Cᴰ / Q) [ Δ,Δᴰ,q , Γ,Γᴰ,q' ] and p at (Γ,Γᴰ,q'),
    -- fun (iso at Δ,Δᴰ,q) (f ⋆ p) ≡ f ⋆ (fun (iso at Γ,Γᴰ,q') p)
    FrobeniusReciprocity-natural :
      ∀ (Δ,Δᴰ,q : (Cᴰ / Q) .Category.ob) (Γ,Γᴰ,q' : (Cᴰ / Q) .Category.ob)
      (f : (Cᴰ / Q) [ Δ,Δᴰ,q , Γ,Γᴰ,q' ])
      (p : ⟨ LHS .F-ob Γ,Γᴰ,q' ⟩) →
      Iso.fun (FrobeniusReciprocity-ptwise Δ,Δᴰ,q) (LHS .F-hom f p)
        ≡
      RHS .F-hom f (Iso.fun (FrobeniusReciprocity-ptwise Γ,Γᴰ,q') p)
    FrobeniusReciprocity-natural (Δ , Δᴰ , q) (Γ , Γᴰ , q') (γ , γᴰ , e)
      (p , (pᴰ , qᴰ) , e') =
        ΣPathP (refl , (Qᴰ.rectifyOut $
          Qᴰ.reindEq-filler⁻ _
          ∙ Qᴰ.reind-revealed-filler⁻ _
          ∙ Qᴰ.reind-revealed-filler⁻ _
          ∙ sym (Qᴰ.⋆ᴰ-reind _)
          ∙ Qᴰ.⟨⟩⋆⟨ Qᴰ.reindEq-filler (Eq.sym e') ⟩
          ∙ Qᴰ.⋆ᴰ-reind _
          ))

    FrobeniusReciprocity : PshIsoEq LHS RHS
    FrobeniusReciprocity .PshIsoEq.isos = FrobeniusReciprocity-ptwise
    FrobeniusReciprocity .PshIsoEq.nat c c' (γ , γᴰ , Eq.refl) p' p Eq.refl =
      Eq.pathToEq $ sym $ FrobeniusReciprocity-natural c c' (γ , γᴰ , Eq.refl) p'
