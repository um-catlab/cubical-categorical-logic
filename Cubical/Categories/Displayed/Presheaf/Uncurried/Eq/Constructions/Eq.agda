{-

  Uncurried Presheaves using EqElement
-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Constructions.Eq where

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

  module _ {P : Presheaf C ℓP} {Q : Presheaf C ℓQ} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
    wkPshᴰ : Presheafᴰ (P ×Psh Q) Cᴰ ℓPᴰ
    wkPshᴰ = (π₁Strict P Q) *↑ Pᴰ

  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ} (Pᴰ : Presheafᴰ (P ×Psh Q) Cᴰ ℓPᴰ) where
    private
      module P = PresheafNotation P
      module Q = PresheafNotation Q
      module P×Q = PresheafNotation (P ×Psh Q)
      module Pᴰ = PresheafᴰNotation Pᴰ

    ΣPshEq : Presheafᴰ P Cᴰ (ℓ-max ℓQ ℓPᴰ)
    ΣPshEq .F-ob (Γ , Γᴰ , p) .fst = Σ[ q ∈ Q.p[ Γ ] ] Pᴰ.p[ p , q ][ Γᴰ ]
    ΣPshEq .F-ob (Γ , Γᴰ , p) .snd =
      isSetΣ (Q .F-ob Γ .snd) (λ x → Pᴰ .F-ob (Γ , Γᴰ , p , x) .snd)
    ΣPshEq .F-hom (γ , γᴰ , γ⋆≡) (q , pᴰ) .fst = γ Q.⋆ q
    ΣPshEq .F-hom (γ , γᴰ , γ⋆≡) (q , pᴰ) .snd =
      Pᴰ.reindEq (Eq.pathToEq (ΣPathP (Eq.eqToPath γ⋆≡ , refl))) (γᴰ Pᴰ.⋆ᴰ pᴰ)
    ΣPshEq .F-id {x = x} = funExt λ (q , pᴰ) →
      ΣPathP (Q.⋆IdL _ , (Pᴰ.rectifyOut $ Pᴰ.reindEq-filler⁻ (Eq.pathToEq _) ∙ Pᴰ.⋆IdL _))
    ΣPshEq .F-seq _ _ = funExt λ (q , pᴰ) →
      ΣPathP (Q.⋆Assoc _ _ _ , (Pᴰ.rectify $ Pᴰ.≡out $
        Pᴰ.reindEq-filler⁻ (Eq.pathToEq _)
        ∙ Pᴰ.⋆Assoc _ _ _
        ∙ Pᴰ.⟨⟩⋆⟨ Pᴰ.reindEq-filler (Eq.pathToEq _) ⟩
        ∙ Pᴰ.reindEq-filler (Eq.pathToEq _)))

    private
      module ΣPsh = PresheafᴰNotation ΣPshEq

    ΣPshEq-σ : PshHomEq Pᴰ (wkPshᴰ ΣPshEq)
    ΣPshEq-σ .N-ob = λ c z → c .snd .snd .snd , z
    ΣPshEq-σ .N-hom _ _ (f , fᴰ , Eq.refl) _ _ Eq.refl =
      Eq.pathToEq (ΣPathP (refl , (Pᴰ.rectifyOut $ Pᴰ.reindEq-filler⁻ (Eq.pathToEq _))))

    module _ {Rᴰ : Presheafᴰ P Cᴰ ℓRᴰ} where
      private
        module Rᴰ = PresheafᴰNotation Rᴰ
        ΣPshEq-rec : PshHomEq Pᴰ (wkPshᴰ Rᴰ) → PshHomEq ΣPshEq Rᴰ
        ΣPshEq-rec αᴰ .N-ob = λ c z →
          αᴰ .N-ob (c .fst , c .snd .fst , c .snd .snd , z .fst) (z .snd)
        ΣPshEq-rec αᴰ .N-hom c c' (f , fᴰ , Eq.refl) p' p Eq.refl =
          (Eq.pathToEq $ Rᴰ.rectifyOut $ Rᴰ.⋆ᴰ-reind _)
          Eq.∙ αᴰ .N-hom _ _ _ _ _ (Eq.pathToEq (Pᴰ.rectifyOut $ Pᴰ.reindEq-filler (Eq.pathToEq _)))

        ΣPshEq-UMP : Iso (PshHomEq ΣPshEq Rᴰ) (PshHomEq Pᴰ (wkPshᴰ Rᴰ))
        ΣPshEq-UMP .Iso.fun αᴰ = ΣPshEq-σ ⋆PshHomEq ((π₁Strict _ _) *↑F αᴰ)
        ΣPshEq-UMP .Iso.inv = ΣPshEq-rec
        ΣPshEq-UMP .Iso.sec _ = makePshHomEqPath refl
        ΣPshEq-UMP .Iso.ret _ = makePshHomEqPath refl

  module _ (P : Presheaf C ℓP) where
    private
      module P = PresheafNotation P

    EqPsh' : Functor ((∫C (EqElement (P ×Psh P))) ^op) (PROP ℓP)
    EqPsh' = mkFunctor (PROP ℓP) hasPropHomsPROP
      (λ (_ , p , p') → (p Eq.≡ p') , Eq.isSet→isSetEq P.isSetPsh)
      λ (_ , fp,fp'≡q,q') → λ {Eq.refl → Eq.sym (Eq.ap fst fp,fp'≡q,q') Eq.∙ Eq.ap snd fp,fp'≡q,q'}

    EqPsh : Presheafᴰ (P ×Psh P) Cᴰ ℓP
    EqPsh = PROP→SET ∘F EqPsh' ∘F (∫F (Sndⱽ Cᴰ (EqElement (P ×Psh P))) ^opF)

    private
      module EqPsh = PresheafᴰNotation EqPsh

    Refl : PshHomEq UnitPsh (ΔPshHomStrict *↑ EqPsh)
    Refl .N-ob = λ c z → Eq.refl
    Refl .N-hom _ _ (_ , _ , Eq.refl) _ _ Eq.refl =
      Eq.pathToEq $ isProp→PathP (λ _ → Eq.isSet→isSetEq P.isSetPsh) _ _

    module _ {Rᴰ : Presheafᴰ (P ×Psh P) Cᴰ ℓRᴰ} where
      private
        module Rᴰ = PresheafᴰNotation Rᴰ
      EqPsh-rec : PshHomᴰ ΔPshHomStrict UnitPsh Rᴰ → PshHomEq EqPsh Rᴰ
      EqPsh-rec αᴰ .N-ob (c , cᴰ , p , p') e =
        Rᴰ.reindEq (Eq.pathToEq (λ i → p , Eq.eqToPath e i)) (αᴰ .N-ob (c , cᴰ , p) _)
      EqPsh-rec αᴰ .N-hom c c' (f , fᴰ ,  Eq.refl) Eq.refl Eq.refl Eq.refl =
        (Eq.pathToEq $ Rᴰ.rectifyOut $
         Rᴰ.⟨⟩⋆⟨ Rᴰ.reindEq-filler⁻ (Eq.pathToEq _) ⟩
         ∙ Rᴰ.⋆ᴰ-reind _
         ∙ (Rᴰ.≡in $ Eq.eqToPath $ αᴰ .N-hom _ (_ , _ , _) (f , fᴰ , Eq.refl) _ _ Eq.refl)
         ∙ Rᴰ.reindEq-filler (Eq.pathToEq _))

      EqPsh-UMP : Iso (PshHomEq EqPsh Rᴰ) (PshHomᴰ ΔPshHomStrict UnitPsh Rᴰ)
      EqPsh-UMP .Iso.fun αᴰ = Refl ⋆PshHomEq (ΔPshHomStrict *↑F αᴰ)
      EqPsh-UMP .Iso.inv = EqPsh-rec
      EqPsh-UMP .Iso.sec αᴰ = makePshHomEqPath (funExt₂ λ _ _ →
        Rᴰ.rectifyOut $ Rᴰ.reindEq-filler⁻ (Eq.pathToEq _))
      EqPsh-UMP .Iso.ret αᴰ =
        makePshHomEqPath (funExt₂ λ u v → Rᴰ.rectifyOut $
          Rᴰ.reindEq-filler⁻ (Eq.pathToEq _)
          ∙ (ΣPathP (ΣPathP (refl , (Eq.eqToPath v)) ,
              congP₂ (λ _ → αᴰ .N-ob) (ΣPathP (refl , (ΣPathP (refl , ΣPathP (refl , Eq.eqToPath v)))))
                (isProp→PathP (λ _ → Eq.isSet→isSetEq P.isSetPsh) Eq.refl v))))
