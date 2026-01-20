
module Cubical.Categories.LocallySmall.Presheaf.GloballySmall.IntoFiberCategory.Constructions.BinProduct.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Presheaf.GloballySmall.IntoFiberCategory.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Level
open import Cubical.Categories.LocallySmall.Instances.Functor.IntoFiberCategory
open import Cubical.Categories.LocallySmall.Constructions.BinProduct
  renaming (π₁ to ×Cπ₁ ; π₂ to ×Cπ₂)
open import Cubical.Categories.LocallySmall.Bifunctor.Base
open import Cubical.Categories.LocallySmall.Functor
open import Cubical.Categories.LocallySmall.Functor.Constant
open import Cubical.Categories.LocallySmall.NaturalTransformation.IntoFiberCategory

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Section.Base
open import Cubical.Categories.LocallySmall.Displayed.Section.Bisection
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Total
open import Cubical.Categories.LocallySmall.Displayed.Constructions.BinProduct.Base
open import Cubical.Categories.LocallySmall.Displayed.Instances.Sets.Base
open import Cubical.Categories.LocallySmall.Displayed.Bifunctor.Base

open Category
open Categoryᴰ
open Σω
open Liftω

module _ (C : SmallCategory ℓC ℓC') where
  private
    module C = SmallCategory C
    module SET = CategoryᴰNotation SET
    PSHC = PRESHEAF C
    module PSHC = CategoryᴰNotation PSHC

  open Functor
  open Functorᴰ
  open NatTransDefs (C ^opsmall) SET
  open NatTrans
  PshProd' : Functorᴰ ℓ-MAX (PSHC ×Cᴰ PSHC) PSHC
  PshProd' .F-obᴰ (P , Q) .F-ob c = liftω (_ , isSet× (P .F-ob c .lowerω .snd) (Q .F-ob c .lowerω .snd))
  PshProd' .F-obᴰ (P , Q) .F-hom = λ c (p , q) → F-hom P c p , F-hom Q c q
  PshProd' .F-obᴰ (P , Q) .F-id = funExt λ pq →
    ΣPathP (funExt⁻ (P .F-id) (pq .fst) , funExt⁻ (Q .F-id) (pq .snd))
  PshProd' .F-obᴰ (P , Q) .F-seq f g = funExt λ pq →
    ΣPathP ((funExt⁻ (P .F-seq f g) (pq .fst)) , (funExt⁻ (Q .F-seq f g) (pq .snd)))
  PshProd' .F-homᴰ (α , β) =
    natTrans
      (λ c x → (α .N-ob c (x .fst)) , (β .N-ob c (x .snd)))
      λ f → ΣPathP (refl , (funExt λ x →
        ΣPathP ((λ i → α .N-hom f i .snd (x .fst)) , λ i → β .N-hom f i .snd (x .snd))))
  PshProd' .F-idᴰ = makeNatTransPath refl (λ _ → refl)
  PshProd' .F-seqᴰ α β = makeNatTransPath refl (λ _ → refl)

  PshProdᴰ : Bifunctorᴰ (ParFunctorToBifunctor ℓ-MAX) PSHC PSHC PSHC
  PshProdᴰ = ParFunctorᴰToBifunctorᴰ PshProd'

  PshProd : Bifunctor PSHC.∫C PSHC.∫C PSHC.∫C
  PshProd = Bifunctorᴰ.∫F PshProdᴰ

  open Bifunctor
  _×Psh_ : Presheaf C ℓP → Presheaf C ℓQ → Presheaf C (ℓ-max ℓP ℓQ)
  P ×Psh Q = PshProd .Bif-ob (_ , P) (_ , Q) .snd
  module _ (P : Presheaf C ℓP)(Q : Presheaf C ℓQ) where
    private
      module P = PresheafNotation P
      module Q = PresheafNotation Q
    open Functor
    π₁ : PshHom (P ×Psh Q) P
    π₁ = mkPshHom (λ _ → fst) (λ _ _ → refl)

    π₂ : PshHom (P ×Psh Q) Q
    π₂ = mkPshHom (λ _ → snd) (λ _ _ → refl)

  module _
    {P : Presheaf C ℓP}
    {Q : Presheaf C ℓQ}
    {R : Presheaf C ℓR}
    (α : PshHom R P)
    (β : PshHom R Q)
    where
    private
      module P = PresheafNotation P
      module Q = PresheafNotation Q

    ×PshIntro : PshHom {C = C} R (P ×Psh Q)
    ×PshIntro =
      mkPshHom (λ c r → α .N-ob c r , β .N-ob c r)
        λ f p → λ i → (α .N-hom f i .snd p) , (β .N-hom f i .snd p)

    ×Pshβ₁ : ×PshIntro PSHC.⋆ᴰ π₁ P Q PSHC.∫≡ α
    ×Pshβ₁ = makeNatTransPath refl (λ _ → refl)

    ×Pshβ₂ : ×PshIntro PSHC.⋆ᴰ π₂ P Q PSHC.∫≡ β
    ×Pshβ₂ = makeNatTransPath refl (λ _ → refl)

  module _ (P : Presheaf C ℓP)(Q : Presheaf C ℓQ) where
    ×Psh-UMP :
      ∀ {R : Presheaf C ℓR} →
      Iso (PshHom {C = C} R (P ×Psh Q))
          (PshHom {C = C} R P × PshHom {C = C} R Q)
    ×Psh-UMP .Iso.fun α = (α PSHC.⋆ᴰ π₁ P Q) , (α PSHC.⋆ᴰ π₂ P Q)
    ×Psh-UMP .Iso.inv (α , β) = ×PshIntro α β
    ×Psh-UMP .Iso.sec (α , β) i = (×Pshβ₁ α β i .snd) , ×Pshβ₂ α β i .snd
    ×Psh-UMP .Iso.ret α = cong snd (makeNatTransPath refl λ _ → refl)

  private
    module BadDefinitionalBehavior where
      -- The below definition gives a compositional construction for PshProd'
      -- but when defined in this compositional manner, the composition operation
      -- of the resulting presheaf introduces a transport whereas the manual definition above
      -- does not
      -- I believe these transports come from FUNCTOR→FUNCTOR-EQ, and in particular
      -- the functor fib→fibEq.
      PshProd'Bad : Functorᴰ ℓ-MAX (PSHC ×Cᴰ PSHC) PSHC
      PshProd'Bad =
        FUNCTOR→FUNCTOR-EQ (C ^opsmall) SET Eq.refl
        ∘Fᴰ (postcomposeF _ _ ×SET
        ∘Fᴰ (,Fⱽ (C ^opsmall) SET SET
        ∘Fᴰ introF-×Cᴰ (×Cπ₁ _ _) (×Cπ₂ _ _)
          (FUNCTOR-EQ→FUNCTOR (C ^opsmall) SET Eq.refl
            ∘Fᴰ π₁ᴰ _ _)
          (FUNCTOR-EQ→FUNCTOR (C ^opsmall) SET Eq.refl
          ∘Fᴰ π₂ᴰ _ _)))

      PshProdᴰBad : Bifunctorᴰ (ParFunctorToBifunctor ℓ-MAX) PSHC PSHC PSHC
      PshProdᴰBad = ParFunctorᴰToBifunctorᴰ PshProd'Bad

      PshProdBad : Bifunctor PSHC.∫C PSHC.∫C PSHC.∫C
      PshProdBad = Bifunctorᴰ.∫F PshProdᴰBad

      open Bifunctor
      _×PshBad_ : Presheaf C ℓP → Presheaf C ℓQ → Presheaf C (ℓ-max ℓP ℓQ)
      P ×PshBad Q = PshProdBad .Bif-ob (_ , P) (_ , Q) .snd
      module _ (P : Presheaf C ℓP)(Q : Presheaf C ℓQ) where
        private
          module P = PresheafNotation P
          module Q = PresheafNotation Q
        open Functor

        -- This is bad because it is not definitionally equivalent
        -- to the definitions in
        -- Cubical.Categories.Presheaf.Constructions.BinProduct.Base
        -- To see this, note that the naturality for the following PshHom
        -- involves a transportRefl.
        -- However both in
        -- Cubical.Categories.Presheaf.Constructions.BinProduct.Base
        -- and with the manual definition of PshProd' above
        -- the naturality follows by refl
        π₁Bad : PshHom (P ×PshBad Q) P
        π₁Bad =
          mkPshHom (λ _ → fst) λ _ _ → transportRefl _ ∙ P.⟨⟩⋆⟨ transportRefl _ ⟩
