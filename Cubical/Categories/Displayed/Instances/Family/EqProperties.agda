-- Would be nice to have some kind of abstract nonsense reason for all of these...
--
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Family.EqProperties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Equiv.Dependent.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.HLevels.More

open import Cubical.Data.Unit
open import Cubical.Data.Empty renaming (rec to ⊥-rec) hiding (elim)
open import Cubical.Data.Empty.Properties
open import Cubical.Data.Sum.Base renaming (rec to ⊎-rec; elim to ⊎-elim)
open import Cubical.Data.Sum.Properties
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.More
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Exponentials.Small
open import Cubical.Categories.Instances.Fiber hiding (fiber)
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.IndexedProduct.Base
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.Terminal as Unitᴰ
open import Cubical.Categories.Displayed.Instances.Sets.Base as Setᴰ hiding (_[-][-,_])
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.BinProduct.More
open import Cubical.Categories.Displayed.Instances.Graph.Presheaf
open import Cubical.Categories.Displayed.Instances.Reindex.Eq
import Cubical.Categories.Displayed.Presheaf.Base as Curried
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Sets
open import Cubical.Categories.Displayed.Instances.Family.Base

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓE ℓE' ℓEᴰ ℓEᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Category
open Functor
open Functorᴰ
open isIsoOver
open NatTrans
open NatTransᴰ
open NatIso
open NatIsoᴰ
open PshHom
open PshIso

-- TODO:
--
-- The fiber of Fam C over Unit is definitionally isomorphic to C, and
-- the vertical universal properties in that fiber are equivalent to
-- the ordinary biCCC ones
module _ {ℓ} (C : Category ℓC ℓC') where
  private
    module C = Category C
    module Fam = Fibers (Fam {ℓ = ℓ} C)
  -- this is ... not very ergonomic
  isFibrationFam : Fibration (Fam {ℓ = ℓ} C) SetAssoc
  isFibrationFam {x} {y} f yᴰ = UEⱽ→Reprⱽ (yoRecEq (SET ℓ [-, y ]) (SetAssoc y) f *Presheafᴰ (Fam C [-][-, yᴰ ])) SetIdR fibUE
    where
    fibUE : UEⱽ _ _
    fibUE .UEⱽ.v = λ z → yᴰ (f z)
    fibUE .UEⱽ.e = λ x₁ → id C
    fibUE .UEⱽ.universal .isPshIsoEq.nIso c .fst x x₁ = x x₁
    fibUE .UEⱽ.universal .isPshIsoEq.nIso c .snd .fst b = funExt (λ _ → ⋆IdR C _)
    fibUE .UEⱽ.universal .isPshIsoEq.nIso c .snd .snd a = funExt (λ x₁ → ⋆IdR C _)

  FamTerminalsⱽ : Terminal' C → Terminalsⱽ (Fam {ℓ = ℓ} C)
  FamTerminalsⱽ term X = UEⱽ→Reprⱽ (UnitⱽPsh {P = SET ℓ [-, X ]}) SetIdR ueⱽ
    where
      module term = TerminalNotation term

      ueⱽ : UEⱽ _ _
      ueⱽ .UEⱽ.v _ = term.𝟙ue.vertex
      ueⱽ .UEⱽ.e = tt
      ueⱽ .UEⱽ.universal .isPshIsoEq.nIso ΓΓᴰf .fst _ γ = term.!t
      ueⱽ .UEⱽ.universal .isPshIsoEq.nIso ΓΓᴰf .snd .fst _ = refl
      ueⱽ .UEⱽ.universal .isPshIsoEq.nIso ΓΓᴰf .snd .snd f𝟙 = funExt (λ _ → sym term.𝟙ue.η)

  isFibrationFam^op :
    IndexedProducts (C ^op) ℓ
    → Fibration ((Fam {ℓ = ℓ} C) ^opᴰ) SetAssoc^op
  isFibrationFam^op CΣ {Y} {X} f Xᴰ = UEⱽ→Reprⱽ (yoRecEq ((SET ℓ ^op) [-, X ]) (SetAssoc^op X) f *Presheafᴰ
                                              ((Fam C ^opᴰ) [-][-, Xᴰ ])) SetIdR^op
    ueⱽ
    where
      module CΣ = IndexedProductsNotation CΣ

      ueⱽ : UEⱽ _ _
      ueⱽ .UEⱽ.v y = CΣ.Π {X = Eq.fiber f y} λ (f⁻y , _) → Xᴰ f⁻y
      ueⱽ .UEⱽ.e x = CΣ.app _ (x , Eq.refl)
      ueⱽ .UEⱽ.universal .isPshIsoEq.nIso c .fst fᴰ y = CΣ.lda _ (λ { (x , Eq.refl) → fᴰ x })
      ueⱽ .UEⱽ.universal .isPshIsoEq.nIso c .snd .fst fᴰ = funExt (λ x → CΣ.Πβ _ _ _)
      ueⱽ .UEⱽ.universal .isPshIsoEq.nIso c .snd .snd fᴰ = funExt (λ y →
        CΣ.intro≡ _ (funExt (λ { (x , Eq.refl) → refl {x = CΣ.app _ (x , Eq.refl) C.⋆ fᴰ (f x)} })))

  FamTerminalsⱽ^op : Terminal' (C ^op) → Terminalsⱽ ((Fam {ℓ = ℓ} C) ^opᴰ)
  FamTerminalsⱽ^op init X = UEⱽ→Reprⱽ (UnitⱽPsh {P = (SET ℓ ^op) [-, X ]}) SetIdR^op ueⱽ
    where
      module init = TerminalNotation init

      ueⱽ : UEⱽ _ _
      ueⱽ .UEⱽ.v x = init.𝟙ue.vertex
      ueⱽ .UEⱽ.e = tt
      ueⱽ .UEⱽ.universal .isPshIsoEq.nIso c .fst _ x = init.!t
      ueⱽ .UEⱽ.universal .isPshIsoEq.nIso c .snd .fst _ = refl
      ueⱽ .UEⱽ.universal .isPshIsoEq.nIso c .snd .snd k𝟘 = funExt (λ _ → sym init.𝟙ue.η)

  FamBPⱽ : BinProducts C → BinProductsⱽ (Fam {ℓ = ℓ} C)
  FamBPⱽ bp {x = X} P Q = UEⱽ→Reprⱽ ((Fam C [-][-, P ]) ×ⱽPsh (Fam C [-][-, Q ])) SetIdR ueⱽ
    where
      module bp = BinProductsNotation bp

      ueⱽ : UEⱽ _ _
      ueⱽ .UEⱽ.v x = P x bp.× Q x
      ueⱽ .UEⱽ.e = (λ _ → bp.π₁) , (λ _ → bp.π₂)
      ueⱽ .UEⱽ.universal .isPshIsoEq.nIso c .fst f,g x = f,g .fst x bp.,p f,g .snd x
      ueⱽ .UEⱽ.universal .isPshIsoEq.nIso c .snd .fst _ = ≡-× (funExt (λ _ → bp.×β₁)) (funExt (λ _ → bp.×β₂))
      ueⱽ .UEⱽ.universal .isPshIsoEq.nIso c .snd .snd a = funExt (λ x → sym $ bp.×ue.η _ _)

  FamBPⱽ^op : BinProducts (C ^op) → BinProductsⱽ ((Fam {ℓ = ℓ} C) ^opᴰ)
  FamBPⱽ^op coprod {x = X} P Q = UEⱽ→Reprⱽ (((Fam C ^opᴰ) [-][-, P ]) ×ⱽPsh ((Fam C ^opᴰ) [-][-, Q ])) SetIdR^op ueⱽ
    where
      module coprod = BinProductsNotation coprod

      ueⱽ : UEⱽ _ _
      ueⱽ .UEⱽ.v x = P x coprod.× Q x
      ueⱽ .UEⱽ.e = (λ _ → coprod.π₁) , (λ _ → coprod.π₂)
      ueⱽ .UEⱽ.universal .isPshIsoEq.nIso c .fst f,g x = f,g .fst x coprod.,p f,g .snd x
      ueⱽ .UEⱽ.universal .isPshIsoEq.nIso c .snd .fst _ = ≡-× (funExt (λ _ → coprod.×β₁)) (funExt (λ _ → coprod.×β₂))
      ueⱽ .UEⱽ.universal .isPshIsoEq.nIso c .snd .snd a = funExt (λ x → sym $ coprod.×ue.η _ _)

  FamLRⱽ : BinProducts C → AllLRⱽ (Fam {ℓ = ℓ} C) SetAssoc
  FamLRⱽ bp = BPⱽ+Fibration→AllLRⱽ (Fam C) SetAssoc (FamBPⱽ bp) isFibrationFam

  FamExpⱽ : (bp : BinProducts C) (exp : AllExponentiable C bp) → Exponentialsⱽ (Fam {ℓ = ℓ} C) SetAssoc SetIdL (FamLRⱽ bp)
  FamExpⱽ bp exp xᴰ yᴰ = UEⱽ→Reprⱽ (reindPsh (LRⱽF (Fam C) SetAssoc SetIdL xᴰ (FamLRⱽ bp xᴰ)) (Fam C [-][-, yᴰ ])) SetIdR ueⱽ
    where
      module exp = ExponentialsNotation bp exp
      module bp = BinProductsNotation bp
      ueⱽ : UEⱽ _ _
      ueⱽ .UEⱽ.v x = xᴰ x exp.⇒ yᴰ x
      ueⱽ .UEⱽ.e x = exp.app
      ueⱽ .UEⱽ.universal .isPshIsoEq.nIso c .fst x x₁ = exp.lda (x x₁)
      -- This is a bit of a code smell that this isn't literally
      -- ⇒ue.β but I don't see an easy way to avoid it? Maybe Bifunctorᴰ ?
      ueⱽ .UEⱽ.universal .isPshIsoEq.nIso c .snd .fst f⟨x⟩⟨xᴰ⟩ = funExt (λ x →
        ((((C.id C.⋆ bp.π₁) C.⋆ exp.lda (f⟨x⟩⟨xᴰ⟩ x)) bp.,p ((C.id C.⋆ bp.π₂) C.⋆ C.id)) C.⋆ exp.app)
          ≡⟨ C.⟨ cong₂ bp._,p_ C.⟨ C.⋆IdL _ ⟩⋆⟨ refl ⟩ (C.⋆IdR _ ∙ C.⋆IdL _) ⟩⋆⟨ refl ⟩ ⟩
        (((bp.π₁ C.⋆ exp.lda (f⟨x⟩⟨xᴰ⟩ x)) bp.,p (bp.π₂)) C.⋆ exp.app)
          ≡⟨ exp.⇒ue.β _ _ ⟩
        f⟨x⟩⟨xᴰ⟩ x
          ∎ )
      ueⱽ .UEⱽ.universal .isPshIsoEq.nIso c .snd .snd f⟨x⟩⇒ = funExt λ x →
        exp.lda ((((C.id C.⋆ bp.π₁) C.⋆ f⟨x⟩⇒ x) bp.,p ((C.id C.⋆ bp.π₂) C.⋆ C.id)) C.⋆ exp.app)
          ≡⟨ cong exp.lda C.⟨ cong₂ bp._,p_ C.⟨ C.⋆IdL _ ⟩⋆⟨ refl ⟩ (C.⋆IdR _ ∙ C.⋆IdL _) ⟩⋆⟨ refl ⟩ ⟩
        exp.lda (((bp.π₁ C.⋆ f⟨x⟩⇒ x) bp.,p bp.π₂) C.⋆ exp.app)
          ≡⟨ (sym $ exp.⇒ue.η _ _) ⟩
        f⟨x⟩⇒ x
          ∎

  -- Similar here: can we get rid of these ids?
  Fam∀ :
    (IndexedProducts C ℓ)
    → UniversalQuantifiers (Fam {ℓ = ℓ} C) SetIdL SetAssoc isFibrationFam BinProductsSET Setπ₁NatEq Set×aF-seq
  Fam∀ Π X {Γ} Γᴰ = UEⱽ→Reprⱽ (reindPsh
                              (wkF (Fam C) SetIdL SetAssoc isFibrationFam X
                               (λ c → BinProductsSET (c , X)) (Setπ₁NatEq X) (Set×aF-seq X) Γ)
                              (Fam C [-][-, Γᴰ ])) SetIdR ueⱽ
    where
      module Π = IndexedProductsNotation Π
      ueⱽ : UEⱽ _ _
      ueⱽ .UEⱽ.v γ = Π.Π (λ x → Γᴰ (γ , x))
      ueⱽ .UEⱽ.e γ,x = Π.app _ (γ,x .snd)
      ueⱽ .UEⱽ.universal .isPshIsoEq.nIso ΓΓᴰf .fst f γ = Π.lda _ (λ x → f (γ , x))
      ueⱽ .UEⱽ.universal .isPshIsoEq.nIso ΓΓᴰf .snd .fst b = funExt λ x →
        C.⟨ C.⟨ C.⋆IdL _ ⟩⋆⟨ refl ⟩ ∙ C.⋆IdL _ ⟩⋆⟨ refl ⟩
        ∙ Π.Πβ _ _ _
      ueⱽ .UEⱽ.universal .isPshIsoEq.nIso ΓΓᴰf .snd .snd a = funExt (λ γ →
        Π.intro≡ _ (funExt λ x →
          C.⟨ C.⟨ C.⋆IdL _ ⟩⋆⟨ refl ⟩ ∙ C.⋆IdL _ ⟩⋆⟨ refl ⟩))
