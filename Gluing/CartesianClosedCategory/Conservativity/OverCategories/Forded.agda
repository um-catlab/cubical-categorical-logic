{-# OPTIONS --lossy-unification #-}
module Gluing.CartesianClosedCategory.Conservativity.OverCategories.Forded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Quiver.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base

open import Cubical.Categories.Instances.Free.Category.Forded as FC
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Forded as FCCC
open import
  Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
  hiding (_×_)

open import Cubical.Categories.Displayed.Instances.Terminal.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Codomain.Presheaves
open import Cubical.Categories.Presheaf.CCC
open import Cubical.Categories.Presheaf.StrictHom
open import Cubical.Categories.Presheaf.Nerve using (RightAdjointProf-pres-bp)
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More

private
  variable ℓQ ℓQ' : Level

open Category
open Functor
open Categoryᴰ
open Section
open NatTrans

module _ (Q : Quiver ℓQ ℓQ') where
  private
    module Q = QuiverOver (Q .snd)
    ×⇒Q = Quiver→×⇒Quiver Q
    module ×⇒Q = ×⇒Quiver ×⇒Q

  FREE : Category _ _
  FREE = FreeCat Q

  private module FREE = Category FREE

  FREE-1,×,⇒ : CartesianClosedCategory _ _
  FREE-1,×,⇒ = FreeCartesianClosedCategory ×⇒Q

  private
    module FREE-1,×,⇒ = CartesianClosedCategory FREE-1,×,⇒
    ℓ = ℓ-max ℓQ ℓQ'

  ı : FC.Interp Q FREE-1,×,⇒.C
  ı .HetQG._$g_ = ↑_
  ı .HetQG._<$g>_ = FCCC.↑ₑ ×⇒Q

  ⊆ : Functor FREE FREE-1,×,⇒.C
  ⊆ = FC.rec Q ı

  extension : Functor FREE-1,×,⇒.C (PRESHEAF FREE _)
  extension = FCCC.rec ×⇒Q (CCC-PRESHEAF FREE (ℓ-max ℓQ ℓQ'))
    (mkElimInterpᴰ (YOStrict ⟅_⟆) λ f → YOStrict ⟪ ⇑ _ f ⟫)

  commutes : YOStrict ≡ extension ∘F ⊆
  commutes = FreeCatFunctor≡ Q _ _
    (record { _$gᴰ_ = λ _ → refl ; _<$g>ᴰ_ = λ _ → refl })

  ⊆-Faithful : isFaithful ⊆
  ⊆-Faithful = isFaithful-YOStrict-factor commutes

  nerve : Functor FREE-1,×,⇒.C (PresheafCategory FREE ℓ)
  nerve = RightAdjointProf ⊆

  private
    nerve-pres-bp :
      preservesProvidedBinProducts nerve (FREE-1,×,⇒.CC .CartesianCategory.bp)
    nerve-pres-bp =
      RightAdjointProf-pres-bp ⊆ (FREE-1,×,⇒.CC .CartesianCategory.bp)

  OB : (o : Q .fst) → Presheafᴰ (nerve ⟅ ⊆ ⟅ o ⟆ ⟆) (Unitᴰ FREE) ℓ
  OB o .F-ob (o' , _ , f) =
    (Σ[ g ∈ FREE [ o' , o ] ] ⊆ ⟪ g ⟫ ≡ f) ,
    isSetΣ (FREE .isSetHom)
      (λ _ → isSet→isGroupoid (FREE-1,×,⇒.C .isSetHom) _ _)
  OB o .F-hom (h , _ , e) (g , p) =
    h FREE.⋆ g ,
    ⊆ .F-seq h g ∙ cong (λ x → ⊆ ⟪ h ⟫ ⋆⟨ FREE-1,×,⇒.C ⟩ x) p ∙ e
  OB o .F-id = funExt λ _ → ΣPathPProp
    (λ _ → FREE-1,×,⇒.C .isSetHom _ _) (FREE .⋆IdL _)
  OB o .F-seq _ _ = funExt λ _ → ΣPathPProp
    (λ _ → FREE-1,×,⇒.C .isSetHom _ _) (FREE .⋆Assoc _ _ _)

  HOM : (e : Q.mor) →
    Categoryᴰ.Hom[_][_,_] (PSHCod ℓ) (nerve ⟪ ⊆ ⟪ FC.⇑ Q e ⟫ ⟫)
      (OB (Q.dom e)) (OB (Q.cod e))
  HOM e = mkPsh ℓ
    ( (λ Γ z →
        ( (z .fst ⋆⟨ FREE-1,×,⇒.C ⟩ ⊆ ⟪ FC.⇑ Q e ⟫)
        , (z .snd .fst FREE.⋆ FC.⇑ Q e
          , ⊆ .F-seq (z .snd .fst) (FC.⇑ Q e)
            ∙ cong (λ x → x ⋆⟨ FREE-1,×,⇒.C ⟩ ⊆ ⟪ FC.⇑ Q e ⟫) (z .snd .snd)))
        , refl)
    , λ ρ → funExt λ z → ΣPathP
        ( FREE-1,×,⇒.C .⋆Assoc _ _ _
        , ΣPathPProp (λ _ → FREE-1,×,⇒.C .isSetHom _ _)
            (FREE .⋆Assoc _ _ _)))

  S : Section nerve (PSHCod ℓ)
  S = FCCC.elimLocal ×⇒Q (nerve , nerve-pres-bp) (PSHCodCCCⱽ ℓ-zero)
    (mkElimInterpᴰ OB HOM)

  preimage : ∀ {o o'} (f : FREE-1,×,⇒.C [ ⊆ ⟅ o ⟆ , ⊆ ⟅ o' ⟆ ])
    → Σ[ g ∈ FREE [ o , o' ] ] ⊆ ⟪ g ⟫ ≡ FREE-1,×,⇒.C .id ⋆⟨ FREE-1,×,⇒.C ⟩ f
  preimage {o} f =
    let w = ptPsh ℓ (S .F-homᴰ f) .fst o (FREE-1,×,⇒.C .id , FREE .id , refl)
    in w .fst .snd .fst , w .fst .snd .snd ∙ w .snd

  ⊆-Full : isFull ⊆
  ⊆-Full o o' f =
    ∣ preimage f .fst , preimage f .snd ∙ FREE-1,×,⇒.C .⋆IdL f ∣₁

  ⊆-FullyFaithful : isFullyFaithful ⊆
  ⊆-FullyFaithful = isFull+Faithful→isFullyFaithful {F = ⊆} ⊆-Full ⊆-Faithful
