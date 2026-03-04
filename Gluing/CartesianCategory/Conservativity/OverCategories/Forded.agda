{-# OPTIONS --lossy-unification #-}
module Gluing.CartesianCategory.Conservativity.OverCategories.Forded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Quiver.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Limits.Cartesian.Base

open import Cubical.Categories.Instances.Free.Category.Forded as FC
open import Cubical.Categories.Instances.Free.CartesianCategory.Forded as FCC
open import
  Cubical.Categories.Instances.Free.CartesianCategory.ProductQuiver
  hiding (_×_)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Limits.CartesianV' as V'
import Cubical.Categories.Displayed.Instances.Terminal.Base as Unitᴰ
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base
open import Cubical.Categories.Displayed.Instances.Presheaf.Eq.Base as PshBase
  using (PRESHEAFᴰ; PSHAssoc)
open import Cubical.Categories.Displayed.Instances.Presheaf.Eq.Cartesian
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.StrictHom
open import Cubical.Categories.Presheaf.Nerve using (Nerve)

private
  variable ℓQ ℓQ' : Level

open Category
open Functor
open Categoryᴰ
open Section
open PshHomStrict
open PshHom

module _ (Q : Quiver ℓQ ℓQ') where
  private module Q = QuiverOver (Q .snd)

  FREE : Category _ _
  FREE = FreeCat Q

  private module FREE = Category FREE

  FREE-1,× : CartesianCategory _ _
  FREE-1,× = FreeCartesianCategory (Quiver→×Quiver Q)

  private
    module FREE-1,× = CartesianCategory FREE-1,×
    ℓ = ℓ-max ℓQ ℓQ'

  ı : FC.Interp Q FREE-1,×.C
  ı .HetQG._$g_ = ↑_
  ı .HetQG._<$g>_ = FCC.↑ₑ (Quiver→×Quiver Q)

  ⊆ : Functor FREE FREE-1,×.C
  ⊆ = FC.rec Q ı

  extension : Functor FREE-1,×.C (PRESHEAF FREE _)
  extension = FCC.rec (Quiver→×Quiver Q) (Cartesian-PRESHEAF FREE (ℓ-max ℓQ ℓQ'))
    (mkElimInterpᴰ (YOStrict ⟅_⟆) λ f → YOStrict ⟪ ⇑ _ f ⟫)

  commutes : YOStrict ≡ extension ∘F ⊆
  commutes = FreeCatFunctor≡ Q _ _
    (record { _$gᴰ_ = λ _ → refl ; _<$g>ᴰ_ = λ _ → refl })

  ⊆-Faithful : isFaithful ⊆
  ⊆-Faithful = isFaithful-YOStrict-factor commutes

  nerve : Functor FREE-1,×.C (PRESHEAF FREE ℓ)
  nerve = Nerve ⊆

  private
    FREEᴰ : Categoryᴰ FREE ℓ-zero ℓ-zero
    FREEᴰ = Unitᴰ.Unitᴰ FREE

    PSHᴰ = PRESHEAFᴰ FREEᴰ ℓ ℓ

    module PSHᴰ = Categoryᴰ PSHᴰ

    PSHᴰCartesianⱽEq : isCartesianⱽ PSHAssoc PSHᴰ
    PSHᴰCartesianⱽEq = isCartesianⱽPSHᴰ

    PSHᴰCartesianⱽ : V'.CartesianCategoryⱽ (PRESHEAF FREE ℓ) _ _
    PSHᴰCartesianⱽ = EqCCⱽ→CCⱽ PSHAssoc PSHᴰ PSHᴰCartesianⱽEq

    PSHᴰCᴰ : Categoryᴰ (PRESHEAF FREE ℓ) _ _
    PSHᴰCᴰ = V'.CartesianCategoryⱽ.Cᴰ PSHᴰCartesianⱽ

  S : Section nerve PSHᴰCᴰ
  S = FCC.elimLocal (Quiver→×Quiver Q) nerve PSHᴰCartesianⱽ
       (mkElimInterpᴰ OB HOM)
    where
    OB : (o : Q .fst) → PSHᴰ.ob[ nerve ⟅ ⊆ ⟅ o ⟆ ⟆ ]
    OB o .F-ob (o' , _ , f) =
      (Σ[ g ∈ FREE [ o' , o ] ] ⊆ ⟪ g ⟫ ≡ f) ,
      isSetΣ (FREE .isSetHom)
        (λ _ → isSet→isGroupoid (FREE-1,×.C .isSetHom) _ _)
    OB o .F-hom {x = o' , _ , f} {y = o'' , _ , f'} (h , _ , eq) (g , p) =
      h FREE.⋆ g ,
      ⊆ .F-seq h g ∙ cong (λ x → ⊆ ⟪ h ⟫ ⋆⟨ FREE-1,×.C ⟩ x) p ∙ Eq.eqToPath eq
    OB o .F-id = funExt λ (g , p) → ΣPathP (FREE .⋆IdL _ ,
      isSet→SquareP (λ _ _ → FREE-1,×.C .isSetHom) _ _ _ _)
    OB o .F-seq _ _ = funExt λ _ → ΣPathP (FREE .⋆Assoc _ _ _ ,
      isSet→SquareP (λ _ _ → FREE-1,×.C .isSetHom) _ _ _ _)

    HOM : (e : Q.mor) →
      PSHᴰ.Hom[ nerve ⟪ ⊆ ⟪ FC.⇑ Q e ⟫ ⟫ ][ OB (Q.dom e) , OB (Q.cod e) ]
    HOM e .N-ob (o , _ , f) (g , p) =
      FC.⇑ Q e ∘⟨ FREE ⟩ g ,
      ⊆ .F-seq g (FC.⇑ Q e) ∙ cong (λ x → x ⋆⟨ FREE-1,×.C ⟩ ⊆ ⟪ FC.⇑ Q e ⟫) p
    HOM e .N-hom (o , _ , f) (o' , _ , f') (h , _ , eq) (g , p) =
      ΣPathP (FREE .⋆Assoc _ _ _ ,
        isSet→SquareP (λ _ _ → FREE-1,×.C .isSetHom) _ _ _ _)

  ⊆-Full : isFull ⊆
  ⊆-Full o o' f[o→o'] = ∣ g , q ∙ FREE-1,×.C .⋆IdL _ ∣₁
    where
    witness : Σ[ g ∈ FREE [ o , o' ] ] ⊆ ⟪ g ⟫ ≡ FREE-1,×.C .id ⋆⟨ FREE-1,×.C ⟩ f[o→o']
    witness = (S .F-homᴰ f[o→o'] .N-ob (o , tt , FREE-1,×.C .id)) (FREE .id , refl)

    g : FREE [ o , o' ]
    g = witness .fst

    q : ⊆ ⟪ g ⟫ ≡ FREE-1,×.C .id ⋆⟨ FREE-1,×.C ⟩ f[o→o']
    q = witness .snd

  ⊆-FullyFaithful : isFullyFaithful ⊆
  ⊆-FullyFaithful = isFull+Faithful→isFullyFaithful {F = ⊆} ⊆-Full ⊆-Faithful
