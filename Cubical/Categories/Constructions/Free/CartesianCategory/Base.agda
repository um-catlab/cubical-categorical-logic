{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.Free.CartesianCategory.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.CartesianCategory.BinaryCartesianCategory
open import Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
open import Cubical.Categories.Functor
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path
open BinaryCartesianCategory
open StrictCartesianFunctor
open Category
open ProductQuiver
open Functor

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level
  ℓq ℓq' : Level
  ℓc ℓc' : Level
  ℓd ℓd' : Level

module _ (Q : ProductQuiver ℓq ℓq') where
  open import Cubical.Categories.Limits.BinProduct
  open import Cubical.Categories.Limits.BinProduct.More
  open BinProduct
  open Notation

  ProdTypeExpr' = ProdTypeExpr (Q .vertex)

  data EdgeExpr[_,_] : ProdTypeExpr' → ProdTypeExpr' → Type (ℓ-max ℓq ℓq') where
    ↑ₑ : (e : Q .edge) → EdgeExpr[ Q .dom e , Q .cod e ]
    idₑ : ∀{A} → EdgeExpr[ A , A ]
    _⋆ₑ_ : ∀{A B C} → EdgeExpr[ A , B ] → EdgeExpr[ B , C ] → EdgeExpr[ A , C ]
    ⋆ₑIdL : ∀{A B}(f : EdgeExpr[ A , B ]) → idₑ ⋆ₑ f ≡ f
    ⋆ₑIdR : ∀{A B}(f : EdgeExpr[ A , B ]) → f ⋆ₑ idₑ ≡ f
    ⋆ₑAssoc : ∀{A B C D}(f : EdgeExpr[ A , B ])(g : EdgeExpr[ B , C ])(h : EdgeExpr[ C , D ]) → (f ⋆ₑ g) ⋆ₑ h ≡ f ⋆ₑ (g ⋆ₑ h)
    isSetEdgeExpr : ∀{A B} → isSet EdgeExpr[ A , B ]
    π₁ₑ : ∀{A B} → EdgeExpr[ A ×̬ B , A ]
    π₂ₑ : ∀{A B} → EdgeExpr[ A ×̬ B , B ]
    ⟨_,ₑ_⟩ : ∀{A B C} → EdgeExpr[ C , A ] → EdgeExpr[ C , B ] → EdgeExpr[ C , A ×̬ B ]
    !ₑ : ∀{A} → EdgeExpr[ A , ⊤̬ ]
    ×̬β₁ : ∀{A B C}{f : EdgeExpr[ C , A ]}{g : EdgeExpr[ C , B ]} → ⟨ f ,ₑ g ⟩ ⋆ₑ π₁ₑ ≡ f
    ×̬β₂ : ∀{A B C}{f : EdgeExpr[ C , A ]}{g : EdgeExpr[ C , B ]} → ⟨ f ,ₑ g ⟩ ⋆ₑ π₂ₑ ≡ g
    ×̬η : ∀{A B C}{f : EdgeExpr[ C , A ×̬ B ]} → ⟨ f ⋆ₑ π₁ₑ ,ₑ f ⋆ₑ π₂ₑ ⟩ ≡ f
    ⊤̬η : ∀{A}{f : EdgeExpr[ A , ⊤̬ ]} → f ≡ !ₑ

  FreeCartesianCategory : BinaryCartesianCategory _ _
  FreeCartesianCategory .cat .ob = ProdTypeExpr'
  FreeCartesianCategory .cat .Hom[_,_] = EdgeExpr[_,_]
  FreeCartesianCategory .cat .id = idₑ
  FreeCartesianCategory .cat ._⋆_ = _⋆ₑ_
  FreeCartesianCategory .cat .⋆IdL = ⋆ₑIdL
  FreeCartesianCategory .cat .⋆IdR = ⋆ₑIdR
  FreeCartesianCategory .cat .⋆Assoc = ⋆ₑAssoc
  FreeCartesianCategory .cat .isSetHom = isSetEdgeExpr
  FreeCartesianCategory .prod A B .binProdOb = A ×̬ B
  FreeCartesianCategory .prod A B .binProdPr₁ = π₁ₑ
  FreeCartesianCategory .prod A B .binProdPr₂ = π₂ₑ
  FreeCartesianCategory .prod A B .univProp f g = (⟨ f ,ₑ g ⟩ , ×̬β₁ , ×̬β₂) ,
    λ (h , p , q) →
      λ i → sym (×η-lemma h p q) i , isSet→isSet' isSetEdgeExpr ×̬β₁ p (congS (λ x → x ⋆ₑ π₁ₑ) (sym (×η-lemma h p q))) refl i , isSet→isSet' isSetEdgeExpr ×̬β₂ q (congS (λ x → x ⋆ₑ π₂ₑ) (sym (×η-lemma h p q))) refl i
    where
    -- this direction has more `sym` s, but I like it more 
    ×η-lemma : ∀{A B C f g} → (h : EdgeExpr[ C , A ×̬ B ]) → h ⋆ₑ π₁ₑ ≡ f → h ⋆ₑ π₂ₑ ≡ g → h ≡ ⟨ f ,ₑ g ⟩
    ×η-lemma h p q = (sym ×̬η) ∙ cong₂ (λ x y → ⟨ x ,ₑ y ⟩) p q
  FreeCartesianCategory .⊤ = ⊤̬
  FreeCartesianCategory .! = !ₑ
  FreeCartesianCategory .⊤η = ⊤̬η
  open Interp
  reinterp-trivial : (A : ProdTypeExpr') → interpret-objects Q FreeCartesianCategory ↑̬ A ≡ A
  reinterp-trivial (↑̬ B) = refl
  reinterp-trivial (B ×̬ C) i = reinterp-trivial B i ×̬ reinterp-trivial C i
  reinterp-trivial ⊤̬  = refl
  reinterp-trivial' : _
  reinterp-trivial' = funExt reinterp-trivial
  η : Interp Q FreeCartesianCategory
  η .I-ob = ↑̬
  η .I-hom e = transport⁻ inside-EdgeExpr (↑ₑ e)
    where
    inside-EdgeExpr : ∀{A B} → EdgeExpr[ interpret-objects Q FreeCartesianCategory ↑̬ A , interpret-objects Q FreeCartesianCategory ↑̬ B ] ≡ EdgeExpr[ A , B ]
    inside-EdgeExpr {A} {B} = congS (λ x → EdgeExpr[ x A , x B ]) reinterp-trivial'
  module _ {𝓒 : BinaryCartesianCategory ℓc ℓc'}(F : StrictCartesianFunctor FreeCartesianCategory 𝓒) where
  module _ {𝓒 : BinaryCartesianCategory ℓc ℓc'}(F F' : StrictCartesianFunctor FreeCartesianCategory 𝓒) where
    module _ (agree-on-η : {!!}) where
      open import Cubical.Foundations.HLevels
      open import Cubical.Foundations.Path
      open import Cubical.Foundations.Isomorphism

      open Iso
      aoo : ∀ t → F .functor ⟅ t ⟆ ≡ F' .functor ⟅ t ⟆
      aoo (↑̬ A) i = agree-on-η i .I-ob A
      aoo (A ×̬ B) = {!!}
      -- F .preserves-× ∙ inside-× 𝓒 (aoo A) (aoo B) ∙ sym (F' .preserves-×)
      aoo ⊤̬ = F .preserves-⊤ ∙ sym (F' .preserves-⊤)
      aoo' = funExt aoo
      aom-type : ∀{t t'} → (f : FreeCartesianCategory .cat [ t , t' ]) → Type _
      aom-type {t} {t'} f = PathP (λ i → congS (λ x → 𝓒 .cat [ x t , x t' ]) aoo' i) (F .functor .F-hom f) (F' .functor .F-hom f)
