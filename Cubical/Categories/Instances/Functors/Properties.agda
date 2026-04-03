module Cubical.Categories.Instances.Functors.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base

private
  variable ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
  variable ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓEᴰ ℓEᴰ' : Level

open Category
open UniversalElement
open NatTrans

module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') where
  private
    module D = Category D
  module _ (term : Terminal' D) where
    private
      module term = TerminalNotation term
    TerminalFUNCTOR : Terminal' (FUNCTOR C D)
    TerminalFUNCTOR .vertex = Constant C D term.𝟙ue.vertex
    TerminalFUNCTOR .element = _
    TerminalFUNCTOR .universal F .equiv-proof _ .fst .fst .N-ob x = term.!t
    TerminalFUNCTOR .universal F .equiv-proof _ .fst .fst .N-hom _ = term.𝟙extensionality
    TerminalFUNCTOR .universal F .equiv-proof _ .fst .snd = refl
    TerminalFUNCTOR .universal F .equiv-proof _ .snd (α , _) = ΣPathPProp (λ _ → isSetUnit _ _) (makeNatTransPath (funExt (λ _ → term.𝟙extensionality)))

  module _ (bp : BinProducts D) where
    private
      module bp = BinProductsNotation bp
    BinProductsFUNCTOR : BinProducts (FUNCTOR C D)
    BinProductsFUNCTOR (F , G) .vertex = bp.×F ∘F (F ,F G)
    BinProductsFUNCTOR (F , G) .element .fst .N-ob = λ _ → bp.π₁
    BinProductsFUNCTOR (F , G) .element .fst .N-hom f = bp.π₁Nat .N-hom _
    BinProductsFUNCTOR (F , G) .element .snd .N-ob = λ _ → bp.π₂
    BinProductsFUNCTOR (F , G) .element .snd .N-hom = λ _ → bp.π₂Nat .N-hom _
    BinProductsFUNCTOR (F , G) .universal H .equiv-proof (α , β) .fst .fst .N-ob x = α .N-ob x bp.,p β .N-ob x
    BinProductsFUNCTOR (F , G) .universal H .equiv-proof (α , β) .fst .fst .N-hom f =
      bp.×ue.intro-natural _ _
      ∙ bp.×ue.intro⟨_⟩ _ _ (≡-×
        (N-hom α f
        ∙ D.⟨ sym bp.×β₁ ⟩⋆⟨ refl ⟩ ∙ D.⋆Assoc _ _ _)
        (N-hom β f
        ∙ D.⟨ sym bp.×β₂ ⟩⋆⟨ refl ⟩ ∙ D.⋆Assoc _ _ _))
      ∙ sym (bp.×ue.intro-natural _ _)
    BinProductsFUNCTOR (F , G) .universal H .equiv-proof (α , β) .fst .snd = ≡-×
      (makeNatTransPath (funExt (λ _ → bp.×β₁)))
      (makeNatTransPath (funExt (λ _ → bp.×β₂)))
    BinProductsFUNCTOR (F , G) .universal H .equiv-proof (α , β) .snd (αβ , αβ≡α,β) = ΣPathPProp (λ _ → isSet× isSetNatTrans isSetNatTrans _ _)
      (makeNatTransPath (funExt (λ x → bp.×ue.intro≡ _ _ (≡-× (sym $ funExt⁻ (cong N-ob (PathPΣ αβ≡α,β .fst)) _) ((sym $ funExt⁻ (cong N-ob (PathPΣ αβ≡α,β .snd)) _))))))
