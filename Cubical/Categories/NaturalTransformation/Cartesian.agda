-- A natural transformation is *Cartesian* when its naturality squares
-- are pullbacks

module Cubical.Categories.NaturalTransformation.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism renaming (iso to iIso)
open import Cubical.Data.Sigma
import      Cubical.Data.Equality as Eq
open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Equality
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Morphism
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.Limits.Pullback

open import Cubical.Categories.Instances.Functors

private
  variable
    ℓA ℓA' ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
    ℓ ℓ' ℓ'' : Level
    B C D E : Category ℓ ℓ'

open Category
open NatTrans
open NatIso
open isIsoC

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  where
  module _ {F G : Functor C D} (α : NatTrans F G) where
    isCartesian : Type _
    isCartesian = ∀ {x y}(f : C [ x , y ])
      → isPullback D (cospan (F ⟅ y ⟆) (G ⟅ y ⟆) (G ⟅ x ⟆) (α ⟦ y ⟧) (G ⟪ f ⟫)) {F ⟅ x ⟆}
          (F ⟪ f ⟫)
          (α ⟦ x ⟧)
          (α .N-hom f)
  CartesianNatTrans : (F G : Functor C D) → Type _
  CartesianNatTrans F G = Σ (NatTrans F G) isCartesian

  module _ {F G : Functor C D} ((α , α-cart) : CartesianNatTrans F G)  where
    CartesianNatTrans→PBSq : ∀ {x y} (f : C [ x , y ]) → Pullback D (cospan (F ⟅ y ⟆) (G ⟅ y ⟆) (G ⟅ x ⟆) (α ⟦ y ⟧) (G ⟪ f ⟫))
    CartesianNatTrans→PBSq {x}{y} f = record
                              { pbOb = F ⟅ x ⟆
                              ; pbPr₁ = F ⟪ f ⟫
                              ; pbPr₂ = α ⟦ x ⟧
                              ; pbCommutes = α .N-hom f
                              ; univProp = α-cart f
                              }
    module CartNatTransPBs {x y} (f : C [ x , y ]) = Pullback (CartesianNatTrans→PBSq f)

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}{F : Functor C C}{F' : Functor D D}
  (G : Functor C D)
  ((π , π-Cart) : CartesianNatTrans F Id)
  ((π' , π'-Cart) : CartesianNatTrans F' Id)
  where
  private
    module D = Category D using (_⋆_)
  preservesCartNatTrans : Type _
  preservesCartNatTrans = Σ[ swap ∈ NatIso (G ∘F F) (F' ∘F G) ]
    (∀ Γ → (swap .trans ⟦ Γ ⟧ D.⋆ π' ⟦ G ⟅ Γ ⟆ ⟧) ≡ G ⟪ π ⟦ Γ ⟧ ⟫)
