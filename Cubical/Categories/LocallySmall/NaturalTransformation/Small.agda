module Cubical.Categories.LocallySmall.NaturalTransformation.Small where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Reflection.RecordEquiv.More

import Cubical.Categories.Category as Small
open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.Variables

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties

open Category
open Categoryᴰ

-- To make a small type of natural transformations, we need
-- 1. C to have a small type of objects and a global universe level of all homs (i.e., a Small Category)
-- 2. D to have a global universe level
module _ {C : SmallCategory ℓC ℓC'} where
  private
    module C = SmallCategory C
  record NatTrans
    {D : GloballySmallCategory Dob ℓD'}
    (F G : Functor C.cat D)
    : Type (ℓ-max ℓC $ ℓ-max ℓC' $ ℓD')
    where
    no-eta-equality
    constructor natTrans
    private
      module F = FunctorNotation F
      module G = FunctorNotation G
      module D = CategoryNotation D
    field
      N-ob : ∀ x → D.Hom[ F.F-ob (liftω x) , G.F-ob (liftω x) ]
      N-hom : ∀ {x y}(f : C.Hom[ liftω x , liftω y ])
        → (F.F-hom f D.⋆ N-ob y) ≡ (N-ob x D.⋆ G.F-hom f)
-- open NatTrans

module _ {C : SmallCategory ℓC ℓC'}{D : GloballySmallCategory Dob ℓD'} where
  private
    module C = SmallCategory C
    module D = CategoryNotation D

  open NatTrans
  idTrans : (F : Functor C.cat D) → NatTrans F F
  idTrans F = natTrans (λ x → D.id) (λ f → D.⋆IdR _ ∙ (sym $ D.⋆IdL _))
    where module F = Functor F

  seqTrans :
    {F G H : Functor C.cat D}
    (α : NatTrans F G)
    (β : NatTrans G H)
    → NatTrans F H
  seqTrans α β = natTrans
    (λ x → α .N-ob x D.⋆ β .N-ob x)
    λ f → sym (D.⋆Assoc _ _ _)
      ∙ D.⟨ α .N-hom f ⟩⋆⟨⟩
      ∙ D.⋆Assoc _ _ _
      ∙ D.⟨⟩⋆⟨ β .N-hom f ⟩
      ∙ sym (D.⋆Assoc _ _ _)

  module _ (F G : Functor C.cat D) where
    private
      module F = Functor F
      module G = Functor G
    NatTransIsoΣ :
      Iso (NatTrans F G)
          (Σ[ N-ob ∈ (∀ x → D.Hom[ F.F-ob (liftω x) , G.F-ob (liftω x) ]) ]
            (∀ {x y}(f : C.Hom[ liftω x , liftω y ])
             → (F.F-hom f D.⋆ N-ob y) ≡ (N-ob x D.⋆ G.F-hom f)))
    unquoteDef NatTransIsoΣ = defineRecordIsoΣ NatTransIsoΣ (quote (NatTrans))

  makeNatTransPath : ∀ {F G : Functor C.cat D}
    {α β : NatTrans F G}
    → α .N-ob ≡ β .N-ob
    → α ≡ β
  makeNatTransPath {α = α}{β} α≡β = isoFunInjective (NatTransIsoΣ _ _) α β
    (ΣPathPProp (λ _ → isPropImplicitΠ2 (λ _ _ → isPropΠ (λ _ → D.isSetHom _ _)))
    α≡β)
