-- The co-Eilenberg–Moore category of a comonad
module Cubical.Categories.Displayed.Instances.CoEilenbergMoore where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Algebras
open import Cubical.Categories.Displayed.Instances.Coalgebras
open import Cubical.Categories.Displayed.Instances.StructureOver
open import Cubical.Categories.Instances.TotalCategory

private
  variable ℓC ℓC' : Level

-- A comonad is given by its underlying endofunctor together with
-- counit and comultiplication
-- TODO package this up into a single type like Monad, or use Monad in the
-- opposite category
module _ {C : Category ℓC ℓC'} (W : Functor C C)
  (ε : ∀ x → C [ Functor.F-ob W x , x ])
  (δ : ∀ x → C [ Functor.F-ob W x , Functor.F-ob W (Functor.F-ob W x) ])
  where

  private
    module C = Category C
    module W = Functor W

  --   ε x ∘ α ≡ id          (counit law)
  --   W α ∘ α ≡ δ x ∘ α      (comultiplication law)
  coEMStructureOver : StructureOver (∫C (CoAlgCatᴰ W)) ℓC' ℓ-zero
  StructureOver.ob[_] coEMStructureOver (x , α) =
    (α C.⋆ ε x ≡ C.id)
      × (α C.⋆ δ x ≡ α C.⋆ W.F-hom α)
  StructureOver.Hom[_][_,_] coEMStructureOver _ _ _ = Unit
  StructureOver.idᴰ coEMStructureOver = tt
  StructureOver._⋆ᴰ_ coEMStructureOver _ _ = tt
  StructureOver.isPropHomᴰ coEMStructureOver = isPropUnit

  coEMCatᴰ : Categoryᴰ (∫C (CoAlgCatᴰ W)) ℓC' ℓ-zero
  coEMCatᴰ = StructureOver→Catᴰ coEMStructureOver

  coEMCategory : Category (ℓ-max ℓC ℓC') (ℓ-max ℓC' ℓC')
  coEMCategory = (∫C coEMCatᴰ) ^op

module _ {C : Category ℓC ℓC'} {W : Functor C C}
  {ε : ∀ x → C [ Functor.F-ob W x , x ]}
  {δ : ∀ x → C [ Functor.F-ob W x , Functor.F-ob W (Functor.F-ob W x) ]}
  where

  coEMHom≡ : {X Y : Category.ob (coEMCategory W ε δ)}
    {f g : coEMCategory W ε δ [ X , Y ]}
    → f .fst .fst ≡ g .fst .fst → f ≡ g
  coEMHom≡ p = ΣPathP
    (Σ≡Prop (λ _ → hasPropHomsStructureOver (AlgStructureOver (W ^opF)) _ _ _) p
    , refl)
