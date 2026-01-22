{-

  Simple categories with families are one approach to modeling the
  judgmental structure of simply typed lambda calculus.

  Definition 9 in https://arxiv.org/abs/1904.00827

-}
module Cubical.Categories.WithFamilies.Simple.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.More

open Category
open UniversalElement

private
  variable
    ℓC ℓC' ℓT ℓT' ℓD ℓD' ℓS ℓS' : Level

-- Design choice: should the terminal object and context extension be
-- separate structure? More like a "cartesian" SCwF?
record SCwF (ℓC ℓC' ℓT ℓT' : Level) : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-suc ℓC) (ℓ-suc ℓC')) (ℓ-suc ℓT)) (ℓ-suc ℓT')) where
  field
    C : Category ℓC ℓC'
    Ty : Type ℓT
    Tm : Ty → Presheaf C ℓT'
    term : Terminal' C
    -- "Simple comprehension"
    ext : ∀ A → LocallyRepresentable (Tm A)

  module C = Category C
  module Tm {A} = PresheafNotation (Tm A)
  module term = TerminalNotation term
  module _ (A : Ty) (Γ : C.ob) where
    module ext = UniversalElementNotation (ext A Γ)

  Tm[_,_] : (Γ : C.ob)(A : Ty) → Type ℓT'
  Tm[ Γ , A ] = Tm.p[_] {A} Γ 
    
  [_] : Ty → C.ob
  [ A ] = ext A (term .vertex) .vertex

  TmUE : ∀ A → UniversalElement C (Tm A)
  TmUE A .vertex = [ A ]
  TmUE A .element = ext A _ .element .snd
  TmUE A .universal Γ = isIsoToIsEquiv
    ( (λ M → ext.intro A _ (term.!t , M))
    , (λ M → PathPΣ (ext.β _ _) .snd)
    , (λ *,M → ext.intro≡ _ _ (ΣPathP (term.𝟙extensionality , refl))))

  TmRepr : ∀ A → PshIso (C [-, [ A ] ]) (Tm A)
  TmRepr A =
    yoRecIso (ext A _)
    ⋆PshIso ×PshIso (yoRecIso term) idPshIso
    ⋆PshIso lUnit×PshIso (Tm A)
