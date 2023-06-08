{-# OPTIONS --safe #-}
{-
   Monads as extension systems,
   i.e., in terms of unit and bind, deriving the rest of the structure
   https://ncatlab.org/nlab/show/extension+system
-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Comonad.ExtensionSystem where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Monad.Base
import Cubical.Categories.Monad.ExtensionSystem as MES

private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') where
  open Category
  private
    variable
      a b c : C .ob
      f g h : C [ a , b ]

  -- record ExtensionSystemFor (D : C .ob → C .ob) : Type (ℓ-max ℓ ℓ') where
  --   field
  --     ε : C [ D a , a ]
  --     extend : C [ D a , b ] → C [ D a , D b ]
  --     extend-l : extend (ε {a = a}) ≡ C .id
  --     extend-r : ε ∘⟨ C ⟩ extend f ≡ f
  --     extend-comp : extend f ∘⟨ C ⟩ extend g ≡ extend (f ∘⟨ C ⟩ extend g)

  ExtensionSystemFor = MES.ExtensionSystemFor (C ^op)
  ExtensionSystem = MES.ExtensionSystem (C ^op)

  COMONAD : Category _ _
  COMONAD = (MES.MONAD (C ^op)) ^op

  ComonadMorphism = COMONAD .Hom[_,_]
  ComonadMorphism≡ = MES.MonadMorphism≡ (C ^op)


  module _ (E : ExtensionSystem) where
    Kleisli : Category _ _
    Kleisli = (MES.Kleisli (C ^op) E) ^op

    F : Functor Kleisli C
    F = (MES.G (C ^op) E) ^opF

    open import Cubical.Categories.Adjoint.UniversalElements
    G : RightAdjoint _ _ F
    G = MES.F (C ^op) E

  pull : {T T' : ExtensionSystem} → ComonadMorphism T T' →
         Functor (Kleisli T') (Kleisli T)
  pull {T}{T'} ϕ = (MES.push (C ^op) ϕ) ^opF

  open Functor

  -- not sure why pushId doesn't work here
  pullId : {T : ExtensionSystem} → pull (COMONAD .id {T}) ≡ Id
  pullId = Functor≡ (λ c → refl) λ f → C .⋆IdL _

  pullComp : {T T' T'' : ExtensionSystem} (ϕ' : COMONAD [ T' , T'' ])
             (ϕ : COMONAD [ T , T' ]) →
             pull (ϕ' ∘⟨ COMONAD ⟩ ϕ) ≡ (pull ϕ ∘F pull ϕ')
  pullComp ϕ' ϕ = Functor≡ (λ _ → refl) (λ f → (C .⋆Assoc _ _ _))
