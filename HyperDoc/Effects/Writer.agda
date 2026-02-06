module HyperDoc.Effects.Writer where 


open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base 

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.EilenbergMoore
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Monad.ExtensionSystem hiding (F ; push)

open import Cubical.Data.Sigma

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure 


open ExtensionSystemFor

module Writer {ℓS : Level}{M : Monoid ℓS} where

  open MonoidStr (M .snd)

  W' : ExtensionSystem (SET ℓS) 
  W' .fst X = ⟨ M ⟩ × ⟨ X ⟩ , isSet× is-set (X .snd)
  W' .snd .η x = ε , x
  W' .snd .bind f (w , a) = (w · f a .fst) , (f a .snd)
  W' .snd .bind-r = funExt λ (w , a) → ΣPathP (·IdR  w , refl)
  W' .snd .bind-l = funExt λ w → ΣPathP ((·IdL _) , refl)
  W' .snd .bind-comp = funExt λ (w , a) → ΣPathP ((sym (·Assoc _ _ _)) , refl)

  W : Monad (SET ℓS) 
  W = ExtensionSystem→Monad  _ W'

  F : Functor (SET ℓS) (SET ℓS) 
  F = W .fst

  EM : Category (ℓ-suc ℓS) ℓS 
  EM = EMCategory W