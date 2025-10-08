module Cubical.Categories.Instances.FinSets.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function as Func
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors

open import Cubical.Categories.Category renaming (pathToIso to catPathToIso)
open import Cubical.Categories.WithFamilies.Simple
open import Cubical.Categories.WithFamilies.Simple.Instances.Democratic
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Instances.FinSets.Base
open import Cubical.Categories.Instances.FinSets.Base
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Constructions.TotalCategory

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level

open Categoryᴰ
open UniversalElement

-- U : Functor (FINSET {ℓ}) (SET ℓ)
-- U = {!!}

-- TODO i can probably derive these by giving
-- a displayed CCCⱽ structure over SET's trivial display
-- Then FINSET should arise as the reindexing of
-- that along U
TerminalFINSET : Terminal' (FINSET {ℓ})
TerminalFINSET =
  record {
    vertex = 𝟙 , isFinite𝟙 ;
    element = tt ;
    universal = λ A → isoToIsEquiv (iso (λ _ → tt) (λ _ → (λ _ → tt*) , tt) (λ _ → refl) λ _ → refl) }
  where
  open TerminalNotation TerminalSET
  isFinite𝟙 : isFinSet ⟨ 𝟙 ⟩
  isFinite𝟙 = isFinSetLift isFinSetUnit

BinProductFINSET : BinProducts (FINSET {ℓ})
BinProductFINSET (A , B) = record {
    vertex = vert , isFinSet× (⟨ A .fst ⟩ , A .snd) (⟨ B .fst ⟩ , B .snd) ;
    element = ((λ z → z .fst) , tt) , (λ z → z .snd) , tt ;
    universal = λ C → isoToIsEquiv (iso _ _ (λ _ → refl) λ _ → refl) }
  where
  open BinProductNotation (BinProductsSET (A .fst , B .fst))

FINSETCartesianCategory : CartesianCategory _ ℓ
FINSETCartesianCategory .CartesianCategory.C = FINSET
FINSETCartesianCategory .CartesianCategory.term = TerminalFINSET
FINSETCartesianCategory .CartesianCategory.bp = BinProductFINSET

FINSETSCwF : SCwF (ℓ-suc ℓ) ℓ (ℓ-suc ℓ) ℓ
FINSETSCwF = CartesianCategory→SCwF FINSETCartesianCategory

TerminalFINSET^op : Terminal' (FINSET^op {ℓ})
TerminalFINSET^op .vertex = (⊥* , (λ ())) , isFinSetLift isFinSet⊥
TerminalFINSET^op .element = tt
TerminalFINSET^op .universal A =
  isoToIsEquiv (iso (λ _ → tt) (λ _ → (λ ()) , _) (λ _ → refl) λ a → ΣPathP ((funExt λ ()) , (isContrUnit .snd tt)))

open Category

BinProductFINSET^op : BinProducts (FINSET^op {ℓ})
BinProductFINSET^op (A , B) .vertex =
  (_ , isFinSet→isSet (isFinSet⊎ ⟨ A ⟩fs ⟨ B ⟩fs)) ,
  isFinSet⊎ ⟨ A ⟩fs ⟨ B ⟩fs
BinProductFINSET^op (A , B) .element .fst = inl , tt
BinProductFINSET^op (A , B) .element .snd = inr , tt
BinProductFINSET^op (A , B) .universal C =
  isoToIsEquiv
    (iso
      (λ x → (x .fst Func.∘ inl  , _) , x .fst Func.∘ inr , _)
      (λ x → Sum.elim (x .fst .fst) (x .snd .fst) , _)
      (λ x → refl)
      λ x → ≡-× (funExt λ { (inl a) → refl ; (inr b) → refl}) (isContrUnit .snd _))

FINSET^opCartesianCategory : CartesianCategory _ ℓ
FINSET^opCartesianCategory .CartesianCategory.C = FINSET^op
FINSET^opCartesianCategory .CartesianCategory.term = TerminalFINSET^op
FINSET^opCartesianCategory .CartesianCategory.bp = BinProductFINSET^op

FINSET^opSCwF : SCwF (ℓ-suc ℓ) ℓ (ℓ-suc ℓ) ℓ
FINSET^opSCwF = CartesianCategory→SCwF FINSET^opCartesianCategory
