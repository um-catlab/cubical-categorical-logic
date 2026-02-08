module HyperDoc.CBPVModel where 

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure 

open import Cubical.Categories.Category 
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Constructions.Unit

open import HyperDoc.Lib
open import Cubical.Data.List using (_∷_ ; [])

open Category
open Functor

record Model (ℓV ℓV' ℓC ℓC' ℓS : Level) : Type (levels (ℓsuc (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ []))) where 
  field 
    V : Category ℓV ℓV' 
    C : Category ℓC ℓC' 
    O : Functor ((V ^op) ×C C) (SET ℓS) 

  O[_,-] : (v : ob V) → Functor C (SET ℓS)
  O[_,-] v = O ∘F rinj _ _ v

  O[-,_] : (c : ob C) → Functor (V ^op) (SET ℓS)
  O[-,_] c = O ∘F linj _ _ c

  O[_,_] : ob V → ob C → Type ℓS
  O[_,_] v c = ⟨ O .F-ob (v , c)⟩

  lcomp : ∀{v v' c} → V [ v , v' ] → O[ v' , c ] → O[ v , c ] 
  lcomp f o = O .F-hom (f , (C .id)) o

  rcomp : ∀{v c c'} → O[ v , c ] → C [ c , c' ] → O[ v , c' ] 
  rcomp o g = O .F-hom ((V .id) , g) o
  

module _
  {ℓV ℓV' ℓC ℓC' ℓS : Level}
  (M : Model ℓV ℓV' ℓC ℓC' ℓS ) where 

  open Model M

  HasV⊤ : Type (ℓ-max ℓV ℓV') 
  HasV⊤ = Σ[ ⊤ ∈ ob V ] PshIso (V [-, ⊤ ]) (Unit*Psh {ℓ'' = ℓV'})

  HasV+ : Type (ℓ-max (ℓ-max (ℓ-max ℓV ℓC) ℓC') ℓS) 
  HasV+  = (A A' : ob V) → Σ[ A+A' ∈ ob V ] PshIso (O[ A+A' ,-] ∘F from^op^op) ((O[ A ,-] ∘F from^op^op) ×Psh (O[ A' ,-] ∘F from^op^op))

  HasUTy : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓV ℓV') ℓC) ℓC') ℓS) 
  HasUTy = Σ[ U ∈ Functor C V ] ∀ (B : ob C) → PshIso O[-, B ] (V [-, U .F-ob B ])

  HasFTy : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓV ℓV') ℓC) ℓC') ℓS) 
  HasFTy = Σ[ F ∈ Functor V C ] (∀ (A : ob V) → PshIso (O[ A ,-] ∘F from^op^op) ((C [ F .F-ob A ,-]) ∘F from^op^op))

  HasC× : Type (ℓ-max ℓC ℓC') 
  HasC× = (B B' : ob C) → Σ[ B×B' ∈ ob C ] PshIso (C [-, B×B' ]) ((C [-, B ]) ×Psh (C [-, B' ]))