{-# OPTIONS --type-in-type #-} -- Max's favorite
module HyperDoc.SimpleDGP where 

open import Cubical.Data.Empty
import Cubical.Data.Equality as Eq
open import Cubical.Data.FinData 
open import Cubical.Data.Nat 
open import Cubical.Data.Sigma hiding (I)
open import Cubical.Data.Sum
open import Cubical.Data.Unit

open import Cubical.Foundations.Prelude hiding (I ; J)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure 

open import Cubical.Categories.Category 
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monoidal
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf

open Category 
open Functor
open NatTrans

-- big dumb stupid
_+C_ : Category _ _ → Category _ _ → Category _ _ 
(C +C D) .ob = C .ob ⊎ D .ob
Hom[ C +C D , inl c ] (inl c') = C [ c , c' ]
Hom[ C +C D , inl _ ] (inr _) = ⊥
Hom[ C +C D , inr _ ] (inl _) = ⊥
Hom[ C +C D , inr d ] (inr d') = D [ d , d' ]
(C +C D) .id {inl x} = C .id
(C +C D) .id {inr x} = D .id
_⋆_ (C +C D) {inl x} {inl x₁} {inl x₂} = _⋆_ C
_⋆_ (C +C D) {inl x} {inl x₁} {inr x₂} = λ f₁ ()
_⋆_ (C +C D) {inl x} {inr x₁} {z} = λ ()
_⋆_ (C +C D) {inr x} {inl x₁} {z} = λ ()
_⋆_ (C +C D) {inr x} {inr x₁} {inl x₂} = λ f₁ ()
_⋆_ (C +C D) {inr x} {inr x₁} {inr x₂} = _⋆_ D
(C +C D) .⋆IdL {inl x} {inl x₁} = ⋆IdL C 
(C +C D) .⋆IdL {inl x} {inr x₁} = λ ()
(C +C D) .⋆IdL {inr x} {inl x₁} = λ ()
(C +C D) .⋆IdL {inr x} {inr x₁} = ⋆IdL D
(C +C D) .⋆IdR {inl x} {inl x₁} = ⋆IdR C
(C +C D) .⋆IdR {inl x} {inr x₁} = λ ()
(C +C D) .⋆IdR {inr x} {inl x₁} = λ ()
(C +C D) .⋆IdR {inr x} {inr x₁} = ⋆IdR D
(C +C D) .⋆Assoc {inl x} {inl x₁} {inl x₂} {inl x₃} = ⋆Assoc C
(C +C D) .⋆Assoc {inl x} {inl x₁} {inl x₂} {inr x₃} = λ f₁ g ()
(C +C D) .⋆Assoc {inl x} {inl x₁} {inr x₂} {w} = λ f₁ ()
(C +C D) .⋆Assoc {inl x} {inr x₁} {z} {w} = λ ()
(C +C D) .⋆Assoc {inr x} {inl x₁} {z} {w} = λ ()
(C +C D) .⋆Assoc {inr x} {inr x₁} {inl x₂} {w} = λ f₁ ()
(C +C D) .⋆Assoc {inr x} {inr x₁} {inr x₂} {inl x₃} = λ f₁ g ()
(C +C D) .⋆Assoc {inr x} {inr x₁} {inr x₂} {inr x₃} = ⋆Assoc D
(C +C D) .isSetHom {inl x} {inl x₁} = isSetHom C
(C +C D) .isSetHom {inl x} {inr x₁} = λ ()
(C +C D) .isSetHom {inr x} {inl x₁} = λ ()
(C +C D) .isSetHom {inr x} {inr x₁} = isSetHom D

⊥C : Category _ _ 
⊥C .ob = ⊥
⊥C .Hom[_,_] ()
⊥C .id {()}
⊥C ._⋆_  {()}
⊥C .⋆IdL  {()}
⊥C .⋆IdR  {()}
⊥C .⋆Assoc  {()}
⊥C .isSetHom  {()}


⊤C : Category _ _ 
⊤C .ob = Unit
⊤C .Hom[_,_] tt tt = Unit
⊤C .id = tt
⊤C ._⋆_ tt tt = tt
⊤C .⋆IdL _ = refl
⊤C .⋆IdR _ = refl
⊤C .⋆Assoc _ _ _ = refl
⊤C .isSetHom = isSetUnit

!⊤C : {C : Category _ _} → Functor C ⊤C 
!⊤C .F-ob = λ _ → tt
!⊤C .F-hom = λ _ → tt
!⊤C .F-id = refl
!⊤C .F-seq _ _ = refl

+n : ℕ → Category _ _ → Category _ _ 
+n zero C = ⊤C
+n one C = C
+n (suc (suc n)) C = C +C +n (suc n) C

_L⋆_ : ℕ → Category _ _ → Category _ _
_L⋆_ n C .ob = Σ[ i ∈ Fin n ] C .ob
_L⋆_ n C .Hom[_,_] (i , c)(j , c') = (i Eq.≡ j) × (C [ c , c' ])
_L⋆_ n C .id = Eq.refl , (C .id)
_L⋆_ n C ._⋆_ (Eq.refl , f)(Eq.refl , g) = Eq.refl , ((C ⋆ f) g)
_L⋆_ n C .⋆IdL (Eq.refl , f) = ΣPathP (refl , C .⋆IdL f)
_L⋆_ n C .⋆IdR (Eq.refl , f) = ΣPathP (refl , C .⋆IdR f)
_L⋆_ n C .⋆Assoc (Eq.refl , f) (Eq.refl , g) (Eq.refl , h)=  
  ΣPathP (refl , C .⋆Assoc f g h)
_L⋆_ n C .isSetHom = isSet×  {!   !} (C .isSetHom)

∇ : {C : Category _ _ } → (n : ℕ) → Functor (n L⋆ C) C 
∇ {C} n .F-ob = snd
∇ {C} n .F-hom = snd
∇ {C} n .F-id = refl
∇ {C} n .F-seq (Eq.refl , f)(Eq.refl , g) = refl

!∇ : (C : Category _ _ ) → Functor (0 L⋆ C) C
!∇ C .F-ob ()
!∇ C .F-hom {()} 
!∇ C .F-id {()} 
!∇ C .F-seq {()}

∐-map : (n : ℕ) → (C : Category _ _ ) → Functor (n L⋆ C) (+n n C) 
∐-map zero C = !⊤C ∘F (!∇ C)
∐-map one C = ∇ one
∐-map (suc (suc n)) C = {!   !}

-- Discete Genrealized Monomial
record Mon (I J : Category _ _ ) : Type where 
  field  
    {C} : Category _ _
    {n}  : ℕ
    f : Functor (n L⋆ C) I
    g : Functor C J