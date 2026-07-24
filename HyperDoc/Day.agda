{-# OPTIONS --type-in-type #-} -- Max's favorite
module HyperDoc.Day where 

open import Cubical.Data.Empty
import Cubical.Data.Equality as Eq
open import Cubical.Data.FinData 
open import Cubical.Data.Nat 
open import Cubical.Data.Sigma hiding (I)
open import Cubical.Data.Sum

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

Psh : Category _ _ →  Category _ _ 
Psh C = PresheafCategory C _

record GPoly : Type _ where 
  field 
    I E B J : Category _ _ 
    s : Functor E I 
    f : Functor E B
    t : Functor B J

  s^* : Functor (Psh I) (Psh E) 
  s^* = precomposeF (SET _) (s ^opF)

  open Ran _ f
  f_* : Functor (Psh E)  (Psh B) 
  f_* = Ran

  open Lan _ t 
  t_!  : Functor (Psh B) (Psh J ) 
  t_! = Lan

  den : Functor (Psh I) (Psh J) 
  den = (t_! ∘F f_*) ∘F s^*

open GPoly
-- Restricted class with nicer properties
-- Discrete Generalized Polynomial Functors

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

-- Discete Genrealized Monomial
record Mon (I J : Category _ _ ) : Type where 
  field  
    {C} : Category _ _
    {n}  : ℕ
    f : Functor (n L⋆ C) I
    g : Functor C J


MonToGPoly : {I J : Category _ _ } → Mon I J → GPoly 
MonToGPoly {I} m .I = I
MonToGPoly m .E = Mon.n m L⋆ Mon.C m
MonToGPoly m .B = Mon.C m
MonToGPoly {_} {J} m .J = J
MonToGPoly m .s = Mon.f m
MonToGPoly m .f = ∇ (Mon.n m)
MonToGPoly m .t = Mon.g m

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

module _ (M : MonoidalCategory _ _ ) where 
  open MonoidalCategory M

  𝓟 = Psh C

  f'  : Functor (2 L⋆ (C ×C C)) (C +C C)
  f' .F-ob (zero , p) = inl (fst p)
  f' .F-ob (one , p) = inr (snd p)
  f' .F-hom {zero , _} {zero , _} (Eq.refl , f , g) = f
  f' .F-hom {one , _} {one , _} (Eq.refl , f , g) = g
  f' .F-id {zero , _} = refl
  f' .F-id {one , _} = refl
  f' .F-seq {zero , _}{zero , _ }{zero , _} (Eq.refl , f) (Eq.refl , g) = refl
  f' .F-seq {one , _}{one , _ }{one , _} (Eq.refl , f) (Eq.refl , g) = refl


  DayMon : Mon (C +C C) C 
  DayMon .Mon.C = C ×C C
  DayMon .Mon.n = 2
  DayMon .Mon.f = f'
  DayMon .Mon.g = ─⊗─

  DayConv' : Functor (Psh (C +C C)) 𝓟 
  DayConv' = den (MonToGPoly DayMon)

  -- An iso
  convert : Functor (𝓟 ×C 𝓟) (Psh (C +C C))
  convert .F-ob (P , Q) .F-ob (inl x) = P .F-ob x
  convert .F-ob (P , Q) .F-ob (inr x) = Q .F-ob x
  convert .F-ob (P , Q) .F-hom {inl x} {inl x₁} = P .F-hom
  convert .F-ob (P , Q) .F-hom {inl x} {inr x₁} = λ ()
  convert .F-ob (P , Q) .F-hom {inr x} {inl x₁} = λ ()
  convert .F-ob (P , Q) .F-hom {inr x} {inr x₁} = Q .F-hom
  convert .F-ob (P , Q) .F-id {inl x} = P .F-id
  convert .F-ob (P , Q) .F-id {inr x} = Q .F-id
  convert .F-ob (P , Q) .F-seq {inl x} {inl x₁} {inl x₂} = P .F-seq
  convert .F-ob (P , Q) .F-seq {inl x} {inl x₁} {inr x₂} = λ f₁ ()
  convert .F-ob (P , Q) .F-seq {inl x} {inr x₁} {z} = λ ()
  convert .F-ob (P , Q) .F-seq {inr x} {inl x₁} {z} = λ ()
  convert .F-ob (P , Q) .F-seq {inr x} {inr x₁} {inl x₂} = λ f₁ ()
  convert .F-ob (P , Q) .F-seq {inr x} {inr x₁} {inr x₂} = Q .F-seq
  convert .F-hom (n , m) .N-ob (inl x) = N-ob n x
  convert .F-hom (n , m) .N-ob (inr x) = N-ob m x
  convert .F-hom (n , m) .N-hom {inl x} {inl x₁} = N-hom n
  convert .F-hom (n , m) .N-hom {inl x} {inr x₁} = λ ()
  convert .F-hom (n , m) .N-hom {inr x} {inl x₁} = λ ()
  convert .F-hom (n , m) .N-hom {inr x} {inr x₁} = N-hom m
  convert .F-id = makeNatTransPath (funExt λ {(inl x) → refl
                                            ; (inr x) → refl})
  convert .F-seq f g = makeNatTransPath (funExt λ {(inl x) → refl
                                                 ; (inr x) → refl})

  DayConv : Functor (𝓟 ×C 𝓟) 𝓟
  DayConv = DayConv' ∘F convert
