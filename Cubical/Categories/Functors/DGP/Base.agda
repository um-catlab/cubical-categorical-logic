{-# OPTIONS --type-in-type #-} -- Max's favorite
module Cubical.Categories.Functors.DGP.Base where 

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
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monoidal
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.KanExtension
open import Cubical.Categories.Presheaf.Constructions.Reindex using (reindPshF)

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

_L⋆_ : ℕ → Category _ _ → Category _ _
_L⋆_ n C .ob = Σ[ i ∈ Fin n ] C .ob
_L⋆_ n C .Hom[_,_] (i , c)(j , c') = (i Eq.≡ j) × (C [ c , c' ])
_L⋆_ n C .id = Eq.refl , (C .id)
_L⋆_ n C ._⋆_ (Eq.refl , f)(Eq.refl , g) = Eq.refl , ((C ⋆ f) g)
_L⋆_ n C .⋆IdL (Eq.refl , f) = ΣPathP (refl , C .⋆IdL f)
_L⋆_ n C .⋆IdR (Eq.refl , f) = ΣPathP (refl , C .⋆IdR f)
_L⋆_ n C .⋆Assoc (Eq.refl , f) (Eq.refl , g) (Eq.refl , h)=  
  ΣPathP (refl , C .⋆Assoc f g h)
_L⋆_ n C .isSetHom = isSet×  {! !} (C .isSetHom)

-- Discete Genrealized Monomial
record Mon (I J : Category _ _ ) : Type where 
  field  
    {B} : Category _ _
    {n}  : ℕ
    s : Functor (n L⋆ B) I
    t : Functor B J

  Δs : Functor (PresheafCategory I _) (PresheafCategory (n L⋆ B) _) 
  Δs = reindPshF s

  Σt : Functor (PresheafCategory B _) (PresheafCategory J _) 
  Σt = Lan.Lan _ t
 
  Π∇ : Functor ((PresheafCategory (n L⋆ B) _)) ((PresheafCategory B _)) 
  Π∇ .F-ob X .F-ob b .fst = (i : Fin n) → X .F-ob  (i , b) .fst
  Π∇ .F-ob X .F-ob b .snd = isSetΠ λ x → X .F-ob (x , b) .snd
  Π∇ .F-ob X .F-hom {b}{b'} f xfam i = X .F-hom (Eq.refl , f) (xfam i)
  Π∇ .F-ob X .F-id i xfam j = X .F-id i (xfam j)
  Π∇ .F-ob X .F-seq {b}{b'}{b''} f g i xfam j = X .F-seq (Eq.refl , f) (Eq.refl , g) i (xfam j)
  Π∇ .F-hom {X} {Y} nt .N-ob b xfam i = N-ob nt (i , b) (xfam i)
  Π∇ .F-hom {X} {Y} nt .N-hom {b}{b'} f i xfam j = nt .N-hom (Eq.refl , f) i (xfam j)
  Π∇ .F-id = refl
  Π∇ .F-seq nt nt' = refl

  F : Functor (PresheafCategory I _) (PresheafCategory J _) 
  F = (Σt ∘F Π∇) ∘F Δs

exProd : {C : Category _ _ } → Mon (C +C C) C 
exProd {C} .Mon.B = C
exProd {C} .Mon.n = 2
exProd {C} .Mon.s .F-ob (zero , c) = inl c
exProd {C} .Mon.s .F-ob (one , c) = inr c
exProd {C} .Mon.s .F-hom {zero , c}{zero , c'} (Eq.refl , f) = f
exProd {C} .Mon.s .F-hom {one , c}{one , c'} (Eq.refl , f) = f
exProd {C} .Mon.s .F-id {zero , c} = refl
exProd {C} .Mon.s .F-id {one , c} = refl
exProd {C} .Mon.s .F-seq {zero , c} {zero , c'} {zero , c''} 
  (Eq.refl , snd₁) (Eq.refl , snd₂) = refl
exProd {C} .Mon.s .F-seq {one , c} {one , c'} {one , c''} 
  (Eq.refl , snd₁) (Eq.refl , snd₂) = refl
exProd {C} .Mon.t = Id

Prod : {C : Category _ _ } → 
  Functor (PresheafCategory (C +C C) ℓ-zero) (PresheafCategory C ℓ-zero) 
Prod {C} = Mon.F (exProd {C})

record DGP (I J : Category _ _) : Type where
  field
    K'  : hSet _
    mon : K' .fst → Mon I J

  P-ob : PresheafCategory I _ .ob → PresheafCategory J _ .ob
  P-ob X .F-ob j .fst = Σ[ k ∈ K' .fst ] Mon.F (mon k) .F-ob X .F-ob j .fst
  P-ob X .F-ob j .snd = isSetΣ (K' .snd) λ k → Mon.F (mon k) .F-ob X .F-ob j .snd
  P-ob X .F-hom {j} {j'} f (k , m) = k , Mon.F (mon k) .F-ob X .F-hom f m
  P-ob X .F-id =
    funExt λ (k , m) →
      ΣPathP
        ( refl
        , λ i →
            Mon.F (mon k) .F-ob X .F-id i m
        )
  P-ob X .F-seq f g =
    funExt λ (k , m) →
      ΣPathP
        ( refl
        , λ i →
            Mon.F (mon k) .F-ob X .F-seq f g i m
        )

  P-hom :
    {X Y : PresheafCategory I _ .ob} →
    NatTrans X Y →
    NatTrans (P-ob X) (P-ob Y)
  P-hom nt .N-ob j (k , m) = k , Mon.F (mon k) .F-hom nt .N-ob j m
  P-hom nt .N-hom {j} {j'} f =
    funExt λ (k , m) →
      ΣPathP
        ( refl
        , funExt⁻
            (Mon.F (mon k) .F-hom nt .N-hom f)
            m
        )

  P :
    Functor
      (PresheafCategory I _)
      (PresheafCategory J _)

  P .F-ob = P-ob
  P .F-hom = P-hom

  P .F-id {X} =
    makeNatTransPath (funExt λ j → funExt λ (k , m) → 
      ΣPathP (refl , funExt⁻
        (cong (λ nt → nt .N-ob j)
          (Mon.F (mon k) .F-id)) m))

  P .F-seq {X} {Y} {Z} nt nt' =
    makeNatTransPath (funExt λ j →
        funExt λ (k , m) → 
        ΣPathP (refl , funExt⁻
      (cong (λ α → α .N-ob j)
        (Mon.F (mon k) .F-seq nt nt'))
      m))




{-}
+n : ℕ → Category _ _ → Category _ _ 
+n zero C = ⊤C
+n one C = C
+n (suc (suc n)) C = C +C +n (suc n) C
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
-}