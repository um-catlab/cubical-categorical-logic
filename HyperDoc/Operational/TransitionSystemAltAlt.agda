module HyperDoc.Operational.TransitionSystemAltAlt where

open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty renaming (elim to ⊥elim)
open import Cubical.Data.Maybe renaming (rec to mrec)
open import Cubical.Data.Maybe.More
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.Sum renaming (rec to rec⊎)
open import Cubical.Data.Unit

open import Cubical.Relation.Nullary

open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Preorders.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.FullSubcategory 

open Category
open Functor
open Iso


TS : Type _
TS = Σ[ S ∈ Type ] (S → S → Type) 

isFin : TS → Type 
isFin (S , R) = (s : S) → Σ[ n ∈ ℕ ] Iso (Σ[ s' ∈ S ] R s s') (Fin n)

TSHom :  TS → TS → Type _ 
TSHom (A , A↦) (B , B↦)  = Σ[ f ∈ (A → B) ] (∀{a a'} → A↦ a a' → B↦ (f a) (f a'))


TSysCat : Category _ _ 
TSysCat .ob = TS
TSysCat .Hom[_,_] = TSHom 
TSysCat .id = (λ x → x) , λ x → x
TSysCat ._⋆_ (f , prf) (g , prf') = (λ x → g (f x)) , λ z → prf' (prf z)
TSysCat .⋆IdL _ = refl
TSysCat .⋆IdR _ = refl
TSysCat .⋆Assoc _ _ _ = refl
TSysCat .isSetHom = {!   !} 

TSysFinCat : Category _ _ 
TSysFinCat = FullSubcategory TSysCat isFin


data NatEx : Type where
  num : ℕ → NatEx 
  plus : NatEx → NatEx → NatEx

-- finite powerset
-- https://github.com/um-catlab/cbpv-functorial-opsem/blob/44006aa2a45918ec664b1382c478fc1c733944ae/agda/src/PFin.agda#L6
data Rel : NatEx → NatEx → Type where 
  radd : ∀ {n m } → Rel (plus (num n) (num m)) (num (n + m)) 
  rstepL : ∀ {l l' r } → 
    Rel l l'  → 
    Rel (plus l r) (plus l' r) 
  rstepR : ∀ {l  r r' n} → 
    Rel r r'  → 
    Rel (plus (num n) r) (plus (num n) r')

ex : ob TSysFinCat
ex .fst .fst = NatEx
ex .fst .snd = Rel
ex .snd (num x) .fst = 0
ex .snd (num x) .snd .fun ()
ex .snd (num x) .snd .inv ()
ex .snd (num x) .snd .sec ()
ex .snd (num x) .snd .ret ()
ex .snd (plus s s₁) = {!  !}

{-
-- labeled transition system
TS : Type → Type _
TS L = Σ[ S ∈ Type ] (S → L →  S → Type) 

isFin : Type 
isFin = {!   !}

TSHom : {L : Type} → TS L → TS L → Type _ 
TSHom (A , A↦) (B , B↦)  = Σ[ f ∈ (A → B) ] (∀{a l a'} → A↦ a l a' → B↦ (f a) l (f a'))

TSysCat : Type → Category _ _ 
TSysCat L .ob = TS L
TSysCat L .Hom[_,_] = TSHom {L}
TSysCat L .id = (λ x → x) , λ x → x
TSysCat L ._⋆_ (f , prf) (g , prf') = (λ x → g (f x)) , λ z → prf' (prf z)
TSysCat L .⋆IdL _ = refl
TSysCat L .⋆IdR _ = refl
TSysCat L .⋆Assoc _ _ _ = refl
TSysCat L .isSetHom = {!   !} 


data Label : Type where 
  stepL stepR add : Label 


data NatEx : Type where
  num : ℕ → NatEx 
  plus : NatEx → NatEx → NatEx


data Rel : NatEx → Unit → NatEx → Type where 
  radd : ∀ {n m } → Rel (plus (num n) (num m)) tt (num (n + m)) 
  rstepL : ∀ {l l' r } → 
    Rel l tt l'  → 
    Rel (plus l r) tt (plus l' r) 
  rstepR : ∀ {l  r r' n} → 
    Rel r tt r'  → 
    Rel (plus (num n) r) tt (plus (num n) r') 

ex : TS Unit
ex .fst = NatEx
ex .snd = Rel
-}