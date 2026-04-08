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
open import Cubical.Categories.Displayed.Base
open Category
open Categoryᴰ
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

antiTSᴰ : TS → Type _ 
antiTSᴰ (S , R) = Σ[ P ∈ (S → Type _) ] (∀ {s s'} → R s s' → P s' → P s)

antiTSHomᴰ : {S T : TS} → TSHom S T → antiTSᴰ S → antiTSᴰ T → Type _ 
antiTSHomᴰ {S}{T} f P Q = 
  Σ[ fᴰ ∈ ((s : S .fst) →  P .fst s → Q .fst (f .fst s))  ] 
    (∀ {s s'} (sRs' : S .snd s s') (Ps' : P .fst s') →
                   fᴰ s (P .snd sRs' Ps') ≡ Q .snd (f .snd sRs') (fᴰ s' Ps'))

antiTSHomᴰ≡ :  {S T : TS}{f : TSHom S T}{P : antiTSᴰ S}{Q : antiTSᴰ T}{fᴰ gᴰ : antiTSHomᴰ f P Q} → fᴰ .fst ≡ gᴰ .fst → fᴰ ≡ gᴰ
antiTSHomᴰ≡  prf = ΣPathP (prf , (toPathP {!  snd gᴰ !}))
  -- Σ≡Prop (λ x x₁ y → isPropImplicitΠ (λ x₂ x₃ y₁  → isPropImplicitΠ (λ x₄ x₅ y₂  → isPropΠ2 (λ x₆ y₃ x₇ y₄  → {!  !}) _ _) _ _) _  _) prf

antiTSysCatᴰ : Categoryᴰ TSysCat _ _ 
ob[ antiTSysCatᴰ ] = antiTSᴰ
antiTSysCatᴰ .Hom[_][_,_] = antiTSHomᴰ
antiTSysCatᴰ .idᴰ .fst s Ps = Ps
antiTSysCatᴰ .idᴰ .snd _ _ = refl
_⋆ᴰ_ antiTSysCatᴰ {X} {Y} {Z} {f} {g} {Xᴰ} {Yᴰ} {Zᴰ} (fᴰ , presf) (gᴰ , presg) .fst x Xᴰx = gᴰ (f .fst x) (fᴰ x Xᴰx)
_⋆ᴰ_ antiTSysCatᴰ {X} {Y} {Z} {f} {g} {Xᴰ} {Yᴰ} {Zᴰ} (fᴰ , presf) (gᴰ , presg) .snd {x}{x'} xRx' Xᴰx' = cong (λ h → gᴰ (f .fst x)  h) (presf   _ _) ∙ presg _ _
antiTSysCatᴰ .⋆IdLᴰ _ = antiTSHomᴰ≡ refl
antiTSysCatᴰ .⋆IdRᴰ _ = antiTSHomᴰ≡ refl
antiTSysCatᴰ .⋆Assocᴰ _ _  _ = antiTSHomᴰ≡ refl
antiTSysCatᴰ .isSetHomᴰ = {!   !}

TSᴰ : TS → Type _ 
TSᴰ (S , R) = Σ[ P ∈ (S → Type _) ] (∀ {s s'} → R s s' → P s → P s' → Type)

TSHomᴰ : {S T : TS} → TSHom S T → TSᴰ S → TSᴰ T → Type _ 
TSHomᴰ {S}{T} f P Q = 
  Σ[ fᴰ ∈ ((s : S .fst) → P .fst s → Q .fst (f .fst s)) ] 
    ({s s' : S .fst}{sRs' : S .snd s s'}(Ps : P .fst s)(Ps' : P .fst s') → 
    P .snd sRs' Ps Ps' → Q .snd (f .snd sRs') (fᴰ s Ps) (fᴰ s' Ps'))

TSysCatᴰ : Categoryᴰ TSysCat _ _ 
ob[ TSysCatᴰ ] = TSᴰ
TSysCatᴰ .Hom[_][_,_] = TSHomᴰ
TSysCatᴰ .idᴰ .fst s Ps = Ps
TSysCatᴰ .idᴰ .snd Ps Ps' PsRPs' = PsRPs'
(TSysCatᴰ ._⋆ᴰ_ {X}{Y}{Z}{f}{g}{Xᴰ}{Yᴰ}{Zᴰ} (fᴰ , Rᴰ)) (gᴰ , R'ᴰ) .fst s Xs = gᴰ (f .fst s) (fᴰ s Xs)
(TSysCatᴰ ._⋆ᴰ_ {X}{Y}{Z}{f}{g}{Xᴰ}{Yᴰ}{Zᴰ} (fᴰ , Rᴰ)) (gᴰ , R'ᴰ) .snd Xs Xs' XsRXs' = 
  R'ᴰ (fᴰ _ Xs) (fᴰ _ Xs') (Rᴰ Xs Xs' XsRXs')
TSysCatᴰ .⋆IdLᴰ _ = ΣPathP (refl , refl)
TSysCatᴰ .⋆IdRᴰ _ = ΣPathP (refl , refl)
TSysCatᴰ .⋆Assocᴰ _ _ _ = ΣPathP (refl , refl)
TSysCatᴰ .isSetHomᴰ = {!   !}

∫TS : (S : TS) → TSᴰ S → TS 
∫TS (S , R) (Sᴰ , Rᴰ) .fst = Σ S Sᴰ
∫TS (S , R) (Sᴰ , Rᴰ) .snd (s , sᴰ)(s' , s'ᴰ)= Σ[ sRs' ∈ R s s' ]  Rᴰ sRs' sᴰ s'ᴰ

∫TSHom : {S T : TS}{P : TSᴰ S}{Q : TSᴰ T} (f : TSHom S T) → TSHomᴰ {S}{T} f P Q → TSHom (∫TS S P) (∫TS T Q) 
∫TSHom {S} {T} {P} {Q} (f , fpres) (fᴰ , fᵈpres) .fst = 
  λ z → f (z .fst) , fᴰ (z .fst) (z .snd)
∫TSHom {S} {T} {P} {Q} (f , fpres) (fᴰ , fᵈpres) .snd {a}{a'} = 
  λ z → fpres (z .fst) , fᵈpres (a .snd) (a' .snd)  (z .snd)

TSysFinCat : Category _ _ 
TSysFinCat = FullSubcategory TSysCat isFin
{-}

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
-}
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