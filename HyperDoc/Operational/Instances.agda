{-# OPTIONS --type-in-type #-}
module HyperDoc.Operational.Instances where 

open import Cubical.Data.Sigma

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import HyperDoc.Operational.Model 
open import HyperDoc.Operational.Graph
open import HyperDoc.Operational.Initial

open BifunctorSep
open BifunctorSepᴰ
open Categoryᴰ
open Functor
open NatTrans

-- functions and pointwise relations
Gr : hSet _ → Graph _ _ → Graph _ _  
Gr A (N , E) .fst = (⟨ A ⟩ → ⟨ N ⟩) , isSet→ (N .snd)
Gr A (N , E) .snd f g = ((a : ⟨ A ⟩) → ⟨ E (f a) (g a) ⟩) , isSetΠ λ _ → E (f _) (g _) .snd

Gr-homL : {X Y : hSet _ }→ (SET _) [ X , Y ] → (G : Graph _ _ ) → (GRAPH _ _ ) [ Gr Y G , Gr X G ]
Gr-homL {X} {Y} f G .fst h x = h (f x)
Gr-homL {X} {Y} f G .snd h x = h (f x)

Gr-homR : {G G' : Graph _ _ } → 
  (A : hSet ℓ-zero) → GRAPH ℓ-zero ℓ-zero [ G , G' ] → GRAPH ℓ-zero ℓ-zero [ Gr A G , Gr A G' ]
Gr-homR {G} {G'} A G'' .fst f a = G'' .fst (f a)
Gr-homR {G} {G'} A G'' .snd f a = G'' .snd (f a)

Sem : CBPVModel _ _ _ _ _ _ 
Sem .fst = SET _
Sem .snd .fst = GRAPH _ _
Sem .snd .snd .Bif-ob = Gr
Sem .snd .snd .Bif-homL {X}{Y} = Gr-homL {Y}{X}
Sem .snd .snd .Bif-L-id = refl
Sem .snd .snd .Bif-L-seq _ _ = refl
Sem .snd .snd .Bif-homR {G}{G'} = Gr-homR {G}{G'}
Sem .snd .snd .Bif-R-id = refl
Sem .snd .snd .Bif-R-seq _ _ = refl
Sem .snd .snd .SepBif-RL-commute _ _ = refl

rGr : hSet _ → RGraph _ _ → RGraph _ _  
rGr A ((N , E), rid) .fst .fst = (⟨ A ⟩ → ⟨ N ⟩) , isSet→ (N .snd)
rGr A ((N , E), rid) .fst .snd f g = ((a : ⟨ A ⟩) → ⟨ E (f a) (g a) ⟩) , isSetΠ λ _ → E (f _) (g _) .snd
rGr A ((N , E), rid) .snd f a = rid (f a)

{-
import Cubical.Data.Equality as Eq
hrm : Functor (SET _) (RGRAPH _ _ ) 
hrm .F-ob A .fst .fst = A
hrm .F-ob A .fst .snd a a' .fst = a ≡ a'
hrm .F-ob A .fst .snd a a' .snd x y = {! A .snd _ _  _ _   !}
hrm .F-ob A .snd a = refl
hrm .F-hom f .fst .fst = f
hrm .F-hom f .fst .snd = cong f
hrm .F-hom f .snd i = refl
hrm .F-id {A} = Relator≡  _ _ refl
hrm .F-seq f g = Relator≡ _ _ refl

hrm : Functor (SET _) (RGRAPH _ _ ) 
hrm .F-ob A .fst .fst = A
hrm .F-ob A .fst .snd a a' .fst = a Eq.≡ a'
hrm .F-ob A .fst .snd a a' .snd Eq.refl y = {! y  !}
hrm .F-ob A .snd a = Eq.refl
hrm .F-hom f .fst .fst = f
hrm .F-hom f .fst .snd Eq.refl = Eq.refl
hrm .F-hom f .snd = refl
hrm .F-id {A} = Relator≡ {G = {!   !}}{{!   !}}_ _  refl
hrm .F-seq f g = Relator≡ _ _ refl
-}

{-
rSem : CBPVModel _ _ _ _ _ _ 
rSem .fst = SET _
rSem .snd .fst = RGRAPH _ _
rSem .snd .snd .Bif-ob = {!  rGr !}
rSem .snd .snd .Bif-homL = {!   !}
rSem .snd .snd .Bif-L-id = {!   !}
rSem .snd .snd .Bif-L-seq = {!   !}
rSem .snd .snd .Bif-homR = {!   !}
rSem .snd .snd .Bif-R-id = {!   !}
rSem .snd .snd .Bif-R-seq = {!   !}
rSem .snd .snd .SepBif-RL-commute = {!   !}
-}

open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import HyperDoc.Operational.TypeStructure
open TypeStructure Sem 
open Has+'
open WkRepresentation

semHas𝟙 : Has𝟙 
semHas𝟙 .fst = Unit , isSetUnit
semHas𝟙 .snd .N-ob = λ x _ _ → tt
semHas𝟙 .snd .N-hom _ = refl

semHas× : Has× 
semHas× A A' .fst = (⟨ A ⟩ × ⟨ A' ⟩) , (isSet× (A .snd) (A' .snd))
semHas× A A' .snd .N-ob A'' (f , g) a'' = f a'' , g a''
semHas× A A' .snd .N-hom _ = refl

semHas+ : Has+ 
semHas+ A A' .A+A' = (⟨ A ⟩ ⊎ ⟨ A' ⟩) , isSet⊎ (A .snd) (A' .snd)
semHas+ A A' .Has+'.match .N-ob G (f , g) (inl x) = f x
semHas+ A A' .Has+'.match .N-ob G (f , g) (inr x) = g x
semHas+ A A' .Has+'.match .N-hom h i fg (inl x) = h .fst (fg .fst x)
semHas+ A A' .Has+'.match .N-hom h i fg (inr x) = h .fst (fg .snd x)
semHas+ A A' .Has+'.σ₁ = inl
-- f a = f (inl a)
semHas+ A A' .Has+'.σ₂ = inr
-- f a' = f (inr a')
-- need at least reflexive closure of a graph
semHas+ A A' .Has+'.+β₁ M M' a = {!   !} -- ⟨ B .snd (M a) (M a) ⟩
semHas+ A A' .Has+'.+β₂ M M' a' = {!   !} --⟨ B .snd (M' a') (M' a') ⟩

semHasUTy : HasUTy 
semHasUTy G .rep = G .fst
semHasUTy G .fwd .N-ob A f = f
semHasUTy G .fwd .N-hom _ = refl
semHasUTy G .bkwd f = f
semHasUTy G .wkretract {A} f a = {!   !} -- ⟨ G .snd (f a) (f a) ⟩

semHasFTy : HasFTy 
semHasFTy A .rep = A , λ a a' → ⊥ , λ()
semHasFTy A .fwd .N-ob G = fst
semHasFTy A .fwd .N-hom _ = refl
semHasFTy A .bkwd f = f , λ ()
semHasFTy A .wkretract {G} f a = {!   !} -- ⟨ G .snd (f a) (f a) ⟩

CL : CBPVMorphism Syn Sem 
CL .fst = V [ 𝟙 ,-]
CL .snd .fst = appL (mkBifunctorSep O) 𝟙
CL .snd .snd .N-ob (A , B) .fst M V = subC V M
CL .snd .snd .N-ob (A , B) .snd {M}{M'} M↦M' V = subC-cong M↦M'
CL .snd .snd .N-hom (V , S) = ΣPathP ((funExt (λ M → funExt λ V' → plugSub ∙ cong₂ plug refl subDist)) , 
  toPathP (implicitFunExt (implicitFunExt (funExt λ _ → funExt λ V' → isProp↦ _ _))) ) 
  
Grᴰ : {A : hSet _}{G : Graph _ _ } → 
  (SETᴰ _ _ .ob[_] A) → (Graphᴰ _ _ G) → Graphᴰ _ _  (Gr A G)
Grᴰ {A} {G} Aᴰ (Nᴰ , Eᴰ) .fst n = ((a : ⟨ A ⟩) → ⟨ Aᴰ a ⟩ → ⟨ Nᴰ (n a) ⟩) , isSetΠ2 λ x y → Nᴰ (n x) .snd
Grᴰ {A} {G} Aᴰ (Nᴰ , Eᴰ) .snd {n}{n'} n↦n' nᴰ n'ᴰ = 
  ({ a a' : ⟨ A ⟩}(aᴰ : ⟨ Aᴰ a ⟩)(a'ᴰ : ⟨ Aᴰ a ⟩)→ ⟨ Eᴰ (n↦n' a) (nᴰ a aᴰ) (n'ᴰ a a'ᴰ) ⟩) , 
  isSetImplicitΠ2 λ _ _ → isSetΠ2 λ _ _ → Eᴰ (n↦n' _) (nᴰ _ _) (n'ᴰ _ _) .snd



open import Cubical.Categories.Instances.Preorders.Monotone

open import HyperDoc.Operational.Logic
open import HyperDoc.Logics.SetPred  
open import Cubical.Categories.Instances.Posets.Base

Hmm : Functor ((GRAPH _ _) ^op) (POSET _ _) 
Hmm .F-ob G = pred (G .fst)
Hmm .F-hom = λ z →
    record
    { f = λ z₁ z₂ → fst (z₁ (z .fst z₂)) , z₁ (z .fst z₂) .snd
    ; isMon = λ {x = x₁} {y = y₁} z₁ x₂ → z₁ (z .fst x₂)
    }
Hmm .F-id = eqMon _ _ refl
Hmm .F-seq f g = eqMon _ _ refl

-- anti reduction closed ?
L : CBPVLogic Sem 
L .CBPVLogic.LV = Pred
L .CBPVLogic.LC = Hmm
L .CBPVLogic.LSq .N-ob (A , G) f = record
  { f = λ z z₁ → fst (z (f z₁)) , z (f z₁) .snd
  ; isMon = λ {x} {y} z x₁ → z (f x₁)
  }
L .CBPVLogic.LSq .N-hom (f , h )= funExt λ g → eqMon _ _  refl
L .CBPVLogic.LRel f g h = Unit , isPropUnit
L .CBPVLogic.RelLComp = λ e _ → tt
L .CBPVLogic.RelRComp = λ e _ → tt

open LogicStruct L 

-- Q: why is all the type structure trivial ? 
-- is it because we are actually mapping into universal properties and should expect Isomorphisms?

has𝟙ᴸ : Has𝟙ᴸ 
has𝟙ᴸ = has⊤

has×ᴸ : Has×ᴸ
has×ᴸ .fst = has∧
has×ᴸ .snd = has∃

has+ᴸ : Has+ᴸ semHas+
has+ᴸ .fst = has∨
has+ᴸ .snd .fst = has∃
has+ᴸ .snd .snd .LogicStruct.Has+ᴸ'.anti-1 = λ x z → z
has+ᴸ .snd .snd .LogicStruct.Has+ᴸ'.anti-2 = λ x z → z
has+ᴸ .snd .snd .LogicStruct.Has+ᴸ'.edge-1 = λ φ ψ → tt
has+ᴸ .snd .snd .LogicStruct.Has+ᴸ'.edge-2 = λ φ ψ → tt

hasUTyᴸ : HasUTyᴸ semHasUTy 
hasUTyᴸ .fst = λ x z → z
hasUTyᴸ .snd = λ φ ψ → tt

hasFTyᴸ : HasFTyᴸ semHasFTy
hasFTyᴸ .fst f .fst = {!   !}
hasFTyᴸ .fst f .snd = {!   !}
hasFTyᴸ .snd .fst = λ x z → z
hasFTyᴸ .snd .snd = λ φ ψ → tt


Semᴰ : CBPVModelᴰ Sem _ _ _ _ _ _
Semᴰ .fst = SETᴰ _ _
Semᴰ .snd .fst = GRAPHᴰ _ _ _ _
Semᴰ .snd .snd .Bif-obᴰ {A}{G} = Grᴰ {A}{G}
Semᴰ .snd .snd .Bif-homLᴰ {A} {A'} {f} {Aᴰ} {A'ᴰ} fᴰ {G} Gᴰ .fst h hᴰ a' a'ᴰ = hᴰ (f a') (fᴰ a' a'ᴰ)
Semᴰ .snd .snd .Bif-homLᴰ {A} {A'} {f} {Aᴰ} {A'ᴰ} fᴰ {G} Gᴰ .snd {h}{h'}{e} hᴰ h'ᴰ z {a} {a'} aᴰ a'ᴰ = 
  z {f a}{f a'} (fᴰ a aᴰ) (fᴰ a a'ᴰ)
Semᴰ .snd .snd .Bif-L-idᴰ = refl
Semᴰ .snd .snd .Bif-L-seqᴰ _ _ = refl
Semᴰ .snd .snd .Bif-homRᴰ {G} {G'} {h} {Gᴰ} {Gᴰ'} hᴰ {A} Aᴰ .fst n nᵈ a aᴰ = hᴰ .fst (n a) (nᵈ a aᴰ)
Semᴰ .snd .snd .Bif-homRᴰ {G} {G'} {h} {Gᴰ} {Gᴰ'} hᴰ {A} Aᴰ .snd {n}{nᵈ}{e} nᴰ n'ᴰ eᴰ {a}{a'} aᴰ aᴰ' = 
  hᴰ .snd  (nᴰ a aᴰ) (n'ᴰ a aᴰ') (eᴰ {a}{a'} aᴰ aᴰ')
Semᴰ .snd .snd .Bif-R-idᴰ = refl
Semᴰ .snd .snd .Bif-R-seqᴰ _ _ = refl
Semᴰ .snd .snd .SepBif-RL-commuteᴰ _ _ = refl

