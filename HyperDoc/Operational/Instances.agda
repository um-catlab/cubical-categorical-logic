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

open import Cubical.Data.Empty
open import HyperDoc.Operational.TypeStructure
open import Cubical.Categories.Presheaf.Morphism.Alt
open PshHom
open TypeStructure Sem 

-- these seem trivial
-- uhm.. what..?
semHasUTy : HasUTy 
semHasUTy .TypeStructure.HasUTy.wkrep (N , E) .fst = N
-- force ; idPshHom
semHasUTy .TypeStructure.HasUTy.wkrep (N , E) .snd .fst .N-ob A f = f
semHasUTy .TypeStructure.HasUTy.wkrep (N , E) .snd .fst .N-hom A A' V f = refl
-- thunk ; idPshHom
semHasUTy .TypeStructure.HasUTy.wkrep (N , E) .snd .snd .N-ob A f = f
semHasUTy .TypeStructure.HasUTy.wkrep (N , E) .snd .snd .N-hom A A' V f = refl
semHasUTy .TypeStructure.HasUTy.Fβ {A}{N , E}{M} a = goal where 
  goal : ⟨ E (M a) (M a) ⟩ 
  goal = {!   !}

semHasFTy : HasFTy 
semHasFTy .TypeStructure.HasFTy.wkrep A .fst = A , λ a a' → ⊥ , λ()
semHasFTy .TypeStructure.HasFTy.wkrep A .snd .fst .N-ob G = fst
semHasFTy .TypeStructure.HasFTy.wkrep A .snd .fst .N-hom G G' h p = refl
semHasFTy .TypeStructure.HasFTy.wkrep A .snd .snd .N-ob G f = f , (λ ())
semHasFTy .TypeStructure.HasFTy.wkrep A .snd .snd .N-hom G G' h p = ΣPathP (refl , {!   !})
semHasFTy .TypeStructure.HasFTy.FU {A}{N , E}{M} a = goal where 
  goal : ⟨ E (M a) (M a) ⟩ 
  goal = {!   !}

CL : CBPVMorphism Syn Sem 
CL .fst = V [ 𝟙 ,-]
CL .snd .fst = appL (mkBifunctorSep O) 𝟙
CL .snd .snd .N-ob (A , B) .fst M V = subC V M
CL .snd .snd .N-ob (A , B) .snd {M}{M'} M↦M' V = subC-cong M↦M'
CL .snd .snd .N-hom (V , S) = 
    ΣPathP ((funExt (λ M → funExt λ V' → plugSub ∙ cong₂ plug refl subDist)) , 
    implicitFunExt (implicitFunExt (funExt λ _ → funExt λ V' → λ i → {! plug-subC-cong {M↦M' = ?} i  !})))
  {-ΣPathP ((funExt (λ M → funExt λ V' → plugSub ∙ cong₂ plug refl subDist)) , 
  toPathP (implicitFunExt (implicitFunExt (funExt λ _ → funExt λ V' → isProp↦ _ _))) ) -}
  
Grᴰ : {A : hSet _}{G : Graph _ _ } → 
  (SETᴰ _ _ .ob[_] A) → (Graphᴰ _ _ G) → Graphᴰ _ _  (Gr A G)
Grᴰ {A} {G} Aᴰ (Nᴰ , Eᴰ) .fst n = ((a : ⟨ A ⟩) → ⟨ Aᴰ a ⟩ → ⟨ Nᴰ (n a) ⟩) , isSetΠ2 λ x y → Nᴰ (n x) .snd
Grᴰ {A} {G} Aᴰ (Nᴰ , Eᴰ) .snd {n}{n'} n↦n' nᴰ n'ᴰ = 
  ({ a a' : ⟨ A ⟩}(aᴰ : ⟨ Aᴰ a ⟩)(a'ᴰ : ⟨ Aᴰ a ⟩)→ ⟨ Eᴰ (n↦n' a) (nᴰ a aᴰ) (n'ᴰ a a'ᴰ) ⟩) , 
  isSetImplicitΠ2 λ _ _ → isSetΠ2 λ _ _ → Eᴰ (n↦n' _) (nᴰ _ _) (n'ᴰ _ _) .snd

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

{-}
Semᴰ .snd .snd .Bif-obᴰ
--  {A} {G} Aᴰ Gᴰ .fst f = ((a : ⟨ A ⟩) → ⟨ Aᴰ a ⟩ → ⟨ Gᴰ .fst (f a) ⟩) , {!   !}
Semᴰ .snd .snd .Bif-obᴰ {A} {G} Aᴰ Gᴰ .snd {n}{n'} e fᴰ gᴰ = ({a a' : ⟨ A ⟩} → (p : e a a') → ⟨ Gᴰ  .snd e (gᴰ a p) (fᴰ a p) ⟩) , {!   !}
Semᴰ .snd .snd .Bif-homLᴰ {A'} {A} {f} {Aᴰ} {A'ᴰ} fᴰ {G} Gᴰ .fst x = x 9
Semᴰ .snd .snd .Bif-homLᴰ {A'} {A} {f} {Aᴰ} {A'ᴰ} fᴰ {G} Gᴰ .snd = {!   !}
Semᴰ .snd .snd .Bif-L-idᴰ = {!   !}
Semᴰ .snd .snd .Bif-L-seqᴰ = {!   !}
Semᴰ .snd .snd .Bif-homRᴰ = {!   !}
Semᴰ .snd .snd .Bif-R-idᴰ = {!   !}
Semᴰ .snd .snd .Bif-R-seqᴰ = {!   !}
Semᴰ .snd .snd .SepBif-RL-commuteᴰ = {!   !}

-}
