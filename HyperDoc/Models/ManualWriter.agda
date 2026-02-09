module HyperDoc.Models.ManualWriter where 

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure hiding(str)
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Logic
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation renaming (rec to trec ; map to tmap)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.FunctorAlgebras 
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Posets.Base

open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Instances.Preorders.Monotone hiding (_≤X_ ; _≤Y_)
open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint

open import HyperDoc.CBPVModel
open import HyperDoc.Logics.SetPred 
open import HyperDoc.CBPVLogic
open import HyperDoc.Syntax
-- open import HyperDoc.Logics.WriterMonadAlg
open import HyperDoc.Lib
open import HyperDoc.Effects.ManualWriter
open import HyperDoc.Connectives.Connectives
import Cubical.Data.Equality as Eq 

open Algebra
open AlgebraHom
open Category
open Functor
open Model
open Logic
open _⊣_
open MonFun
open Iso renaming (ret to ret')

module _ 
  {ℓS  ℓP ℓP' : Level}
  {M : hSet ℓS} where

  open Writer M
 -- open |push|

  U : Functor (WRITERALG ℓS) (SET ℓS) 
  U .F-ob A = (A .fst .fst) , (A .snd)
  U .F-hom f = f .fst
  U .F-id = refl
  U .F-seq _ _ = refl

  F : Functor (SET ℓS) (WRITERALG ℓS) 
  F .F-ob X = FreeWriterAlg ⟨ X ⟩ , {!   !}
  F .F-hom {X}{Y} f = ext (FreeWriterAlg ⟨ Y ⟩) λ x → ret (f x)
  F .F-id = WriterHom≡ {!   !} {! refl  !} -- up
  F .F-seq = {!   !}

  𝓥 = SET ℓS 
  𝓒 = WRITERALG ℓS 

  CBPVWrite : Model  (ℓ-suc ℓS) ℓS (ℓ-suc ℓS) ℓS ℓS
  CBPVWrite .V = SET ℓS
  CBPVWrite .C = WRITERALG ℓS
  CBPVWrite .O .F-ob (A , B) = (SET ℓS) [ A , U .F-ob B ] , isSetHom (SET ℓS) {A}{U .F-ob B} 
  CBPVWrite .O .F-hom (f , g) h x = g .fst (h (f x)) 
  CBPVWrite .O .F-id = refl
  CBPVWrite .O .F-seq _ _ = refl

  hasV+ : HasV+ CBPVWrite 
  hasV+ A A' .fst .fst = ⟨ A ⟩ ⊎ ⟨ A' ⟩
  hasV+ A A' .fst .snd = isSet⊎  (A .snd) (A' .snd)
  hasV+ A A' .snd .PshIso.trans .PshHom.N-ob B f = (λ z → f (_⊎_.inl z)) , λ z → f (_⊎_.inr z)
  hasV+ A A' .snd .PshIso.trans .PshHom.N-hom B B' f g = refl
  hasV+ A A' .snd .PshIso.nIso B .fst (f , g) (_⊎_.inl x) = f x
  hasV+ A A' .snd .PshIso.nIso B .fst (f , g) (_⊎_.inr x) = g x
  hasV+ A A' .snd .PshIso.nIso B .snd .fst (f , g) = ΣPathP (refl , refl)
  hasV+ A A' .snd .PshIso.nIso B .snd .snd f = funExt λ { (_⊎_.inl x) → refl
                                                        ; (_⊎_.inr x) → refl }
    
  has⊤ : HasV⊤ CBPVWrite 
  has⊤ .fst .fst = Unit*
  has⊤ .fst .snd = isSetUnit*
  has⊤ .snd .PshIso.trans .PshHom.N-ob = λ c _ → tt*
  has⊤ .snd .PshIso.trans .PshHom.N-hom _ _ _ _ = refl
  has⊤ .snd .PshIso.nIso A .fst _ _  = tt*
  has⊤ .snd .PshIso.nIso A .snd .fst tt* = refl
  has⊤ .snd .PshIso.nIso A .snd .snd _ = refl

  hasUTy : HasUTy CBPVWrite 
  hasUTy .fst = U
  hasUTy .snd B .PshIso.trans .PshHom.N-ob A f = f
  hasUTy .snd B .PshIso.trans .PshHom.N-hom _ _ _ _ = refl
  hasUTy .snd B .PshIso.nIso A .fst f b = f b
  hasUTy .snd B .PshIso.nIso A .snd .fst b = refl
  hasUTy .snd B .PshIso.nIso A .snd .snd a = refl

  hasFTy : HasFTy CBPVWrite
  hasFTy .fst = F
  hasFTy .snd A .PshIso.trans .PshHom.N-ob B f = {!  ext  !} , {!   !} -- ? f = {! e  !} , {!   !}
  hasFTy .snd A .PshIso.trans .PshHom.N-hom = {!   !}
  hasFTy .snd A .PshIso.nIso = {!   !}

  hasC× : HasC× CBPVWrite
  hasC× B B' .fst .fst = (B .fst .fst × B' .fst .fst) , λ m (b , b') → (B .fst .snd m b) , B' .fst .snd m b'
  hasC× B B' .fst .snd = isSet× (B .snd) (B' .snd)
  hasC× B B' .snd .PshIso.trans .PshHom.N-ob B'' f = ((λ b' → f .fst b' .fst) , λ c b'' → {!   !}) , (λ b'' → f .fst b'' .snd) , {!   !}
  hasC× B B' .snd .PshIso.trans .PshHom.N-hom C C' f p = {!   !}
  hasC× B B' .snd .PshIso.nIso B'' .fst f = (λ p → f .fst .fst p , f .snd .fst p) , {!   !}
  hasC× B B' .snd .PshIso.nIso B'' .snd .fst b = ΣPathP ((WriterHom≡ (B .snd) refl) , WriterHom≡  (B' .snd) refl)
  hasC× B B' .snd .PshIso.nIso B'' .snd .snd a = WriterHom≡ (isSet× (B .snd) (B' .snd)) refl

  CL : Functor (WRITERALG ℓS ^op) (POSET (ℓ-suc ℓS) ℓS )
  CL .F-ob = subAlgPo
  CL .F-hom f .f = pull f
  CL .F-hom f .isMon = λ z x₂ → z (f .fst x₂)
  CL .F-id {B} = eqMon _ _ (funExt λ X → subAlg≡ {B' = B .fst} refl )
  CL .F-seq f g = eqMon _ _ (funExt λ X → subAlg≡ {B' = {!   !}} refl)

  -- just factor through Set's logic ?

  -- VH : Functor (SET ℓS ^op) (POSET (ℓ-suc ℓS) ℓS) 
  -- VH = Pred {ℓS}{ℓP}{ℓP'}

  -- CH : Functor (WRITERALG ℓS ^op) (POSET (ℓ-suc ℓS) ℓS)
  -- CH = VH ∘F (U ^opF) 

  -- the codomains don't align
  -- one maps into posets of the form Σ[ P ∈ Pred X ] closed P 
  -- and the other maps into just Pred X

  VL : Functor (SET ℓS ^op) (POSET (ℓ-suc ℓS) ℓS) 
  VL = Pred {ℓS}{ℓP}{ℓP'}

  CBPVLogic : Logic CBPVWrite 
  CBPVLogic .VH = VL
  CBPVLogic .CH = CL

  -- this should just be inherited from Set in some nice way
  Alg∧ : L∧.Has∧ CL
  Alg∧ .fst B .L∧.HA._∧_ (P , clP)(Q , clQ) = (P ∩ Q) , λ w a (Pa , Qa) → (clP w a  Pa) , (clQ w a Qa)
  Alg∧ .fst B .L∧.HA.and-intro f g x Px = (f x Px) , (g x Px)
  Alg∧ .fst B .L∧.HA.and-elim1 f x Px = f x Px .fst
  Alg∧ .fst B .L∧.HA.and-elim2 f x Px = f x Px .snd
  Alg∧ .snd f .L∧.HAHom.f-and  B B' = refl

  -- direct image 
  direct : ∀{A : ob 𝓥}{B : ob 𝓒} → (o : (SET ℓS) [ A , U .F-ob B ]) → ℙ ⟨ A ⟩ → ℙ ⟨ B .fst  ⟩ 
  direct {A} {B} o P b = ∥ (Σ[ a ∈ ⟨ A ⟩ ] (a ∈ P ) × (b ≡ o a) ) ∥ₚ

  push :  ∀{A : ob 𝓥}{B : ob 𝓒} → (o : (SET ℓS) [ A , U .F-ob B ]) → ℙ ⟨ A ⟩ → ⟨ B .fst ⟩ → Type ℓS
  push {A}{B} o P b = Gen{ℓS = ℓS} {A = M}{(B .fst .fst) , (B .snd)} (B .fst .snd) (direct {A}{B} o P) b 

  pushₚ :  ∀{A : ob 𝓥}{B : ob 𝓒} → (o : (SET ℓS) [ A , U .F-ob B ]) → ℙ ⟨ A ⟩ → ℙ ⟨ B .fst  ⟩ 
  pushₚ {A}{B} o P b = ∥ push {A} {B} o P b  ∥ₚ


  to : ∀{A : ob 𝓥}{B : ob 𝓒} → (o : (SET ℓS) [ A , U .F-ob B ]) → MonFun (VL .F-ob A .fst) (CL .F-ob B .fst) 
  to {A} {B} o .f P .fst = pushₚ {A = A }{B}o P 
  to {A} {B} o .f P .snd w b = tmap (step w b) 
  to {A} {B} o .isMon {P}{Q} P⊆Q b = 
    tmap (λ g → 
      Gen-elim 
        (λ b _ → push o Q b)  
        (λ b' b'∈direct → base b' (tmap (λ (a , a∈P , b'≡ ) → a  , P⊆Q a a∈P , b'≡) b'∈direct)) 
        (λ a b' g g' → step a b' g') 
        b 
        g)

  hasUF⊣ : HasUF⊣ CBPVLogic 
  hasUF⊣ o .fst = to o 
  hasUF⊣ o .snd .fst .f P a = P .fst (o a)
  hasUF⊣ o .snd .fst .isMon P a = P (o a)
  hasUF⊣ o .snd .snd .adjIff {P}{Q} .fun pushP a a∈P = pushP (o a) ∣ (base (o a) ∣ a , a∈P , refl ∣₁) ∣₁
  hasUF⊣ o .snd .snd .adjIff {P}{Q} .inv  P⊆Q b = trec (∈-isProp (λ z → Q .fst b) b) λ p → 
    Gen-elim 
      (λ b₁ _ → b₁ ∈ Q .fst) 
      ((λ b → 
        trec 
          (Q .fst b .snd) 
          (λ (a , a∈P , b≡) → subst (λ h → h ∈ Q .fst) (sym b≡) (P⊆Q a a∈P)))) 
      (λ a b g → Q .snd a b) 
      b 
      p
  hasUF⊣ o .snd .snd .adjIff {P}{Q} .sec b = ⊆-isProp P (λ a → Q .fst (o a))  _ b 

  hasUF⊣ o .snd .snd .adjIff {P}{Q} .ret' a = ⊆-isProp (pushₚ o P) (Q .fst) _ a
