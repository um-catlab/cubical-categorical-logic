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

open import Cubical.Categories.NaturalTransformation
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
open NatTrans
open Logic
open _⊣_
open MonFun
open Iso renaming (ret to ret')

module _ 
  {ℓS  ℓP ℓP' : Level}
  {M : hSet ℓS} where

  open Writer M
 
  𝓥 = SET ℓS 
  𝓒 = WRITERALG ℓS 

  CBPVWrite : Model  (ℓ-suc ℓS) ℓS (ℓ-suc ℓS) ℓS ℓS
  CBPVWrite .V = SET ℓS
  CBPVWrite .C = WRITERALG ℓS
  CBPVWrite .O .F-ob (A , B) = (SET ℓS) [ A , (B .fst .fst , B .snd) ] , isSetHom (SET ℓS) {A}{(B .fst .fst , B .snd)} 
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

  hasUTy : HasUTy CBPVWrite 
  hasUTy B .fst = B .fst .fst , B .snd
  hasUTy B .snd .PshIso.trans .PshHom.N-ob A f = f
  hasUTy B .snd .PshIso.trans .PshHom.N-hom _ _ _ _  = refl
  hasUTy B .snd .PshIso.nIso A .fst f = f
  hasUTy B .snd .PshIso.nIso A .snd .fst _ = refl
  hasUTy B .snd .PshIso.nIso A .snd .snd _ = refl

  U : Functor (WRITERALG ℓS) (SET ℓS) 
  U = Ucomp CBPVWrite hasUTy

  hasFTy : HasFTy CBPVWrite 
  hasFTy A .fst = (FreeWriterAlg ⟨ A ⟩) , {!   !}
  hasFTy A .snd .PshIso.trans .PshHom.N-ob B (f , fhom) a = f (ret a)
  hasFTy A .snd .PshIso.trans .PshHom.N-hom B B' f (g , ghom) = refl
  hasFTy A .snd .PshIso.nIso B .fst f = ext (B .fst) f
  hasFTy A .snd .PshIso.nIso B .snd .fst b = refl
  hasFTy A .snd .PshIso.nIso B .snd .snd a = {!  refl !}
    -- ext (B .fst) (λ a₁ → a .fst (ret a₁)) ≡ a 
    -- provable

  F : Functor (SET ℓS)  (WRITERALG ℓS)
  F = Fcomp CBPVWrite hasFTy
  
  has⊤ : HasV⊤ CBPVWrite 
  has⊤ .fst .fst = Unit*
  has⊤ .fst .snd = isSetUnit*
  has⊤ .snd .PshIso.trans .PshHom.N-ob = λ c _ → tt*
  has⊤ .snd .PshIso.trans .PshHom.N-hom _ _ _ _ = refl
  has⊤ .snd .PshIso.nIso A .fst _ _  = tt*
  has⊤ .snd .PshIso.nIso A .snd .fst tt* = refl
  has⊤ .snd .PshIso.nIso A .snd .snd _ = refl

  hasC× : HasC× CBPVWrite
  hasC× B B' .fst .fst = (B .fst .fst × B' .fst .fst) , λ m (b , b') → (B .fst .snd m b) , B' .fst .snd m b'
  hasC× B B' .fst .snd = isSet× (B .snd) (B' .snd)
  hasC× B B' .snd .PshIso.trans .PshHom.N-ob B'' f = ((λ b' → f .fst b' .fst) , λ c b''  → cong fst (f .snd c b'')) , (λ b'' → f .fst b'' .snd) , λ c b''  → cong snd (f .snd c b'')
  hasC× B B' .snd .PshIso.trans .PshHom.N-hom C C' f p = ΣPathP ((WriterHom≡ {B' = B .fst}(B .snd) refl) , WriterHom≡ {B' = B' .fst}(B' .snd) refl)
  hasC× B B' .snd .PshIso.nIso B'' .fst (f , g) = (λ p → f .fst p , g .fst p) , λ c b → ΣPathP (f .snd c b , g .snd c b)
  hasC× B B' .snd .PshIso.nIso B'' .snd .fst b = ΣPathP ((WriterHom≡ {B' = B .fst}(B .snd) refl) , WriterHom≡ {B' = B' .fst} (B' .snd) refl)
  hasC× B B' .snd .PshIso.nIso B'' .snd .snd a = WriterHom≡ {B' = B  .fst .fst × B' .fst .fst , λ w (b , b') → B .fst .snd w b , B' .fst .snd w b'} (isSet× (B .snd) (B' .snd)) refl

  CL : Functor (WRITERALG ℓS ^op) (POSET (ℓ-suc ℓS) ℓS )
  CL .F-ob = subAlgPo
  CL .F-hom f .f = pull f
  CL .F-hom f .isMon = λ z x₂ → z (f .fst x₂)
  CL .F-id {B} = eqMon _ _ (funExt λ X → subAlg≡ {B' = B .fst} refl )
  CL .F-seq {X}{Y}{Z} f g = eqMon _ _ (funExt λ W → subAlg≡ {B' = _} refl)

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

  -- direct image 
  direct : ∀{A : ob 𝓥}{B : ob 𝓒} → (o : (SET ℓS) [ A , U .F-ob B ]) → ℙ ⟨ A ⟩ → ℙ ⟨ B .fst  ⟩ 
  direct {A} {B} o P b = ∥ (Σ[ a ∈ ⟨ A ⟩ ] (a ∈ P ) × (b ≡ o a) ) ∥ₚ

  push :  ∀{A : ob 𝓥}{B : ob 𝓒} → (o : (SET ℓS) [ A , U .F-ob B ]) → ℙ ⟨ A ⟩ → ⟨ B .fst ⟩ → Type ℓS
  push {A}{B} o P b = Gen{ℓS = ℓS} {A = M}{(B .fst .fst) , (B .snd)} (B .fst .snd) (direct {A}{B} o P) b 

  pushₚ :  ∀{A : ob 𝓥}{B : ob 𝓒} → (o : (SET ℓS) [ A , U .F-ob B ]) → ℙ ⟨ A ⟩ → ℙ ⟨ B .fst  ⟩ 
  pushₚ {A}{B} o P b = ∥ push {A} {B} o P b  ∥ₚ

  CBPVLogic : Logic CBPVWrite 
  CBPVLogic .VH = VL
  CBPVLogic .CH = CL
  CBPVLogic .pushV {A} {B} o .f P .fst = pushₚ {A = A }{B}o P
  CBPVLogic .pushV {A} {B} o .f P .snd w b = tmap (step w b)
  CBPVLogic .pushV {A} {B} o .isMon {P}{Q} P⊆Q b = 
    tmap (λ g → 
      Gen-elim 
        (λ b _ → push {A = A} o Q b)  
        (λ b' b'∈direct → base b' (tmap (λ (a , a∈P , b'≡ ) → a  , P⊆Q a a∈P , b'≡) b'∈direct)) 
        (λ a b' g g' → step a b' g') 
        b 
        g)
  CBPVLogic .pullC {A} {B} o .f P a = P .fst (o a)
  CBPVLogic .pullC {A} {B} o .isMon P a = P (o a)
  CBPVLogic .pushPullAdj {o = o} .adjIff {P} {Q} .fun pushP a a∈P = pushP (o a) ∣ (base (o a) ∣ a , a∈P , refl ∣₁) ∣₁
  CBPVLogic .pushPullAdj {o = o} .adjIff {P} {Q} .inv P⊆Q b = trec (∈-isProp (λ z → Q .fst b) b) λ p → 
    Gen-elim 
      (λ b₁ _ → b₁ ∈ Q .fst) 
      ((λ b → 
        trec 
          (Q .fst b .snd) 
          (λ (a , a∈P , b≡) → subst (λ h → h ∈ Q .fst) (sym b≡) (P⊆Q a a∈P)))) 
      (λ a b g → Q .snd a b) 
      b 
      p
  CBPVLogic .pushPullAdj {o = o} .adjIff {P} {Q} .sec b = ⊆-isProp P (λ a → Q .fst (o a))  _ b 
  CBPVLogic .pushPullAdj {A}{_}{o} .adjIff {P} {Q} .ret' a = ⊆-isProp (pushₚ {A = A} o P) (Q .fst) _ a


  -- this should just be inherited from Set in some nice way
  Alg∧ : L∧.Has∧ CL
  Alg∧ .fst B .L∧.HA._∧_ (P , clP)(Q , clQ) = (P ∩ Q) , λ w a (Pa , Qa) → (clP w a  Pa) , (clQ w a Qa)
  Alg∧ .fst B .L∧.HA.and-intro f g x Px = (f x Px) , (g x Px)
  Alg∧ .fst B .L∧.HA.and-elim1 f x Px = f x Px .fst
  Alg∧ .fst B .L∧.HA.and-elim2 f x Px = f x Px .snd
  Alg∧ .snd f .L∧.HAHom.f-and  B B' = refl
