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

open Algebra
open AlgebraHom
open Category
open Functor
open Model
open Logic
open _⊣_
open Iso renaming (ret to ret')

module _ 
  {ℓS  ℓP ℓP' : Level}
  {M : hSet ℓS} where

  open Writer M

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


  open MonFun
  CH' : Functor (WRITERALG ℓS ^op) (POSET (ℓ-suc ℓS) ℓS )
  CH' .F-ob = subAlgPo
  CH' .F-hom f .f = pull f
  CH' .F-hom f .isMon = λ z x₂ → z (f .fst x₂)
  CH' .F-id {B} = eqMon _ _ (funExt λ X → subAlg≡ {B' = B .fst} refl )
  CH' .F-seq f g = eqMon _ _ (funExt λ X → subAlg≡ {B' = {!   !}} refl)

  CBPVLogic : Logic CBPVWrite 
  CBPVLogic .VH = Pred {ℓS}{ℓP}{ℓP'}
  CBPVLogic .CH = Pred {ℓS}{ℓP}{ℓP'} ∘F (U ^opF) -- just factor through Set's logic
    -- CH'

{-
  hasUF⊣ : HasUF⊣ CBPVLogic 
  hasUF⊣ o .fst .f P = {! ∣push∣   !} , {!   !}
  hasUF⊣ o .fst .isMon = {!   !}
  hasUF⊣ o .snd .fst .f B = B .fst ∘S o
  hasUF⊣ o .snd .fst .isMon X≤Y a = X≤Y (o a)
  hasUF⊣ o .snd .snd .adjIff .fun = {!   !}
  hasUF⊣ o .snd .snd .adjIff .inv = {!   !}
  hasUF⊣ o .snd .snd .adjIff .sec = {!   !}
  hasUF⊣ o .snd .snd .adjIff .ret' = {!   !}
-}
  open import HyperDoc.Connectives.Connectives
  open L∨⊤ using (Has∨⊤)
  open L∧ using (Has∧)

  -- shoud really define ∧ ∨ ⊤ ... on the Powerset type
  -- logical instructure inherited from Pred hyperdoc on SetPred
  -- just use U?
  has∧ : Has∧ CH'
  has∧ .fst B .L∧.HA._∧_ X Y = (λ b → {! X .fst  !} ⊓  {!   !}) , {! B .fst .fst  !}
  has∧ .fst B .L∧.HA.and-intro = {!   !}
  has∧ .fst B .L∧.HA.and-elim1 = {!   !}
  has∧ .fst B .L∧.HA.and-elim2 = {!   !}
  has∧ .snd = {!   !}

