{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.CBPV.MultiStep where 

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.CoData.Delay

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.CBPV.Base
open import Cubical.Categories.CBPV.Functor
open import Cubical.Categories.CBPV.Instances.TransitionSystem
open import Cubical.Categories.CBPV.Instances.Kleisli
open import Cubical.Categories.Enriched.Functors.Base
open import Cubical.Categories.Enriched.Instances.FromCat 
open import Cubical.Categories.Enriched.Instances.Presheaf.ChangeBase
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.TransitionSystem
open import Cubical.Categories.Monad.ExtensionSystem 
  renaming (Kleisli to KleisliCat)
open import Cubical.Categories.Monoidal.Instances.Presheaf
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.WithFamilies.Simple.Functor
open import Cubical.Categories.WithFamilies.Simple.Instances.Sets
  renaming (SET to SETSCwF)

open EnrichedFunctor
open Functor
open PshHom
open TSystem
open TSystem[_,_]

private 
  variable
    ℓ : Level 

-- TODO generalize this to (any?) extension system
-- not just delay
module _ (ℓ : Level) where 

  IdPreFun : PreFunctor (SETSCwF ℓ) (SETSCwF ℓ)
  IdPreFun .fst = Id
  IdPreFun .snd .fst ty = ty
  IdPreFun .snd .snd .N-ob c x = x
  IdPreFun .snd .snd .N-hom _ _ _ _ = refl

  𝓥 = PshMon.𝓟Mon (SET ℓ) ℓ

  -- F-stacks can be defined by a non enriched functor 
  -- implement enrichF

  S : CBPVModel (ℓ-suc ℓ) ℓ (ℓ-suc ℓ) ℓ (ℓ-suc ℓ) ℓ 
  S = (TSystemModel ℓ)

  T : CBPVModel (ℓ-suc ℓ) ℓ (ℓ-suc ℓ) ℓ (ℓ-suc ℓ) ℓ 
  T = (Kleisli DExt) 

  open import Cubical.Categories.Limits.Terminal
  open import Cubical.Categories.Instances.FunctorAlgebras
  open AlgebraHom
  open import Cubical.Data.Sum renaming (rec to rec⊎)
  open import Cubical.Data.Unit 

  exe : (B : TSystem ℓ) → ⟨ B .state ⟩ → Delay {ℓ = ℓ} ⟨ B .term ⟩ 
  exe B = 
    terminalArrow 
      (CoAlg (B .term)) 
      (FinalCoAlg (B .term)) 
      (algebra (B .state) (B .trans))  
      .carrierHom

  runE : {B B' : TSystem ℓ} → 
    TSysCat [ B , B' ] → (K DExt) [ B .term , B' .term ] 
  runE {B} {B'} f t = 
      rec⊎ 
        (delay_ ∘S inl) -- done, ret
        (exe B') -- exec
        (f .tmap t) -- either it is done, or we execute

  EF' : Functor TSysCat (K DExt)
  EF' .F-ob S = S .term
  EF' .F-hom = runE
  EF' .F-id = refl
  EF' .F-seq {S}{T}{R} f g = funExt goal where 

    -- just do this by cases
    -- TODO: break the cong₃ rec⊎ into lemmas about steping if done or not
    goal : (s : ⟨ S .term ⟩ ) → runE (f ∘TS g) s ≡ (K DExt Category.⋆ runE f) (runE g) s 
    goal s with matcht {f = f} s
    ... | inl (t-trm , p) with matcht {f = g} t-trm 
    ... | inl (r-trm , q) = 
      cong₃ rec⊎ refl refl (cong₃ rec⊎ refl refl p) 
      ∙ cong₃ rec⊎ refl refl q 
      ∙ ((cong₃ rec⊎ refl refl (sym q)) 
      ∙ sym (bind-ret-l _ _)) 
      ∙  cong₂ bind-d (cong₃ rec⊎ refl refl (sym p)) refl
      
    ... | inr (t , h) = 
      cong₃ rec⊎ refl refl (cong₃ rec⊎ refl refl p) 
      ∙ cong₃ rec⊎ refl refl h 
      ∙ (cong₃ rec⊎ refl refl (sym h) 
      ∙ sym (bind-ret-l _ _ )) 
      ∙ cong₂ bind-d (cong₃ rec⊎ refl refl (sym p)) refl
    ... | inr x = ?


  EF : EnrichedFunctor 𝓥 (S . snd .fst) (T .snd .fst)
  EF = Functor→Enriched TSysCat (K DExt) EF' 


  -- thse coercions are essentially Id since there is no lifting
  -- as the CBPV models are of the same levels
  dumb1 : EnrichedFunctor 𝓥 (LiftE (S .snd .fst)) (S .snd .fst)
  dumb1 = ?

  dumb2 : EnrichedFunctor 𝓥 (T .snd .fst) (BaseChange (IdPreFun .fst) ℓ ℓ (T .snd .fst))
  dumb2 .F-ob X = X
  dumb2 .F-hom = ?
  dumb2 .F-id = {!   !}
  dumb2 .F-seq = {!   !}

  MultiStep : CBPVFunctor S T 
  MultiStep = IdPreFun , ((eseq 𝓥  dumb1 (eseq 𝓥 EF dumb2 ) ) , {!   !})
{-
  MultiStep : CBPVFunctor S T
  MultiStep .PreF = IdPreFun
  -- My machine dies trying to work with these holes
  -- or rather .. LiftE and BaseChange ..
  MultiStep .F-stacks = {!   !} -- eseq 𝓥 ? ?
  MultiStep .F-comp = {!   !}
-}
