{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.CBPV.MultiStep where 
open import Cubical.Data.Sum renaming (rec to rec⊎)
open import Cubical.Data.Unit 

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
open import Cubical.Categories.Enriched.Instances.Presheaf.ChangeBaseFunctor
open import Cubical.Categories.Enriched.Instances.Presheaf.Self
open import Cubical.Categories.Enriched.NaturalTransformation.Base
open import Cubical.Categories.Instances.FunctorAlgebras
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.TransitionSystem
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Monad.ExtensionSystem 
  renaming (Kleisli to KleisliCat)
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Monoidal.Instances.Presheaf
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.WithFamilies.Simple.Functor
open import Cubical.Categories.WithFamilies.Simple.Instances.Sets
  renaming (SET to SETSCwF)

open AlgebraHom
open EnrichedFunctor
open EnrichedNatTrans
open Functor
open PshHom
open NatTrans
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

  𝓥 = PshMon.𝓟Mon (SET ℓ) (ℓ-suc ℓ)

  S : CBPVModel (ℓ-suc ℓ) ℓ (ℓ-suc ℓ) ℓ (ℓ-suc ℓ) ℓ 
  S = (TSystemModel ℓ)

  T : CBPVModel (ℓ-suc ℓ) ℓ (ℓ-suc ℓ) ℓ (ℓ-suc ℓ) ℓ 
  T = (Kleisli DExt) 

  exe : (B : TSystem ℓ) → ⟨ state B ⟩ → Delay {ℓ = ℓ} ⟨ B .term ⟩ 
  exe B = 
    terminalArrow 
      (CoAlg (B .term)) 
      (FinalCoAlg (B .term)) 
      (algebra (state B) (step B))  
      .carrierHom

  runE : {B B' : TSystem ℓ} → 
    TSysCat [ B , B' ] → (K DExt) [ B .term , B' .term ] 
  runE {B} {B'} f t = exe B' (f .s-map (inl t))

  EF' : Functor (TSysCat {ℓ}) (K {ℓ} DExt) 
  EF' .F-ob S = S .term
  EF' .F-hom = runE
  EF' .F-id = funExt λ t → eq-d refl
  EF' .F-seq {S}{T}{R} f g = funExt λ s → eq-d {!   !}

  EF : EnrichedFunctor (PshMon.𝓟Mon (SET ℓ) ℓ) (S . snd .fst) (T .snd .fst)
  EF = Functor→Enriched TSysCat (K DExt) EF'

  exe-lemma : {S T : TSystem ℓ}
    {f : TSystem[ S , T ]}
    {s : ⟨ state S ⟩} → 
    exe T (f .s-map s) 
    ≡ bind-d (exe S s) (runE f)
  exe-lemma {S}{T}{f}{s}= {!   !}
  
  ENT : EnrichedNatTrans (S .snd .snd) (eseq _ EF (T .snd .snd)) 
  ENT .E-N-ob S = 
    adjL _ _ (
      natTrans 
        (λ X (tt* , s) → lift λ x → exe S (s x .lower)) 
        λ f → funExt λ _ → cong lift refl) 
        -- could just be refl, Agda says no
  ENT .E-N-hom S T = helper _ _  (
    makeNatTransPath (funExt λ X → funExt λ (f , s) → 
      cong lift (funExt λ x → exe-lemma{S}{T}{f .lower x}{s x .lower})))

{-
  exe-term : (B : TSystem ℓ)(s :  ⟨ state B ⟩)→ 
    (isTerm : Σ[ t ∈ ⟨ B . term ⟩ ] (step B) s ≡ inl t) → 
    exe B s ≡ ret-d (isTerm .fst) 
  exe-term B s p = {!   !}
-}

{-
  dumb : EnrichedFunctor 𝓥 (LiftE (T .snd .fst)) (BaseChange Id ℓ ℓ (T .snd .fst)) 
  dumb .F-ob X = X
  dumb .F-hom = natTrans (λ x x₁ → x₁) λ f → refl
  dumb .F-id = makeNatTransPath refl
  dumb .F-seq = makeNatTransPath refl

  efun = eseq 𝓥 (LiftEF EF (ℓ-suc ℓ)) dumb
-}
  -- this proof will be similar to the one for monotone sequences
  


{-}
    -- just do this by cases
    -- TODO: break the cong₃ rec⊎ into lemmas about steping if done or not
    goal : (s : ⟨ S .term ⟩ ) → runE (f ∘TS g) s ≡ (K {ℓ} DExt Category.⋆ runE f) (runE g) s 
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
      -}
      
{-
  -- this is what is really going on without level bs
  ENT : EnrichedNatTrans (S .snd .snd) (eseq _ EF (T .snd .snd)) 
  ENT .E-N-ob S .N-ob Γ tt* = 
    pshhom 
      (λ Δ (γ , m) → lift λ Δ∙ → exe S (m Δ∙ .lower)) 
      λ Δ Θ γ (δ , m) → refl
  ENT .E-N-ob S .N-hom f = funExt λ tt* → 
    makePshHomPath (funExt λ Γ → funExt λ (Δ , m) → 
      refl)
  ENT .E-N-hom S T = {!   !}

    makeNatTransPath (funExt λ Γ → funExt λ k → 
    makePshHomPath (funExt λ Δ → funExt λ (γ , m) → 
    cong lift (funExt λ Δ∙ → exe-lemma {S}{T}{k .lower (γ Δ∙)}{m Δ∙ .lower})))
    -}
{-
  -- this is the really dumb lifting version
  -- note that is just the same as the above definition
  -- but with an extra lift
  ent : EnrichedNatTrans 
    (eseq 𝓥 (LiftEF (S .snd .snd) (ℓ-suc ℓ)) (LiftSelf ℓ (ℓ-suc ℓ))) 
    (eseq 𝓥 
      efun
      (eseq 𝓥 
        (BaseChangeF Id {ℓS = ℓ} ℓ (T .snd .snd)) 
        (BaseLiftSelf Id (ℓ-suc ℓ)))) 
  ent .E-N-ob S .N-ob Γ tt* .N-ob Δ (γ , m) = 
    lift (lift λ Δ∙ → exe S (m .lower Δ∙ .lower))
  ent .E-N-ob S .N-ob Γ tt* .N-hom Δ Θ γ (δ , m) = refl
  ent .E-N-ob S .N-hom f = funExt λ tt* → 
    makePshHomPath (funExt λ Γ → funExt λ (Δ , m) → 
      refl)
  ent .E-N-hom S T = 
    makeNatTransPath (funExt λ Γ → funExt λ k → 
    makePshHomPath (funExt λ Δ → funExt λ (γ , m) → 
    cong lift (cong lift (funExt λ Δ∙ → 
      exe-lemma {S}{T}{k .lower .lower (γ Δ∙)}{m .lower Δ∙ .lower}))))

  MultiStep : CBPVFunctor S T 
  MultiStep = 
    IdPreFun , efun , ent
    -}