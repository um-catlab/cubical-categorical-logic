{-# OPTIONS --type-in-type #-}
module HyperDoc.Operational.BiAlg where

open import Cubical.Data.Sigma 
open import Cubical.Data.Sum 

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Structure
open import Cubical.HITs.PropositionalTruncation renaming (rec to hrec)
open import Cubical.Functions.Logic

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets 
open import Cubical.Categories.NaturalTransformation 

open import HyperDoc.Operational.Graph
open import HyperDoc.Algebra.Algebra 


open Category
open Functor
open NatTrans


{-
sigToFun : Signature → Functor (SET _) (SET _) 
sigToFun Sig .F-ob X = {!   !}
sigToFun Sig .F-hom = {!   !}
sigToFun Sig .F-id = {!   !}
sigToFun Sig .F-seq = {!   !}
-}



module getSig where 
  Sig : Functor (SET _ )(SET _) 
  Sig .F-ob (X , isSetX) .fst = X × X
  Sig .F-ob (X , isSetX) .snd = isSet× isSetX isSetX
  Sig .F-hom f (M , N) = f M , f N
  Sig .F-id = {!   !}
  Sig .F-seq = {!   !}

  Pow : Functor (SET _) (SET _) 
  Pow .F-ob (X , isSetX) = (ℙ X) , isSetℙ
  Pow .F-hom {X}{Y} f P y = (∃[ x ∈ ⟨ X ⟩ ] (f x ≡ y) × (x ∈ P)) , squash₁
  Pow .F-id = {!   !}
  Pow .F-seq = {!   !}



  SigAlg : Type 
  SigAlg = Σ[ X ∈ hSet _ ] (⟨ Sig .F-ob X ⟩ → ⟨ X ⟩)

  PowCoAlg : Type 
  PowCoAlg = Σ[ X ∈ hSet _ ] (⟨ X ⟩ → ⟨ Pow .F-ob X ⟩)

  Distr : Type 
  Distr = NatTrans (Sig ∘F Pow) (Pow ∘F Sig) 
  record BiAlg : Type where 
    field 
      car : hSet _ 
      alg : ⟨ Sig .F-ob car ⟩ → ⟨ car ⟩
      coalg : ⟨ car ⟩ → ⟨ Pow .F-ob car ⟩
      lam : Distr
      cond : (x : ⟨ Sig .F-ob car ⟩ ) → coalg (alg x) ≡ Pow .F-hom alg (lam .N-ob car (Sig .F-hom coalg x))

  open BiAlg

  data VTy : Type where
  data CTy : Type where 

  data _⊢c_ : VTy → CTy → Type where 
    isSet⊢c : ∀ {A B} → isSet ( A ⊢c B)
    get : ∀ {A B} → A ⊢c B → A ⊢c B → A ⊢c B 



  data _↦_ : ∀{A B} →  A ⊢c B → A ⊢c B → Type where 
    isProp↦ : ∀{A B}{M M' : A ⊢c B} → isProp (M ↦ M')

  co : ∀{A B} → A ⊢c B → ℙ (A ⊢c B) 
  co M M' = (M ↦ M') , isProp↦


  lam' : Distr 
  lam' .N-ob (X , isSetX)(P , P') (x , x') = P x ⊓ P' x'
  lam' .N-hom f = funExt λ (P , P') → funExt λ (y , y') →
    Σ≡Prop (λ _ → isPropIsProp) {!   !}
    -- yes, just need to shuffle sigma and truncation
    -- but I think this is safe because the first and second component of sigma are truncated

  biAlg : VTy → CTy → BiAlg 
  biAlg A B .car = (A ⊢c B) , isSet⊢c
  biAlg A B .alg (M , N) = get M N
  biAlg A B .coalg M M' = (M ↦ M') , isProp↦
  biAlg A B .lam = lam'
  biAlg A B .cond (M , M') = funExt λ N → ⇔toPath 
    {- this direction is a bit trickier 
        Given 
          get M M' ↦ N 

        Provide 
          Ms,M's : A ⊢c B 
          get Ms M's ≡ N 
          M ↦ Ms 
          M' ↦ M's 

        So this direction is like the inverse of the rule.
        if we pattern match on derivation 
          get M M' ↦ N 
        we must be able to get this information

        So it should be the case that this is the only possible reduction rule 
        for top level operations ..?

    -}
    ({!   !}) 
    {- 
    Yes, if we have reduction congruence rule
      ∀ i, M_i ↦ M'_i 
      ---------------- 
      op(M1,...,Mn)↦op(M1',...,Mn')
    -}
    (hrec isProp↦ λ {((Ms , M's) , getMsM's≡N ,  M↦Ms , M'↦M's) → subst (λ h → get M M' ↦ h ) getMsM's≡N {!   !}})
  -- Σ≡Prop (λ _ → isPropIsProp) {! ⇔toPath  !} 
  {-
  (get M M' ↦ M'')  ≡

    ∥
    Σ (Σ (N : A ⊢c B) (N' : A ⊢c B))
    ( Σ (get N N' ≡ M'')
        Σ (M ↦ N) (M ↦ N'))
    ∥₁

  So this says 
      M ↦ N  M' ↦ N'
    ------------------------
      get M M' ↦ get N N'



-}

module getsetSig where 
  Sig : Functor (SET _ )(SET _) 
  Sig .F-ob (X , isSetX) .fst = (X × X) ⊎ X
  Sig .F-ob (X , isSetX) .snd = {!   !}
  Sig .F-hom f (_⊎_.inl (x , x')) = _⊎_.inl ((f x) , f x)
  Sig .F-hom f (_⊎_.inr x) = _⊎_.inr (f x)
  Sig .F-id = {!   !}
  Sig .F-seq = {!   !}

  Pow : Functor (SET _) (SET _) 
  Pow .F-ob (X , isSetX) = (ℙ X) , isSetℙ
  Pow .F-hom {X}{Y} f P y = (∃[ x ∈ ⟨ X ⟩ ] (f x ≡ y) × (x ∈ P)) , squash₁
  Pow .F-id = {!   !}
  Pow .F-seq = {!   !}



  SigAlg : Type 
  SigAlg = Σ[ X ∈ hSet _ ] (⟨ Sig .F-ob X ⟩ → ⟨ X ⟩)

  PowCoAlg : Type 
  PowCoAlg = Σ[ X ∈ hSet _ ] (⟨ X ⟩ → ⟨ Pow .F-ob X ⟩)

  Distr : Type 
  Distr = NatTrans (Sig ∘F Pow) (Pow ∘F Sig) 
  record BiAlg : Type where 
    field 
      car : hSet _ 
      alg : ⟨ Sig .F-ob car ⟩ → ⟨ car ⟩
      coalg : ⟨ car ⟩ → ⟨ Pow .F-ob car ⟩
      lam : Distr
      cond : (x : ⟨ Sig .F-ob car ⟩ ) → coalg (alg x) ≡ Pow .F-hom alg (lam .N-ob car (Sig .F-hom coalg x))

  open BiAlg

  data VTy : Type where
  data CTy : Type where 

  data _⊢c_ : VTy → CTy → Type where 
    isSet⊢c : ∀ {A B} → isSet ( A ⊢c B)
    get : ∀ {A B} → A ⊢c B → A ⊢c B → A ⊢c B 
    set0 : ∀ {A B} → A ⊢c B → A ⊢c B  



  data _↦_ : ∀{A B} →  A ⊢c B → A ⊢c B → Type where 
    isProp↦ : ∀{A B}{M M' : A ⊢c B} → isProp (M ↦ M')

  co : ∀{A B} → A ⊢c B → ℙ (A ⊢c B) 
  co M M' = (M ↦ M') , isProp↦


  lam' : Distr 
  lam' .N-ob (X , isSetX) (_⊎_.inl (P , P')) (_⊎_.inl (x , x')) = P x ⊓ P' x'
  lam' .N-ob (X , isSetX) (_⊎_.inl (P , P')) (_⊎_.inr x) = ⊥
  lam' .N-ob (X , isSetX) (_⊎_.inr P) (_⊎_.inl x) = ⊥
  lam' .N-ob (X , isSetX) (_⊎_.inr P) (_⊎_.inr x) = P x
  lam' .N-hom {X} {Y} f = funExt λ {(_⊎_.inl (P , P')) → funExt λ {(_⊎_.inl (x , x')) →
     ⇔toPath {!  !} {!   !}
                                                                 ; (_⊎_.inr x) → {!   !}}
                                  ; (_⊎_.inr P) → {!   !}}
  {-}
  lam' .N-ob (X , isSetX)(P , P') (x , x') = P x ⊓ P' x'
  lam' .N-hom f = funExt λ (P , P') → funExt λ (y , y') →
    Σ≡Prop (λ _ → isPropIsProp) {!   !}
    -- yes, just need to shuffle sigma and truncation
    -- but I think this is safe because the first and second component of sigma are truncated
-}
{-}
  biAlg : VTy → CTy → BiAlg 
  biAlg A B .car = (A ⊢c B) , isSet⊢c
  biAlg A B .alg (M , N) = get M N
  biAlg A B .coalg M M' = (M ↦ M') , isProp↦
  biAlg A B .lam = lam'
  biAlg A B .cond (M , M') = funExt λ N → ⇔toPath {!   !} {!   !}
-}
{-

-}
  --  funExt λ N → ΣPathP ({!   !} , {!   !})

{-
-- get, set0, set1
Sig : Functor (SET _ )(SET _) 
Sig .F-ob (X , isSetX) .fst = (X × X) ⊎ (X ⊎ X)
Sig .F-ob (X , isSetX) .snd = isSet⊎ (isSet× isSetX isSetX) {!   !}
Sig .F-hom f (inl x) = inl (f (x .fst) , f (x .snd))
Sig .F-hom f (inr (inl x)) = inr (inl (f x))
Sig .F-hom f (inr (inr x)) = inr (inr (f x))
Sig .F-id = {!   !}
Sig .F-seq = {!   !}

SigAlg : Type 
SigAlg = Σ[ X ∈ hSet _ ] (⟨ Sig .F-ob X ⟩ → ⟨ X ⟩)

PowCoAlg : Type 
PowCoAlg = Σ[ X ∈ hSet _ ] (⟨ X ⟩ → ⟨ Pow .F-ob X ⟩)

Distr : Type 
Distr = NatTrans (Sig ∘F Pow) (Pow ∘F Sig) 
record BiAlg : Type where 
  field 
    car : hSet _ 
    alg : ⟨ Sig .F-ob car ⟩ → ⟨ car ⟩
    coalg : ⟨ car ⟩ → ⟨ Pow .F-ob car ⟩
    lam : Distr
    cond : (x : ⟨ Sig .F-ob car ⟩ ) → coalg (alg x) ≡ Pow .F-hom alg (lam .N-ob car (Sig .F-hom coalg x))

open BiAlg
module _ (O[A,B] : Graph _ _ ) where
  data VTy : Type where
  data CTy : Type where 

  data _⊢c_ : VTy → CTy → Type where 
    isSet⊢c : ∀ {A B} → isSet ( A ⊢c B)
    get : ∀ {A B} → A ⊢c B → A ⊢c B → A ⊢c B 
    set0 : ∀ {A B} → A ⊢c B → A ⊢c B
    set1 : ∀ {A B} → A ⊢c B → A ⊢c B 

  
  data _↦_ : ∀{A B} →  A ⊢c B → A ⊢c B → Type where 
    isProp↦ : ∀{A B}{M M' : A ⊢c B} → isProp (M ↦ M')

  co : ∀{A B} → A ⊢c B → ℙ (A ⊢c B) 
  co M M' = (M ↦ M') , isProp↦


  biAlg : VTy → CTy → BiAlg 
  biAlg A B .car = (A ⊢c B) , isSet⊢c
  biAlg A B .alg (inl (M , N)) = get M N
  biAlg A B .alg (inr (inl M)) = set0 M
  biAlg A B .alg (inr (inr M)) = set1 M
  biAlg A B .coalg = co
  biAlg A B .lam .N-ob (X , isSetX) (inl (P , P')) (inl (x , x')) = {!   !}
  biAlg A B .lam .N-ob (X , isSetX) (inl (P , P')) (inr (inl x)) = {!   !} -- bot ?
  biAlg A B .lam .N-ob (X , isSetX) (inl (P , P')) (inr (inr x)) = {!   !} -- bot ?, not natural?
  biAlg A B .lam .N-ob (X , isSetX) (inr (inl P)) = {!   !}
  biAlg A B .lam .N-ob (X , isSetX) (inr (inr P)) = {!   !}
  biAlg A B .lam .N-hom = {!   !}
  biAlg A B .cond = {!   !} 

-}