{-# OPTIONS --allow-unsolved-metas #-}
module Cubical.Categories.Instances.TransitionSystem where

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to rec⊎ ; map to map⊎)
open import Cubical.Data.Sum.More

open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Categories.Category

open Category
open Iso

private
  variable
    ℓ : Level

record TSystem (ℓ : Level) : Type(ℓ-suc ℓ) where
  field
    term : hSet ℓ
    redex : hSet ℓ 
  state : hSet ℓ 
  state = ⟨ term ⟩ ⊎ ⟨ redex ⟩ , isSet⊎ (term .snd) (redex .snd) 

  field 
    red : ⟨ redex ⟩ → ⟨ state ⟩ 

  step : ⟨ state ⟩ → ⟨ term ⟩ ⊎ ⟨ state ⟩ 
  step = map⊎ (idfun _) red 

  open import Cubical.Data.Nat

  stepn : ℕ → ⟨ state ⟩ → ⟨ state ⟩
  stepn zero s = s
  stepn (suc n) = rec⊎ inl λ r → stepn n (inr r)

  _↦*_ : (s t : ⟨ state ⟩) → hProp ℓ
  _↦*_ s t = (Σ[ n ∈ ℕ ] stepn n s ≡ t) , {!   !}

open TSystem
open import Cubical.Data.Unit
open import Cubical.Data.Empty

_≤_ : {ℓ : Level}{A B : Set ℓ} → (A ⊎ B) → (A ⊎ B) →  Set ℓ 
inl t ≤ _ = Unit*
inr r ≤ inl t' = ⊥*
inr r ≤ inr r' = r ≡ r'
-- not an ordering on state, but an ordering on ⟨ term ⟩ ⊎ ⟨ state ⟩ 


module _ (S T : TSystem ℓ) where
  record TSystem[_,_] : Type ℓ where
    field
      s-map : ⟨ state S ⟩ → ⟨ state T ⟩ 

    laxTy : ⟨ state S ⟩ → Type ℓ 
    laxTy s = 
      rec⊎ 
        (λ _ → Unit*) 
        (λ rs → 
          rec⊎ 
            (λ _ → ⊥*) 
            (λ rt → s-map (red S rs) ≡ red T rt) 
            (s-map (inr rs))) 
        s    
    field 
      lax : (s : ⟨ state S ⟩) → laxTy s
         -- (λ r → inr (s-map (red S r)) ≡ step T (s-map (inr r))) s



  TSystemHomSigma : Type ℓ
  TSystemHomSigma =
    Σ[ s-map ∈ (⟨ state S ⟩ → ⟨ state T ⟩) ]
    ((s : ⟨ state S ⟩) → 
        rec⊎ 
          (λ _ → Unit*) 
          (λ rs → 
          rec⊎ 
            (λ _ → ⊥*) 
            (λ rt → s-map (red S rs) ≡ red T rt) 
            (s-map (inr rs)))
          s)

        
  TSysHomIsoΣ : Iso (TSystem[_,_]) (TSystemHomSigma)
  unquoteDef TSysHomIsoΣ =
    defineRecordIsoΣ TSysHomIsoΣ (quote (TSystem[_,_]))

open TSystem[_,_]

TSysMap≡ : {S T : TSystem ℓ}{f g : TSystem[ S , T ]} →
  f .s-map ≡ g .s-map → f ≡ g
TSysMap≡ {S = S}{T}{f}{g} p = 
  isoFunInjective 
    (TSysHomIsoΣ S T) 
    f 
    g 
    (ΣPathP (p , funExt λ {(inl x) → refl
                         ; (inr x) → toPathP {! isSet⊎ ? ? ? ? ? ?!}}))

idSysHom : {S : TSystem ℓ} → TSystem[ S , S ]
idSysHom {S} .s-map x = x
idSysHom {S = S} .lax (inl x) = tt*
idSysHom {S = S} .lax (inr x) = refl

_∘TS_ : {S T R : TSystem ℓ} →
  TSystem[ S , T ] → TSystem[ T , R ] → TSystem[ S , R ]
(f ∘TS g) .s-map = g .s-map ∘S f .s-map
(f ∘TS g) .lax (inl x) = tt*
(f ∘TS g) .lax (inr x) = {!   !}

TSysCat : {ℓ : Level} → Category (ℓ-suc ℓ) ℓ
TSysCat .ob = TSystem _
TSysCat .Hom[_,_] = TSystem[_,_]
TSysCat .id = idSysHom
TSysCat ._⋆_ = _∘TS_
TSysCat .⋆IdL = {!   !}
TSysCat .⋆IdR = {!   !}
TSysCat .⋆Assoc = {!   !}
TSysCat .isSetHom = {!   !}

{-
  TSystemHomSigma : Type ℓ
  TSystemHomSigma =
    Σ[ s-map ∈ (⟨ state S ⟩ → ⟨ state T ⟩) ]
    ((s : ⟨ state S ⟩) → 
        rec⊎ 
          (λ _ → Unit*) 
          (λ r → inr (s-map (red S r)) ≡ step T (s-map (inr r))) s)

  TSysHomIsoΣ : Iso (TSystem[_,_]) (TSystemHomSigma)
  unquoteDef TSysHomIsoΣ =
    defineRecordIsoΣ TSysHomIsoΣ (quote (TSystem[_,_]))
    
open TSystem[_,_]


TSysMap≡ : {S T : TSystem ℓ}{f g : TSystem[ S , T ]} →
  f .s-map ≡ g .s-map → f ≡ g
TSysMap≡ {S = S}{T}{f}{g} p = 
  isoFunInjective 
    (TSysHomIsoΣ S T) 
    f 
    g 
    (ΣPathP (p , funExt λ {(inl x) → refl
                         ; (inr x) → toPathP 
                          (isSet⊎ (T . term .snd) (state T .snd)  _ _ _ _)}))

TSysMapisSet : {S T : TSystem ℓ} → isSet (TSystem[ S , T ])
TSysMapisSet {S = S} {T} =
  isSetRetract
    (fun (TSysHomIsoΣ S T))
    (inv (TSysHomIsoΣ S T))
    (leftInv (TSysHomIsoΣ S T))
    (isSetΣ (isSet→ (state T .snd)) λ f →  
      isProp→isSet (isPropΠ λ {(inl x) → isPropUnit*
                             ; (inr x) → isSet⊎ (T .term .snd) (state T .snd) _ _ }))
    
idSysHom : {S : TSystem ℓ} → TSystem[ S , S ]
idSysHom {S} .s-map x = x
idSysHom {S = S} .lax (inl x) = tt*
idSysHom {S = S} .lax (inr x) = refl

match : {S : TSystem ℓ} → (s : ⟨ state S ⟩) → 
  (Σ[ t ∈ ⟨ S .term ⟩ ] (step S s ≡ inl t)) 
  ⊎ (Σ[ s' ∈ ⟨ state S ⟩ ] step S s ≡ inr s')
match {S = S} s with step S s
... | inl x = inl (x , refl)
... | inr x = inr (x , refl)

_∘TS_ : {S T R : TSystem ℓ} →
  TSystem[ S , T ] → TSystem[ T , R ] → TSystem[ S , R ]

(f ∘TS g) .s-map = g .s-map ∘S f .s-map
(f ∘TS g) .lax (inl x) = tt*
(_∘TS_){S = S}{T}{R} f g .lax (inr Sr) with match (f .s-map (inr Sr))
... | inl (t-term , p) = {!   !}
... | inr (t , p) = {!   !}

-}





{-
= goal where 

  have1 : inr (f .s-map (red S x)) ≡ step T (f .s-map (inr x)) 
  have1 = f .lax (inr x)

  have2 : {!g .lax (f .s-map (inr x))!}
  have2 = g .lax (f .s-map (inr x))

  goal : inr (g .s-map (f .s-map (red S x))) 
    ≡ step R (g .s-map (f .s-map (inr x)))
  goal = {!   !}

-}


    --sSetΠ λ {(inl x) → isSetUnit*
     --                                               ; (inr x) → {!   !}})
   {-} (isSetΣ (isSet→ (T .state .snd)) λ _ → 
    isSetΣ (isSet→ (isSet⊎ (T .term .snd) (T .state .snd))) 
    λ _ → isProp→isSet (isPropImplicitΠ  λ _ → 
    isSet⊎ (T .term .snd) (T .state .snd) _ _)) -}



   -- (ΣPathP (p , ΣPathP (q , implicitFunExt λ {_} → 
   -- toPathP (isSet⊎ (T .term .snd) (T .state .snd) _ _  _ _))))
{-
-- t-map is not used 
module _ (S T : TSystem ℓ) where
  record TSystem[_,_] : Type ℓ where
    field
      s-map : ⟨ state S ⟩ → ⟨ state T ⟩ 
      t-map : ⟨ term S ⟩ → ⟨ term T ⟩  
      lax : {s : ⟨ state S ⟩} → 
         map⊎ t-map s-map (step S s) ≤ step T (s-map s) 

    -- proofs 
    case1 : {t : ⟨ term S ⟩} → lax {inl t} ≡ tt* 
    case1 = refl

    type : {r : ⟨ redex S ⟩} → inr (s-map (red S r)) ≤ step T (s-map (inr r)) 
    type {r} = lax{inr r} 

    --case2' : {r : ⟨ redex S ⟩}{t' : ⟨ term T ⟩} → {!  lax {inr r} !} 
   --  case2' = {!   !} 

    -- s = inr r   
    -- s is a redex and therefore MUST step
    -- s-map (inr r) = inl t'  
    -- s-map maps into a terminal, so T does NOT step
    -- false
    case2 : {r : ⟨ redex S ⟩}{t' : ⟨ term T ⟩} → 
      inr (s-map (red S r)) ≤ step T (inl t') ≡ ⊥* 
    case2 = refl

    -- s = inr r 
    -- s is a redex and therefore MUST step
    -- s-map (inr r) = inr r' 
    -- s-map maps into a redex, so T MUST step
    case3 : {r : ⟨ redex S ⟩}{r' : ⟨ redex T ⟩} → 
      inr (s-map (red S r)) ≤ step T (inr r') 
      ≡ ((s-map (red S r) ≡ (red T r'))) 
      -- s-map (red S r) ≡ (red T (s-map r))
    case3 = refl

    _ : {r' : ⟨ redex T ⟩}→ step T (inr r') ≡ inr (red T r')
    _ = refl

-}
    




{-
record TSystem (ℓ : Level) : Type(ℓ-suc ℓ) where
  field
    state : hSet ℓ
    term : hSet ℓ
    trans : ⟨ state ⟩ → ⟨ term ⟩ ⊎ ⟨ state ⟩ 

open TSystem

module _ (S T : TSystem ℓ) where
  record TSystem[_,_] : Type ℓ where
    field
      smap : ⟨ S .state ⟩  → ⟨ T .state ⟩
      tmap : ⟨ S .term ⟩ → ⟨ T . term ⟩ ⊎ ⟨ T . state ⟩
      comm : {s : ⟨ S . state ⟩} → 
        T .trans (smap s) ≡ rec⊎ tmap (λ s' → inr (smap s')) (S .trans s) 
    {-
      If s steps to a terminal
      then tmap must behave the same as smap
        
        s -- S .trans --> ■ 
        |                 |
      f .smap           f .tmap
        |                 |
        t -- T .trans --> t'

      If s steps to a non-terminal
      then we just have a graph homomorphism

        s -- S .trans --> s'
        |                 |
      f .smap           f .smap 
        |                 |
        t -- T .trans --> t'
    -}


  TSystemHomSigma : Type ℓ
  TSystemHomSigma =
    Σ[ smap ∈ (⟨ S .state ⟩ → ⟨ T .state ⟩) ]
    Σ[ tmap ∈ (⟨ S .term ⟩ → ⟨ T .term ⟩ ⊎ ⟨ T .state ⟩ ) ] 
    ({s : ⟨ S .state ⟩} → 
      T .trans (smap s) ≡ rec⊎ tmap (λ s' → inr (smap s')) (S .trans s))

  TSysHomIsoΣ : Iso (TSystem[_,_]) (TSystemHomSigma)
  unquoteDef TSysHomIsoΣ =
    defineRecordIsoΣ TSysHomIsoΣ (quote (TSystem[_,_]))
    
open TSystem[_,_]

TSysMap≡ : {S T : TSystem ℓ}{f g : TSystem[ S , T ]} →
  f .smap ≡ g .smap → 
  f .tmap ≡ g .tmap → f ≡ g
TSysMap≡ {S = S}{T}{f}{g} p q = 
  isoFunInjective 
    (TSysHomIsoΣ S T) 
    f 
    g 
    (ΣPathP (p , ΣPathP (q , implicitFunExt λ {_} → 
    toPathP (isSet⊎ (T .term .snd) (T .state .snd) _ _  _ _))))

TSysMapisSet : {S T : TSystem ℓ} → isSet (TSystem[ S , T ])
TSysMapisSet {S = S} {T} =
  isSetRetract
    (fun (TSysHomIsoΣ S T))
    (inv (TSysHomIsoΣ S T))
    (leftInv (TSysHomIsoΣ S T))
    (isSetΣ (isSet→ (T .state .snd)) λ _ → 
    isSetΣ (isSet→ (isSet⊎ (T .term .snd) (T .state .snd))) 
    λ _ → isProp→isSet (isPropImplicitΠ  λ _ → 
    isSet⊎ (T .term .snd) (T .state .snd) _ _))

idSysHom : {S : TSystem ℓ} → TSystem[ S , S ]
idSysHom {S} .smap x = x
idSysHom {S} .tmap x = inl x
idSysHom {S = S} .comm {s = s} with S .trans s 
... | inl x = refl
... | inr x = refl

match : {S : TSystem ℓ} → (s : ⟨ S .state ⟩) → 
  (Σ[ t ∈ ⟨ S .term ⟩ ] (S .trans s ≡ inl t)) 
  ⊎ (Σ[ s' ∈ ⟨ S .state ⟩ ] S .trans s ≡ inr s')
match {S = S} s with S .trans s 
... | inl x = inl (x , refl)
... | inr x = inr (x , refl)

matcht : {S T : TSystem ℓ}{f : TSystem[ S , T ]}→ 
  (s : ⟨ S .term ⟩) →  (Σ[ t-trm ∈  ⟨ T .term ⟩ ] (f .tmap s ≡ inl t-trm))
                       ⊎ (Σ[ t ∈ ⟨ T .state ⟩ ] (f .tmap s ≡ inr t))
matcht {f = f} s with (f .tmap s)
... | inl x = inl (x , refl)
... | inr x = inr (x , refl)

_∘TS_ : {S T R : TSystem ℓ} →
  TSystem[ S , T ] → TSystem[ T , R ] → TSystem[ S , R ]
(f ∘TS g) .smap = g .smap ∘S f .smap
(f ∘TS g) .tmap = rec⊎ (g .tmap) (inr ∘S g .smap) ∘S f .tmap
(_∘TS_){S = S}{T}{R}f g .comm {s} with match {S = S} s 
... | inl (t , p) = goal  
    ∙ cong₃ rec⊎ refl refl (sym p) where 

    have : T .trans (f .smap s) ≡ f .tmap t
    have = f .comm {s} ∙ cong₃  rec⊎ refl refl p 

    goal : R .trans (g .smap (f .smap s)) 
      ≡ rec⊎ (g .tmap) (λ s' → inr (g .smap s')) (f .tmap t) 
    goal  = g .comm {f .smap s} ∙ cong₃ rec⊎ refl refl have
    
... | inr (s' , p) = goal 
    ∙ cong₃ rec⊎ refl refl (sym p) where 

    have : T .trans (f .smap s) ≡ inr (f .smap s') 
    have = f .comm {s} ∙ cong₃ rec⊎ refl refl p

    goal : R .trans (g .smap (f .smap s)) ≡ inr (g .smap (f .smap s')) 
    goal = g .comm {f .smap s} ∙ cong₃ rec⊎ refl refl have

TSysCat : {ℓ : Level} → Category (ℓ-suc ℓ) ℓ
TSysCat .ob = TSystem _
TSysCat .Hom[_,_] = TSystem[_,_]
TSysCat .id = idSysHom
TSysCat ._⋆_ = _∘TS_
TSysCat .⋆IdL _ = TSysMap≡ refl refl
TSysCat .⋆IdR _ = TSysMap≡ refl (funExt λ _ → rec-eta)
TSysCat .⋆Assoc {x = S} f g h = TSysMap≡ refl (funExt goal) where 
  goal : (t : ⟨ S .term ⟩)  → rec⊎ (h .tmap) (λ x → inr (h .smap x))
      (rec⊎ (g .tmap) (λ x → inr (g .smap x)) (f .tmap t))
      ≡
      rec⊎ (λ x → rec⊎ (h .tmap) (λ x₁ → inr (h .smap x₁)) (g .tmap x))
      (λ x → inr (h .smap (g .smap x))) (f .tmap t)
  goal t with f .tmap t 
  ... | inl x = refl
  ... | inr x = refl
TSysCat .isSetHom = TSysMapisSet
-}













{-
record TSystem (ℓ : Level) : Type(ℓ-suc ℓ) where
  field
    term : hSet ℓ 
    redex : hSet ℓ 
    red : ⟨ redex ⟩ → ⟨ term ⟩ ⊎ ⟨ redex ⟩ 

  state : hSet ℓ 
  state = (⟨ term ⟩ ⊎ ⟨ redex ⟩) , isSet⊎ (term .snd) (redex .snd)

  step : ⟨ state ⟩ → ⟨ state ⟩ 
  step = rec⊎ inl red

  step' : ⟨ state ⟩ → ⟨ term ⟩ ⊎ ⟨ state ⟩ 
  step' = rec⊎ inl λ r → map⊎ (λ x → x) inr (red r) 

open TSystem
open import Cubical.Data.Unit
open import Cubical.Data.Empty

_≤_ : {ℓ : Level}{S : TSystem ℓ} → ⟨ state S ⟩ → ⟨ state S ⟩ → Set ℓ 
inl t ≤ _ = Unit*
inr r ≤ inl t' = ⊥*
inr r ≤ inr r' = r ≡ r'

module _ (S T : TSystem ℓ) where
  record TSystem[_,_] : Type ℓ where
    field
      s-map : ⟨ state S ⟩ → ⟨ state T ⟩
      lax : {s : ⟨ state S ⟩} → 
        rec⊎ (λ _ → Unit*) (λ r → _≤_{ℓ}{T}  (s-map (red S r)) (step T (s-map s))) s
       
        _≤_{ℓ}{T} 
          (rec⊎ (λ s-term → {!   !}) {!   !} s) 
          (step T ((s-map s))) 
        
   --   t-map : ⟨ S . term ⟩ → ⟨ T . term ⟩ 
    --  r-map : ⟨ S . redex ⟩ → ⟨ T . redex ⟩  

    s-map :  ⟨ state S ⟩ → ⟨ state T ⟩
  --  s-map = map⊎ t-map r-map

    field 
      lax : {s : ⟨ state S ⟩} → 
        _≤_{ℓ}{T} 
          (s-map (step S s)) 
          (step T ((s-map s))) 
-}