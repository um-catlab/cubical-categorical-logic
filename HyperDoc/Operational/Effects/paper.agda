{-# OPTIONS --type-in-type #-}
module HyperDoc.Operational.Effects.paper where

open import Cubical.Foundations.Prelude 
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Bool renaming (not to bnot)


record Poly : Type where 
  constructor _◂_ 
  field 
    shape : Type 
    pos : shape -> Type 
open Poly

den : Poly → Type → Type 
den (S ◂ P) X = Σ[ s ∈ S ] (P s → X)

mapP : {X Y : Type} → (p : Poly) → (X → Y) → den p X → den p Y 
mapP p f (s , P) = s , (λ z → f (P z))


open import Cubical.Categories.Monad.ExtensionSystem hiding (F)
open import Cubical.Categories.Category 
open import Cubical.Categories.Instances.Sets
module general  where 
  
  open import Cubical.Data.FinData renaming (rec to frec ; elim to felim )
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Data.Nat 
  open import Cubical.Data.List
  open Iso 

  module polynomial (P : Poly)
    (finitePos  : (∀ (s : shape P) → Σ[ n ∈ ℕ ] Iso (Fin n) (pos P s) ))
    where 

    T : Type → Type 
    T X = den P X 

    module monad
      (μ : {X : Type} → T (T X) → T X)
      (η : {X : Type} → X → T X ) where 

      _>>=_ : {X Y : Type} → T X → (X → T Y) → T Y 
      _>>=_ m f = μ (mapP P f m)

      asList : {X : Type}{n : ℕ} → (Fin n → X) → List X 
      asList f = foldrFin _∷_ [] f

      _ : asList {ℕ} {4} (λ {zero → 1
                          ; (suc zero) → 2
                          ; two → 3
                          ; three → 4}) ≡ (1 ∷ (2 ∷ (3 ∷ [ 4 ]))) 
      _ = refl

      leaves : {X : Type} → den P X → List X 
      leaves (s , p) = asList λ i → p (finitePos s .snd .fun i)

      open import HyperDoc.Algebra.Algebra
      open import Cubical.Data.Maybe
      open import Cubical.Data.Sum
      open import Cubical.Data.Nat.Order

      find : {X : Type}{n : ℕ} → (Fin n → X) → (X → Bool) → Maybe (Fin n)
      find {X}{zero} f p = nothing
      find {X}{suc n} f p = 
        if p (f zero) 
        then (just zero) 
        else (map-Maybe suc (find (λ i → f (suc i)) p))
  
      open Signature
      module algebra
        (Sig : Signature)
        (TAlg : (X : hSet _) → IsAlg Sig (T ⟨ X ⟩ , {!   !})) where 
       
        Trm : Type → Type 
        Trm = FreeOn Sig

        sem : {X : Type} → Trm X → T (Trm X )
        sem (inc x) = η (inc x)
        sem {X} (ops op args) = TAlg (Trm X  , _) op λ i → η (args i)

        plug : {X : Type} → T (Trm X ⊎ Unit) → T (Trm X) → T (Trm X)
        plug m x = m >>= λ {(inl x) → η x
                      ; (inr tt) → x}
        
        candidate : {X : Type} → Trm X → Bool 
        candidate (inc x) = false
        candidate (ops o x) = true

        hole? : {X : Type} → T (Trm X) → Maybe (T (Trm X ⊎ Unit) × Trm X)
        hole? {X} (s , p) = map-Maybe (λ i → punchout i , branches i) hindex where 
          n : ℕ 
          n = finitePos s .fst

          branches : Fin n → Trm X 
          branches i = p (fun (finitePos s .snd) i)

          -- "left" most hole, if it exists
          hindex : Maybe (Fin n)
          hindex = find branches candidate

          placehole : Fin n → Fin n → Trm X ⊎ Unit
          placehole h i = if h == i then inr tt else inl (branches i)

          punchout : Fin n → T (Trm X ⊎ Unit)
          punchout i = s , λ j → placehole i (finitePos s .snd .inv j)

        {-# TERMINATING #-}
        termsize : {X : Type} → FreeOn Sig X → ℕ 
        termsize (inc x) = 0
        termsize (ops op args) = 1 + foldrFin (λ t n → termsize t + n) 0 args

        size : {X : Type} → T (Trm X) → ℕ 
        size (s , p) = foldrFin (λ t n → termsize t + n) 0 λ i → p (fun (finitePos s .snd) i)

        reduce' : {X : Type} → ℕ → T (Trm X) → T (Trm X)
        reduce' zero t = t
        reduce' (suc n) t with (hole? t)
        ... | nothing = t
        ... | just (h , e) = reduce' n (plug h (sem e))

        reduce : {X : Type} → Trm X → T (Trm X)
        reduce {X} t = reduce' (size (η t)) (η t) 

        history : {X : Type} → Trm X → List (T (Trm X))
        history {X} t = go (suc (size (η t)))where 
          go : ℕ → List (T (Trm X))
          go zero = []
          go (suc n) = go n ++ [ reduce' n (η t) ]
        

     {-}   ex : Fin 4 → FreeOn Sig ℕ 
        ex zero = inc _ 
        ex (suc zero) = inc _
        ex two = ops _ _ 
        ex three = ops _ _ 

        _ : find ex candidate ≡ just two
        _ = {! find ex candidate  !}
-}

module usage where 
  open general
  open import Cubical.Data.Nat 
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Data.FinData
  open import HyperDoc.Algebra.Algebra

  StateP : Poly 
  StateP = (Bool → Bool) ◂ λ _ → Bool

  State : Type → Type 
  State = den StateP 

  μ : {X : Type} → State (State X) → State X 
  μ {X} (f , g) = (λ b → fst (g b) (f b)) , λ b → snd (g b) (f b)

  η : {X : Type} → X → State X 
  η x = (λ b → b) , (λ _ → x)

  open Signature
   
  data Ops : Type where 
    get set0 set1 : Ops 

  Sig : Signature 
  Sig .Op = Ops
  Sig .arity get = 2
  Sig .arity set0 = 1
  Sig .arity set1 = 1

  sget : {X : Type} → State X → State X → State X 
  sget m n = (λ {false → m .fst false
              ; true → n .fst true}) , 
            λ {false → m .snd false
            ; true → n .snd true}

  sset0 : {X : Type} → State X → State X 
  sset0 m = (λ _ → m .fst false) , (λ _ → m .snd false)

  sset1 : {X : Type} → State X → State X 
  sset1 m = (λ _ → m .fst true) , (λ _ → m .snd true)

  isAlg : (X : hSet _)  → IsAlg Sig (State (X .fst) , {!   !})
  isAlg X get x = sget (x zero) (x one)
  isAlg X set0 x = sset0 (x zero)
  isAlg X set1 x = sset1 (x zero)

  stFin : (s : shape StateP) → Σ-syntax ℕ (λ n → Iso (Fin n) (pos StateP s)) 
  stFin s .fst = 2
  stFin s .snd .Iso.fun zero = false
  stFin s .snd .Iso.fun one = true
  stFin s .snd .Iso.inv false = zero
  stFin s .snd .Iso.inv true = one
  stFin s .snd .Iso.sec = {!   !}
  stFin s .snd .Iso.ret = {!   !}

  open polynomial StateP stFin 
  open monad μ η 
  open algebra Sig isAlg 

  data Shapes : Type where 
    not idd zero onee : Shapes

  convS : (Bool → Bool) → Shapes 
  convS f with (f true , f false)
  ... | false , false = zero
  ... | false , true = not
  ... | true , false = idd
  ... | true , true = onee

  Config : Type → Type 
  Config X = Shapes × X × X 

  config : {X : Type} → State X → Config X
  config (s , p) = convS s , p false , p true

  t : Trm ℕ
  t = ops set0 λ _ → ops get λ {zero → inc 2
                              ; one → inc 7}

  res : T (Trm ℕ)
  res = reduce t

  _ : config (reduce t) ≡ (zero , inc 2 , inc 2)
  _ = refl

  open import Cubical.Data.List

  convert : List (Config (Trm ℕ))
  convert = map config (history t)
  {-
  (idd ,
 ops set0
 (λ z → ops get (λ { zero → inc 2 ; one → inc 7 ; (suc (suc ())) }))
 ,
 ops set0
 (λ z →
    ops get (λ { zero → inc 2 ; one → inc 7 ; (suc (suc ())) })))
∷
(idd ,
 ops get (λ { zero → inc 2 ; one → inc 7 ; (suc (suc ())) }) ,
 ops set0
 (λ z →
    ops get (λ { zero → inc 2 ; one → inc 7 ; (suc (suc ())) })))
∷
(idd ,
 inc 2 ,
 ops set0
 (λ z →
    ops get (λ { zero → inc 2 ; one → inc 7 ; (suc (suc ())) })))
∷
(zero ,
 inc 2 ,
 ops get (λ { zero → inc 2 ; one → inc 7 ; (suc (suc ())) }))
∷ (zero , inc 2 , inc 2) ∷ [] 
  -}

module state where 

  data Shapes : Type where 
    not idd zero one : Shapes

  data Pos : Type where 
    left right : Pos

  StateP : Poly 
  StateP = (Bool → Bool) ◂ λ _ → Bool

  StateP' : Poly 
  StateP' = Shapes ◂ (λ _ → Pos)

  State : Type → Type 
  State = den StateP

  State' : Type → Type 
  State' = den StateP'

  μ : {X : Type} → State (State X) → State X 
  μ {X} (f , g) = (λ b → fst (g b) (f b)) , λ b → snd (g b) (f b)

  convS : (Bool → Bool) → Shapes 
  convS f with (f true , f false)
  ... | false , false = zero
  ... | false , true = not
  ... | true , false = idd
  ... | true , true = one

  convP : Bool → Pos 
  convP false = left
  convP true = right

  conv : {X : Type} → State X → State' X 
  conv (s , p) = convS s , λ {left → p false
                            ; right → p true}

  Config : Type → Type 
  Config X = Shapes × X × X 

  config : {X : Type} → State X → Config X
  config (s , p) = convS s , p false , p true

  η : {X : Type} → X → State X 
  η x = (λ b → b) , λ _ → x

  _>>=_ : {X Y : Type} → State X → (X → State Y) → State Y 
  _>>=_ m f = μ (mapP StateP f m)



  hState : hSet _ → hSet _ 
  hState (X , _)= (State X) , {!   !}

  StMon : ExtensionSystemFor (SET _) hState
  StMon .ExtensionSystemFor.η = η
  StMon .ExtensionSystemFor.bind f m = m >>= f
  StMon .ExtensionSystemFor.bind-r = refl
  StMon .ExtensionSystemFor.bind-l = refl
  StMon .ExtensionSystemFor.bind-comp = refl

  get : {X : Type} → State X → State X → State X 
  get m n = (λ {false → m .fst false
              ; true → n .fst true}) , 
            λ {false → m .snd false
            ; true → n .snd true}

  set0 : {X : Type} → State X → State X 
  set0 m = (λ _ → m .fst false) , (λ _ → m .snd false)

  set1 : {X : Type} → State X → State X 
  set1 m = (λ _ → m .fst true) , (λ _ → m .snd true)

  set0get : {X : Type}{s t : State X} → set0 (get s t) ≡ set0 s
  set0get = refl

  set1get : {X : Type}{s t : State X} → set1 (get s t) ≡ set1 t 
  set1get = refl

  set0set0 : {X : Type}{s : State X} → set0 (set0 s) ≡ set0 s 
  set0set0 = refl

  set0set1 : {X : Type}{s : State X} → set0 (set1 s) ≡ set1 s 
  set0set1 = refl

  set1set0 : {X : Type}{s : State X} → set1 (set0 s) ≡ set0 s 
  set1set0 = refl

  set1set1 : {X : Type}{s : State X} → set1 (set1 s) ≡ set1 s 
  set1set1 = refl

  getdiag : {X : Type}{s : State X} → get s s ≡ s 
  getdiag = ΣPathP ((funExt λ {false → refl
                            ; true → refl }) , funExt λ {false → refl
                                                        ; true → refl} )

  getget : {X : Type}{s t r u : State X} → get (get s t) (get r u) ≡ get s u 
  getget = ΣPathP ((funExt λ {false → refl
                            ; true → refl }) , funExt λ {false → refl
                                                        ; true → refl} ) 

  getset : {X : Type}{s t : State X} → get (set0 s) (set1 t) ≡ get s t 
  getset = ΣPathP ((funExt λ {false → refl
                            ; true → refl }) , funExt λ {false → refl
                                                        ; true → refl} )                                                                                           



  data FreeStAlg (X : Type) : Type where 
    var : X → FreeStAlg X 
    fget : FreeStAlg X → FreeStAlg X → FreeStAlg X 
    fset0 fset1  : FreeStAlg X → FreeStAlg X

  open import Cubical.Data.Nat 
  open import Cubical.Data.Unit 
  open import Cubical.Data.Sum

  e' : FreeStAlg ℕ 
  e' = fget (var 2) (var 7)

  e : FreeStAlg ℕ 
  e = fset0 (e')

  sem : {X : Type} → FreeStAlg X → State (FreeStAlg X)
  sem (var x) = η (var x)
  sem (fget x x₁) = get (η x) (η x₁)
  sem (fset0 x) = set0 (η x)
  sem (fset1 x) = set1 (η x)

  eval : {X : Type} → FreeStAlg X → State (FreeStAlg X)
  eval (var x) = η (var x)
  eval (fget x x₁) = get (eval x) (eval x₁)
  eval (fset0 x) = set0 (eval x)
  eval (fset1 x) = set1 (eval x)

  -- the hole is the opposite of the given position
  hole : {X : Type} → Shapes → Pos → FreeStAlg X → State (FreeStAlg X ⊎ Unit)
  hole not left x = bnot , (if_then inr tt else inl x)
  hole not right x = bnot , (if_then inl x else inr tt)
  hole idd left x = (λ b → b) , (if_then inr tt else inl x)
  hole idd right x = (λ b → b) , (if_then inl x else inr tt)
  hole zero left x = (λ _ → false)  , (if_then inr tt else inl x)
  hole zero right x = (λ _ → false) , (if_then inl x else inr tt)
  hole one left x = (λ _ → true) , (if_then inr tt else inl x)
  hole one right x = (λ _ → true) , (if_then inl x else inr tt)                
                      
  plug : {X : Type} → State (FreeStAlg X ⊎ Unit) → State (FreeStAlg X) → State (FreeStAlg X)
  plug m x = m >>= λ {(inl x) → η x
                      ; (inr tt) → x}

  start : State (FreeStAlg ℕ)
  start = η e

  open import Cubical.Data.List

  Commands : (X : Type) → Type 
  Commands X = List (State (FreeStAlg X) → State (FreeStAlg X)) 

  reduce : {X : Type} → State (FreeStAlg X) → Commands X → List (Config (FreeStAlg X))
  reduce {X} s xs = [ config s ] ++ go s xs where 
    go : State (FreeStAlg X) → List (State (FreeStAlg X) → State (FreeStAlg X)) → List (Config (FreeStAlg X))
    go s [] = []
    go s (x ∷ xs) = config (x s) ∷ go (x s) xs

  lstep : {X : Type} → State (FreeStAlg X) → State (FreeStAlg X)
  lstep s = plug (hole (convS (s .fst)) right (s .snd true)) (sem (s .snd false))

  rstep : {X : Type} → State (FreeStAlg X) → State (FreeStAlg X)
  rstep s = plug (hole (convS (s .fst)) left (s .snd false)) (sem (s .snd true)) 

  final : {X : Type} →  FreeStAlg X  → Commands X → List (Config (FreeStAlg X)) 
  final e cmds = take 1 (rev (reduce (η e) cmds))

  _ : config (eval e) ≡ (zero , var 2 , var 2)
  _ = refl

  _ : final e (lstep ∷ lstep ∷ rstep ∷ rstep ∷ [])  ≡ [ (zero , var 2 , var 2) ] 
  _ = refl

  -- testing confluence
  _ = {! reduce start (lstep ∷ lstep ∷ rstep ∷ rstep ∷ [])  !}
  _ = {!  reduce start (rstep ∷ rstep ∷ lstep ∷ lstep ∷ [])   !}
  _ = {! reduce start  (lstep ∷ rstep ∷ lstep ∷ rstep ∷ [])  !}
  _ = {! reduce start  (rstep ∷ lstep ∷ rstep ∷ lstep ∷ [])  !}
  _ = {! reduce start  (rstep ∷ lstep ∷ lstep ∷ rstep ∷ [])  !}

  _ : config start ≡ (idd , e , e) 
  _ = refl
