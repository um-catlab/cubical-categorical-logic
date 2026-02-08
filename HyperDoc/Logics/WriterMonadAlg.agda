{-# OPTIONS --allow-unsolved-metas #-}

module HyperDoc.Logics.WriterMonadAlg where

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base 
open import Cubical.Data.Sigma 

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure 
open import Cubical.Foundations.Powerset
open import Cubical.Functions.Logic

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monad.ExtensionSystem hiding (F ; push ; pushId)
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Instances.EilenbergMoore
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Instances.FunctorAlgebras
open import Cubical.Categories.Instances.Preorders.Monotone hiding (_≤X_ ; _≤Y_)

open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.HITs.PropositionalTruncation.Properties

open import Cubical.Relation.Binary.Preorder
 
open import HyperDoc.Effects.Writer
open import HyperDoc.Lib

open Category
open ExtensionSystemFor
open Functor
open PreorderStr
open IsPreorder
open MonFun
open AlgebraHom
open IsEMAlgebra
-- specialized to some monoid on SET
module _ {ℓS : Level}{M : Monoid ℓS} where

  open MonoidStr (M .snd)
  
  open Writer {M = M}


  module _ (Alg : ob EM) where 
    open Algebra (Alg .fst) renaming (str to α)

    private 
      A : hSet ℓS
      A = carrier

    closure : ℙ ⟨ A ⟩ → Type ℓS 
    closure P = (a' : ⟨ A ⟩)(w : ⟨ M ⟩) → a' ∈ P → α (w , a') ∈ P

    isPropclosure : (P : ℙ ⟨ A ⟩) → isProp (closure P) 
    isPropclosure P p q = funExt λ a → funExt λ w → funExt λ Pa → P (α (w , a)) .snd (p a w Pa) (q a w Pa)

    subAlg : Type (ℓ-suc ℓS) 
    subAlg = Σ[ P ∈ ℙ ⟨ A ⟩ ] closure P

  subAlgPo : ob EM → ob (POSET (ℓ-suc ℓS) ℓS) 
  subAlgPo A .fst .fst = subAlg A
  subAlgPo A .fst .snd ._≤_ P Q = P .fst ⊆ Q .fst 
  subAlgPo A .fst .snd .isPreorder .is-prop-valued P Q = ⊆-isProp (P .fst)(Q .fst)
  subAlgPo A .fst .snd .isPreorder .is-refl P = ⊆-refl (P .fst)
  subAlgPo A .fst .snd .isPreorder .is-trans P Q R = ⊆-trans (P .fst) (Q .fst) (R .fst)
  -- this follows from antisym in ℙ
  subAlgPo A .snd = {!   !}

  open Algebra renaming (str to α)
  -- pushforward, op-cartesian lift

  module OpLift
    {X Y : ob EM}
    (f : EM [ X , Y ])
    (X' : subAlg X) where


    -- direct image closed under monad alg 
    close : ℙ ⟨ Y .fst .carrier ⟩ 
    close y = ∥ (Σ[ x ∈ ⟨ X .fst .carrier ⟩ ] Σ[ w ∈ ⟨ M ⟩ ] (x ∈ X' .fst) × (y ≡ α (Y .fst) (w , f .carrierHom x))) ∥ₚ

    push : subAlg Y 
    push .fst = close
    push .snd y w = map λ (x , w' , Px , y≡) → x , (w · w') , Px , 
      cong₂ (λ h h' →  α (Y .fst) (h , h' )) (sym (·IdR _)) y≡ 
      ∙ sym (funExt⁻ (str-μ (Y .snd)) (w , w' , f .carrierHom  x))


  ML : Functor EM (POSET (ℓ-suc ℓS) ℓS) 
  ML .F-ob = subAlgPo
  ML .F-hom {X} {Y} f .MonFun.f = OpLift.push {X}{Y} f
  ML .F-hom {X} {Y} f .isMon {Xs}{Xs'} = goal where 
   
    module L = OpLift {X}{Y} f Xs 
    module L' = OpLift {X}{Y} f Xs'

    goal : Xs .fst ⊆ Xs' .fst → L.push .fst ⊆ L'.push .fst
    goal TA y = map λ (x , w , Px , y≡ ) → x , w , TA x Px , y≡

  ML .F-id {X} = eqMon _ _ (funExt goal) where 
    open OpLift {X} {X} (EM .id{X}) 

    goal : (X' : subAlg X) → push X' ≡ X'
    goal X' = 
      ΣPathP 
        ((funExt (λ x → 
          ⇔toPath 
            -- trick here is to use closure of X'
            (rec (X' .fst x .snd) λ (x' , w , Px' , x≡ ) → subst (λ h → X' .fst h .fst) (sym x≡) (X' .snd x' w Px') ) 
            λ Px → ∣ (x , ε , Px , funExt⁻ (sym (str-η (X .snd))) x) ∣₁)) 
        , toPathP (isPropclosure X (X' .fst) _ (X' .snd)))

  ML .F-seq {X}{Y}{Z} f g = eqMon _ _ goal where 

    module Lfg = OpLift {X}{Z} (EM ._⋆_ {X}{Y}{Z} f g) 
    module Lf = OpLift {X}{Y} f 
    module Lg = OpLift {Y}{Z} g
    

    {-
    f : X → Y
    push : (P : X → Prop) →  ℙ ⟨ Y .fst .carrier ⟩ 
    push P y = ∥ Σ[ x ∈ X ] Σ[ w ∈ ⟨ M ⟩ ] x ∈ P × y ≡ α (Y .fst) (w , f .carrierHom x) ∥ₚ


    -- every subalgebra has 
      closure : ℙ ⟨ A ⟩ → Type ℓS 
      closure P = (a' : ⟨ A ⟩)(w : ⟨ M ⟩) → a' ∈ P → α (w , a') ∈ P

    -}


    hm : (A : Type) → ⟨  ∥ A ∥ₚ ⟩  → ∥ A ∥₁
    hm A = λ z → z


    goal : Lfg.push ≡ λ X' → Lg.push (Lf.push X')
    goal = funExt λ X' → 
      ΣPathP ((funExt (λ z → ⇔toPath (to X' z) (fro X' z))) , {!   !})  where 
        to : (X' : subAlg X)(z : ⟨ Z .fst .carrier ⟩) → ⟨ fst (Lfg.push X') z ⇒ fst (Lg.push (Lf.push X')) z ⟩ 
        to X' z prf = 
          propBind prf 
            λ ( x , w , X'x , z≡ ) →   ∣ (f .carrierHom x , w , ∣ x , w , X'x , {! X' .snd x w X'x!} ∣₁ , z≡) ∣₁

        -- f.push X' .fst (f .carrierHom x)
        fro : (X' : subAlg X)(z : ⟨ Z .fst .carrier ⟩) → ⟨ fst (Lg.push (Lf.push X')) z ⇒ fst (Lfg.push X') z ⟩ 
        fro X' z p = 
            propBind p 
              λ (y , w , X'y , z≡) → 
            propBind X'y 
              λ (x , w' , Px , y≡ ) → 
              ∣ (x , (w · w') , Px , 
                z≡ 
                ∙ cong (λ h → α (Z .fst) (w , g .carrierHom h)) y≡ 
                ∙ cong (λ h → α (Z .fst) h ) (ΣPathP ((sym (·IdR _)) , funExt⁻ (g .strHom) (w' , f .carrierHom x))) 
                ∙ cong (λ h → α (Z .fst) (w · ε , α (Z .fst) (h , carrierHom g (carrierHom f x))))  (·IdR _)
                ∙ funExt⁻ (sym (str-μ (Z .snd))) (w , w' , EM ._⋆_ {X}{Y}{Z} f g .carrierHom x)) ∣₁

              


{-

  -- freely closed under monad algebra
  data Gen (B : ob EM)(P : ℙ ⟨ B .fst .carrier ⟩) : ⟨ B .fst .carrier ⟩ → Type ℓS where
    base  : ∀ {b} → b ∈ P → Gen B P b
    step  : ∀ {b w} → Gen B P b → Gen B P (α (B .fst) (w , b)) 

  Gen-rec :
    ∀ {B : ob EM}{P : ℙ ⟨ B .fst .carrier ⟩} {X : Type ℓS} →
    -- base case
    (baseC : ∀ {b} → b ∈ P → X) →
    -- step case
    (stepC : ∀ {b : ⟨ B .fst .carrier ⟩}{w : ⟨ M ⟩} → X → X) →
    ∀ {b} → Gen B P b → X
  Gen-rec baseC stepC (base x) = baseC x
  Gen-rec {B} baseC stepC (step {b} {w} g) = stepC {b} {w} (Gen-rec {B} baseC (stepC {b}{w}) g)

  Gen-ind :{B : ob EM}
    (P : ℙ ⟨ B .fst .carrier ⟩) →
    (R : ⟨ B .fst .carrier ⟩ → Type ℓS) →
    -- base case
    (baseC : (b : ⟨ B .fst .carrier ⟩) → (b∈P : b ∈ P) → R b) →
    -- step case
    (stepC : (b : ⟨ B .fst .carrier ⟩) → (w : ⟨ M ⟩) → (g : Gen B P b) → R b → R (α (B .fst) (w , b))) →
    (b : ⟨ B .fst .carrier  ⟩) → (g : Gen B P b) → R b
  Gen-ind P R baseC stepC b (base {b} x) = baseC b x
  Gen-ind P R baseC stepC b (step {b'} {w} g) = stepC b' w g (Gen-ind P R baseC stepC b' g)

  

  module _ 
    {A B : ob EM} 
    (f : EM [ A , B ])
    (P : subAlg A )  where 

    -- direct image
    direct : ℙ ⟨ B .fst .carrier ⟩ 
    direct b = ∥ (Σ[ a ∈ ⟨ A .fst .carrier ⟩ ] (a ∈ P .fst) × (b ≡ f .carrierHom a)) ∥ₚ

    push : subAlg B 
    push .fst b = ∥ Gen B direct b ∥ₚ
    push .snd b w = map step
    
  pushMono : {AlgA AlgB : ob EM}(f : EM [ AlgA , AlgB ]){A A' : subAlg AlgA} → 
    A .fst ⊆ A' .fst → push {AlgA}{AlgB} f A .fst ⊆ push {AlgA}{AlgB} f A' .fst 
  pushMono {AlgA}{AlgB} f {A}{A'} TA b =
    map (
      Gen-ind 
      {AlgB} 
      (direct {AlgA}{AlgB} f A) 
      (λ b → Gen AlgB (direct {AlgA}{AlgB} f A') b) 
      (λ b b∈fA → base (map (λ (a , Pa , b≡) → a , (TA a Pa) , b≡) b∈fA)) 
      (λ b w → λ g → step) 
      b)

  pushId : {A : ob EM}{subA : subAlg A} → push {A}{A} (EM .id{A}) subA ≡ subA
  pushId {A}{subA} = 
    ΣPathP (
      funExt (λ a → 
        ⇔toPath 
          (rec (subA .fst a .snd) (
            Gen-ind 
              (direct {A}{A} (EM .id{A}) subA)
              (λ a → subA .fst a .fst) 
              (λ a → rec (subA .fst a .snd) λ (a' , Pa' , a≡a') → subst (λ h → subA . fst h .fst) (sym a≡a') Pa')
              (λ {a' w (base x) Pa' → subA .snd a' w Pa'
                ; a' w (step g) Pa' → subA .snd (α (A .fst) (_ , _)) w Pa'}) 
              a)) 
          λ Pa → ∣ (base ∣ (a , (Pa , refl)) ∣₁) ∣₁) 
      , toPathP (isPropclosure A (subA .fst) _ (subA .snd)) )


  pushSeq : {A B C : ob EM}{subA : subAlg A}(f : EM [ A , B ])(g : EM [ B , C ]) → 
    push {A}{C} (EM ._⋆_ {A}{B}{C} f g ) subA
    ≡  
    push {B}{C} g (push {A}{B} f subA)
  pushSeq {A}{B}{C}{subA} f g = 
    ΣPathP (
      (funExt (λ c → 
        ⇔toPath 
          (rec {!   !} 
            (Gen-ind 
              (direct {A}{C} ((EM ⋆ f) g) subA) 
              (λ c → ∥ Gen C  (direct {B}{C} g (push f subA))  c ∥₁) 
              (λ c' → map λ (a , Pa , a≡) → base {!   !}) 
              {!   !} 
              c))  
          {!   !})) 
      , {!   !})


  ML : Functor EM (POSET (ℓ-suc ℓS) ℓS) 
  ML .F-ob = subAlgPo
  ML .F-hom {A}{B} f .MonFun.f = push {A}{B} f
  ML .F-hom {AlgA}{AlgB} f .isMon {A} {A'} = pushMono {AlgA}{AlgB} f {A}{A'}
  ML .F-id {Alg} = eqMon _ _ (funExt λ subA → pushId {Alg}{subA})
  ML .F-seq {A}{B}{C} f g = eqMon _ _ (funExt λ subA → pushSeq {A}{B}{C}{subA} f g)

-}