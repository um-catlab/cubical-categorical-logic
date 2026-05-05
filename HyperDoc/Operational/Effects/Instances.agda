{-# OPTIONS --type-in-type #-}
module HyperDoc.Operational.Effects.Instances where 

open import Cubical.Data.Sigma
open import Cubical.Data.FinData

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

open import HyperDoc.Operational.Effects.Model 
open import HyperDoc.Operational.Effects.Syntax
open import HyperDoc.Operational.Effects.BiAlgebra
open import HyperDoc.Algebra.Algebra 
open import HyperDoc.Operational.Graph hiding(_⊢_ ; ref ; tran ; sub)

open BifunctorSep
open BifunctorSepᴰ
open Category
open Categoryᴰ
open Functor
open NatTrans

open import Cubical.Categories.Instances.Preorders.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Relation.Binary.Preorder renaming (Preorder to Preorder')
open MonFun renaming (f to fun)
open PreorderStr
open IsPreorder
open BiAlg
open BiAlgHom
open Alg 
open AlgHom
open Signature


module _ (Sig : Signature) where 

  -- pointwise bialg
  O-ob : hSet _ → BiAlg Sig → BiAlg Sig 
  O-ob X B .car =  (⟨ X ⟩ → ⟨ B .car ⟩)  , isSet→ (car B .snd) 
  O-ob X B .isAlg op args x = isAlg B op (λ z → args z x)
  O-ob X B .isRGraph .fst f g = ((x : ⟨ X ⟩) → Edge[_,_] B (f x) (g x)) , isPropΠ λ _ → isPropEdge B
  O-ob X B .isRGraph .snd f x = isRGraph B .snd (f x)
  O-ob X B .congruence op args args' steps x = 
    congruence B op 
      (λ z → args z x) 
      (λ z → args' z x)
      (λ i → steps i x)
    
  leftAction : {X Y : hSet _ }{B : BiAlg Sig} → (⟨ Y ⟩ → ⟨ X ⟩) → BIALG Sig [ O-ob X B , O-ob Y B ] 
  leftAction {X} {Y} {B} f .BiAlgHom.map g y = g (f y)
  leftAction {X} {Y} {B} f .BiAlgHom.isAlgHom op args = refl
  leftAction {X} {Y} {B} f .BiAlgHom.isRelator .fst = λ z x → z (f x)
  leftAction {X} {Y} {B} f .BiAlgHom.isRelator .snd = refl

  rightAction : {X : hSet _ }{B B' : BiAlg Sig} → BIALG Sig [ B , B' ] → BIALG Sig [ O-ob X B , O-ob X B' ]
  rightAction {X} {B} {B'} g .BiAlgHom.map f x = g .BiAlgHom.map (f x)
  rightAction {X} {B} {B'} g .BiAlgHom.isAlgHom op args = funExt λ x → g .BiAlgHom.isAlgHom op (λ z → args z x)
  rightAction {X} {B} {B'} g .BiAlgHom.isRelator .fst = λ z x → g .BiAlgHom.isRelator .fst (z x)
  -- filled in by auto
  rightAction {X} {B} {B'} g .BiAlgHom.isRelator .snd {n} = 
    funExt λ x → isRGraph B' .fst (rightAction {X} g .BiAlgHom.map n x)
    (rightAction {X} g .BiAlgHom.map n x) .snd
    (rightAction {X} g .BiAlgHom.isRelator .fst (rgraph (O-ob X B) .snd n)
     x)
    (rgraph (O-ob X B') .snd (rightAction {X} g .BiAlgHom.map n) x)


  Sem : CBPVModel Sig
  Sem .fst = SET _
  Sem .snd .fst = BIALG Sig
  Sem .snd .snd .Bif-ob = O-ob
  Sem .snd .snd .Bif-homL {X}{Y} f B = leftAction {X}{Y}{B} f 
  Sem .snd .snd .Bif-L-id = BiAlgHom≡ refl
  Sem .snd .snd .Bif-L-seq _ _ = BiAlgHom≡ refl
  Sem .snd .snd .Bif-homR {B}{B'} X g = rightAction{X}{B}{B'} g
  Sem .snd .snd .Bif-R-id = BiAlgHom≡ refl
  Sem .snd .snd .Bif-R-seq _ _ = BiAlgHom≡ refl
  Sem .snd .snd .SepBif-RL-commute _ _ = BiAlgHom≡ refl

  open import HyperDoc.Operational.Effects.TypeStructure
  open TypeStructure Sem 
  open WkRepresentation

  hasFTy : HasFTy 
  hasFTy A .rep = FreeBiAlg {Sig} A
  hasFTy A .fwd .N-ob B h = λ z → h .map (inc z)
  hasFTy A .fwd .N-hom f = refl
  hasFTy A .bkwd f = {!   !}
  hasFTy A .wkretract = {!   !}

  module SynMod =  SynModel Sig
  module Syn =  Syntax Sig 
  CL : CBPVMorphism SynMod.Syn Sem 
  CL .fst = SynMod.V [ Syn.𝟙 ,-]
  -- Previously i did 
  -- RTC.RTCAlgGraphF Sig ∘F appL (mkBifunctorSep SynMod.O) Syn.𝟙
  -- to get the RTC of the graph .. 
  CL .snd .fst = appL (mkBifunctorSep SynMod.O) Syn.𝟙
  CL .snd .snd .N-ob (A , B) .BiAlgHom.map M V = Syn.subC V M
  CL .snd .snd .N-ob (A , B) .BiAlgHom.isAlgHom op args = funExt λ V → Syn.opsSub V op args
  CL .snd .snd .N-ob (A , B) .BiAlgHom.isRelator .fst {M}{M'} M↦M' V = Syn.subC-cong M↦M'
  CL .snd .snd .N-ob (A , B) .BiAlgHom.isRelator .snd = funExt λ V → Syn.isProp↦ _ _
  CL .snd .snd .N-hom (V , S) = BiAlgHom≡ (funExt λ M → funExt λ W → Syn.plugSub ∙ cong₂ Syn.plug refl Syn.subDist)

  open import HyperDoc.Operational.Effects.Logic
  open import HyperDoc.Logics.SetPred  
  open import Cubical.Categories.Instances.Posets.Base
  open import Cubical.Foundations.Powerset 
  open import HyperDoc.Lib 
  open import Cubical.Functions.Logic 
  open import Cubical.HITs.PropositionalTruncation renaming (map to hmap ; rec to hrec)
  open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint
  open import Cubical.Foundations.Isomorphism
  open Iso
  -- anti reduction, and algebra closed ? 

  -- transitive closure 
  -- Q: why this an not something involving the coalgebra?
  data _◂_↦*_ (B : BiAlg Sig) : Node B → Node B → Type where 
    ref : {X : Node B} → ⟨ rgraph B .fst .snd X X ⟩ → B ◂ X ↦* X  
    tran : {X Y Z : Node B} →  
      Edge[_,_] B X Y →  
      B ◂ Z ↦* X  → 
      B ◂ Z ↦* Y  
    isProp↦* : {X Y : Node B} → isProp (B ◂ X ↦* Y) 

  inc↦ : {B : BiAlg Sig}{n n' : Node B} → ⟨ rgraph B .fst .snd n n' ⟩ → B ◂ n ↦* n'
  inc↦ {B}{n} e = tran e (ref (rgraph B .snd n))

  seq↦* : {B : BiAlg Sig}{n n' n'' : Node B} → B ◂ n ↦* n' → B ◂ n' ↦* n'' → B ◂ n ↦* n'' 
  seq↦* f (ref x) = f
  seq↦* f (tran x g) = tran x (seq↦* f g)
  seq↦* f (isProp↦* g g₁ i) = isProp↦* {!   !} {!   !}  i

  lemma : {B B' : BiAlg Sig }{b b' : ⟨ car B ⟩} → (h : BiAlgHom B B') → 
    B ◂ b ↦* b' →  B' ◂ map h b ↦* map h b' 
  lemma h (ref x) = ref (h .isRelator .fst x)
  lemma h (tran x prf) = tran (h .isRelator .fst x) (lemma h prf)
  lemma h (isProp↦* prf prf₁ i) = isProp↦* (lemma h prf) (lemma h prf₁) i

  AntiRedCl : {B : BiAlg Sig} → ℙ ⟨ car B ⟩ → Type 
  AntiRedCl {B} P = (n n' : Node B) → (B ◂ n ↦* n') × (n' ∈ P) → n ∈ P

  isPropRedCl : {B : BiAlg Sig}{P : ℙ ⟨ car B ⟩} → isProp (AntiRedCl {B} P) 
  isPropRedCl {B}{P} = isPropΠ λ s → isPropΠ λ t → isProp→ (∈-isProp P s)

  AlgCl : {B : BiAlg Sig} → ℙ ⟨ car B ⟩ → Type 
  AlgCl {B} P = 
    (op : Op Sig)
    (args : (Fin (arity Sig op) → Σ[ b ∈ ⟨ car B ⟩ ] (b ∈ P) )) → 
    interp (alg B) op (λ x → args x .fst) ∈ P  

  isPropAlgCl : {B : BiAlg Sig} → (P : ℙ ⟨ car B ⟩) → isProp (AlgCl {B} P) 
  isPropAlgCl {B} P = 
    isPropΠ  λ op → 
    isPropΠ λ args → ∈-isProp P (interp (alg B) op (λ i → args i .fst))

  BiPred : BiAlg Sig → Type 
  BiPred  B = Σ[ P ∈ ℙ ⟨ car B ⟩ ] AntiRedCl  {B} P × AlgCl {B} P

  BiPred≡ : {B : BiAlg Sig}(P Q : BiPred B) → (P .fst) ⊃⊂ (Q .fst) → P ≡ Q 
  BiPred≡ {B}P Q prf = 
    Σ≡Prop (λ f → isProp× (isPropRedCl {B}{f}) (isPropAlgCl{B} f)) 
    (funExt (λ b → ⇔toPath (prf .fst b) (prf .snd b)))

  biAlgPo : BiAlg Sig → POSET _ _ .ob
  biAlgPo B .fst .fst = BiPred  B 
  biAlgPo B .fst .snd ._≤_ P Q = P .fst ⊆ Q .fst
  biAlgPo B .fst .snd .isPreorder .is-prop-valued P Q = ⊆-isProp (P .fst)(Q .fst)
  biAlgPo B .fst .snd .isPreorder .is-refl P = ⊆-refl (P .fst)
  biAlgPo B .fst .snd .isPreorder .is-trans P Q R = ⊆-trans (P .fst) (Q .fst) (R .fst)
  biAlgPo B .snd = {!   !}

  biAlgMon : {B B' : BiAlg Sig} → (BIALG Sig) [ B' , B ] → POSET _ _ [ biAlgPo B , biAlgPo B' ]
  biAlgMon {B} {B'} f .fun P .fst b' = P .fst (f .BiAlgHom.map b')
  biAlgMon {B} {B'} f .fun P .snd .fst n n' (n↦n , Pn') = 
    P .snd .fst (f .BiAlgHom.map n) (f .BiAlgHom.map n') (lemma f n↦n , Pn')
  biAlgMon {B} {B'} f .fun P .snd .snd op args = goal where 
    goal : isAlg B' op (λ x → args x .fst) ∈ (λ b' → P .fst (f .map b'))
    goal = subst (λ h → h ∈ P .fst) (sym (algHom f .pres op  λ a → args a .fst)) 
      (P .snd .snd op λ z → f .map (args z .fst) , args z .snd)
  biAlgMon {B} {B'} f .isMon = λ z x₁ → z (f .map x₁)

  LC : Functor (BIALG Sig ^op) (POSET  _ _)
  LC .F-ob = biAlgPo
  LC .F-hom {B}{B'} h = biAlgMon h
  LC .F-id = eqMon _ _ (funExt λ P → BiPred≡ _ _ ((λ x₁ z → z) , λ x₁ z → z))
  LC .F-seq _ _ = eqMon _ _ (funExt λ P → BiPred≡ _ _ ((λ x₁ z₁ → z₁) , (λ x₁ z₁ → z₁)))

  pull' : {A : hSet _}{B : BiAlg Sig} → 
    (⟨ A ⟩ → ⟨ car B ⟩) → 
    MonFun (biAlgPo B .fst) (pred A .fst) 
  pull' {A} {B} f .fun = λ z z₁ → z .fst (f z₁)
  pull' {A} {B} f .isMon = λ z x₁ → z (f x₁)

  SemLog : CBPVLogic Sem 
  SemLog .CBPVLogic.LV = Pred
  SemLog .CBPVLogic.LC = LC
  SemLog .CBPVLogic.LSq .N-ob (A , B) = pull' {A}{B}
  SemLog .CBPVLogic.LSq .N-hom (V , S)= funExt λ M → eqMon _ _ refl
  SemLog .CBPVLogic.antired {A}{B}{Q}{M}{M'} e a M'Q = 
    Q .snd .fst (M a) (M' a) (tran (e a) (ref (isRGraph B .snd (M a))) , M'Q)
  SemLog .CBPVLogic.pullOp = λ op args P Q dargs x z →
      Q .snd .snd op (λ z₁ → args z₁ x , dargs z₁ x z)

  open CBPVModelSyntax Sem hiding (interp)
  open LogicStruct SemLog 

  has𝟙ᴸ : Has𝟙ᴸ
  has𝟙ᴸ = has⊤

  has+ᴸ : Has+ᴸ
  has+ᴸ = has∨ , has∃
  
  data FreeBiPred' {A : hSet _}{B : BiAlg Sig}(M : O'[ A , B ])(P : ℙ ⟨ A ⟩) : ⟨ car B ⟩ → Type where 
    base : (a : ⟨ A ⟩)(b : ⟨ car B ⟩) → b ≡ M a → a ∈ P → FreeBiPred' {A}{B} M P b  
    algCl : 
      (op : Op Sig)
      (args : Fin (arity Sig op) → ⟨ car B ⟩ )
      (dargs : (a : Fin (arity Sig op)) → FreeBiPred' {A} {B} M P (args a) ) → 
      FreeBiPred' {A}{B} M P (interp (alg B) op args)
    antiCl : {b b' : ⟨ car B ⟩} → 
        B ◂ b ↦* b'  → 
        FreeBiPred' {A}{B} M P b' → 
        -------------------------
        FreeBiPred' {A}{B} M P b  

  FreeBiPred-Elim : {A : hSet _}{B : BiAlg Sig}(M : O'[ A , B ])(P : ℙ ⟨ A ⟩) → 
    (motive : ∀ (b : ⟨ car B ⟩) → FreeBiPred' {A}{B} M P b → Type ) 
    (base-case : 
      (a : ⟨ A ⟩)
      (b : ⟨ car B ⟩)
      (b≡Ma : b ≡ M a)
      (a∈P : a ∈ P) → 
      motive b (base a b b≡Ma a∈P))
    (alg-case : 
      (op : Op Sig)
      (args : Fin (arity Sig op) → ⟨ car B ⟩)
      (dargs : (x : Fin (arity Sig op)) → FreeBiPred' {A}{B} M P (args x))
      (motives : (x : Fin (arity Sig op)) → motive (args x)(dargs x)) → 
      motive (interp (alg B) op args) (algCl op args dargs) )
    (anti-case : 
      {b b' : ⟨ car B ⟩}
      (r : B ◂ b ↦* b')
      (d : FreeBiPred' M P b')
      (ih : motive b' d)
      → motive b (antiCl r d))
    → (b : ⟨ car B ⟩) → (F : FreeBiPred'  {A}{B} M P b ) → motive b F
  FreeBiPred-Elim {A} {B} M P mot bc algc antic b (base a .b red a∈P) = 
    bc a b red a∈P
  FreeBiPred-Elim {A} {B} M P mot bc algc antic b (algCl op args dargs) = 
    algc  op args dargs λ x → FreeBiPred-Elim {A}{B} M P mot bc algc antic (args x) (dargs x)
  FreeBiPred-Elim {A} {B} M P mot bc algc antic b (antiCl {.b}{b'}  b↦*b' b'∈Free) =
    antic b↦*b' b'∈Free (FreeBiPred-Elim {A}{B} M P mot bc algc antic b' b'∈Free) 

  FreeBiPred : {A : hSet _}{B : BiAlg Sig}(M : O'[ A , B ])(P : ℙ ⟨ A ⟩) → BiPred B 
  FreeBiPred {A} {B} M P .fst b = ∥ FreeBiPred' {A}{B} M P b ∥ₚ
  FreeBiPred {A} {B} M P .snd .fst b b' (b↦b' , prf) = hmap (antiCl b↦b') prf 
  FreeBiPred {A} {B} M P .snd .snd op args =
     recFin {m = arity Sig op} squash₁ 
      (λ x → ∣ (algCl op (λ x₁ → args x₁ .fst) x) ∣₁) λ i → args i .snd

  push : ∀{A B} → O'[ A , B ] → MonFun (pred A .fst) (biAlgPo B .fst) 
  push {A} {B} M .fun P = FreeBiPred {A}{B} M P
  push {A} {B} M .isMon {P}{P'} f b = hmap goal where 
    goal : FreeBiPred' M P b → FreeBiPred' M P' b
    goal = FreeBiPred-Elim {A}{B} M P 
      (λ b _ → FreeBiPred' M P' b) 
      (λ a b b≡Ma a∈P → base a b b≡Ma (f a a∈P)) 
      (λ op args dargs → algCl op args) 
      (λ {b = b₁} {b'} r d → antiCl r) 
      b

  hasFTyᴸ : HasFTyᴸ 
  hasFTyᴸ {A}{B} M .fst = push {A}{B} M
  hasFTyᴸ {A}{B} M .snd ._⊣_.adjIff {P} {Q} .fun = goal where 
    goal : 
      ((x : fst (car B)) → ∥ FreeBiPred' {A}{B} M P x ∥₁ → fst (Q .fst x)) →
      (x : fst A) → fst (P x) → fst (Q .fst (M x))
    goal f a Pa = f (M a) ∣ (base a (M a) refl Pa) ∣₁
  hasFTyᴸ {A}{B} M .snd ._⊣_.adjIff {P} {Q} .inv = goal where 
    goal : 
      ((x : fst A) → fst (P x) → fst (Q .fst (M x))) →
      (x : fst (car B)) → ∥ FreeBiPred' {A}{B} M P x ∥₁ → fst (Q .fst x)
    goal f b free = 
      hrec 
        (∈-isProp (λ z → z) (Q .fst b)) 
        (FreeBiPred-Elim {A}{B} M P  
          (λ b _ → b ∈ (Q .fst)) 
          (λ a b eq a∈P → subst (λ h → h ∈ Q .fst) (sym eq) (f a a∈P)) 
          (λ op args dargs mot → Q  .snd .snd op λ x → (args x) , mot x) 
          (λ {b}{b'} b↦*b' b'∈free → λ ih → Q .snd .fst b b' (b↦*b' , ih)) 
          b) 
        free

  hasFTyᴸ M .snd ._⊣_.adjIff {P} {Q} .sec b = ⊆-isProp P ((λ x → Q .fst  (M x))) _ b
  hasFTyᴸ {A}{B} M .snd ._⊣_.adjIff {P} {Q} .ret a = ⊆-isProp (FreeBiPred {A}{B} M P .fst) (Q .fst) _ a
