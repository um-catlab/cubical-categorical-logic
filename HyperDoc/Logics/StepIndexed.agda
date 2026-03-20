{-# OPTIONS --type-in-type #-}
module HyperDoc.Logics.StepIndexed where 

open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty renaming (rec to ⊥rec)

open import Cubical.Foundations.Prelude hiding(_▷_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Relation.Binary.Preorder

open import Cubical.Categories.Category
open import Cubical.Categories.Functor 
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.NaturalTransformation

open import HyperDoc.Algebra.Algebra
open import HyperDoc.CBPV.Model.Base
open import HyperDoc.Connectives.Connectives
open import HyperDoc.Logic.Base
open import HyperDoc.Syntax 

open Category
open Functor
open NatTrans
open MonFun renaming (f to fun)
open PreorderStr renaming(_≤_ to _≤P_)


↓Closed : {P : POSET _ _ .ob} → (ℕ → P .fst .fst) → Type
↓Closed {P} f = (∀ (n m : ℕ) → m ≤ n → _≤P_ (P .fst .snd) (f n) (f m))

isProp↓Closed :  {P : POSET _ _ .ob} → (f : ℕ → P .fst .fst) → 
  isProp (↓Closed {P} f)
isProp↓Closed {P} f = 
  isPropΠ λ n → isPropΠ λ m → isProp→ 
    (IsPreorder.is-prop-valued (isPreorder (P .fst .snd)) (f n) (f m))

SIProp : POSET _ _ .ob → Type 
SIProp P = Σ[ f ∈ (ℕ → P .fst .fst) ] ↓Closed {P} f

SIProp≡ : {P : POSET _ _ .ob}{p q : SIProp P} → 
  p .fst ≡ q .fst → p ≡ q
SIProp≡ {P}{p}{q} prf = ΣPathP (prf , toPathP (isProp↓Closed {P} (prf i1) _ _))

MonPo : POSET _ _ .ob → POSET _ _ .ob 
MonPo P .fst .fst = SIProp P
MonPo P .fst .snd .PreorderStr._≤_ p q  = (n : ℕ) → _≤P_ (P .fst .snd) (p .fst n) (q .fst n)
MonPo P .fst .snd .isPreorder .IsPreorder.is-prop-valued p q = isPropΠ λ x → IsPreorder.is-prop-valued (isPreorder (P .fst .snd)) (p .fst x)
  (q .fst x)
MonPo P .fst .snd .isPreorder .IsPreorder.is-refl = λ a n → IsPreorder.is-refl (isPreorder (P .fst .snd)) (a .fst n)
MonPo P .fst .snd .isPreorder .IsPreorder.is-trans = λ a b c z z₁ n →
    IsPreorder.is-trans (isPreorder (P .fst .snd)) (a .fst n)
    (b .fst n) (c .fst n) (z n) (z₁ n)
MonPo P .snd = {!   !}

-- exponentiate with ω^op
StepIndex : Functor (POSET _ _ )(POSET _ _ )
StepIndex .F-ob = MonPo
StepIndex .F-hom f .MonFun.f = λ z →
    (λ z₁ → f .MonFun.f (z .fst z₁)) ,
    (λ n m z₁ → f .MonFun.isMon (z .snd n m z₁))
StepIndex .F-hom f .MonFun.isMon = λ z n → f .MonFun.isMon (z n)
StepIndex .F-id = eqMon _ _ refl
StepIndex .F-seq _ _ = eqMon _ _ refl

-- Equip a hyperdoctrine with a later modality
module Later     
  {C : Category _ _ }
  (H : Functor (C ^op) (POSET _ _))
  (has⊤ : L⊤.Has⊤ H) where 

  H' = (StepIndex ∘F H)

  module L = HDSyntax H 
  module SL = HDSyntax H'

  open L▷
  open L⊤ renaming (HAHom to HAHom⊤)
  open LaterStr  
  open HA
  open HAHom⊤

  has⊤' : Has⊤ H' 
  has⊤' .fst c .top = (λ _ → top (has⊤ .fst c)) , (λ n m z → top-top (has⊤ .fst c))
  has⊤' .fst c .top-top = λ n → top-top (has⊤ .fst c)
  has⊤' .snd {c}{c'} f .f-top = SIProp≡ {H .F-ob  c'} λ i n → has⊤ .snd f .f-top i

  ▷' : {c : ob C} → HA.X (has⊤' .fst c) → HA.X (has⊤' .fst c)
  ▷' {c} (P , ↓clP) .fst zero = L⊤.HA.top (has⊤ .fst c)
  ▷' {c} ( P , ↓clP) .fst (suc n) = P n
  ▷' {c} ( P , ↓clP) .snd n zero m≤n = L⊤.HA.top-top (has⊤ .fst c)
  ▷' {c} ( P , ↓clP) .snd zero (suc m) m≤n = ⊥rec (¬m+n<m m≤n)
  ▷' {c} ( P , ↓clP) .snd (suc n) (suc m) m≤n = ↓clP  _ _ (pred-≤-pred m≤n)

  ▷-intro' : {c : ob C}{P : HA.X (has⊤' .fst c)} → c SL.◂ P ≤ ▷' P
  ▷-intro' {c} {P , ↓clP} zero = top-top (has⊤ .fst c)
  ▷-intro' {c} {P , ↓clP} (suc n) = ↓clP _ _  (1 , refl)

  ▷-mono' : {c : ob C}{P Q : HA.X (has⊤' .fst c)} → 
    c SL.◂ P ≤ Q → 
    c SL.◂ ▷' P ≤ ▷' Q 
  ▷-mono' {c} {P} {Q} prf zero = L.id⊢
  ▷-mono' {c} {P} {Q} prf (suc n) = prf n

  lob' : {c : ob C}{P : HA.X (has⊤' .fst c)} → 
    c SL.◂ ▷' P ≤ P →  
    c SL.◂ has⊤' .fst c .top ≤ P
  lob' {c} {P , ↓clP} prf zero = prf zero
  lob' {c} {P} prf (suc n) = L.seq (lob' {c} {P} prf n) (prf (suc n))   

  ▷-str : (c : ob C) → LaterStr (H' .F-ob c) (has⊤' .fst c)
  (▷ ▷-str c) = ▷' {c}
  ▷-str c .▷-intro = ▷-intro'
  ▷-str c .▷-mono {P}{Q} = ▷-mono' {c}{P}{Q}
  ▷-str c .lob {P} = lob' {c}{P}

  has▷ : Has▷ H'
  has▷ .fst = has⊤'
  has▷ .snd .fst = ▷-str
  has▷ .snd .snd {c}{c'} f .HAHom.f-▷ (P , ↓clP) = 
    SIProp≡ {H .F-ob c'} goal where 
    goal : H' .F-hom f .fun ((▷ ▷-str c) (P , ↓clP)) .fst ≡ ▷' (H' .F-hom f .fun (P , ↓clP)) .fst 
    goal = funExt λ { zero → has⊤ .snd f .f-top
                    ; (suc n) → refl}

module LogicToSILogic
  {Σ : Signature} 
  {M : CBPVModel Σ}
  (L : Logic M) where 

  module L = Logic L

  SIL : Logic M 
  SIL .Logic.VH = StepIndex ∘F L.VH
  SIL .Logic.CH = StepIndex ∘F L.CH
  SIL .Logic.Sq .N-ob (v , c) M .MonFun.f (P , P↓cl) = 
    (λ n → L.pull M $ P n ) , λ n m z → L.pull M .MonFun.isMon (P↓cl n m z)
  SIL .Logic.Sq .N-ob (v , c) M .MonFun.isMon {P}{Q} P≤Q n = L.pull M .MonFun.isMon (P≤Q n)
  SIL .Logic.Sq .N-hom {(v , c)}{(v' , c')} (V , S) = 
    funExt λ M' → eqMon _ _ 
      (funExt λ P → SIProp≡ {L.VH .F-ob v'}
        (funExt λ n → λ i → 
          L.Sq .N-hom (V , S) i M' $ P .fst n))
  SIL .Logic.pullOp op args P Q dargs n = 
    L.pullOp op args (P .fst n) (Q .fst n) (λ x → dargs x n)



{-
open import Cubical.Data.Nat hiding (_+_)
open import Cubical.Data.Nat.Order hiding(isProp≤)
open import Cubical.Categories.Constructions.BinProduct renaming (Fst to Fst')
ω : Category _ _ 
ω .ob = ℕ
ω .Hom[_,_] = _≤_
ω .id = 0 , refl
ω ._⋆_ = ≤-trans
ω .⋆IdL p = {!   !}
ω .⋆IdR = {!   !}
ω .⋆Assoc = {!   !}
ω .isSetHom = {! ×C  !}

record StepIndexedLogic {Σ : Signature} (M : CBPVModel Σ) : Type _ where 
  open CBPVModel M
  field 
    VH : Functor ((V ×C ω) ^op) (POSET _ _)
    CH : Functor ((C ×C ω) ^op) (POSET _ _)
    Sq : NatTrans 
          (FORGET ∘F O ∘F (((Fst' _ _) ^opF) ×F Fst' _ _)) 
          (Hom^op ∘F (VH ×F ((CH ^opF) ∘F to^op^op)))

-}