-- TODO for later.. come up with a nice way to make this modular
-- can this be a purely modular construction... 
-- perhaps not when we think about laws ?
{-# OPTIONS --type-in-type #-}
module HyperDoc.Connectives.Connectives where

open import Cubical.Data.Sigma hiding (_∧_;_∨_)

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude hiding (_∧_;_∨_)
open import Cubical.Foundations.Structure 

open import Cubical.Categories.Category 
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Relation.Binary.Preorder 
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint

open import HyperDoc.Syntax

open Category
open Functor
open MonFun renaming (f to fun)

module L⊥ where 

  record HA {ℓ ℓ'} (P : ob (POSET ℓ ℓ')) : Type (ℓ-max ℓ ℓ') where 
    
    X : Type ℓ
    X = P .fst .fst

    open PreorderStr (P .fst .snd) renaming (_≤_ to _⊢_)
    field 
      bot : X
      explode : {P : X} → bot ⊢ P

  record HAHom {ℓ ℓ'}{P Q  : ob (POSET ℓ ℓ')}(F : MonFun (P .fst) (Q .fst))(Hx : HA P)(Hy : HA Q) : Type ℓ where 
    module Hx = HA {ℓ} Hx
    module Hy = HA {ℓ} Hy
    X = P .fst .fst
    open MonFun F
    field 
      f-top : f Hx.bot ≡ Hy.bot

  -- this could be parameterized by structure
  Has⊥ :  ∀{ℓC ℓC' ℓP ℓP'}{C : Category ℓC ℓC'} → Functor (C ^op) (POSET ℓP ℓP') → Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓP) ℓP')  
  Has⊥ {C = C} F = Σ[ logic ∈ ((c : ob C) → HA (F .F-ob c)) ] ({c c' : ob C}(f : C [ c' , c ]) → HAHom (F .F-hom f) (logic c) (logic c'))
  

module L⊤ where 

  record HA {ℓ ℓ'} (P : ob (POSET ℓ ℓ')) : Type (ℓ-max ℓ ℓ') where 
    
    X : Type ℓ
    X = P .fst .fst

    open PreorderStr (P .fst .snd) renaming (_≤_ to _⊢_)
    field 
      top : X
      top-top : {P : X} → P ⊢ top

  record HAHom {ℓ ℓ'}{P Q  : ob (POSET ℓ ℓ')}(F : MonFun (P .fst) (Q .fst))(Hx : HA P)(Hy : HA Q) : Type ℓ where 
    module Hx = HA {ℓ} Hx
    module Hy = HA {ℓ} Hy
    X = P .fst .fst
    open MonFun F
    field 
      f-top : f Hx.top ≡ Hy.top

  -- this could be parameterized by structure
  Has⊤ :  ∀{ℓC ℓC' ℓP ℓP'}{C : Category ℓC ℓC'} → Functor (C ^op) (POSET ℓP ℓP') → Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓP) ℓP')  
  Has⊤ {C = C} F = Σ[ logic ∈ ((c : ob C) → HA (F .F-ob c)) ] ({c c' : ob C}(f : C [ c' , c ]) → HAHom (F .F-hom f) (logic c) (logic c'))
  
  Preserve⊤ : ∀{ℓC ℓC' ℓD ℓD' ℓP ℓP'}{C : Category ℓC ℓC'}{D : Category ℓD ℓD'}{L : Functor (C ^op) (POSET ℓP ℓP')}
   →  (F : Functor D C) →  Has⊤ L → Has⊤ (L ∘F (F ^opF)) 
  Preserve⊤ F prf .fst d = prf .fst (F-ob (F ^opF) d) 
  Preserve⊤ F prf .snd f = prf .snd (F-hom (F ^opF) f)

module L∧ where

  {-
  field
    _⊗_ :
      ∀ {A A' : ob C}
      (P  : F∣ A ∣)
      (P' : F∣ A' ∣) →
      F∣ (A × A') ∣

      ⊗-β :
      ∀ {X A A'}
      (f1 : C [ X , A ])
      (f2 : C [ X , A' ])
      (P : F∣ A ∣)
      (P' : F∣ A' ∣) →
      F-hom (pair f1 f2)
        (P ⊗ P')
      ≡
      (F-hom f1 P) ∧ (F-hom f2 P')
  -}

  record HA {ℓ ℓ'} (P : ob (POSET ℓ ℓ')) : Type (ℓ-max ℓ ℓ') where 
    
    X : Type ℓ
    X = P .fst .fst

    open PreorderStr (P .fst .snd) renaming (_≤_ to _⊢_)
    field 
      _∧_ : X → X → X 

      and-intro : {P Q R : X} → P ⊢ Q → P ⊢ R → P ⊢ (Q ∧ R) 
      and-elim1 : {P Q R : X} → P ⊢ Q ∧ R → P ⊢ Q 
      and-elim2 : {P Q R : X} → P ⊢ Q ∧ R → P ⊢ R

    and-mono : {P Q R S : X} → P ⊢ R → Q ⊢ S → (P ∧ Q) ⊢ (R ∧ S)
    and-mono {P'}{Q}{R}{S} p q = 
      and-intro {P' ∧ Q} (is-trans _ _ _ (and-elim1 (is-refl (P' ∧ Q))) p ) (is-trans _ _ _ (and-elim2 (is-refl (P' ∧ Q))) q)  
    
  record HAHom {ℓ ℓ'}{P Q  : ob (POSET ℓ ℓ')}(F : MonFun (P .fst) (Q .fst))(Hx : HA P)(Hy : HA Q) : Type ℓ where 
    module Hx = HA {ℓ} Hx
    module Hy = HA {ℓ} Hy
    X = P .fst .fst
    open MonFun F
    field 
      f-and : (x x' : X) → f (x Hx.∧ x') ≡  (f x) Hy.∧ (f x')

  Has∧ :  ∀{ℓC ℓC' ℓP ℓP'}{C : Category ℓC ℓC'} → Functor (C ^op) (POSET ℓP ℓP') → Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓP) ℓP')  
  Has∧ {C = C} F = Σ[ logic ∈ ((c : ob C) → HA (F .F-ob c)) ] ({c c' : ob C}(f : C [ c' , c ]) → HAHom (F .F-hom f) (logic c) (logic c'))

  Preserve∧ : ∀{ℓC ℓC' ℓD ℓD' ℓP ℓP'}{C : Category ℓC ℓC'}{D : Category ℓD ℓD'}{L : Functor (C ^op) (POSET ℓP ℓP')}
   →  (F : Functor D C) →  Has∧ L → Has∧ (L ∘F (F ^opF)) 
  Preserve∧ {L = L} F prf .fst c = prf .fst (F-ob (F ^opF) c)
  Preserve∧ {L = L} F prf .snd f = prf .snd (F-hom (F ^opF) f)

module L∨ where

  record HA {ℓ ℓ'} (P : ob (POSET ℓ ℓ')) : Type (ℓ-max ℓ ℓ') where 
    
    X : Type ℓ
    X = P .fst .fst

    open PreorderStr (P .fst .snd) renaming (_≤_ to _⊢_)
    field 
      _∨_ : X → X → X 
      or-intro1 : {P Q R : X} → P ⊢ Q → P ⊢ (Q ∨ R) 
      or-intro2 : {P Q R : X} → P ⊢ R → P ⊢ (Q ∨ R) 
      or-elim : {P Q R : X} → Q ⊢ P → R ⊢ P → Q ∨ R ⊢ P 

  record HAHom {ℓ ℓ'}{P Q  : ob (POSET ℓ ℓ')}(F : MonFun (P .fst) (Q .fst))(Hx : HA P)(Hy : HA Q) : Type ℓ where 
    module Hx = HA {ℓ} Hx
    module Hy = HA {ℓ} Hy
    X = P .fst .fst
    open MonFun F
    field 
      f-or : (x x' : X) → f (x Hx.∨ x') ≡  (f x) Hy.∨ (f x')


  Has∨ :  ∀{ℓC ℓC' ℓP ℓP'}{C : Category ℓC ℓC'} → Functor (C ^op) (POSET ℓP ℓP') → Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓP) ℓP')  
  Has∨ {C = C} F = Σ[ logic ∈ ((c : ob C) → HA (F .F-ob c)) ] ({c c' : ob C}(f : C [ c' , c ]) → HAHom (F .F-hom f) (logic c) (logic c'))

  Preserve∨ : ∀{ℓC ℓC' ℓD ℓD' ℓP ℓP'}{C : Category ℓC ℓC'}{D : Category ℓD ℓD'}{L : Functor (C ^op) (POSET ℓP ℓP')}
   →  (F : Functor D C) →  Has∨ L → Has∨ (L ∘F (F ^opF)) 
  Preserve∨ {L = L} F prf .fst c = prf .fst (F-ob (F ^opF) c)
  Preserve∨ {L = L} F prf .snd f = prf .snd (F-hom (F ^opF) f)
  
module L∃ where 

  Has∃ : ∀{ℓC ℓC' ℓP ℓP'}{C : Category ℓC ℓC'} → Functor (C ^op) (POSET ℓP ℓP') → Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓP) ℓP') 
  Has∃ {C = C} F = {A A' : ob C}(f : C [ A , A' ]) → HasLeftAdj (F .F-hom f)

  module ∃Syntax
    {ℓC ℓC' ℓP ℓP' : Level}
    {C : Category ℓC ℓC'}
    {L : Functor (C ^op) (POSET ℓP ℓP')}
    (has∃ : Has∃ L) where

    open HDSyntax L


    ∃f : {c c' : ob C}{f : C [ c , c' ]} → F∣ c ∣  → F∣ c' ∣ 
    ∃f {c}{c'}{f} = has∃ f .fst .fun

 {- HasPush : Type
  HasPush = 
    ∀ {A : V .ob}
      {B : C .ob} → 
      (M : O'[ A , B ]) → 
      HasLeftAdj (pull M) -}
module L▷ where 
    
  {-
    algebraic requirement of later modality 
      https://plv.mpi-sws.org/coqdoc/iris/iris.bi.derived_laws_later.html
      https://plv.mpi-sws.org/coqdoc/iris/iris.bi.interface.html#BiLaterMixin
    
    From CoqDoq
      """
        We prove relations between the following statements:
        1. Contractive (▷), later is contractive as expressed by BiLaterContractive. 
        2. (▷ P ⊢ P) → (True ⊢ P), the external/"weak" of Löb as expressed by BiLöb. 
        3. (▷ P → P) ⊢ P, the internal version/"strong" of Löb. 
        4. □ (□ ▷ P -∗ P) ⊢ P, an internal version of Löb with magic wand instead of implication. 
        5. □ (▷ P -∗ P) ⊢ P, a weaker version of the former statement, which does not make the induction hypothesis intuitionistic.
        
        We prove that:
        (1) implies (2) in all BI logics (lemma later_contractive_bi_löb).
        (2) and (3) are logically equivalent in all BI logics (lemma löb_alt_strong).
        (2) implies (4) and (5) in all BI logics (lemmas löb_wand_intuitionistically and löb_wand).
        (5) and (2) are logically equivalent in affine BI logics (lemma löb_alt_wand).
        In particular, this gives that (2), (3), (4) and (5) are logically equivalent in affine BI logics such as Iris.
      """"
  -}

  open L⊤ renaming (HA to HA⊤ ; HAHom to HAHom⊤)

  record LaterStr {ℓ ℓ'} (P : ob (POSET ℓ ℓ'))(has⊤ : HA⊤ P) : Type (ℓ-max ℓ ℓ')  where 

    open HA⊤ has⊤

    open PreorderStr (P .fst .snd) renaming (_≤_ to _⊢_)
    field 
      ▷_ : X → X
      ▷-intro : {P : X} → P ⊢ (▷ P)
      ▷-mono : {P Q : X} → P ⊢ Q → ▷ P ⊢ ▷ Q
      lob : {P : X} → (▷ P) ⊢ P → top ⊢ P
        
  record HAHom 
    {ℓ ℓ'}
    {P Q  : ob (POSET ℓ ℓ')}
    {has⊤P : HA⊤ P}
    {has⊤Q : HA⊤ Q}
    (F : MonFun (P .fst) (Q .fst))
    (Hx : LaterStr P has⊤P )
    (Hy : LaterStr Q has⊤Q) : Type ℓ where 
    module Hx =  LaterStr {ℓ} Hx
    module Hy =  LaterStr {ℓ} Hy
    X = P .fst .fst
    open MonFun F
    field 
      f-▷ : (x : X) → f (Hx.▷ x) ≡ (Hy.▷ f x)

  Has▷ :  ∀{ℓC ℓC' ℓP ℓP'}{C : Category ℓC ℓC'} → Functor (C ^op) (POSET ℓP ℓP') → Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓP) ℓP')  
  Has▷ {C = C} F = 
    Σ[ has⊤ ∈ Has⊤ F ] 
    Σ[ logic ∈ ((c : ob C) → LaterStr (F .F-ob c) (has⊤ .fst c)) ] 
    ({c c' : ob C}(f : C [ c' , c ]) → HAHom (F .F-hom f) (logic c) (logic c'))

module LBI where



  -- A symmetric monoidal closed structure
  record HA {ℓ ℓ'} (P : ob (POSET ℓ ℓ')) : Type (ℓ-max ℓ ℓ') where 
    X : Type ℓ
    X = P .fst .fst
    open PreorderStr (P .fst .snd) renaming (_≤_ to _⊢_)
    field 
      𝐈 : X -- \BI
      _＊_ : X → X → X --\*>
      _-＊_ : X → X → X
      assocl : {P Q R : X} → (P ＊ Q) ＊ R ⊢ (P ＊ (Q ＊ R))
      assocr : {P Q R : X} → (P ＊ (Q ＊ R)) ⊢ (P ＊ Q) ＊ R
      symtry : {P Q : X} → P ＊ Q ⊢ Q ＊ P
      idl : {P : X} → P ⊢ 𝐈 ＊ P 
      idinv : {P : X} → 𝐈 ＊ P ⊢ P 
      ＊-intro : {P Q R S : X} → P ⊢ Q → R ⊢ S → (P ＊ R) ⊢ (Q ＊ S)
      adj : {P Q R : X} → (P ＊ Q) ⊢ R → P ⊢ (Q -＊ R)
      adjinv : {P Q R : X} → P ⊢ (Q -＊ R) → (P ＊ Q) ⊢ R

  HasBI :  ∀{ℓC ℓC' ℓP ℓP'}{C : Category ℓC ℓC'} → Functor (C ^op) (POSET ℓP ℓP') → Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓP) ℓP')  
  HasBI {C = C} F = 
    Σ[ logic ∈ ((c : ob C) → HA (F .F-ob c)) ] {!   !}
    -- ({c c' : ob C}(f : C [ c' , c ]) → HAHom (F .F-hom f) (logic c) (logic c'))

  -- Typically, a Bialgebra (bunched implication algebra), 
  -- is constructed given a partial commutative monoid (UCMRA in Iris)
  -- The monoid abstacts some notion of resource, 
  -- where operation ＊ says how to combine resources
  open import Cubical.Data.Maybe
  _>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B 
  nothing >>= f = nothing
  just x >>= f = f x

  open import Cubical.Functions.Logic
  isDef : {X : Set} → Maybe X → hProp _ 
  isDef nothing = ⊥
  isDef (just _) = ⊤

  extract : {X : Set} → (m  : Maybe X) → {isDef m .fst} → X 
  extract {X} (just x) = x 
  open PreorderStr renaming(_≤_ to _≤P_)

  record PCM : Type where 
    field 
        M : hSet _ 
        _⊚_ : fst M → fst M → Maybe (fst M) 
        𝟙 : fst M 
        lunit : (x : fst M) → (𝟙 ⊚ x) ≡ just x
        runit : (x : fst M) → (x ⊚ 𝟙) ≡ just x
        comm : (x y : fst M) → (x ⊚ y) ≡ (y ⊚ x)
        assoc : (x y z : fst M) → ((y ⊚ z) >>= (x ⊚_)) ≡ ((x ⊚ y) >>= (_⊚ z))

    _#_ : (a b : fst M) → hProp _ 
    a # b = isDef (a ⊚ b)

    -- for any PCM, we have an ordering called the extension ordering
    _≤ext_ : fst M → fst M → hProp _
    _≤ext_ x y = 
      ∃[ z ∶ fst M ] (((x ⊚ z) ≡ just y) , isOfHLevelMaybe 0 (M .snd) (x ⊚ z) (just y) )

  -- Given a PCM, we can define the Poset of upward closed predicates
  module _ (pcm : PCM) where 
    open PCM pcm
    ↑Closed : {P : POSET _ _ .ob} → (⟨ M ⟩  → ⟨ P .fst ⟩ ) → Type
    ↑Closed {P} f = 
      (∀ (m m' : ⟨ M ⟩ ) → 
      ⟨ m ≤ext m' ⟩  → 
      _≤P_ (P .fst .snd) (f m) (f m'))

    isProp↑Closed :  {P : POSET _ _ .ob} → (f : ⟨ M ⟩  → ⟨ P .fst ⟩ ) → 
      isProp (↑Closed {P} f)
    isProp↑Closed {P} f = 
      isPropΠ λ n → isPropΠ λ m → isProp→ 
        (IsPreorder.is-prop-valued (isPreorder (P .fst .snd)) (f n) (f m))
    
    BIProp : POSET _ _ .ob → Type 
    BIProp P = Σ[ f ∈ (⟨ M ⟩  → ⟨ P .fst ⟩ ) ] ↑Closed {P} f

    BIProp≡ : {P : POSET _ _ .ob}{p q : BIProp P} → 
      p .fst ≡ q .fst → p ≡ q
    BIProp≡ {P}{p}{q} prf = ΣPathP (prf , toPathP (isProp↑Closed {P} (prf i1) _ _))

    MonPo : POSET _ _ .ob → POSET _ _ .ob 
    MonPo P .fst .fst = BIProp P
    MonPo P .fst .snd .PreorderStr._≤_ p q  = (m : ⟨ M ⟩ ) → _≤P_ (P .fst .snd) (p .fst m) (q .fst m)
    MonPo P .fst .snd .isPreorder .IsPreorder.is-prop-valued p q = isPropΠ λ x → IsPreorder.is-prop-valued (isPreorder (P .fst .snd)) (p .fst x)
      (q .fst x)
    MonPo P .fst .snd .isPreorder .IsPreorder.is-refl = λ a n → IsPreorder.is-refl (isPreorder (P .fst .snd)) (a .fst n)
    MonPo P .fst .snd .isPreorder .IsPreorder.is-trans = λ a b c z z₁ n →
        IsPreorder.is-trans (isPreorder (P .fst .snd)) (a .fst n)
        (b .fst n) (c .fst n) (z n) (z₁ n)
    MonPo P .snd = {!   !}

    WithResourceLogic : Functor (POSET _ _ )(POSET _ _ )
    WithResourceLogic .F-ob = MonPo
    WithResourceLogic .F-hom f .fun = λ z →
        (λ z₁ → fun f (z .fst z₁)) , (λ m m' z₁ → isMon f (z .snd m m' z₁))
    WithResourceLogic .F-hom f .isMon = λ z m → isMon f (z m)
    WithResourceLogic .F-id = eqMon _ _ refl
    WithResourceLogic .F-seq _ _ = eqMon _ _ refl

    -- Furthermore, given a logic L 
    -- we can upgrade it to a BI or Resource logic
    -- Not quite.. L needs a fair amount of structure to do this..
    -- just start with Pred
   -- module _ {C : Category _ _ }
   --   (L : Functor (C ^op) (POSET _ _)) where 


