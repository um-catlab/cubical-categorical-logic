-- TODO for later.. come up with a nice way to make this modular
-- can this be a purely modular construction... 
-- perhaps not when we think about laws ?

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


open Category
open Functor

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
