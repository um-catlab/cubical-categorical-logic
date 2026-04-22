{-# OPTIONS --type-in-type #-}
module HyperDoc.Operational.Initial where

open import Cubical.Data.Sigma

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor


open Category
open Functor

mutual 
  data VTy : Type where 
    𝟙 Ans : VTy
    U : CTy → VTy 
    _⊗_ _⊕_ : VTy → VTy → VTy 

  data CTy : Type where 
    F : VTy → CTy

data _⊢v_ : (A A' : VTy) → Type 
data _⊢c_ : (A : VTy)(B : CTy) → Type 
data _⊢k_ : (B B' : CTy) → Type 

subC' : ∀ {A A' B} → A ⊢v A' → A' ⊢c B → A ⊢c B

data _⊢v_  where
  -- category 
  subV : ∀ {A A' A''} → A ⊢v A' → A' ⊢v A'' → A ⊢v A''
  var : ∀ {A} → A ⊢v A
  subVIdl : ∀ {A A'} → (V : A ⊢v A') → subV (var {A}) V ≡ V
  subVIdr : ∀ {A A'} → (V : A ⊢v A') → subV V (var {A'}) ≡ V
  subVAssoc : ∀ {A₁ A₂ A₃ A₄}(V : A₁ ⊢v A₂)(W : A₂ ⊢v A₃)(Y : A₃ ⊢v A₄) → 
    subV (subV V W) Y ≡ subV V (subV W Y)
  isSet⊢v : ∀{A A'} → isSet (A ⊢v A')

  -- type structure
  tt : ∀{A} → A ⊢v 𝟙
  subtt : ∀ {A A'} {V : A ⊢v A'} → tt ≡ subV V tt

  yes : ∀{A} → A ⊢v Ans 
  no : ∀{A} → A ⊢v Ans 
  thunk : ∀{A B} → A ⊢c B → A ⊢v U B

  σ₁ : ∀ {A A'} → A ⊢v (A ⊕ A')
  σ₂ : ∀ {A A'} → A' ⊢v (A ⊕ A') 

  _,p_ : ∀ {A A' A''} → A ⊢v A' → A ⊢v A'' → A ⊢v (A' ⊗ A'')
  sub,p : ∀ {X Y Z Z'} {V : X ⊢v Y}{W : Y ⊢v Z}{W' : Y ⊢v Z'} → 
    (subV V W ,p subV V W') ≡ subV V (W ,p W')

data _⊢k_ where
  -- category 
  kcomp : ∀ {B B' B''} → B ⊢k B' → B' ⊢k B'' → B ⊢k B''
  hole : ∀ {B} → B ⊢k B
  kcompIdl : ∀ {B B'} → (M : B ⊢k B') → kcomp (hole {B}) M ≡ M
  kcompIdr : ∀ {B B'} → (M : B ⊢k B') → kcomp M (hole {B'}) ≡ M
  kcompAssoc : ∀ {B₁ B₂ B₃ B₄}(M : B₁ ⊢k B₂)(N : B₂ ⊢k B₃)(P : B₃ ⊢k B₄) → 
    kcomp(kcomp M N) P ≡  kcomp M (kcomp N P)
  isSet⊢k : ∀{B B'} → isSet (B ⊢k B')

  bind : {A : VTy}{B : CTy} → A ⊢c B → F A ⊢k B

data _⊢c_ where 
  -- profunctor      
  subC : ∀ {A A' B} → A ⊢v A' → A' ⊢c B → A ⊢c B
  plug : ∀ {A B B'} → B ⊢k B' → A ⊢c B → A ⊢c B'
  plugId : ∀ {A B}{M : A ⊢c B} → plug (hole {B}) M ≡ M
  subCId : ∀ {A B}{M : A ⊢c B} → subC (var {A}) M ≡ M
  plugDist : ∀ {A B B' B''}{S : B ⊢k B'}{S' : B' ⊢k B''}{M : A ⊢c B} → --rcomp
    plug S' (plug S M) ≡ plug (kcomp S S') M
  subDist : ∀ {A A' A'' B}{V : A ⊢v A'}{V' : A' ⊢v A''}{M : A'' ⊢c B} → --lcomp
    subC V (subC V' M) ≡ subC (subV V V') M
  plugSub : ∀ {A A' B B'}{V : A ⊢v A'}{M : A' ⊢c B}{S : B ⊢k B'} → 
    subC V (plug S M) ≡ plug S (subC V M)
  isSet⊢c : ∀{A B} → isSet (A ⊢c B)

  -- type structuref
  ret : ∀{A B} → F A ⊢k B → A ⊢c B
  ret-sub : ∀ {A B B'}{S : B ⊢k B'}{S' : F A ⊢k B} → 
    ret (kcomp S' S) ≡ plug S (ret S')
  -- ret : ∀{A} → A ⊢c F A
  -- force : ∀{B} →  U B ⊢c B  
  force : ∀{A B} →  A ⊢v U B → A ⊢c B   
  force-sub : ∀{A A' B}{V : A' ⊢v A}{W : A ⊢v U B} → 
    force (subV V W) ≡ subC V (force W) 


  match : ∀ {A A' B} → (A ⊢c B) → (A' ⊢c B) → (A ⊕ A') ⊢c B
  plugmatch : ∀ {A A' B B'}{S : B ⊢k B'}{M : A ⊢c B}{N : A' ⊢c B} → 
    match (plug S M) (plug S N) ≡ plug S (match M N)

subC' = subC

rec× : ∀ {Γ A A' B} → Γ ⊢v (A ⊗ A') → (A ⊗ A') ⊢c B → Γ ⊢c B 
rec× p m = subC p m

import  Cubical.Data.Equality as Eq

-- Q... what about things like (subC var M) ↦ M 
-- what about congruence rules ? (derivable from substituition rules and subC plug congruence) 
data _↦_ : {A : VTy}{B : CTy} → A ⊢c B → A ⊢c B → Type where 
  Fβ : ∀{A B}{M : A ⊢c B} → 
    ------------------------------------
    ret (bind M)  ↦ M

  Uβ : ∀ {A B} {M : A ⊢c B} → 
    ---------------------
    force (thunk M) ↦ M

  +β₁ : ∀ {A A' B}{M : A ⊢c B}{N : A' ⊢c B} →  
    subC σ₁ (match M N) ↦ M

  +β₂ : ∀ {A A' B}{M : A ⊢c B}{N : A' ⊢c B} →  
    subC σ₂ (match M N) ↦ N
  
  subC-cong : ∀ {A A' B}{V : A' ⊢v A}{M M' : A ⊢c B}  →  
    M ↦ M' → 
    --------- 
    subC V M  ↦ subC V M'

  plug-cong : ∀ {A B B'}{S : B ⊢k B'}{M M' : A ⊢c B}  →  
    M ↦ M' → 
    --------- 
    plug S M ↦ plug S M'

  -- Profunctor laws below
{-
  subC-cong-id : ∀ {A B}{M M' : A ⊢c B}{M↦M' : M ↦ M'} → 
    PathP 
      (λ i → subCId {M = M} i ↦ subCId {M = M'} i) 
      (subC-cong {V = var} M↦M') 
      M↦M'  

  subC-cong-seq : ∀ {A A' A'' B}{V : A'' ⊢v A'}{V' : A' ⊢v A}{M M' : A ⊢c B}{M↦M' : M ↦ M'}  → 
    PathP 
      (λ i → sym (subDist {V = V}{V'}{M})i ↦ sym (subDist {V = V}{V'}{M'}) i) 
      (subC-cong {V = subV V V'} M↦M') 
      (subC-cong {V = V} (subC-cong {V = V'} M↦M'))

  plug-cong-id :  ∀ {A B}{M M' : A ⊢c B}{M↦M' : M ↦ M'} → 
    PathP 
      (λ i → plugId {M = M} i ↦ plugId {M = M'} i) 
      (plug-cong {S = hole} M↦M') 
      M↦M'  

  plug-cong-seq : ∀ {A B B' B''}{S : B ⊢k B'}{S' : B' ⊢k B''}{M M' : A ⊢c B}{M↦M' : M ↦ M'}  → 
    PathP 
      (λ i → sym (plugDist {S = S}{S'}{M})i ↦ sym (plugDist {S = S}{S'}{M'}) i) 
      (plug-cong {S = kcomp S S'} M↦M') 
      (plug-cong {S = S'} (plug-cong {S = S} M↦M'))

  plug-subC-cong : ∀ {A A' B B'}{V : A' ⊢v A}{S : B ⊢k B'}{M M' : A ⊢c B}{M↦M' : M ↦ M'}  →
    PathP 
      (λ i → plugSub {V = V}{M}{S} i  ↦ plugSub {V = V}{M'}{S}i)
      (subC-cong {V = V} (plug-cong {S = S} M↦M'))
      (plug-cong {S = S} (subC-cong {V = V} M↦M')) 


  isSet↦ : ∀ {A B} {M M' : A ⊢c B} → isSet (M ↦ M')
  -}
  -- Prop is problematic in the eliminator.. 
  -- just add the rules .. 
  isProp↦ : ∀ {A B} {M M' : A ⊢c B} → isProp (M ↦ M')


-- subC (V ,p V') M ↦ subC (V ,p V') M
--huh : ∀ {Γ A A' B}{V : Γ ⊢v A}{V' : Γ  ⊢v A'}{M : (A ⊗ A') ⊢c B} → rec× (V ,p V') M ↦ subC ((V ,p V')) M 
--huh = {!   !}

open import HyperDoc.Operational.Model
open import HyperDoc.Operational.Graph



V : Category ℓ-zero ℓ-zero
V .ob = VTy
V .Hom[_,_] = _⊢v_
V .id = var
V ._⋆_ = subV
V .⋆IdL = subVIdl
V .⋆IdR = subVIdr
V .⋆Assoc = subVAssoc
V .isSetHom = isSet⊢v

C : Category ℓ-zero ℓ-zero 
C .ob = CTy
C .Hom[_,_] = _⊢k_
C .id = hole
C ._⋆_ = kcomp
C .⋆IdL = kcompIdl
C .⋆IdR = kcompIdr
C .⋆Assoc = kcompAssoc
C .isSetHom = isSet⊢k


compGraph : VTy → CTy → ob (GRAPH ℓ-zero ℓ-zero ) 
compGraph A B .fst = (A ⊢c B) , isSet⊢c
compGraph A B .snd M M' = (M ↦ M') , isProp→isSet isProp↦


module no {A B B'}{S : B ⊢k B'}{M M' : A ⊢c B}{e : M ↦ M'} where  

  prf : M ↦ M' 
  prf = subst2 (λ h h' →  h ↦ h' ) plugId plugId (plug-cong {S = hole} e)

  prf' : M ↦ M' 
  prf' = subst2 (λ h h' →  h ↦ h' ) subCId subCId (subC-cong {V = var} e)

-- cant prove isProp↦
-- ex)   M↦M' ≡ plug-cong {hole} M↦M' ≡ subC-cong {var}  M↦M'

{-}
pcompGraph : VTy → CTy → ob (pGRAPH ℓ-zero ℓ-zero ) 
pcompGraph A B .fst = compGraph A B
pcompGraph A B .snd M M' = isProp↦
-}

open BifunctorSep
O : BifunctorSep (V ^op) C (GRAPH ℓ-zero ℓ-zero) 
O .Bif-ob = compGraph
O .Bif-homL V B .fst = subC V 
O .Bif-homL V B .snd = subC-cong
O .Bif-L-id = Σ≡Prop (λ f → isPropImplicitΠ2 λ n n' → isProp→ isProp↦) (funExt λ _ → subCId)
O .Bif-L-seq V V' = Σ≡Prop (λ f → isPropImplicitΠ2 λ n n' → isProp→ isProp↦) (funExt λ M → sym subDist)
O .Bif-homR A S .fst = plug S
O .Bif-homR A S .snd = plug-cong
O .Bif-R-id = Σ≡Prop (λ f → isPropImplicitΠ2 λ n n' → isProp→ isProp↦) (funExt λ _ → plugId)
O .Bif-R-seq S S' = Σ≡Prop (λ f → isPropImplicitΠ2 λ n n' → isProp→ isProp↦)  (funExt λ _ → sym plugDist)
O .SepBif-RL-commute V S = Σ≡Prop (λ f → isPropImplicitΠ2 λ n n' → isProp→ isProp↦)  (funExt λ _ → plugSub)
{-
O : BifunctorSep (V ^op) C (pGRAPH ℓ-zero ℓ-zero) 
O .Bif-ob A B = compGraph A B
O .Bif-homL V B .fst M = subC V M
O .Bif-homL V B .snd = subC-cong
O .Bif-L-id {A}{B} = pGraphHom≡  {G = compGraph A B}{compGraph A B} (funExt λ M → subCId)
O .Bif-L-seq {A}{A'}{A''}{B} V V' = pGraphHom≡  {G = compGraph A B }{compGraph A'' B } (funExt λ M → sym subDist)
O .Bif-homR A S .fst M = plug S M
O .Bif-homR A S .snd = plug-cong
O .Bif-R-id {A}{B}=  pGraphHom≡  {G = compGraph A B}{compGraph A B} (funExt λ M → plugId)
O .Bif-R-seq {A}{B}{B'}{B''}S S' = pGraphHom≡  {G = compGraph A B }{compGraph A B'' } (funExt λ M → sym plugDist)
O .SepBif-RL-commute {A}{A'}{B}{B'} V S = pGraphHom≡ {G = compGraph A B }{compGraph A' B'} (funExt λ M → plugSub)

-}
{-
O : BifunctorSep (V ^op) C (GRAPH ℓ-zero ℓ-zero) 
O .Bif-ob A B = compGraph A B
O .Bif-homL V B .fst M = subC V M
O .Bif-homL V B .snd = subC-cong
O .Bif-L-id {A} {B} i .fst M = subCId i
O .Bif-L-id {A} {B} i .snd M↦M' = subC-cong-id {M↦M' = M↦M'} i
O .Bif-L-seq {A} {A'} {A''} {B} V V' i .fst M = sym (subDist {V = V'}{V}) i
O .Bif-L-seq {A} {A'} {A''} {B} V V' i .snd {M}{M'} M↦M' = subC-cong-seq {M↦M' = M↦M'}  i
O .Bif-homR A S .fst M = plug S M
O .Bif-homR A S .snd = plug-cong
O .Bif-R-id {A} {B} i .fst M = plugId i
O .Bif-R-id {A} {B} i .snd  M↦M' = plug-cong-id {M↦M' = M↦M'} i
O .Bif-R-seq {A} {B} {B'} {B''} S S' i .fst M = sym (plugDist {S = S}{S'}) i
O .Bif-R-seq {A} {B} {B'} {B''} S S' i .snd {M}{M'} M↦M' = plug-cong-seq  {M↦M' = M↦M'}  i
O .SepBif-RL-commute {A} {A'} {B} {B'} V S i .fst M = plugSub {V = V}{M}{S} i
O .SepBif-RL-commute {A} {A'} {B} {B'} V S i .snd {M}{M'} M↦M' = plug-subC-cong {M↦M' = M↦M'} i
-}
Syn : CBPVModel ℓ-zero ℓ-zero ℓ-zero ℓ-zero ℓ-zero ℓ-zero 
Syn .fst = V
Syn .snd .fst = C
Syn .snd .snd = O

open import HyperDoc.Operational.TypeStructure  
open import Cubical.Categories.Presheaf.Morphism.Alt
open PshHom
open TypeStructure Syn

open WkRepresentation
open import Cubical.Categories.NaturalTransformation
open NatTrans
open import Cubical.Data.Unit

has𝟙 : Has𝟙 
has𝟙 .fst = 𝟙
has𝟙 .snd .N-ob A tt = tt
has𝟙 .snd .N-hom V = funExt λ {tt → subtt}

has× : Has× 
has× A A' .fst = A ⊗ A'
has× A A' .snd .N-ob A'' (V , V') = V ,p V'
has× A A' .snd .N-hom V = funExt λ (W , W') → sub,p

has+ : Has+ 
has+ A A' .TypeStructure.Has+'.A+A' = A ⊕ A'
has+ A A' .TypeStructure.Has+'.match .N-ob B (M , N) = match M N
has+ A A' .TypeStructure.Has+'.match .N-hom S = funExt λ (M , N) → plugmatch
has+ A A' .TypeStructure.Has+'.σ₁ = σ₁
  -- subC σ₁
has+ A A' .TypeStructure.Has+'.σ₂ = σ₂
has+ A A' .TypeStructure.Has+'.+β₁ M N = +β₁
has+ A A' .TypeStructure.Has+'.+β₂ M N = +β₂

hasUTy : HasUTy 
hasUTy B .rep = U B
hasUTy B .fwd .N-ob A = force
hasUTy B .fwd .N-hom V = funExt λ V' → force-sub
hasUTy B .bkwd = thunk
hasUTy B .wkretract M = Uβ

hasFTy : HasFTy 
hasFTy A .rep = F A
hasFTy A .fwd .N-ob B = ret
hasFTy A .fwd .N-hom {B}{B'}S = funExt λ S' → ret-sub
hasFTy A .bkwd = bind
hasFTy A .wkretract M = Fβ



{-
has𝟙 : Has𝟙 
has𝟙 .rep = 𝟙
has𝟙 .fwd .N-ob A V = tt
has𝟙 .fwd .N-hom _ = refl
has𝟙 .bkwd tt = tt
has𝟙 .wkretract tt = {!   !} -- construct ⊥, impossible!
-}
{-
hasFTy : HasFTy 
hasFTy A .rep = F A
hasFTy A .fwd .N-ob B S = plug S ret
hasFTy A .fwd .N-hom S = funExt λ S' → sym plugDist
hasFTy A .bkwd = bind
hasFTy A .wkretract M = Fβ
-}

{-
hasUTy : HasUTy 
hasUTy B .fst = U B
hasUTy B .snd .fst .N-ob A V = subC V force
hasUTy B .snd .fst .N-hom A A' V V' = sym subDist
hasUTy B .snd .snd .N-ob A M = thunk M
hasUTy B .snd .snd .N-hom A A' V M = {!   !}
-}
-- Q: What is the trick to get away without having to specify this ?
-- thunk (subC V M) ≡ subV V (thunk M) 


{-
open import Cubical.Relation.Binary.Preorder
open import HyperDoc.Lib
open PreorderStr
open IsPreorder 


ABPre : VTy → CTy → Preorder _ _
ABPre A B .fst = A ⊢c B
ABPre A B .snd ._≤_ = RTC _↦_
-- can this be inherited if R is prop valued?
ABPre A B .snd .isPreorder .is-prop-valued = {! Rel  !} 
ABPre A B .snd .isPreorder .is-refl M = ref
ABPre A B .snd .isPreorder .is-trans M N P = trans

open import Cubical.Relation.Binary.Base
RGraph' : Type 
RGraph' = 
  Σ[ S ∈ hSet _ ] 
  Σ[ R ∈ (⟨ S ⟩ → ⟨ S ⟩ → hSet _) ] 
  ((s : ⟨ S ⟩) → {! ⟨ R s s ⟩    !})

-- exactly the notion of transition system
-- except we have a reflexive transition
record RGraph : Type where 
  field 
    Car : Type 
    _R_ : Car → Car → Type 
    Rid : {x : Car} → x R x

-- exactly the notion of transition system morphism 
-- except we need to preserve id 
-- Q : is preservation of identity compatible with our notion of reduction ..?
record Relator (H G : RGraph) : Type where 
  private 
    module H = RGraph H 
    module G = RGraph G 
  field 
    Fv : H.Car → G.Car
    Fe : {x y : H.Car} → x H.R y → Fv x G.R Fv y
    -- this is the identity extension principle! 
    Fid : {x : H.Car} → Fe (H.Rid {x}) ≡ G.Rid{Fv x}
    
RG : Category _ _ 
RG .ob = RGraph
RG .Hom[_,_] = Relator
RG .id = {!   !}
RG ._⋆_ = {!   !}
RG .⋆IdL = {!   !}
RG .⋆IdR = {!   !}
RG .⋆Assoc = {!   !}
RG .isSetHom = {!   !}



-- RG has pointwise products


open import Cubical.Data.Graph.Base 
module _
  {ℓ ℓ' : Level}
  (G : Graph ℓ ℓ') where 

  -- The reflexive graph.. ?
  -- Reynolds
  data _⊢_ : G .Node → G .Node → Type (ℓ-max ℓ ℓ') where  
    var : {X : G .Node} → X ⊢ X

    app : {X Y Z : G .Node} →
      G .Edge X Y →
      Z ⊢ X →
      Z ⊢ Y

  sub : {X Y Z : G .Node} → X ⊢ Y → Y ⊢ Z → X ⊢ Z
  sub m var = m
  sub m (app x n) = app x (sub m n)

  idl : {X Y : G .Node} → (f : X ⊢ Y) → sub var f ≡ f
  idl var = refl
  idl (app x f) = cong₂ app refl (idl f)

  assoc : {X Y Z W : G .Node}(f : X ⊢ Y) (g : Y ⊢ Z) (h : Z ⊢ W) →
    sub (sub f g) h ≡ sub f (sub g h)
  assoc f g var = refl
  assoc f g (app x h) = cong₂ app refl (assoc f g h)

  FreeCat : Category ℓ (ℓ-max ℓ ℓ')
  FreeCat .ob = G .Node
  FreeCat .Hom[_,_] = _⊢_
  FreeCat .id = var
  FreeCat ._⋆_ = sub
  FreeCat .⋆IdL = idl
  FreeCat .⋆IdR _ = refl
  FreeCat .⋆Assoc = assoc
  FreeCat .isSetHom = {!   !} -- requires hLevel restriction on Nodes and Edges
{-
-- hom category.. 
{-
  For each A, B
  - O[A , B] : Algebra
  - O[A , B] : TSystem 
    which is a set 
      A ⊢c B 
      paired with a relation _↦_ : A ⊢c B → A ⊢c B → Type 
    BUT
      if the relation _↦_ is prop valued, 
        we can take the reflexive transitive closure and get
        O[ A , B ] : Preorder 
      OR if the relation _↦_ is set valued 
        we can view (A ⊢c B, _↦_) as a Graph 
        and yield the Free Category for that graph, giving 
        O[ A , B ] : Category 

  There is some kind of 2-categorical structure here ...

  What if.. Instead of Category.. 
  we mapped into Reflexive Graphs.. 
    Given a one step relation _↦_ : A ⊢c B → A ⊢c B → Type ..
      We can give a relflexive closure on it.. 
      which turns it into a reflexive graph


-}

G↦ : VTy → CTy → Graph _ _ 
G↦ A B .Node = A ⊢c B
G↦ A B .Edge = _↦_

Free : VTy → CTy → Category _ _ 
Free A B = FreeCat (G↦ A B)

thing : {A : VTy}{B B' : CTy}{M M' : A ⊢c B} → (S : B ⊢k B') → Free  A B [ M , M' ] → Free  A B' [ plug S M , plug S M' ] 
thing S var = var
thing S (app M↦M' M''↦*M) = app (plug-cong M↦M') (thing S M''↦*M)

plugFun : {A : VTy}{B B' : CTy} → B ⊢k B' → Functor (Free A B) (Free A B') 
plugFun S .F-ob M = plug S M
plugFun {A}{B}{B'} S .F-hom {M} {M'} = thing S
plugFun S .F-id = refl
plugFun {A}{B}{B'} S .F-seq {M}{M'}{M''} = goal M M' M'' where 
  goal : (M M' M'' : A  ⊢c B) (f : Free  A B [ M , M' ]) (g : Free  A B [ M' , M'' ]) →
    thing S (seq' (Free  A B) f g) ≡ seq' (Free  A B') (thing S f) (thing S g)
  goal M M' M'' f var = refl
  goal M M' M'' f (app  x g) = cong (λ h → app (plug-cong x) h )  (goal _ _ _ f g)


ABRGraph : VTy → CTy → RGraph 
ABRGraph A B .RGraph.Car = A ⊢c B
ABRGraph A B .RGraph._R_ = RC _↦_
ABRGraph A B .RGraph.Rid = ref


  So we have 
     O[ A , B ] : RGraph 

  so what.. 
  Can we use Reynolds Program ?

  What about a profunctor 
    O : V^op × C → RGRAPH

  would such a thing be useful ..?


-}



V : Category ℓ-zero ℓ-zero
V .ob = VTy
V .Hom[_,_] = _⊢v_
V .id = var
V ._⋆_ = subV
V .⋆IdL = subVIdl
V .⋆IdR = subVIdr
V .⋆Assoc = subVAssoc
V .isSetHom = isSet⊢v

C : Category ℓ-zero ℓ-zero 
C .ob = CTy
C .Hom[_,_] = _⊢k_
C .id = hole
C ._⋆_ = kcomp
C .⋆IdL = kcompIdl
C .⋆IdR = kcompIdr
C .⋆Assoc = kcompAssoc
C .isSetHom = isSet⊢k

open import HyperDoc.Operational.TransitionSystemAltAlt 

TSys : VTy → CTy → ob TSysCat
TSys A B .fst = A ⊢c B
TSys A B .snd = _↦_ {A}{B}


OR : Functor (V ^op ×C C) RG 
OR .F-ob (A , B) = ABRGraph A B
OR .F-hom (V , S) .Relator.Fv M = subC V (plug S M)
OR .F-hom (V , S) .Relator.Fe {M} {M'} (base M↦M') = base (subC-cong (plug-cong M↦M'))
OR .F-hom (V , S) .Relator.Fe {M} {M'} ref = ref
OR .F-hom (V , S) .Relator.Fid = refl
OR .F-id = {!   !}
OR .F-seq = {!   !}

open import Cubical.Data.Sigma 
O :  Functor ((V ^op) ×C C) TSysCat
O .F-ob (A , B) = TSys A B
O .F-hom (V , S) .fst M = subC V (plug S M)
O .F-hom (V , S) .snd {M}{M'} M↦M' = subC-cong (plug-cong M↦M')
O .F-id = ΣPathP ((funExt λ M → subCId ∙ plugId) , {!   !})
  -- Σ≡Prop (λ f → isPropImplicitΠ  λ M → isPropImplicitΠ  λ M' → isProp→ isProp↦) 
  -- (funExt λ M → subCId ∙ plugId)
O .F-seq (V , S)(V' , S') = 
  Σ≡Prop (λ f → isPropImplicitΠ  λ M → isPropImplicitΠ  λ M' → isProp→ isProp↦)  
    (funExt (λ M → sym (subDist )  ∙ cong₂ subC refl (cong₂ subC refl (sym plugDist) ∙  plugSub)))


open import HyperDoc.Operational.ModelAlt
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open NatTrans 

Syn : CBPVModel
Syn .CBPVModel.V = V
Syn .CBPVModel.C = C
Syn .CBPVModel.O = O

open CBPVModel using (O[_,-])


CL : CBPVMorphism Syn SetModel 
CL .CBPVMorphism.FV = V [ 𝟙 ,-]
CL .CBPVMorphism.FC = O[_,-] Syn 𝟙
CL .CBPVMorphism.FO .N-ob (A , B) .fst M V = subC V M
CL .CBPVMorphism.FO .N-ob (A , B) .snd {M}{M'} M↦M' V = subC-cong M↦M' 
CL .CBPVMorphism.FO .N-hom {A , B}{A' , B'} (V , S) = 
  ΣPathP ((funExt λ M → funExt λ V' → (subDist ∙ plugSub) ∙ sym subCId) ,
     toPathP (implicitFunExt λ {N} → implicitFunExt λ {N'} → funExt λ N↦N' → funExt λ V' → isProp↦ _ _))


open import HyperDoc.Syntax
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Functor 
open Functorᴰ

module Elim (Synᴰ : CBPVModelᴰ Syn ) where 
  open CBPVModelᴰ Synᴰ
  open import Cubical.Categories.Displayed.Bifunctor
  open import Cubical.Categories.Bifunctor

  open Bifunctorᴰ OᴰBif

  mutual 
    vty : (A : VTy) → ob[ Vᴰ ] A
    vty 𝟙 = {!   !}
    vty Ans = {!   !}
    vty (U B) = {!   !}

    cty : (B : CTy) → ob[ Cᴰ ] B
    cty (F A) = {!   !}

    vtm : {A A' : VTy} → (f : Hom[ V , A ] A') → Hom[ Vᴰ ][ f  , vty A ] (vty A')
    vtm (subV f f₁) = (Vᴰ ⋆ᴰ vtm f) (vtm f₁)
    vtm var = idᴰ Vᴰ
    vtm (subVIdl f i) = Vᴰ .⋆IdLᴰ (vtm f) i
    vtm (subVIdr f i) = Vᴰ .⋆IdRᴰ (vtm f) i
    vtm (subVAssoc f f₁ f₂ i) = Vᴰ .⋆Assocᴰ (vtm f) (vtm f₁) (vtm f₂)  i
    vtm (isSet⊢v f f₁ x y i i₁) = Vᴰ .isSetHomᴰ {! vtm f  !} {!   !} {!   !} {!   !} i i₁
    vtm tt = {!   !}
    vtm yes = {!   !}
    vtm no = {!   !}
    vtm (thunk x) = {!   !}

    ctm-sub : {A A' : VTy}{B : CTy} → (V : A' ⊢v A)(M : A ⊢c B) → Oᴰ'[ subC V M  ][ vty A' , cty B ]
    ctm-sub {A}{A'}{B} V M = subst (λ h → F-obᴰ Oᴰ (vty A' , cty B) .fst h) (cong₂ subC refl plugId) (Bif-homLᴰ{f = V} (vtm V) (cty B) .fst M (ctm M))

    ctm-plug : {A : VTy}{B B' : CTy} → (S : B ⊢k B')(M : A ⊢c B) → Oᴰ'[ plug S M  ][ vty A , cty B' ]
    ctm-plug {A}{A'}{B} S M = subst (λ h → F-obᴰ Oᴰ (vty A , cty B) .fst h) subCId (Bif-homRᴰ  (vty A) (ktm S) .fst M (ctm M))
    
    ctm : {A : VTy}{B : CTy} → (M : A ⊢c B) → Oᴰ'[ M ][ vty A , cty B ]
    ctm {A}{B} (subC V M) = ctm-sub V M 
    ctm {A}{B} (plug S M) = ctm-plug S M 
    ctm (plugId i) = {!   !}
    ctm (subCId i) = {!   !}
    ctm (plugDist i) = {!   !}
    ctm (subDist i) = {!   !}
    ctm (plugSub i) = {!   !}
    ctm (isSet⊢c f f₁ x y i i₁) = {!   !}
    ctm (ret x) = {!   !}
    ctm (force x) = {!   !}
    ctm (force-sub i) = {!   !}

    -- this is just some opaque type.. 
    -- impossible!, unless you give me the answer for all parameters! 
    
    ctmRel : {A : VTy}{B : CTy}{M M' : A ⊢c B}(M↦M' : M M.↦O M') → OᴰRel[ M↦M' ][ ctm M , ctm M' ]
    -- F-obᴰ Oᴰ (vty A , cty B) .snd M↦M' (ctm M) (ctm M')
    ctmRel (Fβ{A}{A'}{B}{V}{M}) = {!   !} -- OᴰRel[ Fβ ][ ctm-plug (bind M) (ret V) , ctm-sub V M ]  Exactly!. but this is forward reduction.. not anti reduction.., anti is used above
    ctmRel {A} {B} {M} {M'} Uβ = {!   !} -- ctmRel M↦M'
    ctmRel (subC-cong {A}{A'}{B}{V}{M}{M'} M↦M') = subst {!   !} {!   !} have where 
      have : Bif-obᴰ (vty A') (cty B) .snd
        (Bifunctor.Bif-homL (ParFunctorToBifunctor M.O) V B .snd M↦M')
        (Bif-homLᴰ (vtm V) (cty B) .fst M (ctm M))
        (Bif-homLᴰ (vtm V) (cty B) .fst M' (ctm M')) 
      have = Bif-homLᴰ{f = V} (vtm V) (cty B) .snd {M}{M'}{M↦M'} (ctm M) (ctm M') (ctmRel M↦M')
    -- {! Bif-homLᴰ{f = V} (vtm V) (cty B) .snd {M}{M'}{M↦M'} ? ? ? !} -- OᴰRel[ subC-cong M↦M' ][ ctm-sub V₁ M₁ , ctm-sub V₁ M'' ] given OᴰRel[ M↦M' ][ ctm M₁ , ctm M'' ]
    ctmRel {A} {B} {M} {M'} (plug-cong M↦M') = {!  Oᴰ .F-homᴰ ? .snd  ? ?  ? !}
    ctmRel {A} {B} {M} {M'} (isProp↦ M↦M' M↦M'' i) = {!   !}
    -- essentially 
    module _ (no : VTy → Type) where 
      hopeless : no 𝟙 
      hopeless = {!  !}
      -- unless you give me the answer for all VTy! 


    ktm : {B B' : CTy} → (f : Hom[ C , B ] B') → Hom[ Cᴰ ][ f  , cty B ] (cty B')
    ktm (kcomp g g₁) = (Cᴰ ⋆ᴰ ktm g) (ktm g₁)
    ktm hole = idᴰ Cᴰ
    ktm (kcompIdl g i) = Cᴰ .⋆IdLᴰ (ktm g) i
    ktm (kcompIdr g i) = Cᴰ .⋆IdRᴰ (ktm g) i
    ktm (kcompAssoc g g₁ g₂ i) = Cᴰ .⋆Assocᴰ (ktm g) (ktm g₁) (ktm g₂)  i
    ktm (isSet⊢k g g₁ x y i i₁) = {!   !}
    ktm (bind x) = {!   !}

  SV : Section Id Vᴰ 
  SV .Section.F-obᴰ = vty
  SV .Section.F-homᴰ = vtm
  SV .Section.F-idᴰ = {!   !}
  SV .Section.F-seqᴰ = {!   !}

  SC : Section Id Cᴰ 
  SC .Section.F-obᴰ = cty
  SC .Section.F-homᴰ = ktm
  SC .Section.F-idᴰ = {!   !}
  SC .Section.F-seqᴰ = {!   !}

  open CBPVSection {Syn}{Syn}{idCBPVMorphism}{Synᴰ}
  SO : SectionNat SV SC
  SO .CBPVSection.SectionNat.N-obᴰ = ctm
  SO .CBPVSection.SectionNat.N-obᴰRel {A}{B}{M}{M'}{M↦M'} = ctmRel M↦M'
  SO .CBPVSection.SectionNat.N-homᴰ = {!   !}
  SO .CBPVSection.SectionNat.N-homᴰRel = {!   !}



{-
module ModelSection 
  {M N : CBPVModel }
  (F : CBPVMorphism M N)
  (L : Logic N) where 

  open CBPVMorphism F
  private 
    module M = CBPVModel M 
    module N = CBPVModel N
    module L = Logic L
    module VH' = HDSyntax (L.VH ∘F (FV ^opF))
    module CH' = HDSyntax (L.CH ∘F (FC ^opF))

  open ConvertLogic N L
  module _ 
    (SV : Section FV Vᴰ) 
    (SC : Section FC Cᴰ) where 

    private 
      module SV = Section SV 
      module SC = Section SC
    
    SectionO : Type 
    SectionO = 
      ∀ 
        {A : ob M.V}
        {B : ob M.C}
        (M : M.O[ A , B ] .fst) → 
        Oᴰ .F-obᴰ {FV .F-ob A , FC .F-ob B} (SV.F-obᴰ A , SC.F-obᴰ B)  .fst (FO .N-ob (A , B) .fst M)
      
  CBPVSection : Type 
  CBPVSection = Σ[ SV ∈ Section FV Vᴰ ] Σ[ SC ∈ Section FC Cᴰ ] SectionO SV SC

CBPVGlobalSection : {M : CBPVModel } → Logic M → Type 
CBPVGlobalSection L = ModelSection.CBPVSection idCBPVMorphism L
open import Cubical.Categories.Instances.Preorders.Monotone
open NatTrans 
open MonFun
module hrm (L : Logic Syn) where 
  open Logic L
  module LV = HDSyntax VH
  module LC = HDSyntax CH

  open Push L

  module _ (hasPush : HasPush) where 
    open PushSyntax hasPush

    mutual 
      vty : (A : VTy) → LV.F∣ A ∣ 
      vty 𝟙 = {!   !}
      vty Ans = {!   !}
      vty (U B) = pull (force var) $ cty B

      cty : (B : CTy) → LC.F∣ B ∣
      cty (F A) = hasPush (ret var) .fst $  vty A 

  {-
        vtm-thunk : ∀ {A  B} → (M : A ⊢c B) →  A LV.◂ vty A ≤ LV.f* (thunk M) (pull force $ cty B) 
          vtm-thunk {A}{B} M = 
            LV.seq (ctm M) (
            LV.eqTo≤ (cong (λ h → MonFun.f (pull h) (cty B)) (sym Uβ ∙ sym plugId)
              ∙ cong (λ h → h .MonFun.f (cty B)) (pullLComp (thunk M) force))) 

  data _↦_ : {A : VTy}{B : CTy} → A ⊢c B → A ⊢c B → Type where 
    Fβ : ∀{A A' B}{V : A ⊢v A'}{M : A' ⊢c B} → 
      ------------------------------------
      plug (bind M) (ret V) ↦ (subC V M)

    Uβ : ∀ {A B} {M : A ⊢c B} → 
      ---------------------
      force (thunk M) ↦ M
    
    subC-cong : ∀ {A A' B}{V : A' ⊢v A}{M M' : A ⊢c B}  →  
      M ↦ M' → 
      --------- 
      subC V M  ↦ subC V M'

    plug-cong : ∀ {A B B'}{S : B ⊢k B'}{M M' : A ⊢c B}  →  
      M ↦ M' → 
      --------- 
      plug S M ↦ plug S M'

    isProp↦ : ∀ {A B} {M M' : A ⊢c B} → isProp (M ↦ M')


    -}
      vtm : {A A' : VTy} → (V : A ⊢v A') → A LV.◂ vty A ≤ LV.f* V (vty A')
      vtm (subV V₁ V₂) = {!   !}
      vtm var = {!   !}
      vtm (subVIdl V₁ i) = {!   !}
      vtm (subVIdr V₁ i) = {!   !}
      vtm (subVAssoc V₁ V₂ V₃ i) = {!   !}
      vtm (isSet⊢v V₁ V₂ x y i i₁) = {!   !}
      vtm tt = {!   !}
      vtm yes = {!   !}
      vtm no = {!   !}
      vtm (thunk {A}{B} M) = goal where 

        have : A LV.◂ vty A ≤ (pull (force (thunk M)) $ cty B) 
        have = LV.seq (ctm M) (antiRed Uβ)

        wat : force (thunk M) ≡ subC (thunk M) (plug hole (force var)) 
        wat = (cong force (sym (subVIdr _)) ∙ sym force-sub) ∙ cong₂ subC refl (sym plugId)
        
        goal : A LV.◂ vty A ≤ LV.f* (thunk M) (pull (force var) $ cty B) 
        goal = LV.seq (LV.seq have (LV.eqTo≤ (cong (λ h → f (pull h) (cty B)) wat))) VM*→V*M*

      ktm : {B B' : CTy} → (S : B ⊢k B') → B LC.◂ cty B ≤ LC.f* S (cty B')
      ktm (kcomp S S₁) = {!   !}
      ktm hole = {!   !}
      ktm (kcompIdl S i) = {!   !}
      ktm (kcompIdr S i) = {!   !}
      ktm (kcompAssoc S S₁ S₂ i) = {!   !}
      ktm (isSet⊢k S S₁ x y i i₁) = {!   !}
      ktm (bind {A}{B} M) = {!   !} where 

        have : A LV.◂ vty A ≤ ((pull (plug (bind M) (ret var)) $ cty B)) 
        have = LV.seq (LV.seq (ctm M) (LV.eqTo≤ (cong (λ h → f (pull h) (cty B)) (sym  subCId)))) (antiRed Fβ)

        sub : A LV.◂ vty A ≤ pull (ret var) .f (LC.f* (bind M) (cty B))
        sub = LV.seq have (LV.eqTo≤ {!  !})
        
        goal : F A LC.◂ hasPush (ret var) .fst $ vty A ≤ LC.f* (bind M) (cty B) 
        goal = pullToPush (ret var) sub

      ctm : ∀{A B} → (M : A ⊢c B) → A LV.◂ vty A ≤ (pull M $ cty B)
      ctm (subC x M) = {!   !}
      ctm (plug x M) = {!   !}
      ctm (plugId i) = {!   !}
      ctm (subCId i) = {!   !}
      ctm (plugDist i) = {!   !}
      ctm (subDist i) = {!   !}
      ctm (plugSub i) = {!   !}
      ctm (isSet⊢c M M₁ x y i i₁) = {!   !}
      ctm (ret {A} {A'} V) = {! pushToPull  !} where 
        have : A LV.◂ vty A ≤ LV.f* V (vty A') 
        have = vtm V

        goal : A LV.◂ vty A ≤ (pull (ret V) $ (hasPush (ret var) .fst $ vty A')) 
        goal = {!   !}
      --ctm (bind M M₁) = {!   !}
      ctm (force {A}{B} V) = goal where 
        have : A LV.◂ vty A ≤ LV.f* V (pull (force var) $ cty B) 
        have = vtm V
        
        goal : A LV.◂ vty A ≤ (pull (force V) $ cty B) 
        goal = LV.seq have (LV.seq V*M*→VM* (LV.eqTo≤ (cong (λ h → f (pull h) (cty B)) (cong₂ subC refl plugId ∙ force-sub ∙ cong force (subVIdr _)))))

    GS : CBPVGlobalSection L 
    GS .fst .Section.F-obᴰ = vty
    GS .fst .Section.F-homᴰ = vtm
    GS .fst .Section.F-idᴰ = LV.isProp≤ _ _
    GS .fst .Section.F-seqᴰ _ _ = LV.isProp≤ _ _
    GS .snd .fst .Section.F-obᴰ = cty
    GS .snd .fst .Section.F-homᴰ = ktm
    GS .snd .fst .Section.F-idᴰ = LC.isProp≤ _ _
    GS .snd .fst .Section.F-seqᴰ _ _ = LC.isProp≤ _ _
    GS .snd .snd = ctm
-}

-}