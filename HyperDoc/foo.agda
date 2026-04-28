{-# OPTIONS --type-in-type #-}
--lazy 
module HyperDoc.foo where  

open import Cubical.Data.Nat  hiding ( _^_ )
open import Cubical.Data.Nat.Order 
open import Cubical.Data.FinData
open import Cubical.Data.Sigma 

open import Cubical.Foundations.Prelude 
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Presheaf

open import HyperDoc.Connectives.Connectives
open import HyperDoc.Logics.SetPred

open Category
open Functor

mutual 
  data VTy : Type where 
    𝟙 Ref : VTy 
    U  : CTy → VTy 
    _⊕_ : VTy → VTy → VTy 

  data CTy : Type where 
    F : VTy → CTy 

𝟚 = 𝟙 ⊕ 𝟙
mutual
  data _⊢v_ : VTy → VTy → Type where 
    tt : ∀ {Γ} → Γ ⊢v 𝟙 
    ref : ∀ {Γ} → Γ ⊢v Ref
    thunk : ∀ {Γ B} → Γ ⊢c B → Γ ⊢v U B 
    σ₁ : ∀ {Γ A A'} → Γ ⊢v A → Γ ⊢v (A ⊕ A')
    σ₂ : ∀ {Γ A A'} → Γ ⊢v A' → Γ ⊢v (A ⊕ A')
    isSet⊢v : ∀ {Γ A} → isSet (Γ ⊢v A)
    
  data _⊢c_ : VTy → CTy → Type where 
    new : ∀ {Γ} → Γ ⊢c F Ref
    get : ∀ {Γ} → Γ ⊢v Ref → Γ ⊢c F 𝟚
    set : ∀ {Γ} → Γ ⊢v 𝟚 → Γ ⊢c F 𝟙
    force : ∀ {Γ B} → Γ ⊢v U B → Γ ⊢c B
    match : ∀ {A A' B} → A ⊢c B → A' ⊢c B → (A ⊕ A') ⊢c B 
    ret : ∀ {Γ A} → Γ ⊢v A → Γ ⊢c F A
    bind : ∀ {Γ A B} → Γ ⊢c F A → A ⊢c B → Γ ⊢c B
    isSet⊢c : ∀ {Γ B} → isSet (Γ ⊢c B)

W : Category ℓ-zero ℓ-zero 
W .ob = ℕ
W .Hom[_,_] = _≤_
W .id = ≤-refl
W ._⋆_ = ≤-trans
W .⋆IdL _ = isProp≤ _ _ 
W .⋆IdR _ = isProp≤ _ _ 
W .⋆Assoc _ _ _ = isProp≤ _ _
W .isSetHom = isProp→isSet isProp≤

Clv : VTy → Presheaf W _
Clv 𝟙 = {!   !}
Clv Ref = {!   !}
Clv (U x) = {!   !}
Clv (A ⊕ A₁) = {!   !}
  --  (𝟙 ⊢v A) , isSet⊢v

Clc : CTy → Presheaf W _
Clc B = {!   !}
  -- (𝟙 ⊢c B) , isSet⊢c

open LBI

-- our notion of resource in the logic 
-- is the set of locations which have been allocated
-- Here we pick the representation List ℕ 
open import Cubical.Data.List  
open import Cubical.Data.Nat
open import Cubical.Data.Maybe
open import Cubical.Data.Bool 
open import Cubical.Functions.Logic

locs = List ℕ 

contains : locs → ℕ → Bool 
contains [] n = false
contains (x ∷ xs) n = (x ≡ᵇ n) or contains xs n

-- we say that two sets can be combined only if they are disjoint
disjoint : List ℕ → List ℕ → Bool
disjoint [] ys = true
disjoint (x ∷ xs) ys = (not (contains ys x)) and (disjoint xs ys)

comb : List ℕ → List ℕ → Maybe (List ℕ)
comb xs ys with disjoint xs ys
... | true  = just (xs ++ ys)
... | false = nothing

locPCM : PCM 
locPCM .PCM.M = (List ℕ) , {!   !}
locPCM .PCM._⊚_ = comb
locPCM .PCM.𝟙 = []
locPCM .PCM.lunit _ = refl
locPCM .PCM.runit = {!   !}
locPCM .PCM.comm = {!   !}
locPCM .PCM.assoc = {!   !}

BILogic : Functor (SET _ ^op) (POSET _ _ ) 
BILogic = WithResourceLogic locPCM ∘F Pred

module _ (Γ : hSet _) where 
  open PCM locPCM

  BIPred = BILogic .F-ob Γ .fst .fst 

  has𝐈 : BIPred 
  has𝐈 .fst [] _ = ⊤
  has𝐈 .fst (x ∷ xs) _ = ⊥
  has𝐈 .snd = {!   !}

  -- Day convolution (inProp)
  has＊ : BIPred → BIPred → BIPred 
  has＊ P Q .fst m γ = 
    ∃[ n ∶ locs ] ∃[ p ∶ locs ] (
      (n ⊚ p) ≡ₚ just m) ⊓ 
      P .fst n γ ⊓ 
      Q .fst p γ
  has＊ P Q .snd = {!   !}

  -- for any n disjoint with m
  has-＊ : BIPred → BIPred → BIPred
  has-＊ P Q .fst m γ = 
    ∀[ n ∶ locs ] ∀[ m#n ∶ ⟨ m # n ⟩ ] P .fst m γ ⇒ Q .fst (extract (m ⊚ n) {m#n}) γ
  has-＊ P Q .snd = {!   !}

  biHA : HA (BILogic .F-ob Γ)
  biHA .HA.𝐈 = has𝐈
  biHA .HA._＊_ = has＊
  biHA .HA._-＊_ = has-＊
  biHA .HA.assocl = {!   !}
  biHA .HA.assocr = {!   !}
  biHA .HA.symtry = {!   !}
  biHA .HA.idl = {!   !}
  biHA .HA.idinv = {!   !}
  biHA .HA.＊-intro φ ψ = {!   !}
  biHA .HA.adj = {!   !}
  biHA .HA.adjinv = {!   !}

hasBI : HasBI BILogic 
hasBI .fst = biHA
hasBI .snd = {!   !}

{-}
mutual 
  𝓥[_] : (A : VTy) → BIPred (Clv A) 
  𝓥[ 𝟙 ] .fst m V = V ≡ₚ tt
  𝓥[ 𝟙 ] .snd = {!   !}
  𝓥[ Ref ] .fst m V = {!   !}
  𝓥[ Ref ] .snd = {!   !}
  𝓥[ U B ] .fst m V = 𝓒[ B ] .fst m (force V)
  𝓥[ U B ] .snd = {!   !} 
  𝓥[ A VTy.⊕ A' ] .fst m V = 
    (∃[ W ∶ ⟨ Clv A ⟩ ] V ≡ₚ σ₁ W ⊓ 𝓥[ A ] .fst m W)
    ⊔
    (∃[ W' ∶ ⟨ Clv A' ⟩ ] V ≡ₚ σ₂ W' ⊓ 𝓥[ A' ] .fst m W')
  𝓥[ A VTy.⊕ A' ] .snd = {!   !}

  -- hmm 
  𝓒[_] : (B : CTy) → BIPred (Clc B)
  𝓒[ F A ] .fst m M = {!   !}
  𝓒[ F A ] .snd = {!   !}
-}
{-}
-- : Ref : ℕ → Type
data Ty : Type where
  𝟙 Ref : Ty 
  _⊕_ : Ty → Ty → Ty

𝟚 = 𝟙 ⊕ 𝟙

data _◂_⊢_ : ℕ → Ty → Ty → Type where 
    -- category 
  sub : ∀ {n A A' A''} → n ◂ A ⊢ A' → n ◂ A' ⊢ A'' → n ◂ A ⊢ A''
  var : ∀ {n A} → n ◂ A ⊢ A
  subIdl : ∀ {n A A'} → (V : n ◂ A ⊢ A') → sub (var {n}{A}) V ≡ V
  subIdr : ∀ {n A A'} → (V : n ◂ A ⊢ A') → sub V (var {n}{A'}) ≡ V
  subAssoc : ∀ {n A₁ A₂ A₃ A₄}(V : n ◂ A₁ ⊢  A₂)(W : n ◂ A₂ ⊢ A₃)(Y : n ◂ A₃ ⊢  A₄) → 
    sub (sub V W) Y ≡ sub V (sub W Y)
  isSet⊢ : ∀{n A A'} → isSet (n ◂ A ⊢ A')

  -- type structure 
  tt : ∀{n A} → n ◂ A ⊢ 𝟙
  η𝟙 : ∀{n A} → (V : n ◂ A ⊢ 𝟙) → tt ≡ V

  --π₁ : ∀{B B'} → (B & B') ⊢k B
  --π₂ : ∀{B B'} → (B & B') ⊢k B'
  -- ⟨_,_⟩k : ∀{B B' B''} → B'' ⊢k B → B'' ⊢k B' → B'' ⊢k (B & B')

  σ₁ : ∀ {n A A'} → n ◂  A ⊢ (A ⊕ A')
  σ₂ : ∀ {n A A'} → n ◂  A' ⊢ (A ⊕ A') 
  case : ∀ {n A A' A''} → (n ◂  A ⊢ A'') → (n ◂  A' ⊢ A'') → n ◂ (A ⊕ A') ⊢ A''
  ⊕β₁ : ∀{n A A' A''}{V : n ◂  A ⊢ A''}{W : n ◂  A' ⊢ A''} → sub σ₁ (case V W) ≡ V  
  ⊕β₂ : ∀{n A A' A''}{V : n ◂ A ⊢ A''}{W : n ◂  A' ⊢ A''} → sub σ₂ (case V W) ≡ W 

  ref : ∀ {n Γ} → 
    Fin n → 
    ---------------
    n ◂ Γ ⊢ Ref
  read :  ∀ {n Γ} → 
    (M : n ◂ Γ ⊢ Ref) → 
    -------------------
    n ◂ Γ ⊢ 𝟚

  alloc : ∀ {n Γ} → 
    (M : n ◂ Γ ⊢ 𝟚) → 
    ------------------ 
    suc n ◂ Γ ⊢ Ref

  promote : {A A' : Ty}{n m : ℕ} → 
    n ≤ m → 
    n ◂ A ⊢ A' → 
    ---------------
    m ◂ A ⊢ A' 

  promote-var :
    {A : Ty}{n m : ℕ} → 
    (n≤m : n ≤ m) → 
    var {A = A}≡ promote n≤m var

W : Category ℓ-zero ℓ-zero 
W .ob = ℕ
W .Hom[_,_] = _≤_
W .id = ≤-refl
W ._⋆_ = ≤-trans
W .⋆IdL _ = isProp≤ _ _ 
W .⋆IdR _ = isProp≤ _ _ 
W .⋆Assoc _ _ _ = isProp≤ _ _
W .isSetHom = isProp→isSet isProp≤

open import Cubical.Categories.Presheaf
open import Cubical.Categories.Monoidal.Instances.Presheaf 
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open import HyperDoc.Lib
open EnrichedCategory
open NatTrans

-- open import Cubical.Categories.Monoidal.EnrichedFunctor
open PshMon (W ^op) _

Model : Type 
Model = EnrichedCategory 𝓟Mon _

module _ {ℓV ℓV'  : Level} (V : MonoidalCategory ℓV ℓV') where 
  open MonoidalCategory V
    renaming (ob to obV; Hom[_,_] to V[_,_]; id to idV; _⋆_ to _⋆V_; ⋆Assoc to VAssoc)

  record EnrichedFunctor {ℓE ℓD : Level}(E : EnrichedCategory V ℓE)(D : EnrichedCategory V ℓD) : Type (ℓ-max (ℓ-max (ℓ-max ℓV ℓV') (ℓ-suc ℓE)) (ℓ-suc ℓD)) where 
    private module E = EnrichedCategory E 
    private module D = EnrichedCategory D 
    field 
      F₀ : E.ob → D.ob
      F₁ : {X Y : E.ob} → V[ E.Hom[ X , Y ] , D.Hom[ F₀ X , F₀ Y ] ]
      Fid : {X : E.ob} → (E.id {X} ⋆V F₁ {X} {X}) ≡ D.id {F₀ X}
      Fseq : {X Y Z : E.ob} → (F₁ {X} {Y} ⊗ₕ F₁ {Y} {Z}) ⋆V D.seq (F₀ X) (F₀ Y) (F₀ Z) ≡ E.seq X Y Z ⋆V F₁ {X} {Z} 


ModelMorphism : Model → Model → Type 
ModelMorphism = EnrichedFunctor 𝓟Mon


-- Kleisli Model
SetModel : Model 
SetModel .ob = Presheaf (W ^op) _
SetModel .Hom[_,_] = _^_
SetModel .id = {!   !}
SetModel .seq = {!   !}
SetModel .⋆IdL = {!   !}
SetModel .⋆IdR = {!   !}
SetModel .⋆Assoc = {!   !}

RefF : Presheaf W _  
RefF .F-ob n = (Fin n) , {!   !}
RefF .F-hom {n}{m} n≤m = {!   !}
RefF .F-id = {!   !}
RefF .F-seq = {!   !}

Bool : Presheaf W _
Bool =  {!   !}


synHom : Ty → Ty → Functor W (SET _) 
synHom A A' .F-ob n = n ◂ A ⊢ A' , {!   !}
synHom A A' .F-hom n≤m t = promote n≤m t
synHom A A' .F-id {n} = funExt λ V → {!   !} -- promote ≤-refl V ≡ V
synHom A A' .F-seq V V' = funExt λ V'' → {!   !} -- promote (≤-trans V V') V'' ≡ promote V' (promote V V'')

Syn : Model 
Syn .ob = Ty
Syn .Hom[_,_] A A' = synHom A A' ∘F from^op^op
Syn .id .N-ob n tt* = var
Syn .id .N-hom n≤m = funExt λ tt* → promote-var n≤m
Syn .seq A A' A'' .N-ob n (V , V') = sub V V'
Syn .seq A A' A'' .N-hom _ = funExt λ (V , V') → {!   !}
Syn .⋆IdL A A' = makeNatTransPath (funExt λ n → funExt λ (tt* , V) → {!   !})
Syn .⋆IdR = {!   !}
Syn .⋆Assoc = {!   !}

open import Cubical.Categories.Presheaf.Morphism.Alt
open PshHom
Sem : ModelMorphism Syn SetModel 
Sem .EnrichedFunctor.F₀ Ty.𝟙 = {!   !}
Sem .EnrichedFunctor.F₀ Ref = {!   !}
Sem .EnrichedFunctor.F₀ (A ⊕ A₁) = {!   !}
Sem .EnrichedFunctor.F₁ .N-ob n V .N-ob m n≤m = {!   !}
Sem .EnrichedFunctor.F₁ .N-ob n V .N-hom = {!   !}
Sem .EnrichedFunctor.F₁ .N-hom = {!   !}
Sem .EnrichedFunctor.Fid = {!   !}
Sem .EnrichedFunctor.Fseq = {!   !}

-}