{-# OPTIONS --type-in-type #-}
module HyperDoc.Logics.Free where 
open import Cubical.Data.Unit
open import Cubical.Relation.Binary.Preorder

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Category 
open import Cubical.Categories.Functor
open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.List using (List ; _∷_ ; [])
open import Cubical.Data.Sigma hiding (∃)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Sets

open Category
open Categoryᴰ
open Functor
open Functorᴰ
open NatIso
open NatTrans
open UniversalElement

open Category
open Functor
open PreorderStr
open IsPreorder


module STLC where 
  data VTy : Type where 
    𝟙 : VTy
    _+_ : VTy → VTy → VTy


  data _⊢v_  : (A A' : VTy) → Type where
    -- category 
    subV : ∀ {A A' A''} → A ⊢v A' → A' ⊢v A'' → A ⊢v A''
    var : ∀ {A} → A ⊢v A
    subVIdl : ∀ {A A'} → (V : A ⊢v A') → subV (var {A}) V ≡ V
    subVIdr : ∀ {A A'} → (V : A ⊢v A') → subV V (var {A'}) ≡ V
    subVAssoc : ∀ {A₁ A₂ A₃ A₄}(V : A₁ ⊢v A₂)(W : A₂ ⊢v A₃)(Y : A₃ ⊢v A₄) → 
      subV (subV V W) Y ≡ subV V (subV W Y)
    isSet⊢v : ∀{A A'} → isSet (A ⊢v A')


    tt : ∀{A} → A ⊢v 𝟙
    η𝟙 : ∀{A} → (V : A ⊢v 𝟙) → tt ≡ V

    σ₁ : ∀ {A A'} → A ⊢v (A + A')
    σ₂ : ∀ {A A'} → A' ⊢v (A + A') 
    caseV : ∀ {A A' A''} → (A ⊢v A'') → (A' ⊢v A'') → (A + A') ⊢v A''
    +β₁ : ∀{A A' A''}{V : A ⊢v A''}{W : A' ⊢v A''} → subV σ₁ (caseV V W) ≡ V  
    +β₂ : ∀{A A' A''}{V : A ⊢v A''}{W : A' ⊢v A''} → subV σ₂ (caseV V W) ≡ W 
    +ηV : ∀{A A' A''}{V : (A + A') ⊢v A''} → caseV (subV σ₁ V) (subV σ₂ V) ≡ V 

  V : Category ℓ-zero ℓ-zero
  V .ob = VTy
  V .Hom[_,_] = _⊢v_
  V .id = var
  V ._⋆_ = subV
  V .⋆IdL = subVIdl
  V .⋆IdR = subVIdr
  V .⋆Assoc = subVAssoc
  V .isSetHom = isSet⊢v


  mutual
    data Prop (A : VTy) : Type where 
      ⊤ : Prop A
      _⋁_  : Prop A → Prop A → Prop A
      ∃ : {A' : VTy} → A' ⊢v A → Prop A' → Prop A
      antiSym : ∀ {P Q} → A ◂ P ⊢ Q → A ◂ Q ⊢ P → P ≡ Q 

    data _◂_⊢_  : (A : VTy) → Prop A → Prop A → Type where 
      ref : ∀ {A P} → A ◂ P ⊢ P
      tran : ∀ {A P Q R} → A ◂ P ⊢ Q → A ◂ Q ⊢ R → A ◂ P ⊢ R 
      isProp⊢ : ∀ {A P Q} → isProp (A ◂ P ⊢ Q)

      ⊤-intro : ∀ {A P} → A ◂ P ⊢ ⊤ 

      ⋁-intro1 : ∀{A P Q R } → A ◂ P ⊢ Q → A ◂ P ⊢ (Q ⋁ R) 
      ⋁-intro2 : ∀{A P Q R } → A ◂ P ⊢ R → A ◂ P ⊢ (Q ⋁ R) 
      ⋁-elim : ∀{A P Q R } → A ◂ Q ⊢ P → A ◂ R ⊢ P → A ◂ Q ⋁ R ⊢ P 

      ∃-intro : ∀ {A A' P Q} → 
        (f : A' ⊢v A) → 
        A ◂ P ⊢ {! sub f  !} → 
        --------------------------
        A ◂ P ⊢ ∃ f Q
      ∃-elim : 
        ∀ {A A' P Q}
        (f : A' ⊢v A) → 
        {!   !} ◂ {!   !} ⊢ {!   !} → 
        ---------------------------
        {!   !} ◂ {!   !} ⊢ {!   !}

    sub : {A A' : VTy} → (f : V [ A' , A ]) → Prop A → Prop A' 
    sub f ⊤ = ⊤
    sub f (P ⋁ Q) = sub f P ⋁ sub f Q
    sub {A}{A'} f (antiSym {P}{Q} x x₁ i) = antiSym {A'}{sub f P}{sub f Q} (subMon f x) (subMon f x₁) i

    subMon : {A A' : VTy}{P Q : Prop A} → (f : V [ A' , A ]) → A ◂ P ⊢ Q → A' ◂ sub f P ⊢ sub f Q
    subMon f ref = ref
    subMon f (tran p p₁) = tran (subMon f p) (subMon f p₁)
    subMon f (⊤-intro) = ⊤-intro
    subMon f (⋁-intro1 p)= ⋁-intro1 (subMon f p)
    subMon f (⋁-intro2 p)= ⋁-intro2 (subMon f p)
    subMon f (⋁-elim p q )= ⋁-elim (subMon f p) (subMon f q)
    subMon f (isProp⊢ p p₁ i) = isProp⊢ ((subMon f p)) ((subMon f p₁))   i

  isSetProp :  {A : VTy} →  isSet (Prop A)
  isSetProp = {!   !}

  logic : VTy → ob (POSET _ _ ) 
  logic A .fst .fst = Prop A
  logic A .fst .snd ._≤_ =  A ◂_⊢_ 
  logic A .fst .snd .isPreorder .is-prop-valued P Q = isProp⊢
  logic A .fst .snd .isPreorder .is-refl P = ref
  logic A .fst .snd .isPreorder .is-trans P Q R = tran
  logic A .snd .isUnivalent.univ P Q = isoToEquiv (iso (λ z →
       transp (λ i → OrderEquivalent (logic A .fst) P (z i)) i0
       reflOrderEquiv) (λ {(orderequiv left right) → antiSym left right}) (λ b → isPropOrderEquivalent _ _) λ a →  isSetProp  _ _ _ _) .snd




  subId : {A : VTy}{P : Prop A} → sub var P ≡ P 
  subId {A} {⊤} = refl
  subId {A} {P ⋁ P₁} = cong₂ _⋁_ subId subId
  subId {A} {antiSym x x₁ i} = {!   !}

  subSeq : {A A' A'' : VTy}{P : Prop A } → (f : A'' ⊢v A') → (g : A' ⊢v A) → 
    sub (subV f g) P ≡ sub f (sub g P) 
  subSeq {P = ⊤} f g = refl
  subSeq {P = P ⋁ Q} f g = cong₂ _⋁_ (subSeq {P = P} f g) (subSeq {P = Q} f g)
  subSeq {P = antiSym x x₁ i} f g = {!   !}

  L : Functor (V ^op) (POSET _ _) 
  L .F-ob = logic
  L .F-hom f .MonFun.f = sub f
  L .F-hom f .MonFun.isMon = subMon f
  L .F-id = eqMon _ _ (funExt λ P → subId)
  L .F-seq f g  = eqMon _ _ (funExt λ P → subSeq {P = P} g f)

  open import HyperDoc.Logic.Base
  open Convert L
  open import Cubical.Categories.Constructions.TotalCategory

  Total : Category _ _ 
  Total = ∫C Cᴰ  

  term : Terminal' Total 
  term .vertex = 𝟙 , ⊤
  term .element = tt
  term .universal A = isoToEquiv (iso (λ _ → tt) (λ _  → tt , ⊤-intro) (λ _ → refl) λ (t , p) → ΣPathP ((η𝟙 _) , isProp→PathP (λ i → _)  ⊤-intro p)) .snd

  bp : BinProducts (Total ^op) 
  bp ((A , P) , (A' , Q)) .vertex = (A + A') , {!   !}
  bp ((A , P) , A' , Q) .element .fst .fst = σ₁
  bp ((A , P) , A' , Q) .element .fst .snd = {!   !}
  bp ((A , P) , A' , Q) .element .snd = {!   !}
  bp ((A , P) , (A' , Q))  .universal = {!   !}

{-
  mutual 
    -- ignore atoms for now
    data Prop (Γ : Ctx) : Type where
      ⊤ : Prop Γ
      _⋀_  : Prop Γ → Prop Γ → Prop Γ
      antiSym : ∀ {P Q} → Γ ◂ P ⊢ Q → Γ ◂ Q ⊢ P → P ≡ Q 
      
    isSetProp :  {Γ : Ctx} →  isSet (Prop Γ)
    isSetProp = {!   !}

    data _◂_⊢_ (Γ : Ctx) :  Prop Γ → Prop Γ → Type where 
      ref : ∀ {P} → Γ ◂ P ⊢ P
      tran : ∀ {P Q R} → Γ ◂ P ⊢ Q → Γ ◂ Q ⊢ R → Γ ◂ P ⊢ R 
      isProp⊢ : ∀ {P Q} → isProp (Γ ◂ P ⊢ Q)

  logic : Ctx → ob (POSET _ _ ) 
  logic Γ .fst .fst = Prop Γ
  logic Γ .fst .snd ._≤_ =  Γ ◂_⊢_ 
  logic Γ .fst .snd .isPreorder .is-prop-valued P Q = isProp⊢
  logic Γ .fst .snd .isPreorder .is-refl P = ref
  logic Γ .fst .snd .isPreorder .is-trans P Q R = tran
  logic Γ .snd .isUnivalent.univ P Q = isoToEquiv (iso (λ z →
       transp (λ i → OrderEquivalent (logic Γ .fst) P (z i)) i0
       reflOrderEquiv) (λ {(orderequiv left right) → antiSym left right}) (λ b → isPropOrderEquivalent _ _) λ a →  isSetProp  _ _ _ _) .snd

  -}


{-
module STLC where 

  data VTy : Type where
    one : VTy
    prod : VTy → VTy → VTy


  Ctx = List VTy

  · : Ctx
  · = []

  private
    variable
      Δ Γ Θ ξ Δ' Γ' Θ' ξ' : Ctx
      A A' : VTy

  data Sub[_,_] : (Δ : Ctx) (Γ : Ctx) → Type
  data _⊢v_   : (Γ : Ctx) (S : VTy) → Type

  _[_]vP : Γ ⊢v A → Sub[ Δ , Γ ] → Δ ⊢v A
  varP : (A ∷ Γ) ⊢v A

  private
    variable
      γ : Sub[ Δ , Γ ]
      δ : Sub[ Θ , Δ ]
      ρ : Sub[ ξ , Θ ]
      v : Γ ⊢v A


  data Sub[_,_] where
    -- axiomitize substitution as a category
    ids : Sub[ Γ ,  Γ ]
    _∘s_ : Sub[ Δ , Θ ] → Sub[ Γ , Δ ] → Sub[ Γ , Θ ]
    ∘sIdL : ids ∘s γ ≡ γ
    ∘sIdR : γ ∘s ids ≡ γ
    ∘sAssoc : γ ∘s (δ ∘s ρ ) ≡ (γ ∘s δ) ∘s ρ
    isSetSub : isSet (Sub[ Δ , Γ ])

    -- with a terminal object
    !s : Sub[ Γ , · ]
    ·η : γ ≡ !s

    -- universal property of context extension
    _,s_ : Sub[ Γ , Δ ] → Γ ⊢v A → Sub[ Γ , A ∷ Δ ]
    wk : Sub[ A ∷ Γ , Γ ]
    wkβ :  wk ∘s (γ ,s v) ≡ γ
    ,sη : γ  ≡ ((wk ∘s γ) ,s (varP [ γ ]vP))

  data _⊢v_ where
    -- substitution
    _[_]v : Γ ⊢v A → Sub[ Δ , Γ ] → Δ ⊢v A
    subIdV : v [ ids ]v ≡ v
    subAssocV : v [ γ ∘s δ ]v ≡ (v [ γ ]v) [ δ ]v
    isSetVal : isSet (Γ ⊢v A)

    -- variable
    var : (A ∷ Γ) ⊢v A
    varβ : var [ δ ,s v ]v ≡ v

    u :
      ----------
      Γ ⊢v one

    pair :
      Γ ⊢v A →
      Γ ⊢v A' →
      -----------------
      Γ ⊢v (prod A A')


  _[_]vP = _[_]v
  varP = var

  SCat : Category _ _
  SCat .ob = Ctx
  SCat .Hom[_,_] = Sub[_,_]
  SCat .id = ids
  SCat ._⋆_ f g = g ∘s f
  SCat .⋆IdL _ = ∘sIdR
  SCat .⋆IdR _ = ∘sIdL
  SCat .⋆Assoc _ _ _ = ∘sAssoc
  SCat .isSetHom = isSetSub

  vTm : VTy → Functor (SCat ^op) (SET _)
  vTm A .F-ob Γ = (Γ ⊢v A) , isSetVal
  vTm A .F-hom γ v = v [ γ ]v
  vTm A .F-id = funExt λ _ → subIdV
  vTm A .F-seq _ _ = funExt λ _ → subAssocV


  comprehension : (Γ : Ctx) (A : VTy) →
    SCat [-, (A ∷ Γ) ] ≅ᶜ ((SCat [-, Γ ]) ×Psh vTm A)
  comprehension Γ A .trans = goal where
    goal : NatTrans (SCat [-, A ∷ Γ ]) ((SCat [-, Γ ]) ×Psh vTm A)
    goal .N-ob Δ γ = (wk ∘s γ) , (var [ γ ]v)
    goal .N-hom γ = funExt λ δ → ΣPathP (∘sAssoc , subAssocV)
  comprehension Γ A .nIso Δ .isIso.inv (γ , m) = γ ,s m
  comprehension Γ A .nIso Δ .isIso.sec =
    funExt λ (γ , m) → ΣPathP (wkβ , varβ)
  comprehension Γ A .nIso Δ .isIso.ret = funExt λ γ → sym ,sη


  term : Terminal' SCat
  term .vertex = ·
  term .element = tt
  term .universal Γ =
    record {
      equiv-proof = λ tt → (!s , refl) , λ Δ →
      ΣPathP (sym ·η , λ _ _ → tt)
    }

  scwf : SCwF _ _ _ _
  scwf .fst = SCat
  scwf .snd .fst = VTy
  scwf .snd .snd .fst = vTm
  scwf .snd .snd .snd = term , λ A Γ →
    representationToUniversalElement _ _
    ((A ∷ Γ) ,
    (PshIso→PshIsoLift _ _ (NatIso→PshIso _ _ (comprehension Γ A))))


Term : Category _ _ 
Term .ob = Unit
Term .Hom[_,_] _ _ = Unit
Term .id = tt
Term ._⋆_ = λ f g → tt
Term .⋆IdL _ = refl
Term .⋆IdR _ = refl
Term .⋆Assoc _ _ _ = refl
Term .isSetHom = isSetUnit

-- really want the free distributive lattice with generators
module _ where
  open STLC
  open import Cubical.Categories.WithFamilies.Simple.Displayed

  mutual 
    -- ignore atoms for now
    data Prop (Γ : Ctx) : Type where
      ⊤ : Prop Γ
      _⋀_  : Prop Γ → Prop Γ → Prop Γ
      antiSym : ∀ {P Q} → Γ ◂ P ⊢ Q → Γ ◂ Q ⊢ P → P ≡ Q 
      
    isSetProp :  {Γ : Ctx} →  isSet (Prop Γ)
    isSetProp = {!   !}

    data _◂_⊢_ (Γ : Ctx) :  Prop Γ → Prop Γ → Type where 
      ref : ∀ {P} → Γ ◂ P ⊢ P
      tran : ∀ {P Q R} → Γ ◂ P ⊢ Q → Γ ◂ Q ⊢ R → Γ ◂ P ⊢ R 
      isProp⊢ : ∀ {P Q} → isProp (Γ ◂ P ⊢ Q)

  logic : Ctx → ob (POSET _ _ ) 
  logic Γ .fst .fst = Prop Γ
  logic Γ .fst .snd ._≤_ =  Γ ◂_⊢_ 
  logic Γ .fst .snd .isPreorder .is-prop-valued P Q = isProp⊢
  logic Γ .fst .snd .isPreorder .is-refl P = ref
  logic Γ .fst .snd .isPreorder .is-trans P Q R = tran
  logic Γ .snd .isUnivalent.univ P Q = isoToEquiv (iso (λ z →
       transp (λ i → OrderEquivalent (logic Γ .fst) P (z i)) i0
       reflOrderEquiv) (λ {(orderequiv left right) → antiSym left right}) (λ b → isPropOrderEquivalent _ _) λ a →  isSetProp  _ _ _ _) .snd


  sub : {Δ Γ : Ctx} → (SCat [ Δ , Γ ]) → Prop Γ → Prop Δ 
  sub γ  ⊤ = ⊤
  sub γ  (P ⋀ Q) = sub γ P ⋀ sub γ Q
  sub γ (antiSym x x₁ i) = {!   !}


  subMon : {Δ Γ : Ctx}{P Q : Prop Γ} → (SCat [ Δ , Γ ]) → Γ ◂ P ⊢ Q → {!   !} 
  subMon γ = {!   !}

  L : Functor (SCat ^op) (POSET _ _) 
  L .F-ob Γ = logic Γ
  L .F-hom γ .MonFun.f = sub γ
  L .F-hom γ .MonFun.isMon = {!   !}
  L .F-id = {!   !}
  L .F-seq = {!   !} 



  Fᴰ : {A : VTy} → Prop (A ∷ []) →  Functorᴰ (vTm A) (Cᴰ ^opᴰ) (SETᴰ ℓ-zero ℓ-zero) 
  Fᴰ {A} P .F-obᴰ {Γ} Q v = (Cᴰ [ {!   !} ][ {!   !} , {!   !} ]) , {!   !}
  Fᴰ {A} P .F-homᴰ = {!   !}
  Fᴰ {A} P .F-idᴰ = {!   !}
  Fᴰ {A} P .F-seqᴰ = {!   !}

  L' : SCwFᴰ scwf _ _ _ _ 
  L' .fst = Cᴰ
  L' .snd .fst A = Prop (A ∷ [])
  L' .snd .snd .fst = Fᴰ
  L' .snd .snd .snd .fst = {!   !}
  L' .snd .snd .snd .snd = {!   !}

{-
  need : SCwFⱽ scwf _ _ _ _ 
  need .fst = {!   !}
  need .snd .fst = {!   !}
  need .snd .snd .fst = {!   !}
  need .snd .snd .snd .fst = {!   !}
  need .snd .snd .snd .snd .fst = {!   !}
  need .snd .snd .snd .snd .snd .fst = {!   !}
  need .snd .snd .snd .snd .snd .snd = {!   !}
-}

{-
  L : Functor (Term ^op) (POSET _ _) 
  L .F-ob tt = logic
  L .F-hom tt .MonFun.f = λ z → z
  L .F-hom tt .MonFun.isMon = λ z → z
  L .F-id = eqMon _ _ refl
  L .F-seq _ _ = eqMon _ _ refl
  -}



-}