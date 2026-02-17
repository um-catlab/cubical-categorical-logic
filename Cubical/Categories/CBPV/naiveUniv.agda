{-# OPTIONS --type-in-type #-}
module Cubical.Categories.CBPV.naiveUniv where 


open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Displayed.Base 
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets 
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.NaturalTransformation.Base hiding (_⇒_)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Instances.Functors.Currying
open import Cubical.Categories.Instances.Functors
open Category
open Functor
open NatTrans
open Categoryᴰ 
open Functorᴰ
open import Cubical.Data.List using (_∷_ ; [] ; List ; foldl ; map)

levels : List Level → Level 
levels xs = foldl ℓ-max ℓ-zero (map ℓ-suc xs)
{-
module _ 
    {ℓC ℓC' ℓD ℓD' : Level} where 

  record LawlessFunctor (C : Category ℓC ℓC') (D : Category ℓD ℓD') :
          Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
    no-eta-equality

    open Category

    field
      F-ob  : C .ob → D .ob
      F-hom : {x y : C .ob} → C [ x , y ] → D [ F-ob x , F-ob y ]

open LawlessFunctor
conv : {ℓC ℓC' ℓD ℓD' : Level} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} → Functor C D → LawlessFunctor C D 
conv F .F-ob = F .F-ob
conv F .F-hom = F .F-hom

_∘F'_ : {ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level}{C : Category ℓC ℓC'} {D : Category ℓD ℓD'}{E : Category ℓE ℓE'} → 
  LawlessFunctor D E → LawlessFunctor C D → LawlessFunctor C E
(G ∘F' F) .LawlessFunctor.F-ob = λ z → G .LawlessFunctor.F-ob (F .LawlessFunctor.F-ob z)
(G ∘F' F) .LawlessFunctor.F-hom = λ z → G .LawlessFunctor.F-hom (F .LawlessFunctor.F-hom z)

_^opF' : {ℓC ℓC' ℓD ℓD'  : Level}{C : Category ℓC ℓC'} {D : Category ℓD ℓD'} → 
  LawlessFunctor C D → LawlessFunctor (C ^op) (D ^op)
(F ^opF') .LawlessFunctor.F-ob = F .LawlessFunctor.F-ob
(F ^opF') .LawlessFunctor.F-hom = F .LawlessFunctor.F-hom

module _ {ℓC ℓC' ℓD ℓD' : Level}{C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  -- syntax for sequencing in category D
  infixl 15 _⋆ᴰ_
  private
    _⋆ᴰ'_ : ∀ {x y z} (f : D [ x , y ]) (g : D [ y , z ]) → D [ x , z ]
    f ⋆ᴰ' g = f ⋆⟨ D ⟩ g

  open Category
  open LawlessFunctor

  -- type aliases because it gets tedious typing it out all the time
  N-ob-Type' : (F G : LawlessFunctor C D) → Type _
  N-ob-Type' F G = (x : C .ob) → D [(F .F-ob x) , (G .F-ob x)]

  N-hom-Type' : (F G : LawlessFunctor C D) → N-ob-Type' F G → Type _
  N-hom-Type' F G ϕ = {x y : C .ob} (f : C [ x , y ]) → (F .F-hom f) ⋆ᴰ' (ϕ y) ≡ (ϕ x) ⋆ᴰ' (G .F-hom f)

  record NatTrans' (F G : LawlessFunctor C D) : Type (ℓ-max (ℓ-max ℓC ℓC') ℓD') where
    constructor natTrans
    field
      -- components of the natural transformation
      N-ob : N-ob-Type' F G
      -- naturality condition
      N-hom :  N-hom-Type' F G N-ob


  _⇔_ : (F G : LawlessFunctor C D) → Type (ℓ-max (ℓ-max ℓC ℓC') ℓD') 
  _⇔_ F G = NatTrans' F G × NatTrans' G F

-}
record Universe (ℓ ℓ' : Level) : Type (levels (ℓ ∷ ℓ' ∷ [])) where 
  field 
    U : Type ℓ
    el : U → hSet ℓ'

record Naive (ℓV ℓC ℓC' ℓS : Level) : Type (levels (ℓV  ∷ ℓC ∷ ℓC' ∷ ℓS ∷ [])) where 
  field 
    𝓤 : Universe ℓV ℓS
    𝓒 : Category ℓC ℓC' 
    Ctm : Functor 𝓒 (SET ℓS)

  open Universe 𝓤

  𝓥 : Category ℓV ℓS 
  𝓥 .ob = U  
  𝓥 .Hom[_,_] c c' = (SET ℓS) [ el c , el c' ]
  𝓥 .id x = x
  𝓥 ._⋆_ f g x = g (f x)
  𝓥 .⋆IdL _ = refl
  𝓥 .⋆IdR _ = refl
  𝓥 .⋆Assoc _ _ _ = refl
  𝓥 .isSetHom = (SET ℓS) .isSetHom

  𝓥[_,_] = 𝓥 .Hom[_,_]
  𝓒[_,_] = 𝓒 .Hom[_,_]

  𝓞 : Functor ((𝓥 ^op) ×C 𝓒) (SET ℓS) 
  𝓞 .F-ob (A , B) = (SET ℓS) [ el A , Ctm .F-ob B ] , (SET ℓS ) .isSetHom
  𝓞 .F-hom (f , g) h x = Ctm .F-hom g (h (f x))
  𝓞 .F-id i h x = Ctm .F-id i (h x)
  𝓞 .F-seq f g i h z = Ctm .F-seq (f .snd) (g .snd) i (h (f .fst (g .fst z)))

  𝓞[_,_] : ob 𝓥 → ob 𝓒 → hSet _ 
  𝓞[_,_] A B = 𝓞 .F-ob (A , B)

  𝓞[-,_] : ob 𝓒 → Presheaf 𝓥 ℓS 
  𝓞[-,_] B = (λF _ _ _ (𝓞 ∘F Sym) .F-ob B)


record NaiveHom 
  {ℓVS ℓCS ℓC'S ℓSS ℓVT ℓCT ℓC'T ℓST : Level}
  (M : Naive ℓVS ℓCS ℓC'S ℓSS)
  (N : Naive ℓVT ℓCT ℓC'T ℓST ): Type {!   !} where 
  module M = Naive M 
  module N = Naive N
  ℓm = ℓ-max ℓSS ℓST

  field 
    F𝓥 : Functor M.𝓥 N.𝓥
    F𝓒 : Functor M.𝓒 N.𝓒
    FCtm : NatTrans (LiftF {ℓ' = ℓm} ∘F  M.Ctm) ((LiftF {ℓ' = ℓm} ∘F N.Ctm ) ∘F F𝓒) 

record DispNaive 
  {ℓV ℓVD ℓVD' ℓC ℓC' ℓCD ℓCD' ℓS  : Level} 
  (N : Naive ℓV ℓC ℓC' ℓS ) : Type (levels (ℓV ∷ ℓVD ∷ ℓVD' ∷ ℓC ∷ ℓC' ∷ ℓCD ∷ ℓCD' ∷ ℓS ∷ [])) where 
  open Naive N
  field 
    𝓥ᴰ : Categoryᴰ 𝓥 ℓVD ℓVD' 
    𝓒ᴰ : Categoryᴰ 𝓒 ℓCD ℓCD' 
    Ctmᴰ : Functorᴰ Ctm 𝓒ᴰ (SETᴰ ℓS ℓV) 

_↔_ : {ℓ : Level} → (A B : Type ℓ) → Type ℓ 
_↔_ A B = (A → B) × (B → A)

module Types
    {ℓV ℓV' ℓC ℓC' ℓS : Level} 
    (N : Naive ℓV  ℓC ℓC' ℓS) where 

  open Naive N
  open import Cubical.Categories.Limits.BinProduct.More
  open import Cubical.Categories.Limits.Terminal.More

  open UniversalElement

  hasTerm : Type (ℓ-max ℓV ℓS)
  hasTerm = Terminal' 𝓥
    --Σ[ T ∈ Terminal' 𝓥 ] (Iso ⟨ Vtm .F-ob (T .vertex) ⟩ Unit*)
  
  hasVProd : Type (ℓ-max ℓV ℓS)
  hasVProd = BinProducts 𝓥 
    {-Σ[ B ∈ BinProducts 𝓥 ]
   ((X Y : ob 𝓥) → 
    (Iso ⟨ Vtm .F-ob (B ((X , Y)) .vertex) ⟩ (⟨ Vtm .F-ob X ⟩ × ⟨ Vtm .F-ob Y ⟩)))
    -}

  -- Functor is too strong a demand.. 
  -- So is PshIso
  -- can we demand NatTrans F G × NatTrans G F 
  -- or is the commuting condition too strong


  HasU : Type (ℓ-max (ℓ-max (ℓ-max ℓV ℓC) ℓC') ℓS)
  HasU = Σ[ U ∈ (ob 𝓒 → ob 𝓥) ] 
    ((A : ob 𝓥)(B : ob 𝓒) → (𝓥 [ A , U B ]) ↔ ⟨ 𝓞[ A , B ] ⟩)
    
    -- ((B : ob 𝓒) → NatTrans (𝓥 [-, U B ]) 𝓞[-, B ] × NatTrans 𝓞[-, B ] (𝓥 [-, U B ]))
    -- (conv (𝓥 [-, U B ]) ⇔ conv 𝓞[-, B ]))
    --     --Σ[ U ∈ LawlessFunctor 𝓒 𝓥 ] 


    --Σ[ U ∈ Functor 𝓒 𝓥 ] ((A : ob 𝓥)(B : ob 𝓒) → 
   -- PshIso 𝓥 (𝓥 [-, U .F-ob B ]) 𝓞[-, B ])

  HasF : Type {!   !}
  HasF = Σ[ F ∈ (ob 𝓥  → ob 𝓒 ) ] 
      ((A : ob 𝓥)(B : ob 𝓒) → (𝓒 [ F A , B ]) ↔ ⟨ 𝓞[ A , B ] ⟩)

   {-} ((B : ob 𝓒) → NatTrans (
      record { F-ob = λ A → 𝓒[ F A , B ] , {!   !} ; 
        F-hom = λ f g → {!   !} ; 
        F-id = {!   !} ; 
        F-seq = {!   !} }) 𝓞[-, B ] × {!   !})
        -}
    
    --  (conv (𝓒 [-, B ]) ∘F' (F ^opF')) ⇔ conv 𝓞[-, B ])
    --Σ[ F ∈ Functor 𝓥 𝓒 ] ((A : ob 𝓥)(B : ob 𝓒) → 
    -- PshIso 𝓥 ((𝓒 [-, B ]) ∘F (F ^opF)) 𝓞[-, B ])

{-
  module _ (P : hasVProd) where 
    open import Agda.Builtin.Cubical.Equiv
    open UniversalElement

    -×_ : ob 𝓥 → LawlessFunctor 𝓥 𝓥 
    (-× A) .F-ob A' = P (A , A') .vertex
      --P .fst (A , A') .vertex
    (-× A) .F-hom f = P (A , _) .universal ((-× A) .F-ob _) .equiv-proof
      (P  (A , _) .element .fst ,
       (𝓥 ⋆ P  (A , _) .element .snd) f)
      .fst .fst
 

    hasArr : Type (ℓ-max (ℓ-max (ℓ-max ℓV ℓV') ℓC) (ℓ-suc ℓS)) 
    hasArr = (A : ob 𝓥)(B : ob 𝓒) → Σ[ A⇒B ∈ ob 𝓒 ] 
      (conv 𝓞[-, A⇒B ] ⇔ (conv 𝓞[-, B ] ∘F' (((-× A)) ^opF'))) 
 -}

open import Cubical.Categories.CBPV.Instances.DefinedSubstitution renaming (U to U')

open Naive
open Universe
open DispNaive

def : Naive ℓ-zero ℓ-zero ℓ-zero ℓ-zero 
def .𝓤 .U = VTy
def .𝓤 .el A = · ⊢v A , isSetVal

def .𝓒 .ob = CTy
def .𝓒 .Hom[_,_] = · ◂_⊢k_
def .𝓒 .id = varc
def .𝓒 ._⋆_ = _⋆k_
def .𝓒 .⋆IdL _ = sym ⋆kId
def .𝓒 .⋆IdR _ = refl
def .𝓒 .⋆Assoc _ _ _ = ⋆kAssoc
def .𝓒 .isSetHom = isSetStack

def .Ctm .F-ob B = · ⊢c B , isSetComp
def .Ctm .F-hom {B}{B'} S m = plug' S m
def .Ctm .F-id = refl
def .Ctm .F-seq S S' = funExt λ m → plugsubk

open Types def
_ : hasTerm
_ = record { 
  vertex = one ; 
  element = tt ; 
  universal = λ A → record { equiv-proof = λ tt* → ((λ x → u) , refl) , {!   !} } }

PP : hasVProd 
PP = λ (A , A') → record { 
  vertex = prod A A' ; 
  element = (λ {(pair v w) → v}) , λ {(pair v w) → w} ; 
  universal = {!   !} }

_ : HasU 
_ = U' , (λ A B → (λ z z₁ → force (z z₁)) , λ z z₁ → thunk (z z₁))

_ : HasF 
_ = F , (λ A B → (λ S V → plug' S (ret V)) , {!   !}) -- WTF?
{-
_ : HasU 
_ = U' , λ B → (natTrans {!   !} {!   !}) , {!   !} 
-}


{-}
_ : HasU 
_ = (record { 
    F-ob = U' ; 
    F-hom = λ S V → thunk (plug' S (force V)) }) , 
    -- if we had F-id, we'd need to show thunk (force V) ≡ V
    -- but we don't impose any β η equations on our syntax
    λ B → (natTrans (λ A f V → force (f V)) {!   !}) , 
    natTrans (λ A f V → thunk (f V)) {!   !}
-}

open import Cubical.Categories.WithFamilies.Simple.Instances.Free.Base
-- now binders are the issue
{-
_ : HasF 
_ = (record { 
  F-ob = F ; 
  F-hom = λ f → x←∙:M varc (ret {! var v  z  !}) }) , -- how?
  λ B → (
    natTrans 
      (λ A S V → plug' S (ret V)) 
      {!   !}) , 
    (natTrans 
      (λ A f → x←∙:M varc {!   !})  -- how..?
      {!   !})
-}
{-
duh : hasArr PP 
duh A B = (fun A B) , (
  natTrans 
    (λ A' f V → app (f V) V) 
    {!   !}) , (
  natTrans 
    (λ A' f V → lam {! f V !}) -- how

    {!   !})
-}
-- we dont assume the laws force (thunk M) ≡ M ...
-- needed in the definition of the functor and the PshIso
{-
_ : HasU 
_ = (record { 
  F-ob = U' ; 
  F-hom = λ S V → thunk (plug' S (force V)) ; 
  F-id = funExt λ V → {!   !} ; 
  F-seq = {!   !} }) , 
  λ A B → record { 
    trans = 
      natTrans 
        (λ A' (lift V) → lift λ W → force (V W)) 
        λ f → funExt λ (lift g) → cong lift (funExt λ V → {!   !} ∙ {! F-hom Sym (varc , f)  !}) ;
        -- M = plug' varc M 
    nIso = λ A' → isiso (λ (lift M) → lift λ V → thunk (M V)) (funExt (λ f → cong lift (funExt λ V → {!   !}))) {!   !} }

_ : HasF 
_ = (record { 
  F-ob = F ; 
  F-hom = λ {A}{A'} f → x←∙:M varc (ret {!   !});  --  x←∙:M varc (ret {!   !}) ; 
  F-id = {!   !} ; 
  F-seq = {!   !} }) , 
  λ A B → record { 
    trans = natTrans (λ A (lift S) → lift λ V → ret V) {!   !} ; 
    nIso = λ A' → isiso (λ (lift f) → lift (x←∙:M {!   !}  {!   !})) {!   !} {!   !} }
-}


{-

open import Cubical.Categories.Instances.TransitionSystem
open TSystem

trans : {ℓS : Level} → Naive (ℓ-suc ℓS) (ℓ-suc ℓS) ℓS ℓS 
trans {ℓS} .𝓤 .U = hSet ℓS
trans .𝓤 .el x = x

trans .𝓒 = TSysCat

trans .Ctm .F-ob = state
trans .Ctm .F-hom f = f .TSystem[_,_].s-map
trans .Ctm .F-id = refl
trans .Ctm .F-seq _ _ = refl

open NaiveHom

hrm : NaiveHom def trans 
hrm .F𝓥 .F-ob A = (· ⊢v A) , isSetVal
hrm .F𝓥 .F-hom x = x
hrm .F𝓥 .F-id = refl
hrm .F𝓥 .F-seq _ _ = refl

hrm .F𝓒 .F-ob B .TSystem.term = Term B , {!   !}
hrm .F𝓒 .F-ob B .redex = Red B , {!   !}
hrm .F𝓒 .F-ob B .red = red'
hrm .F𝓒 .F-hom S .TSystem[_,_].s-map s = fromComp (plug' S (toComp s))
hrm .F𝓒 .F-hom S .TSystem[_,_].lax = {!   !}
hrm .F𝓒 .F-id = {!  refl !}
hrm .F𝓒 .F-seq = {!   !}

hrm .FCtm .N-ob B (lift M) = lift (fromComp M)
hrm .FCtm .N-hom S = funExt λ (lift M) → cong lift (cong fromComp {!  !})

open import Cubical.Functions.Logic


Pred : {ℓ : Level} →  Categoryᴰ (SET ℓ) (ℓ-suc ℓ) ℓ 
Pred {ℓ} .ob[_] X = ⟨ X ⟩ → hProp ℓ
Pred .Hom[_][_,_] f P Q = ⟨ ∀[ x ] (P x ⇒ Q (f x)) ⟩
Pred .idᴰ = λ x z → z
Pred ._⋆ᴰ_ {f = f} f^d g^d x p = g^d (f x) (f^d x p)
Pred .⋆IdLᴰ _ = refl
Pred .⋆IdRᴰ _ = refl
Pred .⋆Assocᴰ _ _ _ = refl
Pred .isSetHomᴰ {f = f} {x^d}{y^d} = 
  isProp→isSet ((∀[ x ] (x^d x ⇒ y^d (f x))) .snd)

disptrans : {ℓ : Level} →  DispNaive trans 
disptrans {ℓ} .𝓥ᴰ = Pred {ℓ}
disptrans .𝓒ᴰ = {!   !}
disptrans .Ctmᴰ = {!   !}

-}
