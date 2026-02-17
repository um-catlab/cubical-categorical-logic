module Cubical.Categories.CBPV.naive where 


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

record Naive (ℓV ℓV' ℓC ℓC' ℓS : Level) : Type (levels (ℓV  ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ [])) where 
  field 
    𝓥 : Category ℓV ℓV'
    𝓒 : Category ℓC ℓC'
    Vtm : Functor 𝓥 (SET ℓS)
    Ctm : Functor 𝓒 (SET ℓS) 

  𝓞 : Functor ((𝓥 ^op) ×C 𝓒) (SET ℓS) 
  𝓞 .F-ob (A , B) = (SET ℓS)[ Vtm .F-ob  A , Ctm .F-ob B ] , (SET ℓS) .isSetHom
  𝓞 .F-hom (f , g ) h x = Ctm .F-hom g (h (Vtm .F-hom f x))
  𝓞 .F-id  = {!   !}
  𝓞 .F-seq = {!   !}

  𝓞[_,_] : ob 𝓥 → ob 𝓒 → hSet _ 
  𝓞[_,_] A B = 𝓞 .F-ob (A , B)

  𝓞[-,_] : ob 𝓒 → Presheaf 𝓥 ℓS 
  𝓞[-,_] B = (λF _ _ _ (𝓞 ∘F Sym) .F-ob B)

  𝓥[_,_] : ob 𝓥 → ob 𝓥 → Type ℓV'
  𝓥[_,_] A A' = 𝓥 .Hom[_,_] A A'



-- type structure
_↔_ : {ℓ ℓ' : Level} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
_↔_ A B = (A → B) × (B → A)
module Types
    {ℓV ℓV' ℓC ℓC' ℓS : Level} 
    (N : Naive ℓV ℓV' ℓC ℓC' ℓS) where 

  open Naive N
  open import Cubical.Categories.Limits.BinProduct.More
  open import Cubical.Categories.Limits.Terminal.More

  open UniversalElement

  hasTerm : Type (ℓ-max (ℓ-max ℓV ℓV') (ℓ-suc ℓS))
  hasTerm = Σ[ T ∈ Terminal' 𝓥 ] (Iso ⟨ Vtm .F-ob (T .vertex) ⟩ Unit*)
  
  hasVProd : Type (ℓ-max (ℓ-max ℓV ℓV') ℓS)
  hasVProd = Σ[ B ∈ BinProducts 𝓥 ]
   ((X Y : ob 𝓥) → 
    (Iso ⟨ Vtm .F-ob (B ((X , Y)) .vertex) ⟩ (⟨ Vtm .F-ob X ⟩ × ⟨ Vtm .F-ob Y ⟩)))

  module _ (P : hasVProd) where 
    open import Agda.Builtin.Cubical.Equiv

    -×_ : ob 𝓥 → Functor 𝓥 𝓥 
    (-× A) .F-ob A' = P .fst (A , A') .vertex
    (-× A) .F-hom f = P .fst (A , _) .universal ((-× A) .F-ob _) .equiv-proof
      (P .fst (A , _) .element .fst ,
       (𝓥 ⋆ P .fst (A , _) .element .snd) f)
      .fst .fst
    (-× A) .F-id = {!   !}
    (-× A) .F-seq = {!   !}

    hasArr : Type (ℓ-max (ℓ-max (ℓ-max ℓV ℓV') ℓC) (ℓ-suc ℓS)) 
    hasArr = (A : ob 𝓥)(B : ob 𝓒) → 
      Σ[ A⇒B ∈ ob 𝓒 ] (PshIso 𝓥 𝓞[-, A⇒B ] (𝓞[-, B ] ∘F ((-× A)^opF)))

  -- should be Psh Isos?
  {-
    No
    - no isomorphism because we don't have β η 
    - U and F are not even functorial 
    (U would have to prove and η law for F-id thunk(force x) ≡ x)
  -}

  HasU : Type (ℓ-max (ℓ-max (ℓ-max ℓV ℓV') ℓC) ℓS)
  HasU = Σ[ U ∈ (ob 𝓒 →  ob 𝓥) ] ((A : ob 𝓥)(B : ob 𝓒) → 
    (𝓥 [ A , U B ]) ↔ ⟨ 𝓞[ A , B ] ⟩ )
   -- Iso (𝓥 .Hom[_,_] A (U .F-ob  B)) ⟨ 𝓞 .F-ob ((A , B)) ⟩)

  HasF : Type (ℓ-max (ℓ-max (ℓ-max ℓV ℓC) ℓC') ℓS)
  HasF = Σ[ F ∈ (ob 𝓥 → ob 𝓒) ] ((A : ob 𝓥)(B : ob 𝓒) → 
    (𝓒 [ F A , B ]) ↔ ⟨ 𝓞[ A , B ] ⟩ )
    -- Σ[ F ∈ Functor 𝓥 𝓒 ] ((A : ob 𝓥)(B : ob 𝓒) → {!   !})
    
    -- Iso (𝓒 .Hom[_,_] (F .F-ob A) B) ⟨ 𝓞 . F-ob (A , B) ⟩)



  





record DispNaive 
  {ℓV ℓV' ℓVD ℓVD' ℓC ℓC' ℓCD ℓCD' ℓS ℓSD : Level} 
  (N : Naive ℓV ℓV' ℓC ℓC' ℓS) : 
  Type (levels (ℓV ∷ ℓV' ∷ ℓVD ∷ ℓVD' ∷ ℓC ∷ ℓC' ∷ ℓCD ∷ ℓCD' ∷ ℓS ∷ ℓSD ∷  [])) where 
  open Naive N
  field 
    𝓥ᴰ : Categoryᴰ 𝓥 ℓVD ℓVD' 
    𝓒ᴰ : Categoryᴰ 𝓒 ℓCD ℓCD' 
    Vtmᴰ : Functorᴰ Vtm 𝓥ᴰ (SETᴰ ℓS ℓSD)
    Ctmᴰ : Functorᴰ Ctm 𝓒ᴰ (SETᴰ ℓS ℓSD)

  𝓞̂̂ᴰ : Functorᴰ 𝓞 ((𝓥ᴰ ^opᴰ) ×Cᴰ 𝓒ᴰ) (SETᴰ ℓS (ℓ-max ℓS ℓSD) )
  𝓞̂̂ᴰ .F-obᴰ {(A , B)}(aᵈ , bᵈ) o = 
    (SETᴰ ℓS ℓSD)[ o ][ Vtmᴰ .F-obᴰ aᵈ , Ctmᴰ .F-obᴰ bᵈ ] , {!   !}
  𝓞̂̂ᴰ .F-homᴰ {(A , B)}{(A' , B')}{(f , g)} (fᵈ , gᵈ) h hᵈ x xᵈ = 
    Ctmᴰ .F-homᴰ gᵈ (h (Vtm .F-hom f x)) (hᵈ (Vtm .F-hom f x) (Vtmᴰ .F-homᴰ fᵈ x xᵈ))
  𝓞̂̂ᴰ .F-idᴰ = {!   !}
  𝓞̂̂ᴰ .F-seqᴰ = {!   !}

  𝓞ᴰ[_][_,_] : {A : ob 𝓥}{B : ob 𝓒} → ⟨ 𝓞[ A , B ] ⟩ → 𝓥ᴰ .ob[_] A → 𝓒ᴰ .ob[_] B → hSet _ 
  𝓞ᴰ[_][_,_] f aᵈ bᵈ = 𝓞̂̂ᴰ .F-obᴰ (aᵈ , bᵈ) f

module Total   
  {ℓV ℓV' ℓVD ℓVD' ℓC ℓC' ℓCD ℓCD' ℓS ℓSD : Level} 
  {N : Naive ℓV ℓV' ℓC ℓC' ℓS}
  (DN : DispNaive {ℓV} {ℓV'} {ℓVD} {ℓVD'} {ℓC} {ℓC'} {ℓCD} {ℓCD'} {ℓS} {ℓSD} N)
  where 
  open DispNaive DN
  open Naive

  ∫N : Naive (ℓ-max ℓV ℓVD) (ℓ-max ℓV' ℓVD') (ℓ-max ℓC ℓCD) (ℓ-max ℓC' ℓCD') (ℓ-max ℓS ℓSD) 
  ∫N .𝓥 = ∫C 𝓥ᴰ
  ∫N .𝓒 = ∫C 𝓒ᴰ
  ∫N .Vtm = ΣF ∘F ∫F Vtmᴰ
  ∫N .Ctm = ΣF ∘F ∫F Ctmᴰ


module het
  {ℓV ℓV' ℓVD ℓVD' ℓC ℓC' ℓCD ℓCD' ℓS ℓSD : Level} 
  {N : Naive ℓV ℓV' ℓC ℓC' ℓS}
  (DN : DispNaive {ℓV} {ℓV'} {ℓVD} {ℓVD'} {ℓC} {ℓC'} {ℓCD} {ℓCD'} {ℓS} {ℓSD} N)
  where 

  -- has products?

  -- has a quantifier? 


  open Naive N 
  open DispNaive DN

  record isHetCart
    {A : ob 𝓥}{B : ob 𝓒}
    {aᵈ : 𝓥ᴰ .ob[_] A}
    {bᵈ : 𝓒ᴰ .ob[_] B}
    {f : ⟨ 𝓞[ A , B ] ⟩}
    (fᵈ : ⟨ 𝓞ᴰ[ f ][ aᵈ , bᵈ ] ⟩ )
    : Type {!   !} where 
    field 
      -- existence of a mitigating map
      clift : 
        {C : ob 𝓥}
        {cᵈ : 𝓥ᴰ .ob[_] C}
        {g : 𝓥 [ C , A ]}
        (hᵈ : ⟨ 𝓞ᴰ[ (λ x → f (Vtm .F-hom g x)) ][ cᵈ , bᵈ ] ⟩ )
         → 𝓥ᴰ .Hom[_][_,_] g cᵈ aᵈ
      -- this map commutes upstairs
      {- 
      comm : 
        {C : ob 𝓥}
        {cᵈ : 𝓥ᴰ .ob[_] C}
        {g : 𝓥 [ C , A ]}
        (hᵈ : ⟨ 𝓞ᴰ[ (λ x → f (Vtm .F-hom g x)) ][ cᵈ , bᵈ ] ⟩ )
        → _≡[_]_ {! 𝓥ᴰ  !}  {!   !} refl hᵈ
      -}


  record HetLift {A : ob 𝓥}{B : ob 𝓒}
    (f : ⟨ 𝓞[ A , B ] ⟩)
    (bᵈ : 𝓒ᴰ .ob[_] B ) : Type {!   !} where
    field 
      {aᵈ} : 𝓥ᴰ .ob[_] A
      fᵈ : ⟨ 𝓞ᴰ[ f ][ aᵈ , bᵈ ] ⟩ 
      ishet : isHetCart fᵈ


  record isHetCartOp
    {A : ob 𝓥}{B : ob 𝓒}
    {aᵈ : 𝓥ᴰ .ob[_] A}
    {bᵈ : 𝓒ᴰ .ob[_] B}
    {f : ⟨ 𝓞[ A , B ] ⟩}
    (fᵈ : ⟨ 𝓞ᴰ[ f ][ aᵈ , bᵈ ] ⟩ )
    : Type {!   !} where 
    field 
      -- existence of a mitigating map
      clift : 
        {C : ob 𝓒}
        {cᵈ : 𝓒ᴰ .ob[_] C}
        {g : 𝓒 [ B , C ]}
        (hᵈ : ⟨ 𝓞ᴰ[ (λ z → Ctm .F-hom g (f z)) ][ aᵈ , cᵈ ] ⟩ )
          → 𝓒ᴰ .Hom[_][_,_] g bᵈ cᵈ
       --  → 𝓥ᴰ .Hom[_][_,_] g cᵈ aᵈ

  record HetLiftOp {A : ob 𝓥}{B : ob 𝓒}
    (f : ⟨ 𝓞[ A , B ] ⟩)
    (aᵈ : 𝓥ᴰ .ob[_] A ) : Type {!   !} where
    field 
      {bᵈ} : 𝓒ᴰ .ob[_] B 
      fᵈ : ⟨ 𝓞ᴰ[ f ][ aᵈ , bᵈ ] ⟩ 
      ishet : isHetCart fᵈ


  HasLifts : Type _ 
  HasLifts = {A : ob 𝓥}{B : ob 𝓒}(f : ⟨ 𝓞[ A , B ] ⟩)(bᵈ : 𝓒ᴰ .ob[_] B )  → HetLift f bᵈ

  HasLiftsOp : Type _ 
  HasLiftsOp = {A : ob 𝓥}{B : ob 𝓒}(f : ⟨ 𝓞[ A , B ] ⟩)(aᵈ : 𝓥ᴰ .ob[_] A )  → HetLiftOp f aᵈ

record NaiveHom 
  {ℓVS ℓV'S ℓCS ℓC'S ℓSS ℓVT ℓV'T ℓCT ℓC'T ℓST  : Level} 
  (M : Naive ℓVS ℓV'S ℓCS ℓC'S ℓSS )
  (N : Naive ℓVT ℓV'T ℓCT ℓC'T ℓST ): Type {!   !} where
  module M = Naive M 
  module N = Naive N
  
  ℓm = ℓ-max ℓSS ℓST
  field 
    F𝓥 : Functor M.𝓥 N.𝓥
    F𝓒 : Functor M.𝓒 N.𝓒
    FVtm : NatTrans (LiftF {ℓ' = ℓm} ∘F  M.Vtm) ((LiftF {ℓ' = ℓm} ∘F N.Vtm ) ∘F F𝓥) 
    FCtm : NatTrans (LiftF {ℓ' = ℓm} ∘F  M.Ctm) ((LiftF {ℓ' = ℓm} ∘F N.Ctm ) ∘F F𝓒) 



module ex where  
  open import Cubical.Categories.CBPV.Instances.DefinedSubstitution renaming (U to U')
  open import Cubical.Categories.WithFamilies.Simple.Instances.Free.Base
  open import Cubical.Data.List.Dependent
  open Naive
  open NaiveHom
  open DispNaive

  def : Naive ℓ-zero ℓ-zero ℓ-zero ℓ-zero ℓ-zero  
  def .𝓥 .ob = VTy
  def .𝓥 .Hom[_,_] A A' = ( A ,, · ) ⊢v A'
  def .𝓥 .id = var vz
  def .𝓥 ._⋆_ f g = subv (f ∷ []) g
  def .𝓥 .⋆IdL = {!   !}
  def .𝓥 .⋆IdR = {!   !}
  def .𝓥 .⋆Assoc = {!   !}
  def .𝓥 .isSetHom = {!   !}

  def .𝓒 .ob = CTy
  def .𝓒 .Hom[_,_] = · ◂_⊢k_
  def .𝓒 .id = varc
  def .𝓒 ._⋆_ = _⋆k_
  def .𝓒 .⋆IdL _ = sym ⋆kId
  def .𝓒 .⋆IdR _ = refl
  def .𝓒 .⋆Assoc _ _ _ = ⋆kAssoc
  def .𝓒 .isSetHom = isSetStack

  def .Vtm .F-ob A = · ⊢v A  , isSetVal
  def .Vtm .F-hom f v = subv (v ∷ []) f
  def .Vtm .F-id = refl
  def .Vtm .F-seq = {!   !}

  def .Ctm .F-ob B = · ⊢c B , isSetComp
  def .Ctm .F-hom {B}{B'} S m = plug' S m
  def .Ctm .F-id = refl
  def .Ctm .F-seq S S' = funExt λ m → plugsubk

  module yep where 
    open Types def

    _ : hasTerm 
    _ = (record { vertex = one ; element = tt ; universal = {!   !} }) 
      , (iso (λ _ → tt*) (λ _ → u) (λ _ → refl) λ { u → refl})

    _ : hasVProd 
    _ = (λ {(A , A') → 
      record { 
        vertex = prod A A' ; 
        -- A × A' ⊢ A 
        -- A × A' ⊢ A'
        -- nope.. can't construct..
        element = {!   !} , {!   !} ; 
        universal = {!   !} }}) ,
         λ A A' → 
          iso 
            (λ { (pair v w) → v , w}) 
            (λ (v , w) → pair v w) 
            (λ _ → refl) 
            λ { (pair v w) → refl }

    _ : HasU 
    _ = U' , (λ A B → 
      (λ V W → force (subv (W ∷ []) V)) , 
      ?)
{-
    {- 
    _ : HasU 
    _ = (record { 
      F-ob = U' ; 
      F-hom = λ S → thunk (plug' (subk (wksub idSub) S) (force (var vz))) ;
      F-id = {!   !} ; -- still not a functor
      F-seq = {!   !} }) , {!   !}
-}

  open import Cubical.Categories.Instances.TransitionSystem
  open TSystem
  tran : Naive (ℓ-suc ℓ-zero) ℓ-zero (ℓ-suc ℓ-zero) ℓ-zero ℓ-zero  
  tran .𝓥 = SET ℓ-zero

  tran .𝓒 = TSysCat

  tran .Vtm = Id

  tran .Ctm .F-ob = state
  tran .Ctm .F-hom f = f .TSystem[_,_].s-map
  tran .Ctm .F-id = refl
  tran .Ctm .F-seq _ _ = refl

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


  AntiPred* : {ℓ : Level } → ob TSysCat → Type {!   !}
  AntiPred* {ℓ} S =     
    Σ[ P ∈ (⟨ state S ⟩ → hProp ℓ)] 
    ((s t : ⟨ state S ⟩) → ⟨ ( _↦*_ S s t ⊓ P t) ⇒ P s ⟩)

  Preserves : {S : ob TSysCat}(P : ⟨ state S ⟩ → hProp {!   !})(s t : ⟨ state S ⟩) → 
    Type {!   !}
  Preserves {S} P s t = ⟨ _↦*_ S s t ⟩ × ⟨ P t ⟩ → ⟨ P s ⟩
    -- ((s t : ⟨ state S ⟩) → ⟨ ( _↦*_ S s t ⊓ P t) ⇒ P s ⟩)

  open TSystem[_,_]

  AntiPred : Categoryᴰ TSysCat {!   !} {!   !} 
  ob[ AntiPred ] S = 
    Σ[ P ∈ (⟨ state S ⟩ → hProp {!   !})] 
    ((s t : ⟨ state S ⟩ ) → Preserves P s t)
  AntiPred .Hom[_][_,_] {S}{T} f P* Q* = Pred .Hom[_][_,_] (f .s-map) (P* .fst)  (Q* .fst) 
  AntiPred .idᴰ = λ x₁ z → z
  AntiPred ._⋆ᴰ_ = λ z₁ z₂ x₁ z₃ → z₂ (_ .s-map x₁) (z₁ x₁ z₃)
  AntiPred .⋆IdLᴰ _ = {! refl !}
  AntiPred .⋆IdRᴰ = {!   !}
  AntiPred .⋆Assocᴰ = {!   !}
  AntiPred .isSetHomᴰ = {!   !}

  tranPred : DispNaive tran
  tranPred .𝓥ᴰ = Pred
  tranPred .𝓒ᴰ = AntiPred

  tranPred .Vtmᴰ .F-obᴰ {X} PX x = (PX x .fst) , {!   !} -- (isProp→isSet (PX x .snd))
  tranPred .Vtmᴰ .F-homᴰ = λ z → z
  tranPred .Vtmᴰ .F-idᴰ = refl
  tranPred .Vtmᴰ .F-seqᴰ _ _ = refl

  tranPred .Ctmᴰ .F-obᴰ {S} P* s = P*  .fst s .fst , {!   !} -- isProp→isSet (P* .fst s .snd)
  tranPred .Ctmᴰ .F-homᴰ  f^d = f^d
  tranPred .Ctmᴰ .F-idᴰ = refl
  tranPred .Ctmᴰ .F-seqᴰ _ _ = refl 



  open het tranPred
  proof : HasLifts 
  proof f bᵈ = 
    record { 
      aᵈ = λ a → bᵈ .fst (f a) ;
      fᵈ = λ x z → z ; 
      ishet = record { 
        clift = λ hᵈ x x₁ → hᵈ x x₁ } }

  open import Cubical.HITs.PropositionalTruncation renaming (rec to recTrunc)
  other : HasLiftsOp 
  other {A}{B}  f aᵈ = 
    record { 
      bᵈ = 
        (λ b → ∃[ a ∶ ⟨ A ⟩ ] (aᵈ a ⊓ _↦*_ B b (f a))) , 
        λ s t → λ( prf , prf' ) → ∣ ({!   !} , {!   !}) ∣₁ ;
      fᵈ = λ a Pa → ∣ (a , (Pa , (0 , refl))) ∣₁ ; 
      ishet = 
        record { 
          clift = λ hᵈ x x₁ → {!   !} } }

  open import Cubical.Relation.Nullary

  open import Cubical.Data.Sum
  hom : NaiveHom def tran 
  hom .F𝓥 .F-ob A = (· ⊢v A) , isSetVal
  hom .F𝓥 .F-hom f v = subv (v ∷ []) f
  hom .F𝓥 .F-id = {!   !}
  hom .F𝓥 .F-seq = {!   !}

  hom .F𝓒 .F-ob B = record { 
    term = Term B , {!   !} ; 
    redex = (Red B) , {!   !} ; 
    red = red'}
  hom .F𝓒 .F-hom S .TSystem[_,_].s-map s = fromComp (plug' S (toComp s))
  hom .F𝓒 .F-hom S .TSystem[_,_].lax (inl x) = tt*
  hom .F𝓒 .F-hom S .TSystem[_,_].lax (inr x) with isTerm (plug' S (x .fst))
  ... | yes p = {!   !}
  ... | no ¬p = {!   !}

  hom .F𝓒 .F-id = {!   !}
  hom .F𝓒 .F-seq = {!   !}

  hom .FVtm .N-ob A x = x
  hom .FVtm .N-hom _ = refl
  
  hom .FCtm .N-ob B (lift m) = lift (fromComp m)
  hom .FCtm .N-hom S = funExt λ (lift m) → 
    cong lift (cong fromComp {!   !} )


  open Total
    -- Total 

  vRel : {A : VTy} → · ⊢v A → hProp ℓ-zero 
  vRel = {!   !}

  cRel : {B : CTy} → · ⊢c B → hProp ℓ-zero 
  cRel = {!   !}

  FLV : {A : VTy} → (V : · ⊢v A) → ⟨ vRel V ⟩ 
  FLV = {!   !}

  FLC : {B : CTy} → (M : · ⊢c B) → ⟨ cRel M ⟩ 
  FLC = {!   !}

  cRelClosedAnti : {B : CTy} → 
    (s t : ⟨ state (hom .F𝓒 .F-ob B) ⟩) →
    Preserves (λ s₁ → cRel (toComp s₁)) s t
  cRelClosedAnti = {!   !}
    
  tot : NaiveHom def (∫N tranPred)
  tot .F𝓥 .F-ob A = (hom .F𝓥 .F-ob A) , vRel
  tot .F𝓥 .F-hom V = (hom .F𝓥 .F-hom V) , {!   !}
  -- ⟨ ∀[]-syntax (λ x₁ → vRel x₁ ⇒ vRel (subv (x₁ ∷ []) V)) ⟩
  tot .F𝓥 .F-id = {!   !}
  tot .F𝓥 .F-seq = {!   !}
  
  tot .F𝓒 .F-ob B = (hom .F𝓒 .F-ob B) , (λ s → cRel (toComp s)) , cRelClosedAnti
  tot .F𝓒 .F-hom S = (hom .F𝓒 .F-hom S) , {!   !}
  {-
  ∀ x₁ →
   cRel (toComp x₁) ⇒ cRel (plug' S (toComp x₁))
  -}
  tot .F𝓒 .F-id = {!   !}
  tot .F𝓒 .F-seq = {!   !}
  
  tot .FVtm .N-ob A (lift V) = 
    lift ((hom .FVtm .N-ob A (lift V) .lower) , FLV V)
  tot .FVtm .N-hom V = funExt λ (lift W) → cong lift (ΣPathP (refl , {!   !}))

  tot .FCtm .N-ob B (lift M) = 
    lift ((hom .FCtm .N-ob B (lift M) .lower) , FLC)
  tot .FCtm .N-hom S = funExt λ (lift M) → cong lift (ΣPathP ({! refl  !} , {!   !}))
-}





{-
uhg : List Level → Level 
uhg xs = foldl ℓ-max ℓ-zero (map ℓ-suc xs)
 
record Univ (ℓ ℓ' : Level) : Type (uhg (ℓ ∷ ℓ' ∷ [])) where 
  field 
    U : hSet ℓ 
    el : ⟨ U ⟩ → hSet ℓ'

open Univ
 
record Naive (ℓV  ℓC ℓC' ℓS : Level) : Type (uhg (ℓV  ∷ ℓC ∷ ℓC' ∷ ℓS ∷ [])) where 
  field 
    univ : Univ ℓV ℓS
    𝓒 : Category ℓC ℓC'
    Ctm : Functor 𝓒 (SET ℓS) 

  𝓥 : Category ℓV ℓS
  𝓥 .ob = ⟨ univ .U ⟩ 
  𝓥 .Hom[_,_] A A' = ⟨ univ .el A ⟩ → ⟨ univ .el A' ⟩ 
  𝓥 .id x = x
  𝓥 ._⋆_ = λ f g x → g (f x)
  𝓥 .⋆IdL f = refl
  𝓥 .⋆IdR f = refl
  𝓥 .⋆Assoc f g h = refl
  𝓥 .isSetHom {x}{y} = isSet→ (univ .el y .snd)

  𝓞 : Functor ((𝓥 ^op) ×C 𝓒) (SET ℓS) 
  𝓞 .F-ob (A , B) = (univ .el A .fst → Ctm .F-ob B .fst) , isSet→ (Ctm .F-ob B .snd)
  𝓞 .F-hom (f , g) h x = Ctm .F-hom g (h (f x))
  𝓞 .F-id i f x = Ctm .F-id i (f x)
  𝓞 .F-seq f g i h x = Ctm .F-seq (f .snd) (g .snd) i (h (f .fst (g .fst x)))

  𝓞[_,_] : ob 𝓥 → ob 𝓒 → hSet _
  𝓞[_,_] A B = 𝓞 .F-ob (A , B) 


module ex where 
  open Naive
  open Univ

  open import Cubical.Categories.CBPV.Instances.DefinedSubstitution hiding (U)

  N : Naive _ _ _ _ 
  N .univ .U = VTy , isSetVTy
  N .univ .el A = · ⊢v A , isSetVal

  N .𝓒 .ob = CTy
  N .𝓒 .Hom[_,_] = · ◂_⊢k_
  N .𝓒 .id = varc
  N .𝓒 ._⋆_ = _⋆k_
  N .𝓒 .⋆IdL _ = sym ⋆kId
  N .𝓒 .⋆IdR _ = refl
  N .𝓒 .⋆Assoc _ _ _ = ⋆kAssoc
  N .𝓒 .isSetHom = isSetStack

  N .Ctm .F-ob B = · ⊢c B , isSetComp
  N .Ctm .F-hom {B}{B'} S m = plug' S m
  N .Ctm .F-id = refl
  N .Ctm .F-seq S S' = funExt λ m → plugsubk

module displayed 
  {ℓV  ℓVD ℓVD' ℓC ℓC' ℓCD ℓCD' ℓS : Level}
  (N : Naive ℓV  ℓC ℓC' ℓS ) where

  open Naive N

  record DispU (ℓD : Level ): Type ℓ-zero where 
    field 
      Uᴰ : ⟨ univ .U ⟩ → hSet ℓD
      elᴰ : {u : ⟨ univ .U ⟩} → ⟨ univ .el u ⟩ → hSet ℓD

  record Disp : Type (uhg (ℓV ∷ ℓVD ∷ ℓVD' ∷ ℓC ∷ ℓC' ∷ ℓCD ∷ ℓCD' ∷ ℓS ∷ [])) where 
    field 
      univᴰ : DispU ℓVD 
      𝓒ᴰ : Categoryᴰ 𝓒 ℓCD ℓCD' 
      Ctmᴰ : Functorᴰ Ctm 𝓒ᴰ (SETᴰ ℓS ℓV) 

    open DispU univᴰ

    𝓥ᴰ : Categoryᴰ 𝓥 ℓVD  (ℓ-max ℓVD' ℓS)
    ob[ 𝓥ᴰ ] v = ⟨ Uᴰ v ⟩
      --Unit* -- ⟨ Uᴰ v ⟩
    𝓥ᴰ .Hom[_][_,_] f _ _ = (SETᴰ ℓS ℓVD')[ f ][ elᴰ , elᴰ ]
    --tt* tt* = (SETᴰ ℓS ℓVD')[ f ][ elᴰ , elᴰ ]
    𝓥ᴰ .idᴰ _ xᵈ = xᵈ
    𝓥ᴰ ._⋆ᴰ_ = λ z₁ z₂ x₁ z₃ → z₂ (_ x₁) (z₁ x₁ z₃)
    𝓥ᴰ .⋆IdLᴰ _ = refl
    𝓥ᴰ .⋆IdRᴰ _ = refl
    𝓥ᴰ .⋆Assocᴰ _ _ _ = refl
    𝓥ᴰ .isSetHomᴰ = isSetHomᴰ (SETᴰ ℓS ℓVD')


    𝓞ᴰ : Functorᴰ 𝓞 ((𝓥ᴰ ^opᴰ) ×Cᴰ 𝓒ᴰ) (SETᴰ {!   !} {!   !})
    𝓞ᴰ .F-obᴰ {(v , c)}(vᵈ , cᵈ) o =  ((SETᴰ {!   !} {!   !} )[ o ][ elᴰ , Ctmᴰ .F-obᴰ cᵈ ]) , {!   !}
    𝓞ᴰ .F-homᴰ {(v , c)}{(v' , c')}{(f , g)}(fᵈ , gᵈ) h hᵈ w wᵈ = Ctmᴰ .F-homᴰ gᵈ (h (f w)) (hᵈ (f w) (fᵈ w wᵈ))
    𝓞ᴰ .F-idᴰ = {!  refl !}
    𝓞ᴰ .F-seqᴰ = {!   !}

    𝓞ᴰ[_][_,_] : { x : ob 𝓥}{y : ob 𝓒} → ⟨ 𝓞[ x , y ] ⟩ → 𝓥ᴰ .ob[_] x → 𝓒ᴰ .ob[_] y  → hSet _
    𝓞ᴰ[_][_,_] f xᵈ yᵈ = 𝓞ᴰ .F-obᴰ (xᵈ , yᵈ) f
  


module dispex where 
  open ex
  open displayed N
  open Disp
  open DispU

  open import Cubical.Categories.CBPV.Instances.DefinedSubstitution hiding (U)

  LRV : {A : VTy} → · ⊢v A → hProp _ 
  LRV = {!   !}

  DN : Disp 
  DN .univᴰ .elᴰ {A} V = {!   !}
    --LRV V .fst , isProp→isSet (LRV V .snd)
  
  ob[ DN .𝓒ᴰ ] B = · ⊢c B → hProp _
  DN .𝓒ᴰ .Hom[_][_,_] = {!   !}
  DN .𝓒ᴰ .idᴰ = {!   !}
  DN .𝓒ᴰ ._⋆ᴰ_ = {!   !}
  DN .𝓒ᴰ .⋆IdLᴰ = {!   !}
  DN .𝓒ᴰ .⋆IdRᴰ = {!   !}
  DN .𝓒ᴰ .⋆Assocᴰ = {!   !}
  DN .𝓒ᴰ .isSetHomᴰ = {!   !}

  DN .Ctmᴰ = {!   !}


module types 
  {ℓV  ℓC ℓC' ℓS : Level}
  (N : Naive ℓV  ℓC ℓC' ℓS ) where 

  open Naive N
  open displayed N

  HasU : Type (ℓ-max (ℓ-max (ℓ-max ℓV ℓC) ℓC') ℓS) 
  HasU = Σ[ U ∈ Functor 𝓒 𝓥 ] ((A : ob 𝓥)(B : ob 𝓒) → 
    Iso (𝓥 .Hom[_,_] A (U .F-ob  B)) ⟨ 𝓞 .F-ob ((A , B)) ⟩)

  HasF : Type (ℓ-max (ℓ-max (ℓ-max ℓV ℓC) ℓC') ℓS) 
  HasF = Σ[ F ∈ Functor 𝓥 𝓒 ] ((A : ob 𝓥)(B : ob 𝓒) → 
    Iso (𝓒 .Hom[_,_] (F .F-ob A) B) ⟨ 𝓞 . F-ob (A , B) ⟩)

  HasTerm : Type (ℓ-max ℓV ℓS) 
  HasTerm = Σ[ one ∈ ⟨ univ .U ⟩ ] Iso ⟨ univ .el one ⟩ Unit
-}

{-
  module lr 
    (hasU : HasU)
    (hasF : HasF)
    (D : Disp)
    where
    open Disp D
    -- heterogenous lifts 

    record HetCartesian 
      {A : ob 𝓥}{B : ob 𝓒}
      {aᵈ : 𝓥ᴰ .ob[_] A}{bᵈ : 𝓒ᴰ .ob[_] B}
      {f : ⟨ 𝓞[ A , B ] ⟩ }
      (f̂ : ⟨ 𝓞ᴰ[ f ][ aᵈ , bᵈ ] ⟩) : Type _ where 

    record HetLift -- in general
      {A : ob 𝓥}{B : ob 𝓒}
      (f : ⟨ 𝓞[ A , B ] ⟩ )
      (bᵈ : 𝓒ᴰ .ob[_] B)
      : Type _ where 
      field 
        {aᵈ} : 𝓥ᴰ .ob[_] A
        f̂ : ⟨ 𝓞ᴰ[ f ][ aᵈ , bᵈ ] ⟩
        isHetCart : HetCartesian f̂ 


    F : ob 𝓥 → ob 𝓒 
    F = hasF .fst .F-ob

    ret : {A : ob 𝓥} → ⟨ 𝓞[ A , F A ] ⟩ 
    ret = {!   !}
    -- ret has heterogenious cartesion lifts
    retCartesian : (A : ob 𝓥)(faᵈ : 𝓒ᴰ .ob[_] (F A) ) → HetLift {!   !} faᵈ
-}














{-
  record Disp : Type (uhg (ℓV ∷ ℓVD ∷ ℓVD' ∷ ℓC ∷ ℓC' ∷ ℓCD ∷ ℓCD' ∷ ℓS ∷ [])) where 
    field 
      elᴰ : ⟨ univ .U ⟩ → Type
      --𝓥ᴰ : Categoryᴰ 𝓥 _ _
      𝓒ᴰ : Categoryᴰ 𝓒 ℓCD ℓCD' 
      Ctmᴰ : Functorᴰ Ctm 𝓒ᴰ (SETᴰ ℓS ℓV) 

    𝓥ᴰ : Categoryᴰ 𝓥 _ _ 
    ob[ 𝓥ᴰ ] _ = Unit
    𝓥ᴰ .Hom[_][_,_] f tt tt = (SETᴰ _ _ )[ f ][ {!   !} , {!   !} ]
    𝓥ᴰ .idᴰ = {!   !}
    𝓥ᴰ ._⋆ᴰ_ = {!   !}
    𝓥ᴰ .⋆IdLᴰ = {!   !}
    𝓥ᴰ .⋆IdRᴰ = {!   !}
    𝓥ᴰ .⋆Assocᴰ = {!   !}
    𝓥ᴰ .isSetHomᴰ = {!   !}
        
    {-
    𝓞ᴰ : Functorᴰ 𝓞 ((𝓥ᴰ ^opᴰ) ×Cᴰ 𝓒ᴰ) (SETᴰ _ _ )
    𝓞ᴰ .F-obᴰ {(v , c)} (vᵈ , cᵈ) o = ((SETᴰ _ _)[ o ][ (λ v̂ → (𝓥ᴰ .ob[_] {!   !}) , {!   !}) , Ctmᴰ .F-obᴰ cᵈ ]) , {!   !}
    𝓞ᴰ .F-homᴰ = {!   !}
    𝓞ᴰ .F-idᴰ = {!   !}
    𝓞ᴰ .F-seqᴰ = {!   !}

    -}

-}


{-
module _ (ℓ ℓ' : Level ) where

  Term : Category ℓ ℓ' 
  Term .ob = Unit*
  Term .Hom[_,_] tt* tt* = Unit*
  Term .id = tt*
  Term ._⋆_ tt* tt* = tt*
  Term .⋆IdL tt* = refl
  Term .⋆IdR tt* = refl
  Term .⋆Assoc tt* tt* tt* = refl
  Term .isSetHom = isSetUnit*


  module _ (ℓS : Level)(X : hSet ℓS) where 

    hrm : Iso {! PresheafCategory Term ℓS  !} {!   !} 

    to : Functor (PresheafCategory Term ℓS) (SET ℓS) 
    to .F-ob F = F .F-ob tt*
    to .F-hom nt = nt .N-ob tt*
    to .F-id = refl
    to .F-seq f g = refl

    from : Functor (SET ℓS) (PresheafCategory Term ℓS) 
    from .F-ob X .F-ob tt* = X
    from .F-ob X .F-hom tt* = λ z → z
    from .F-ob X .F-id = refl
    from .F-ob X .F-seq tt* tt* = refl
    from .F-hom f .N-ob tt* = f
    from .F-hom f .N-hom tt* = refl
    from .F-id = makeNatTransPath refl
    from .F-seq f g = makeNatTransPath refl

    tofrom : from ∘F to ≡ Id 
    tofrom = Functor≡ (
        λ F → 
          Functor≡ 
            (λ tt* → refl) 
            λ tt* → funExt λ _ → {! F .F-hom tt* !}) 
        λ f → makeNatTransPath refl

    fromto : to ∘F from ≡ Id 
    fromto = Functor≡ (λ _ → refl) λ _ → refl

    hrm = {!   !}
    hmm : Presheaf Term {!  PRESHEAF !} 
    hmm .F-ob tt* = X
    hmm .F-hom tt* = λ x → x
    hmm .F-id = refl
    hmm .F-seq tt* tt* = refl


open import Cubical.Categories.CBPV.Instances.DefinedSubstitution
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.Monoidal.Instances.Presheaf
open import Cubical.Categories.Presheaf.Constructions.BinProduct.LocalRepresentability
open import Cubical.Categories.Presheaf.Constructions.BinProduct.Base
open EnrichedCategory
-- scwf vs enriched cat 


module _ 
  (ℓC ℓC' ℓT ℓT' : Level)
  (S : SCwF ℓC ℓC' ℓT ℓT' ) where 

  open import Agda.Builtin.Cubical.Equiv
  open UniversalElement
  ctx = S .fst  
  vty = S .snd .fst 
  vtm = S .snd .snd .fst 
  ext = S .snd .snd .snd .snd

  {-
    LRProf : (P : Presheaf C ℓP) → Profunctor C C (ℓ-max ℓ' ℓP)
  LRProf P .F-ob x = (C [-, x ]) ×Psh P 

  (F-ob (LRProf (vtm A)) Γ)

    Representation : Type (ℓ-max (ℓ-max ℓo (ℓ-suc ℓh)) (ℓ-suc ℓp))
    Representation = Σ[ A ∈ C .ob ] PshIso C (C [-, A ]) P

    so

    Σ[ Γ' ∈ ctx ] (ctx[-, Γ'] ≅ (ctx [-, Γ ]) ×Psh vtm A))
    -- the Γ' is Γ,A
  -}
  asRepr : (A : vty) → (Γ : ob ctx) → Representation ctx ((ctx [-, Γ ]) ×Psh vtm A)
  asRepr A Γ = universalElementToRepresentation ctx ((ctx [-, Γ ]) ×Psh vtm A)  (ext A Γ)

  _ = PshIso
  open NatIso
  open isIso
  var' : (A : vty) → (Γ : ob ctx) → {!   !} 
  var' A Γ = {!   !}

  ×c : vty → Functor ctx ctx 
  ×c A = LRPsh→Functor (vtm A , ext A)

  V : EnrichedCategory (PshMon.𝓟Mon ctx {!   !}) {!   !}
  V .ob = vty
  V .Hom[_,_] A A' = vtm A' ∘F ((×c A)^opF)
  V .id {A} .N-ob Γ tt* = {! asRepr A Γ .snd .nIso (×c A .F-ob Γ) .inv ? .lower  !}
    --ext _ Γ .element .snd -- var
  V .id .N-hom = {!   !}
  V .seq A₁ A₂ A₃ .N-ob Γ (v , w) = {! ext A₁ Γ .element  !}
    {-vtm A₃ .F-hom -- dunnkno 
    (ext A₂ Γ .UniversalElement.universal
     (×c A₁ .F-ob Γ) .equiv-proof
     (ext A₁ Γ .UniversalElement.element .fst , v)
     .fst .fst)
    w-}
  V .seq A₁ A₂ A₃ .N-hom = {!   !}
  V .⋆IdL = {!   !}
  V .⋆IdR = {!   !}
  V .⋆Assoc = {!   !}

-}