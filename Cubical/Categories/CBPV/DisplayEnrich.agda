{-# OPTIONS --type-in-type #-}
module Cubical.Categories.CBPV.DisplayEnrich where  

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.NaturalTransformation hiding(_⇒_)
open import Cubical.Categories.Instances.Sets 
open import Cubical.Categories.Displayed.Instances.Sets
open import Cubical.Functions.Logic
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Functor
open import Cubical.Categories.Displayed.NaturalTransformation 
open import Cubical.Data.Unit 
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Base
open import Cubical.Categories.Constructions.TotalCategory.Base
open import Cubical.Categories.Instances.FunctorAlgebras
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Enriched.Functors.Base hiding (eseq)
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Monoidal.Instances.Presheaf
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Data.Sigma
open import Cubical.Foundations.Powerset

open Category
open Functor 
open Categoryᴰ 
open MonoidalCategory
open MonoidalStr
open NatTrans
open NatTransᴰ
open EnrichedCategory
open Functorᴰ
open Algebra
open AlgebraHom

module baz
  { ℓ : Level }
  (C : Category ℓ ℓ)
  (Cᴰ : Categoryᴰ C ℓ ℓ)
  (P : EnrichedCategory (PshMon.𝓟Mon C ℓ) ℓ)
  where

  𝟙^D : Functorᴰ (PshMon.𝟙 C ℓ) (Cᴰ ^opᴰ) (SETᴰ ℓ-zero ℓ)
  𝟙^D .F-obᴰ _ _ = Unit* , isSetUnit*
  𝟙^D .F-homᴰ _ _ _ = tt*
  𝟙^D .F-idᴰ = funExt λ _ → refl
  𝟙^D .F-seqᴰ _ _ = refl

  record PshEnrichedᴰ : Type _ where
    field 
      eob[_] : ob P → Type ℓ
      ehom[_,_] : {X Y : ob P} → eob[ X ] → eob[ Y ] → 
        Presheafᴰ (P .Hom[_,_]  X  Y) Cᴰ ℓ
      eid : {X : ob P}{x^d : eob[ X ]} → 
        NatTransᴰ (P .id) 𝟙^D ehom[ x^d , x^d ]
      eseq : {X Y Z : ob P}{x^d : eob[ X ]}{y^d : eob[ Y ]}{z^d : eob[ Z ]} → 
        NatTransᴰ (P .seq _ _ _) (ehom[ x^d , y^d ] ×ᴰPsh ehom[ y^d , z^d ]) ehom[ x^d , z^d ] 
      
    -- such that laws.. etc..   
    {- 
    
      -- Axioms
      ⋆IdL : ∀ x y →   η⟨ _ ⟩  ≡  (id {x} ⊗ₕ idV)  ⋆V  (seq x x y)
      ⋆IdR : ∀ x y →   ρ⟨ _ ⟩  ≡  (idV ⊗ₕ id {y})  ⋆V  (seq x y y)
      ⋆Assoc : ∀ x y z w →
          α⟨ _ , _ , _ ⟩  ⋆V  ((seq x y z) ⊗ₕ idV)  ⋆V  (seq x z w)
                          ≡  (idV ⊗ₕ (seq y z w))  ⋆V  (seq x y w)
   
   
    -}


module bazhom
  { ℓ : Level }
  (C : Category ℓ ℓ)
  (Cᴰ : Categoryᴰ C ℓ ℓ)
  (E D : EnrichedCategory (PshMon.𝓟Mon C ℓ) ℓ)
  (F : EnrichedFunctor (PshMon.𝓟Mon C ℓ) E D) where 

  open baz C Cᴰ 
  open PshEnrichedᴰ
  open EnrichedFunctor

  record PshEnrichedFun 
    (Eᴰ : PshEnrichedᴰ E)
    (Dᴰ : PshEnrichedᴰ D) : Set ℓ  where
    field 
      Fob : {x : ob E} → Eᴰ .eob[_] x → Dᴰ .eob[_] (F-ob F x)
    --  Fhom : {x y : ob E}{xᵈ : Eᴰ .eob[_] x}{yᵈ : Eᴰ .eob[_] y} → 
      --  NatTransᴰ (F-hom F) (Eᴰ .ehom[ xᵈ , yᵈ ]) {!   !} 

{-}
module foo
  { ℓ : Level }
  (C : Category ℓ ℓ)
  (Cᴰ : Categoryᴰ C ℓ ℓ)
  where
  ∫Pᴰ : Category ℓ ℓ 
  ∫Pᴰ = ∫C (PRESHEAFᴰ Cᴰ ℓ ℓ)

  pod : (P Q : ob ∫Pᴰ) → ob ∫Pᴰ 
  pod (P , P') (Q , Q') = (P ×Psh Q) , (P' ×ᴰPsh Q') 

  ⨂ : Functor (∫Pᴰ ×C ∫Pᴰ) ∫Pᴰ 
  ⨂ .F-ob (P , Q) = pod P Q
  ⨂ .F-hom {P}{Q} (n , n')  = 
    natTrans 
      (λ x x₁ → N-ob (n .fst) x (x₁ .fst) , N-ob (n' .fst) x (x₁ .snd)) 
      (λ f i (s , t) → (n .fst .N-hom f i s) , n' .fst .N-hom f i t )
    , record { 
      N-obᴰ = λ xᴰ x x₁ → n .snd .N-obᴰ xᴰ (x .fst) (x₁ .fst) ,
        n' .snd .N-obᴰ xᴰ (x .snd) (x₁ .snd) ; 
      N-homᴰ = λ fᴰ i (s , t) (s' , t') → (n .snd  .N-homᴰ fᴰ i s s') , (n' .snd  .N-homᴰ fᴰ i t t') }
  ⨂ .F-id = {!   !} 
    -- works but is slow
    -- ΣPathP ((makeNatTransPath refl) , makeNatTransPathᴰ (Cᴰ ^opᴰ) (SETᴰ ℓ ℓ) ((makeNatTransPath refl)) refl)
  ⨂ .F-seq f g = {!   !}
    -- works but is slow
    --ΣPathP ((makeNatTransPath refl) , makeNatTransPathᴰ (Cᴰ ^opᴰ) (SETᴰ ℓ ℓ) (makeNatTransPath refl)  refl )

  𝟙 : ob ∫Pᴰ 
  𝟙 = UnitPsh , record { 
    F-obᴰ = λ {x} z z₁ → Unit*  , isSetUnit* ; 
    F-homᴰ = λ {x} {y} {f} {xᴰ} {yᴰ} _ x₁ _ → tt* ; 
    F-idᴰ = refl ; 
    F-seqᴰ = λ _ _ →  refl }

  M' : MonoidalStr ∫Pᴰ 
  M' .tenstr = record { ─⊗─ = ⨂ ; unit = 𝟙 }
  M' .α = {!   !}
  M' .η = {!   !}
  M' .ρ = {!   !}
  M' .pentagon = {!   !}
  M' .triangle = {!   !}

  M : MonoidalCategory ℓ ℓ 
  M = record { C = ∫Pᴰ ; monstr = M' }
-}

module plug 
  { ℓ : Level }
  (C : Category ℓ ℓ)
  (Cᴰ : Categoryᴰ C ℓ ℓ)
  (P : EnrichedCategory (PshMon.𝓟Mon C ℓ) ℓ)
  where 
--  open foo C Cᴰ
  open baz C Cᴰ P

  module _ (Pᴰ : PshEnrichedᴰ) where
    open PshEnrichedᴰ Pᴰ
    -- give a Presheaf ∫Cᴰ enriched cat
    -- inline the change of base
    ∫E : EnrichedCategory (PshMon.𝓟Mon (∫C Cᴰ) ℓ) ℓ
    --M ℓ
    ∫E .ob = Σ (ob P) eob[_]
    ∫E .Hom[_,_] (B , B̂)(B' , B̂') = ∫P {P = P .Hom[_,_] B B'} ehom[ B̂ , B̂' ]

    ∫E .id .N-ob (c , cᵈ) tt* = (N-ob (P .id) c tt*) , eid .N-obᴰ cᵈ tt* tt*
    ∫E .id .N-hom (f , fᵈ) i tt* = 
      N-hom (P .id) f i tt* , N-homᴰ eid fᵈ i tt* tt*

    ∫E .seq (x , xᵈ) (y , yᵈ) (z , zᵈ) .N-ob (c , cᵈ)(Fc , Fᵈcᵈ) = 
      (N-ob (P .seq x y z) c (Fc .fst , Fᵈcᵈ .fst)) , 
      eseq .N-obᴰ cᵈ (Fc .fst , Fᵈcᵈ .fst) (Fc .snd , Fᵈcᵈ .snd)
    ∫E .seq (x , xᵈ) (y , yᵈ) (z , zᵈ) .N-hom (f , fᵈ) i (Fc , Fᵈcᵈ) = 
      P .seq x y z .N-hom f i (Fc .fst , Fᵈcᵈ .fst) , 
      eseq .N-homᴰ fᵈ i (Fc .fst , Fᵈcᵈ .fst) (Fc .snd , Fᵈcᵈ .snd)

    ∫E .⋆IdL (x , xᵈ) (y , yᵈ) = makeNatTransPath λ i x₁ x₂ → 
      (P .⋆IdL x y i .N-ob (x₁ .fst)  (tt* , x₂ .snd .fst)) ,
      {! Pᴰ .ei  !}
    --  makeNatTransPath (funExt λ (z , zᵈ) → funExt λ (tt* ,(f , fᵈ)) → 
     -- ΣPathP ( {! P .seq x x y    !} , {!   !}))
    ∫E .⋆IdR (x , xᵈ) (y , yᵈ) = makeNatTransPath λ i x₁ x₂ → 
      P .⋆IdR x y i .N-ob (x₁ .fst) (x₂ .fst .fst , tt*) , 
      {!   !}
    ∫E .⋆Assoc (x , xᵈ) (y , yᵈ) (z , zᵈ)(w , wᵈ) = 
      makeNatTransPath λ i x₁ x₂ → 
        (P .⋆Assoc x y z w i .N-ob (x₁ .fst) 
          (x₂ .fst .fst , x₂ .snd .fst .fst , x₂ .snd .snd .fst)) 
        , {!   !}


module _ (ℓ : Level) where 
  Pred : Categoryᴰ (SET ℓ) (ℓ) (ℓ)
  Pred. ob[_] X = ⟨ X ⟩ → hProp ℓ
  Pred .Hom[_][_,_] f P Q = ⟨ ∀[ x ] (P x ⇒ Q (f x)) ⟩
  Pred .idᴰ = λ x z → z
  Pred ._⋆ᴰ_ {f = f} f^d g^d x p = g^d (f x) (f^d x p)
  Pred .⋆IdLᴰ _ = refl
  Pred .⋆IdRᴰ _ = refl
  Pred .⋆Assocᴰ _ _ _ = refl
  Pred .isSetHomᴰ {f = f} {x^d}{y^d} = 
    isProp→isSet ((∀[ x ] (x^d x ⇒ y^d (f x))) .snd)
  open import Cubical.Categories.Enriched.Instances.FromCat
  -- EnrichedCategory (PshMon.𝓟Mon (SET ℓ-zero) ℓ-zero) ℓ-zero

  thing : EnrichedCategory (PshMon.𝓟Mon (SET ℓ-zero) ℓ-zero) ℓ-zero
  thing = {!   !}

  open baz (SET ℓ) Pred {!   !}

{-}
open import Cubical.Categories.Monad.ExtensionSystem 
  renaming (Kleisli to KleisliCat)
module bar 
  (ℓ : Level)
  (M : ExtensionSystem (SET ℓ))  
--(F : Functor (SET ℓ)(SET ℓ))
  where

  Pred : Categoryᴰ (SET ℓ) (ℓ) (ℓ)
  Pred. ob[_] X = ⟨ X ⟩ → hProp ℓ
  Pred .Hom[_][_,_] f P Q = ⟨ ∀[ x ] (P x ⇒ Q (f x)) ⟩
  Pred .idᴰ = λ x z → z
  Pred ._⋆ᴰ_ {f = f} f^d g^d x p = g^d (f x) (f^d x p)
  Pred .⋆IdLᴰ _ = refl
  Pred .⋆IdRᴰ _ = refl
  Pred .⋆Assocᴰ _ _ _ = refl
  Pred .isSetHomᴰ {f = f} {x^d}{y^d} = 
    isProp→isSet ((∀[ x ] (x^d x ⇒ y^d (f x))) .snd)



  open import Cubical.Categories.CBPV.Instances.Kleisli
  open ExtensionSystemFor (M .snd) renaming (η to ret)
  open baz (SET ℓ) Pred (Kleisli M .snd .fst)


  E^D : PshEnrichedᴰ 
  E^D .baz.PshEnrichedᴰ.eob[_] X = X .fst → hProp ℓ
  E^D .baz.PshEnrichedᴰ.ehom[_,_] {X}{Y}  X̂  Ŷ .F-obᴰ {Z} Ẑ (lift k) = 
    ((z : ⟨ Z ⟩)(x : ⟨ X ⟩) → 
      ⟨ Ẑ z ⟩ → ⟨ X̂ x ⟩ → Σ[ y ∈ ⟨ Y ⟩ ] (k z x ≡ ret y) × ⟨ Ŷ y ⟩) 
    , {!   !}
  E^D .baz.PshEnrichedᴰ.ehom[_,_] {X}{Y}  X̂  Ŷ  .F-homᴰ 
    {Δ}{Γ}{γ}{Δ̂ }{Γ̂ }Gγ (lift k)k̂ = λ z x γ̂  x̂  → (k̂ (γ z) x (Gγ z γ̂) x̂ .fst) , k̂ (γ z) x (Gγ z γ̂) x̂ .snd
  E^D .baz.PshEnrichedᴰ.ehom[_,_] {X}{Y}  X̂  Ŷ  .F-idᴰ = {!   !}
  E^D .baz.PshEnrichedᴰ.ehom[_,_] {X}{Y}  X̂  Ŷ  .F-seqᴰ = {!   !}
  E^D .baz.PshEnrichedᴰ.eid {X}{X̂}.N-obᴰ {Γ} Γ̂  tt* tt* γ x prfΓ prfX = x , (refl , prfX)
  E^D .baz.PshEnrichedᴰ.eid .N-homᴰ _ = refl
  E^D .baz.PshEnrichedᴰ.eseq {X}{Y}{Z}{X̂}{Ŷ}{Ẑ} .N-obᴰ {Γ} Γ̂  (k , k') prfk prfk' x prfΓ prfX 
    = (prfk .snd prfk' (prfk .fst prfk' x prfΓ prfX .fst) prfΓ
       (prfk .fst prfk' x prfΓ prfX .snd .snd) .fst) 
      , {!   !} 
      , (prfk .snd prfk' (prfk .fst prfk' x prfΓ prfX .fst) prfΓ
         (prfk .fst prfk' x prfΓ prfX .snd .snd) .snd .snd)
  {- 
  bind (k' .lower prfk') (k .lower prfk' x) ≡
ret
(prfk .snd prfk' (prfk .fst prfk' x prfΓ prfX .fst) prfΓ
 (prfk .fst prfk' x prfΓ prfX .snd .snd) .fst)
  -}
  E^D .baz.PshEnrichedᴰ.eseq .N-homᴰ _ = {!   !}


  --Sem : EnrichedCategory (PshMon.𝓟Mon (∫C Pred) ℓ) ℓ
  --Sem = plug.∫E (SET ℓ) Pred (Kleisli M .snd .fst) E^D

-}











    {-
      -- From
  --  category of pairs (P : Presheaf C , Pᴰ : Presheafᴰ P Cᴰ)
  -- To 
  --  category of presheves P : Presheaf ∫Cᴰ
  yosh : Functor ∫Pᴰ 𝓟 
  yosh .F-ob (P , P') = ∫P P'
  
    ∫P Pᴰ = ΣF ∘F ∫F Pᴰ

    where 
      ΣF : Functor (∫C SETᴰ) SET
      ΣF .F-ob (A , B) = Σ[ a ∈ ⟨ A ⟩ ] ⟨ B a ⟩
      ΣF .F-hom (f , g) (x , y) = (f x) , (g x y)
    and
      ∫F : Functor (∫C Cᴰ) (∫C Dᴰ)
      ∫F .F-ob (x , xᴰ)  = F .F-ob x  , Fᴰ.F-obᴰ xᴰ
      ∫F .F-hom (f , fᴰ) = F .F-hom f , Fᴰ.F-homᴰ fᴰ

      so , 
        run the functors pairwise, 
        then merge them to gethter in Set using Σ
  
  yosh .F-hom (n , n') .N-ob (x , xᴰ) (p , pᴰ) = 
    (n .N-ob _ p) , n' .N-obᴰ xᴰ p pᴰ
  yosh .F-hom (n , n') .N-hom (f , f') i (x , xᵈ) = 
    (n .N-hom f i x) , n' .N-homᴰ f' i x xᵈ
  yosh .F-id {(P , P')} = makeNatTransPath λ i (x , x^d) (Px , P'x^d) → Px , P'x^d
  yosh .F-seq (n , n^d) (m , m^d) = makeNatTransPath λ i → λ x z₁ →
      N-ob m (x .fst) (N-ob n (x .fst) (z₁ .fst)) ,
      m^d .N-obᴰ (x .snd) (N-ob n (x .fst) (z₁ .fst))
      (n^d .N-obᴰ (x .snd) (z₁ .fst) (z₁ .snd))
    -}



{-
module bar 
  (ℓ : Level) 
  (F : Functor (SET ℓ)(SET ℓ))
  where

  Pred : Categoryᴰ (SET ℓ) (ℓ) (ℓ)
  Pred. ob[_] X = ⟨ X ⟩ → hProp ℓ
  Pred .Hom[_][_,_] f P Q = ⟨ ∀[ x ] (P x ⇒ Q (f x)) ⟩
  Pred .idᴰ = λ x z → z
  Pred ._⋆ᴰ_ {f = f} f^d g^d x p = g^d (f x) (f^d x p)
  Pred .⋆IdLᴰ _ = refl
  Pred .⋆IdRᴰ _ = refl
  Pred .⋆Assocᴰ _ _ _ = refl
  Pred .isSetHomᴰ {f = f} {x^d}{y^d} = 
    isProp→isSet ((∀[ x ] (x^d x ⇒ y^d (f x))) .snd)

  open foo (SET ℓ) Pred

  subset :{B : hSet _} →  ℙ ⟨ B ⟩  → hSet _
  subset {B} P = 
    (Σ[ b ∈ ⟨ B ⟩ ] ⟨ P b ⟩) , 
    isSetΣ (B .snd) λ _ → isProp→isSet (P _ .snd)

  -- ℙ
  subalgebra : Algebra F → Type _ 
  subalgebra (algebra B αB) = 
    Σ[ sub ∈ ℙ ⟨ B ⟩ ] 
      ((b' : ⟨ subset sub ⟩ ) → αB {! F .F-ob ?  !} ≡ {!   !})


  -- this is inlined total category
  -- but we also want to change the base of enrichment
  E : EnrichedCategory M ℓ
  E .ob = Σ (Algebra F) subalgebra
  E .Hom[_,_] (B , B̂)  (B' , B̂') .fst = (SET ℓ)[-, AlgebraHom F B B' , {!   !} ]
  E .Hom[_,_] (B , B̂)  (B' , B̂') .snd .F-obᴰ {Γ} Γ̂  k = 
    ⟨ ∀[ γ ∶ ⟨ Γ ⟩  ] (∀[ b ∶ ⟨ B .carrier ⟩  ] Γ̂  γ ⇒ B̂ .fst b ⇒ B̂' .fst (k γ .carrierHom b)) ⟩ , {!   !}
  E .Hom[_,_] (B , B̂)  (B' , B̂') .snd .F-homᴰ {Δ}{Γ}{f}(G)k P γ b Gγ Cb = P (f γ) b (G γ Gγ) Cb
  E .Hom[_,_] (B , B̂)  (B' , B̂') .snd .F-idᴰ = refl
  E .Hom[_,_] (B , B̂)  (B' , B̂') .snd .F-seqᴰ _ _ = refl
  E .id = {! idTrans _  !} , {!   !}
  E .seq _ _ _ = {!  makeNatTransPath ? !} , {!   !}
  E .⋆IdL = {!   !}
  E .⋆IdR = {!   !}
  E .⋆Assoc = {!   !}

-}

















{-
open Functorᴰ

-- directly encode presheaf enriched category

module pshEnr
  {ℓ ℓ' ℓS : Level} 
  (C : Category ℓ ℓ') where 
  ℓm = ℓ-max ℓ (ℓ-max ℓ' ℓS)

  𝟙 : Presheaf C ℓm
  𝟙 = LiftPsh (UnitPsh{C = C}) ℓm

  𝟙^D : {ℓ ℓ' ℓS ℓD ℓD' : Level}{C : Category ℓ ℓ'}{C^D : Categoryᴰ C ℓD ℓD'}
    → Presheafᴰ (LiftPsh (UnitPsh{C = C}) (ℓ-max ℓ (ℓ-max ℓ' ℓS))) C^D {!   !}
  𝟙^D .F-obᴰ _ _ = Unit* , isSetUnit*
  𝟙^D .F-homᴰ _ _ _ = tt*
  𝟙^D .F-idᴰ = funExt λ _ → refl
  𝟙^D .F-seqᴰ _ _ = refl

  record PshEnriched (ℓE : Level): Type (ℓ-max (ℓ-suc ℓE) (ℓ-suc ℓm)) where 
    field 
      ob : Type ℓE
      Hom : (X Y : ob) → Presheaf C ℓm
      id : {X : ob} → NatTrans 𝟙 (Hom X X)
      seq : {X Y Z : ob} → NatTrans (Hom X Y ×Psh Hom Y Z) (Hom X Z) 

  record totPshEnriched (C^D : Categoryᴰ C ℓ ℓ )(ℓE : Level): Type (ℓ-max (ℓ-suc ℓE) (ℓ-suc ℓm)) where 
    field 
      ob : Type ℓE
      Hom : (X Y : ob) → Σ[ P ∈ Presheaf C ℓm ] Presheafᴰ P C^D ℓ
      id : {X : ob} → Σ[ f ∈ NatTrans 𝟙 ((Hom X X) .fst) ] NatTransᴰ f 𝟙^D (Hom X X  .snd)

  -- how to change base..?
  {-
  first, how to convert presheaves
    Q: is there a monoidal category where the objects are 
      Σ[ P : Presheaf C] (Presheafᴰ P C^D) ?
      plausable..

    how to convert 
      Σ[ P : Presheaf C] (Presheafᴰ P C^D) → Presheaf ∫C

  -}
  open Functor
  open import Cubical.Data.Sigma
  wrap : {C^D : Categoryᴰ C ℓ ℓ } → 
    Σ[ P ∈ Presheaf C ℓ ] Presheafᴰ P C^D ℓ → Presheaf (∫C C^D) ℓ
  wrap (P , P') .F-ob (c , c') = 
    (Σ ⟨ P . F-ob c ⟩ λ Pc → ⟨ P'  .F-obᴰ c' Pc ⟩) , 
    isSetΣ (P . F-ob c .snd) λ Pc → P' .F-obᴰ c' Pc .snd
  wrap (P , P') .F-hom (f , f')(c , c') = (P .F-hom f c) , P' .F-homᴰ f' c c'
  wrap (P , P') .F-id = funExt λ (p , p') → 
    ΣPathP ((funExt⁻ (P .F-id) _) , λ i → P' .F-idᴰ i p p')
  wrap (P , P') .F-seq f g = funExt λ (p , p') → 
    ΣPathP (funExt⁻ (P .F-seq _ _) _ , (λ i → P' .F-seqᴰ _ _  i p p'))



  {-

  second, change base
  Given 
    C : Category
    C^D : C-disp Cat 
    ∫E : ∫Ĉ-Enriched Cat

    yield 
    E : 
  
  
  -}

module _ 
  {ℓ ℓ' ℓS ℓE ℓCP ℓD ℓD' : Level}
  (C : Category ℓ ℓ')
  where
  open pshEnr C

  record PshEnrichedᴰ (CP : PshEnriched ℓCP)(C^D : Categoryᴰ C ℓD ℓD') : Type _ where
    open PshEnriched CP
    field 
      eob[_] : ob → Type ℓE
      ehom[_,_] : {X Y : ob} → eob[ X ] → eob[ Y ] → 
        Presheafᴰ (Hom X Y) C^D ℓ
      eid : {X : ob}{x^d : eob[ X ]} → 
        NatTransᴰ id 𝟙^D ehom[ x^d , x^d ]
      eseq : {X Y Z : ob}{x^d : eob[ X ]}{y^d : eob[ Y ]}{z^d : eob[ Z ]} → 
        NatTransᴰ seq (ehom[ x^d , y^d ] ×ᴰPsh ehom[ y^d , z^d ]) ehom[ x^d , z^d ] 
    -- such that laws.. etc..   

module _ 
  {ℓ  : Level}
  (C : Category ℓ ℓ)
  (C^D : Categoryᴰ C ℓ ℓ) where 

  open Category
  open Functor
  open NatTrans

  -- it is cartesian monoidal
  -- so it can be used as an enrichment
  -- but we can also map the objects to normal presheaves on ∫C
  ∫Pᴰ : Category ℓ ℓ 
  ∫Pᴰ = ∫C (PRESHEAFᴰ C^D ℓ ℓ)

  open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Base
  pod : (P Q : ob ∫Pᴰ) → ob ∫Pᴰ 
  pod (P , P') (Q , Q') = (P ×Psh Q) , (P' ×ᴰPsh Q') 

  𝓟 : Category ℓ ℓ 
  𝓟 = PresheafCategory (∫C C^D) ℓ
  open import Cubical.Categories.Displayed.NaturalTransformation
  open NatTransᴰ
  open import Cubical.Data.Sigma 
  {-}
    open import Cubical.Categories.Displayed.Presheaf.Morphism

  ∫PshHom : PshHom (∫P Pᴰ) (∫P Qᴰ)
  ∫PshHom .N-ob (x , xᴰ) (p , pᴰ) = (α .N-ob _ p) , (N-obᴰ pᴰ)
  ∫PshHom .N-hom _ _ (f , fᴰ) (p , pᴰ) = ΣPathP ((α .N-hom _ _ f p) , N-homᴰ)
  -}


  -- From
  --  category of pairs (P : Presheaf C , Pᴰ : Presheafᴰ P Cᴰ)
  -- To 
  --  category of presheves P : Presheaf ∫Cᴰ
  yosh : Functor ∫Pᴰ 𝓟 
  yosh .F-ob (P , P') = ∫P P'
  {- 
    ∫P Pᴰ = ΣF ∘F ∫F Pᴰ

    where 
      ΣF : Functor (∫C SETᴰ) SET
      ΣF .F-ob (A , B) = Σ[ a ∈ ⟨ A ⟩ ] ⟨ B a ⟩
      ΣF .F-hom (f , g) (x , y) = (f x) , (g x y)
    and
      ∫F : Functor (∫C Cᴰ) (∫C Dᴰ)
      ∫F .F-ob (x , xᴰ)  = F .F-ob x  , Fᴰ.F-obᴰ xᴰ
      ∫F .F-hom (f , fᴰ) = F .F-hom f , Fᴰ.F-homᴰ fᴰ

      so , 
        run the functors pairwise, 
        then merge them to gethter in Set using Σ
  -}
  yosh .F-hom (n , n') .N-ob (x , xᴰ) (p , pᴰ) = 
    (n .N-ob _ p) , n' .N-obᴰ xᴰ p pᴰ
  yosh .F-hom (n , n') .N-hom (f , f') i (x , xᵈ) = 
    (n .N-hom f i x) , n' .N-homᴰ f' i x xᵈ
  yosh .F-id {(P , P')} = makeNatTransPath λ i (x , x^d) (Px , P'x^d) → Px , P'x^d
  yosh .F-seq (n , n^d) (m , m^d) = makeNatTransPath λ i → λ x z₁ →
      N-ob m (x .fst) (N-ob n (x .fst) (z₁ .fst)) ,
      m^d .N-obᴰ (x .snd) (N-ob n (x .fst) (z₁ .fst))
      (n^d .N-obᴰ (x .snd) (z₁ .fst) (z₁ .snd))


  -- From
  --  category of presheves P : Presheaf ∫Cᴰ
  -- To 
  --  category of pairs (P : Presheaf C , Pᴰ : Presheafᴰ P Cᴰ)
  open Categoryᴰ
  hrm : Functor 𝓟 ∫Pᴰ 
  hrm .F-ob P = Q , {!   !} where 
  {-
    P : Presheaf Cᴰ
  -}
    Q : Functor (C ^op) (SET ℓ) 
    Q .F-ob c = (Σ[ c^d ∈ C^D .ob[_] c ] ⟨ P .F-ob (c , c^d) ⟩) , {!   !}
      --P .F-ob (c , {!   !})
    Q .F-hom {c}{d} f (d^d , Pdd^d) = {! d^d !} , P .F-hom (f , {!   !}) Pdd^d 
      where 
        clift : {x y : ob C} → (f : C [ x , y ]) → {! C^D .Hom[_][_,_] f !} 
        clift = {!   !}
    Q .F-id = {!   !}
    Q .F-seq = {!   !}

    Q' : Functorᴰ Q (C^D ^opᴰ) (SETᴰ ℓ ℓ) 
    Q' .F-obᴰ {c} c^d Pc? = P .F-ob (c , c^d)
    Q' .F-homᴰ {c}{d} {f}{c^d}{d^d} f' = {!   !}
    Q' .F-idᴰ = {!   !}
    Q' .F-seqᴰ = {!   !}

  hrm .F-hom = {!   !}
  hrm .F-id = {!   !}
  hrm .F-seq = {!   !}


module _ 
  {ℓ ℓ' ℓS ℓE ℓCP ℓD ℓD' : Level}
  (C : Category ℓ ℓ')
  (C^D : Categoryᴰ C ℓD ℓD' )
  (F : Functor C C)
  where
  open pshEnr (∫C C^D)
  open PshEnriched
  open Functor
  open import Cubical.Functions.Logic
  
  -- missing a stack ..?
  -- yes.. 
  total : PshEnriched (ℓ-suc ℓE) 
  total .ob = Σ[ X ∈ Type ℓE ] (X → hProp ℓE)
  total .Hom (X , X̂) (Y , Ŷ) .F-ob (Γ , Γ̂ ) = 
    (Σ[ f ∈ (X → Y) ] ⟨ ∀[ x ∶ X ] (X̂ x ⇒ Ŷ (f x)) ⟩) , {!   !}
  total .Hom (X , X̂) (Y , Ŷ) .F-hom (f , f̂ ) x = x
  total .Hom (X , X̂) (Y , Ŷ) .F-id = {!   !}
  total .Hom (X , X̂) (Y , Ŷ) .F-seq = {!   !}
  total .id = {!   !}
  total .seq = {!   !}     



  {-
    displayed vs sub algebra

    A Displayed Monoid over monoid M constists of
      - a monoid N
      - a monoid hom [M,N]

  
  -}

module example (F : Functor (SET ℓ-zero )(SET ℓ-zero))where 
  open pshEnr 
  open Category
  open Categoryᴰ
  open PshEnriched
  open Functor
  open NatTrans
  open PshEnrichedᴰ
  open Algebra
  open import Cubical.Foundations.Structure

  Pred : Categoryᴰ (SET ℓ-zero) (ℓ-zero) (ℓ-zero)
  Pred. ob[_] X = ⟨ X ⟩ → hProp ℓ-zero
  Pred .Hom[_][_,_] f P Q = ⟨ ∀[ x ] (P x ⇒ Q (f x)) ⟩
  Pred .idᴰ = λ x z → z
  Pred ._⋆ᴰ_ {f = f} f^d g^d x p = g^d (f x) (f^d x p)
  Pred .⋆IdLᴰ _ = refl
  Pred .⋆IdRᴰ _ = refl
  Pred .⋆Assocᴰ _ _ _ = refl
  Pred .isSetHomᴰ {f = f} {x^d}{y^d} = 
    isProp→isSet ((∀[ x ] (x^d x ⇒ y^d (f x))) .snd)

  ehom : Algebra F → Algebra F → Presheaf (SET ℓ-zero) (ℓm (SET ℓ-zero)) 
  ehom B B' = (SET _)[-, (AlgebraHom F B B') , {!   !} ]
    --(SET ℓ-zero)[ Γ , (AlgebraHom F B B' , {! isSetAlgebraHom  !}) ] , {!   !}

  -- this is Cat→Enriched on the Algebra category on F
  algPE : PshEnriched (SET ℓ-zero) {!   !}
  algPE .ob = Algebra F
  algPE .Hom = ehom
  algPE .id = {!   !}
  algPE .seq = {!   !}

  open import Cubical.Foundations.Powerset
  subset :{B : hSet _} →  ℙ ⟨ B ⟩  → hSet _
  subset {B} P = 
    (Σ[ b ∈ ⟨ B ⟩ ] ⟨ P b ⟩) , 
    isSetΣ (B .snd) λ _ → isProp→isSet (P _ .snd)

  -- ℙ
  subalgebra : Algebra F → Type _ 
  subalgebra (algebra B αB) = 
    Σ[ sub ∈ ℙ ⟨ B ⟩ ] 
      ((b' : ⟨ subset sub ⟩ ) → αB {! F .F-ob ?  !} ≡ {!   !})

  open AlgebraHom
  E^D : PshEnrichedᴰ (SET ℓ-zero) algPE Pred
  E^D .eob[_] = subalgebra
  ehom[_,_] E^D {B} {B'} (B̂ , _) (B̂' , _) .F-obᴰ {Γ}(Γ̂ ) k = 
    ⟨ ∀[ γ ∶ ⟨ Γ ⟩  ] (∀[ b ∶ ⟨ B .carrier ⟩  ] Γ̂  γ ⇒ B̂ b ⇒ B̂' (k γ .carrierHom b)) ⟩ , {!   !}
  ehom[_,_] E^D {B} {B'} (B̂ , _) (B̂' , _) .F-homᴰ {Δ}{Γ}{f}(G)k P γ b Gγ Cb = P (f γ) b (G γ Gγ) Cb
  ehom[_,_] E^D {B} {B'} (B̂ , _) (B̂' , _) .F-idᴰ = refl
  ehom[_,_] E^D {B} {B'} (B̂ , _) (B̂' , _) .F-seqᴰ _ _ = refl
  E^D .eid = {!   !}
  E^D .eseq = {!   !}

  -- no.. needs to be enriched in displayed presheaves 
  -- (enriched in the total category of presehaves and displayed presheaves)
  -- then converted to normal presheaves?
  -- we are missing the stack here
  -- also this should be enriched in presheaves over the total category
  -- which is why semantic gamma is missing
  totAlg : PshEnriched (SET ℓ-zero) {!   !}
  totAlg .ob = Σ (Algebra F) subalgebra
  totAlg .Hom (B , Balg) (B' , B'alg) .F-ob Γ = {!   !}
  totAlg .Hom (B , Balg) (B' , B'alg) .F-hom = {!   !}
  totAlg .Hom (B , Balg) (B' , B'alg) .F-id = {!   !}
  totAlg .Hom (B , Balg) (B' , B'alg) .F-seq = {!   !}
  totAlg .id = {!   !}
  totAlg .seq = {!   !}
-}

  {-}

  data Ctx : Type where 

  data CTy : Type where 

  data Subst : Ctx → Ctx → Type where 

  data Stk : Ctx → CTy → CTy → Type where 

  SubCat : Category ℓ-zero ℓ-zero 
  SubCat .ob = Ctx
  SubCat .Hom[_,_] = Subst
  SubCat .id = {!   !}
  SubCat ._⋆_ = {!   !}
  SubCat .⋆IdL = {!   !}
  SubCat .⋆IdR = {!   !}
  SubCat .⋆Assoc = {!   !}
  SubCat .isSetHom = {!   !}

  stk : (B B' : CTy) → Presheaf SubCat (ℓm SubCat) 
  stk B B' .F-ob Γ = Stk Γ B B' , {!   !}
  stk B B' .F-hom = {!   !}
  stk B B' .F-id = {!   !}
  stk B B' .F-seq = {!   !}

  E : PshEnriched SubCat ℓ-zero
  E .ob = CTy
  E .Hom = stk
  E .id = {!   !}
  E .seq = {!   !}

  data clCtx : Ctx → Type where

  data clCTy : CTy → Type where 

  data SemCtx : Ctx → Type where 

  data SemCTy : CTy → Type where 

  data reindex {Δ Γ : Ctx}: Subst Δ Γ → SemCtx Δ → SemCtx Γ → Type where

  data Something : Type where 

  𝓖 : (Γ : Ctx) → (clCtx Γ →  hProp ℓ-zero) 
  𝓖 Γ = {!   !}
{-
  how do evaluation contexts interact with logical relations
    compuation logical relation is closed under stacks?

  specific case 
    Prop^D 

  generic case ..?
  NO 
  type vs instance

-}
  plug : {Γ : Ctx}{B B' : CTy} → (k : Stk Γ B B') → clCtx Γ → clCTy B → clCTy B' 
  plug = {!   !}

  -- instance, but type of logical relation
  SubLR : Categoryᴰ SubCat {!   !} {!   !} 
  SubLR .ob[_] Γ = clCtx Γ → hProp ℓ-zero
    --SemCtx
    --clCtx Γ → hProp ℓ-zero
  SubLR .Hom[_][_,_] = {!   !}
    --reindex
  SubLR .idᴰ = {!   !}
  SubLR ._⋆ᴰ_ = {!   !}
  SubLR .⋆IdLᴰ = {!   !}
  SubLR .⋆IdRᴰ = {!   !}
  SubLR .⋆Assocᴰ = {!   !}
  SubLR .isSetHomᴰ = {!   !}

  -- No?, this should be subalgebras!
  -- clCTy B : CTy → Algebra
  E^D : PshEnrichedᴰ SubCat E SubLR
  E^D .eob[_] B = clCTy B → hProp ℓ-zero
    --SemCTy
  --B = clCTy B → hProp ℓ-zero
  ehom[_,_] E^D {B} {B'} B̂ B̂' .F-obᴰ {Γ} Γ̂  k = {!   !}
   -- ((γ* : clCtx Γ) → ⟨ Γ̂  γ* ⟩ → (b : clCTy B) → ⟨ B̂ b ⟩ → ⟨ B̂' (plug k γ* b) ⟩) , {!   !} -- Something , {!   !}
  ehom[_,_] E^D {B} {B'} B̂ B̂' .F-homᴰ {Δ}{Γ}{γ}{Δ̂ }{Γ̂ }= {!   !}
  -- reindex γ Γ̂ Δ̂ → (x : Stk Δ B B') → Something → Something
  ehom[_,_] E^D {B} {B'} B̂ B̂' .F-idᴰ = {!   !}
  ehom[_,_] E^D {B} {B'} B̂ B̂' .F-seqᴰ = {!   !}
  E^D .eid = {!   !}
  E^D .eseq = {!   !}
-}
  -- indexed hom
  {-
      -- set indexed hom
  iHom : (c c' : ob C) → ob PM.𝓟
  iHom c c' = LiftF ∘F ((SET _) [-, (C [ c , c' ]) , C .isSetHom ])
  -}

{-}
  set : PshEnriched (SET ℓ-zero) (ℓ-suc ℓ-zero) 
  set .ob = hSet ℓ-zero
  set .Hom X Y = LiftF ∘F ((SET _) [-, ((SET ℓ-zero) [ X , Y ]) , (SET ℓ-zero) .isSetHom ])
  set .id .N-ob X tt* = lift λ x z → z
  set .id .N-hom f = refl
  set .seq .N-ob X (f , g) = lift λ x z → g .lower x (f .lower x z)
  set .seq .N-hom f = refl

  try : PshEnrichedᴰ (SET ℓ-zero) _ _ _ _ _ (SETᴰ ℓ-zero ℓ-zero)
  try .eob[_] X = X → hProp ℓ-zero
  ehom[ try , P ] Q .F-obᴰ {X} = {!   !}
  ehom[ try , P ] Q .F-homᴰ = {!   !}
  ehom[ try , P ] Q .F-idᴰ = {!   !}
  ehom[ try , P ] Q .F-seqᴰ = {!   !}
  try .eid = {!   !}
  try .eseq = {!   !}
  -}