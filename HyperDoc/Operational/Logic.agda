{-# OPTIONS --type-in-type #-}
module HyperDoc.Operational.Logic where 

open import Cubical.Data.Sigma

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Displayed.Bifunctor 
open import Cubical.Categories.Bifunctor hiding (Sym)


open import HyperDoc.Operational.Model 
open import HyperDoc.Operational.Graph
open import HyperDoc.Lib
open import HyperDoc.Syntax

open BifunctorSep
open Category 
open Functor 
open NatTrans 

module _ 
  {ℓV ℓV' ℓC ℓC' ℓG ℓG' : Level}
  (M : CBPVModel ℓV ℓV' ℓC ℓC' ℓG ℓG') where

  open CBPVModelSyntax M

  
  Hom^op : {ℓL : Level } →  Functor ((POSET ℓL ℓL) ×C (POSET ℓL ℓL)^op) (SET ℓL )
  Hom^op = (HomFunctor _) ∘F Sym
{-
  CBPVLogic' : (ℓL : Level  ) →  Type _ 
  CBPVLogic' ℓL  = 
    Σ[ LV ∈ Functor (V ^op) (POSET ℓL ℓL) ] 
    Σ[ LC ∈ Functor (C ^op) (POSET ℓL ℓL) ] 
    (NatTrans (FORGET ∘F OPar) (Hom^op  ∘F (LV ×F ((LC ^opF) ∘F to^op^op ))))
-}
  record CBPVLogic : Type where 
    field 
      LV : Functor (V ^op) (POSET _ _)
      LC : Functor (C ^op) (POSET _ _)
      LSq : NatTrans (FORGET ∘F OPar) (Hom^op  ∘F (LV ×F ((LC ^opF) ∘F to^op^op )))


    module LV = HDSyntax LV
    module LC = HDSyntax LC

    pull : {A : V .ob}{B : C .ob}(M : O'[ A , B ])  
      → MonFun (F-ob LC B .fst) (F-ob LV A .fst)
    pull {A} {B} M = LSq .N-ob (A , B) M

    field 
      antired : ∀ {A B Q}{M M' : O'[ A , B ]} → 
        Edge[ M , M' ] → 
        A LV.◂ (pull M' $ Q) ≤ (pull M $ Q)


    pullComp : ∀ {A A' B B'}(V : V [ A' , A ])(S : C [ B , B' ])(M : O'[ A , B ]) → 
      pull (OPar .F-hom (V , S) .fst M) ≡ MonComp (LC .F-hom S) (MonComp (pull M) (LV .F-hom V))
    pullComp V S M = funExt⁻ (LSq .N-hom (V , S)) M

    pullLComp : ∀ {A A' B}(V : V [ A' , A ])(M : O'[ A , B ]) → 
      pull (O .Bif-homL V B .fst M) ≡ MonComp (pull M) (LV .F-hom V)
    pullLComp V M = {!   pullComp V (C .id) M
  ∙ cong
      (λ h → MonComp h (MonComp (pull M) (LV .F-hom V)))
      (LC .F-id)  !}
      -- pullComp V (C .id) M  ∙ cong (λ h → MonComp h (MonComp (pull M) (LV .F-hom V))) (LC .F-id)
      -- Bif-L-id
      -- pullComp V (C .id) M  ∙ cong (λ h → MonComp h (MonComp (pull M) (LV .F-hom V))) (LC .F-id)

    pullRComp :  ∀ {A B B'}(S : C [ B , B' ])(M : O'[ A , B ]) → 
      pull (O .Bif-homR A S .fst M) ≡ MonComp (LC .F-hom S) (pull M)
    pullRComp S M = {!   !}
      -- eqMon _ _  (funExt λ Q' → λ i → {! LSq .N-hom (V .id , S) i M .MonFun.f Q'  !})
      -- pullComp (V .id) S M ∙ cong₂ MonComp refl (LV .F-id)

    V*M*→VM* : ∀ {A A' B}{V : V [ A , A' ]}{M : O'[ A' , B ]}{Q : LC.F∣ B ∣}  → 
      A LV.◂ LV.f* V (pull M $ Q) ≤ (pull (O .Bif-homL V B .fst M) $ Q) 
    V*M*→VM* = LV.eqTo≤ (cong₂ MonFun.f (sym (pullLComp _ _ )) refl)

    VM*→V*M*  : ∀ {A A' B}{V : V [ A , A' ]}{M : O'[ A' , B ]}{Q : LC.F∣ B ∣} →  
      A LV.◂ (pull (O .Bif-homL V B .fst M) $ Q) ≤ LV.f* V (pull M $ Q)
    VM*→V*M* = LV.eqTo≤ (cong₂ MonFun.f (pullLComp _ _ ) refl)

    MS*→M*S*  : ∀ {A B B'}{S : C [ B , B' ]}{M : O'[ A , B ]}{Q' : LC.F∣ B' ∣} →  
      A LV.◂ pull (O .Bif-homR A S .fst M) $ Q' ≤ MonFun.f (MonComp (LC .F-hom S) (pull M)) Q'
    MS*→M*S* = LV.eqTo≤ (cong₂ MonFun.f (pullRComp _ _ ) refl)

    M*S*→MS*  : ∀ {A B B'}{S : C [ B , B' ]}{M : O'[ A , B ]}{Q' : LC.F∣ B' ∣} →  
      A LV.◂ MonFun.f (MonComp (LC .F-hom S) (pull M)) Q' ≤ (pull (O .Bif-homR A S .fst M) $ Q')
    M*S*→MS* = LV.eqTo≤ (cong₂ MonFun.f (sym (pullRComp _ _ )) refl)

    proofLcomp : ∀ {A A' B P P' Q V M} → 
      A' LV.◂ P' ≤ LV.f* V P → 
      A LV.◂ P ≤ (pull {B = B} M $ Q) → 
      ---------------------------
      A' LV.◂ P' ≤ (pull (O .Bif-homL V _ .fst M) $ Q)
    proofLcomp {V = V} P'≤VP P≤MQ = LV.seq P'≤VP (LV.seq (LV.mon* V P≤MQ) V*M*→VM*)

    proofRcomp : ∀ {A B B' P Q Q' S M} → 
      A LV.◂ P ≤ (pull {B = B} M $ Q) → 
      B LC.◂ Q ≤ LC.f* {c' = B'} S Q' → 
      ---------------------------
      A LV.◂ P ≤ (pull (O .Bif-homR _ S .fst M) $ Q')
    proofRcomp  {M = M}P≤MQ Q≤SQ' = LV.seq P≤MQ (LV.seq (pull M .MonFun.isMon  Q≤SQ') M*S*→MS*)

{-}
record CBPVRelLogic' {ℓV ℓV' ℓC ℓC' ℓG ℓG' : Level}
    {M : CBPVModel ℓV ℓV' ℓC ℓC' ℓG ℓG'}
    (L : CBPVLogic M): Type where 
  open CBPVModelSyntax M 
  open CBPVLogic L 
  field 
    antired : ∀ {A B P Q}{M M' : O'[ A , B ]} → 
      Edge[ M , M' ] → 
      A LV.◂ P ≤ (pull M' $ Q) → 
      ---------------------------
      A LV.◂ P ≤ (pull M $ Q)
    antiredCompL : ∀ {A A' B P P' Q}{V : V [ A' , A ]}{M M' : O'[ A , B ]}
      (M↦M' : Edge[ M , M' ])
      (P'≤VP : A' LV.◂ P' ≤ LV.f* V P)
      (P≤MQ : A LV.◂ P ≤ (pull M $ Q))
      (P≤M'Q : A LV.◂ P ≤ (pull M' $ Q)) → 
      antired (O .Bif-homL V B .snd M↦M') (proofLcomp P'≤VP P≤M'Q) ≡ proofLcomp P'≤VP P≤MQ

-}
    {-
    (antired (M₁ .snd .snd .Bif-homL V B .snd M↦M')
 (proofLcomp P'≤VP P≤M'Q)
 ≡ proofLcomp P'≤VP P≤MQ)
    -}

module Convert {C : Category _ _} (F : Functor (C ^op) (POSET _ _ )) where 
  open import HyperDoc.Syntax
  open import Cubical.Categories.Displayed.Base 
  open Categoryᴰ
  open HDSyntax F  

  Cᴰ : Categoryᴰ C _ _ 
  ob[ Cᴰ ] = F∣_∣
  Cᴰ .Hom[_][_,_] {x}{y} f Fx Fy = x ◂ Fx ≤ f* f Fy
  Cᴰ .idᴰ = eqTo≤  (sym f*id)
  Cᴰ ._⋆ᴰ_ {f = f} {g} = seq* f g
  Cᴰ .⋆IdLᴰ fᴰ = toPathP (isProp≤ _ fᴰ)
  Cᴰ .⋆IdRᴰ fᴰ = toPathP (isProp≤ _ fᴰ)
  Cᴰ .⋆Assocᴰ _ _ _ = toPathP (isProp≤ _ _)
  Cᴰ .isSetHomᴰ = isProp→isSet isProp≤ 
    
module ConvertLogic 
  {ℓV ℓV' ℓC ℓC' ℓG ℓG' ℓL : Level}
  {M : CBPVModel ℓV ℓV' ℓC ℓC' ℓG ℓG'}
  {L : CBPVLogic M } where
 --  (LR : CBPVRelLogic' L) where 

  open import HyperDoc.Syntax
  open import Cubical.Categories.Displayed.Base 
  open import Cubical.Categories.Displayed.Functor
  open import Cubical.Categories.Displayed.BinProduct
  open import Cubical.Categories.Bifunctor

  open Bifunctor
  open Categoryᴰ
  open Functorᴰ
  open CBPVLogic L
  -- open CBPVRelLogic' LR 


  Vᴰ = Convert.Cᴰ (LV)
  Cᴰ = Convert.Cᴰ (LC)

    
  open CBPVModelSyntax M
  open import Cubical.Data.Unit

  open MonFun renaming (f to fun)
  open BifunctorSepᴰ
  Oᴰ : BifunctorSepᴰ (M .snd .snd) (Vᴰ ^opᴰ) Cᴰ (GRAPHᴰ _ _ _ _ )
  Oᴰ .Bif-obᴰ {A} {B} P Q .fst M = (A LV.◂ P ≤ (pull M $ Q)) , isProp→isSet LV.isProp≤ 
  -- do we need any interesting displayed edge relation?
  Oᴰ .Bif-obᴰ _ _ .snd _ _ _  = Unit , isSetUnit
  Oᴰ .Bif-homLᴰ P'≤VP Q .fst M P≤MQ = proofLcomp P'≤VP P≤MQ
  Oᴰ .Bif-homLᴰ _ _  .snd _ _ _  = tt
  Oᴰ .Bif-L-idᴰ = toPathP (Σ≡Prop (λ x → isPropImplicitΠ3 λ _ _ _ → isPropΠ3 λ _ _ _ → isPropUnit) (funExt λ _ → funExt λ _ → LV.isProp≤ _ _))
  Oᴰ .Bif-L-seqᴰ _ _ = toPathP (Σ≡Prop (λ x → isPropImplicitΠ3 λ _ _ _ → isPropΠ3 λ _ _ _ → isPropUnit) (funExt λ _ → funExt λ _ → LV.isProp≤ _ _))
  Oᴰ .Bif-homRᴰ Q≤SQ' _ .fst _ P≤MQ = proofRcomp P≤MQ Q≤SQ' 
  Oᴰ .Bif-homRᴰ _ _ .snd _ _ _  = tt
  Oᴰ .Bif-R-idᴰ = toPathP (Σ≡Prop (λ x → isPropImplicitΠ3 λ _ _ _ → isPropΠ3 λ _ _ _ → isPropUnit) (funExt λ _ → funExt λ _ → LV.isProp≤ _ _))
  Oᴰ .Bif-R-seqᴰ _ _ = toPathP (Σ≡Prop (λ x → isPropImplicitΠ3 λ _ _ _ → isPropΠ3 λ _ _ _ → isPropUnit) (funExt λ _ → funExt λ _ → LV.isProp≤ _ _))
  Oᴰ .SepBif-RL-commuteᴰ _ _ = toPathP (Σ≡Prop (λ x → isPropImplicitΠ3 λ _ _ _ → isPropΠ3 λ _ _ _ → isPropUnit) (funExt λ _ → funExt λ _ → LV.isProp≤ _ _))

  Mᴰ : CBPVModelᴰ M  _ _ _ _ _ _ 
  Mᴰ .fst = Vᴰ
  Mᴰ .snd .fst = Cᴰ
  Mᴰ .snd .snd = Oᴰ

module LogicStruct 
  {M : CBPVModel _ _ _ _ _ _ }
  {L : CBPVLogic M} where 
  open import HyperDoc.Operational.TypeStructure

  open TypeStructure M
  open CBPVLogic L
  open CBPVModelSyntax M
  open import HyperDoc.Connectives.Connectives
  open import Cubical.Categories.Instances.Preorders.Monotone
  open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint

  open MonFun renaming (f to fun)

  HasFTyᴸ : Type 
  HasFTyᴸ = 
    ({A : ob V}{B : ob C}(M : O'[ A , B ]) → HasLeftAdj (pull M)) 

  Has𝟙ᴸ : Type 
  Has𝟙ᴸ = L⊤.Has⊤ LV

  Has×ᴸ : Type 
  Has×ᴸ = L∧.Has∧ LV × L∃.Has∃ LV

  Has+ᴸ : Type 
  Has+ᴸ = L∨.Has∨ LV × L∃.Has∃ LV 


{-}
  test : {X : hProp _}{x y : ⟨ X ⟩}(p q : x ≡ y) → p ≡ q 
  test {X}{x}{y} p q  = 
    sym (isProp→isContrPath (X .snd) x y .snd p) ∙ isProp→isContrPath (X .snd) x y  .snd q

  Oᴰ : BifunctorSepᴰ (M .snd .snd) (Vᴰ ^opᴰ) Cᴰ (GRAPHᴰ _ _ _ _ )
  Oᴰ .Bif-obᴰ {A} {B} P Q .fst M = (A LV.◂ P ≤ (pull M $ Q)) , isProp→isSet LV.isProp≤ 
  -- Graph of antired
  Oᴰ .Bif-obᴰ {A} {B} P Q .snd {M}{M'} M↦M' P≤MQ P≤M'Q =
     (antired M↦M' P≤M'Q ≡ P≤MQ) , isProp→isSet λ x y  → test {X = (A LV.◂ P ≤ (pull M $ Q)) , LV.isProp≤} x y
     -- test {X = {!   !}} x y
  Oᴰ .Bif-homLᴰ {A} {A'} {V} {P} {P'} P'≤VP {B} Q .fst M P≤MQ = proofLcomp P'≤VP P≤MQ
  Oᴰ .Bif-homLᴰ {A} {A'} {V} {P} {P'} P'≤VP {B} Q .snd {M}{M'}{M↦M'} P≤MQ P≤M'Q lrel = 
    {!   isProp→isContrPath LV.isProp≤  _ _  .snd lrel !}
  Oᴰ .Bif-L-idᴰ = toPathP (Σ≡Prop (λ x → isPropImplicitΠ3 λ _ _ _ → isPropΠ3 λ _ _ _ → test {X = _ , LV.isProp≤}) ((funExt λ _ → funExt λ _ → LV.isProp≤ _ _)))
  Oᴰ .Bif-L-seqᴰ _ _ = toPathP (Σ≡Prop (λ x → isPropImplicitΠ3 λ _ _ _ → isPropΠ3 λ _ _ _ → test {X = _ , LV.isProp≤}) ((funExt λ _ → funExt λ _ → LV.isProp≤ _ _)))
  Oᴰ .Bif-homRᴰ = {!   !}
  Oᴰ .Bif-R-idᴰ = toPathP (Σ≡Prop (λ x → isPropImplicitΠ3 λ _ _ _ → isPropΠ3 λ _ _ _ → test {X = _ , LV.isProp≤}) ((funExt λ _ → funExt λ _ → LV.isProp≤ _ _)))
  Oᴰ .Bif-R-seqᴰ _ _ = toPathP (Σ≡Prop (λ x → isPropImplicitΠ3 λ _ _ _ → isPropΠ3 λ _ _ _ → test {X = _ , LV.isProp≤}) ((funExt λ _ → funExt λ _ → LV.isProp≤ _ _)))
  Oᴰ .SepBif-RL-commuteᴰ _ _ = toPathP (Σ≡Prop (λ x → isPropImplicitΠ3 λ _ _ _ → isPropΠ3 λ _ _ _ → test {X = _ , LV.isProp≤}) ((funExt λ _ → funExt λ _ → LV.isProp≤ _ _)))

  -}

 {-} {-}
  Fib : {A : ob V}{B : ob C}(M : O'[ A , B ]) → Type 
  Fib {A}{B} M = Σ[ P ∈ LV.F∣ A ∣ ] Σ[ Q ∈ LC.F∣ B ∣ ] (A LV.◂ P ≤ (pull M $ Q))
  -}
  open import Cubical.Categories.Displayed.Base
  open Categoryᴰ
  open import Cubical.Categories.Instances.Preorders.Base
  open import Cubical.Relation.Binary.Preorder
  open PreorderStr -}
  -- a local fibration
  {-}
  Fib :  (A : ob V)(B : ob C) → Functor ((FreeCat O[ A , B ]) ^op) (PREORDER  _ _) 
  Fib A B .F-ob M .fst .fst = Σ[ P ∈ LV.F∣ A ∣ ] Σ[ Q ∈ LC.F∣ B ∣ ] (A LV.◂ P ≤ (pull M $ Q))
  Fib A B .F-ob M .fst .snd ._≤_ (P , Q , φ)(P' , Q' , ψ) = 
    Σ[ P≤P' ∈ A LV.◂ P ≤ P' ]  
    Σ[ Q'≤Q ∈ B LC.◂ Q' ≤ Q ] {! LV.seq ? ?   !}
  Fib A B .F-ob M .fst .snd .isPreorder = {!   !}
  Fib A B .F-ob M .snd = {!   !}
  Fib A B .F-hom = {!   !}
  Fib A B .F-id = {!   !}
  Fib A B .F-seq = {!   !}
  -}
  {-}
  Fib :  (A : ob V)(B : ob C) → Categoryᴰ (FreeCat O[ A , B ]) _ _ 
  ob[ Fib A B ] M = Σ[ P ∈ LV.F∣ A ∣ ] Σ[ Q ∈ LC.F∣ B ∣ ] (A LV.◂ P ≤ (pull M $ Q))
  Fib A B .Hom[_][_,_] {M}{M'} M↦M'  (P , Q , φ)(P' , Q' , ψ) = {!   !}
  Fib A B .idᴰ = {!   !}
  Fib A B ._⋆ᴰ_ = {!   !}
  Fib A B .⋆IdLᴰ = {!   !}
  Fib A B .⋆IdRᴰ = {!   !}
  Fib A B .⋆Assocᴰ = {!   !}
  Fib A B .isSetHomᴰ = {!   !} -}

{-
record CBPVRelLogic {ℓV ℓV' ℓC ℓC' ℓG ℓG' : Level}
    {M : CBPVModel ℓV ℓV' ℓC ℓC' ℓG ℓG'}
    (L : CBPVLogic M): Type where 
  open CBPVModelSyntax M 
  open CBPVLogic L 
  field 
    --- graph of a reindexing operation
    {-
        reindex :
      ∀ {A B}
        {M M' : O'[ A , B ]}
      → Edge[ M , M' ]
      → Fib M' → Fib M

    reindex-mon :
      ∀ {e φ φ'}
      → φ ≤Fib φ'
      → reindex e φ ≤Fib reindex e φ'
    -}
    LRel : ∀ {A B P Q}{M M' : O'[ A , B ]} → Edge[ M , M' ] → 
      A LV.◂ P ≤ (pull M $ Q) → A LV.◂ P ≤ (pull M' $ Q) → hProp _

  Rel[_][_,_]  : ∀ {A B P Q}{M M' : O'[ A , B ]} → Edge[ M , M' ] → 
    A LV.◂ P ≤ (pull M $ Q) → A LV.◂ P ≤ (pull M' $ Q) → Type 
  Rel[_][_,_] e φ ψ = ⟨ LRel e φ ψ ⟩ 
  
  field 
    RelLComp : ∀ {A A' B P P' Q V M M'}
      {φ : A LV.◂ P ≤ (pull M $ Q)}
      {φ' : A LV.◂ P ≤ (pull M' $ Q)}
      {ψ : A' LV.◂ P' ≤ LV.f* V P} → 
      (e : Edge[ M , M' ]) → 
      Rel[ e ][ φ , φ' ] → 
      -----------------------------
      Rel[ O .Bif-homL V B .snd e ][ (proofLcomp ψ φ) , (proofLcomp ψ φ') ]
    RelRComp : ∀ {A B B' P Q Q' S M M'}
      {φ : A LV.◂ P ≤ (pull M $ Q)}
      {φ' : A LV.◂ P ≤ (pull M' $ Q)}
      {ψ : B LC.◂ Q ≤ LC.f* {c' = B'} S Q'} → 
      (e : Edge[ M , M' ]) → 
      Rel[ e ][ φ , φ' ] → 
      -----------------------------
      Rel[ O .Bif-homR A S .snd e ][ (proofRcomp φ ψ) , (proofRcomp φ' ψ) ]

module LogicStruct 
  {M : CBPVModel _ _ _ _ _ _ }
  {L : CBPVLogic M }
  (LR : CBPVRelLogic L) where 
  open import HyperDoc.Operational.TypeStructure

  open TypeStructure M
  open CBPVLogic L
  open CBPVRelLogic LR
  open CBPVModelSyntax M
  open import HyperDoc.Connectives.Connectives
  open import Cubical.Categories.Instances.Preorders.Monotone
  open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint

  open MonFun renaming (f to fun)

  module _ (hasUTy : HasUTy) where 
    open UTySyntax hasUTy
    HasUTyᴸ : Type 
    HasUTyᴸ = 
      (∀ {A B}{M : O'[ A , B ]}{Q : LC.F∣ B ∣} → A LV.◂ pull M $ Q ≤ (pull (force (thunk M)) $ Q)) 
      × 
      (∀ {A B P Q}{M : O'[ A , B ]} → (
        (φ : A LV.◂ P ≤ (pull (force (thunk M)) $ Q)) →
        (ψ : A LV.◂ P ≤ (pull M $ Q)) → 
        -----------------------------------
        Rel[ Uβ M ][ φ , ψ ]))

  module _ (hasFTy : HasFTy) where 
    open FTySyntax hasFTy
    HasFTyᴸ : Type 
    HasFTyᴸ = 
      ({A : ob V}{B : ob C}(M : O'[ A , B ]) → HasLeftAdj (pull M)) 
      × (∀ {A B}{M : O'[ A , B ]}{Q : LC.F∣ B ∣} → A LV.◂ (pull M) $ Q ≤ (pull (O .Bif-homR A (bind M) .fst (ret (C .id))) $ Q))
      × (∀ {A B P Q}{M : O'[ A , B ]} → 
        (φ : A LV.◂ P ≤ ((pull (ret (bind M))) $ Q)) →
        (ψ : A LV.◂ P ≤ (pull M $ Q)) → 
        Rel[ Fβ M ][ φ , ψ ] )


  Has𝟙ᴸ : Type 
  Has𝟙ᴸ = L⊤.Has⊤ LV

  Has×ᴸ : Type 
  Has×ᴸ = L∧.Has∧ LV × L∃.Has∃ LV

  module _ (has+ : Has+) where

    record Has+ᴸ' : Type where 
      open Has+'
      field 
        anti-1 : ∀ {A A' B}{M : O'[ A , B ]}{M' : O'[ A' , B ]}{Q : LC.F∣ B ∣} → 
          A LV.◂ pull M $ Q ≤ (pull (O .Bif-homL  (σ₁ (has+ A A')) B .fst (match (has+ A A') .N-ob B (M , M')))  $ Q)
        anti-2 : ∀ {A A' B}{M : O'[ A , B ]}{M' : O'[ A' , B ]}{Q : LC.F∣ B ∣} → 
          A' LV.◂ pull M' $ Q ≤ (pull (O .Bif-homL  (σ₂ (has+ A A')) B .fst (match (has+ A A') .N-ob B (M , M')))  $ Q)
        edge-1 : ∀ {A A' B P Q}{M : O'[ A , B ]}{N : O'[ A' , B ]} → 
          (φ : A LV.◂ P ≤ (pull (O .Bif-homL  (σ₁ (has+ A A')) B .fst (match (has+ A A') .N-ob B (M , N)))  $ Q)) →
          (ψ : A LV.◂ P ≤ (pull M $ Q)) → 
          Rel[ +β₁ (has+ A A') M N ][ φ , ψ ]
        edge-2 : ∀ {A A' B P Q}{M : O'[ A , B ]}{N : O'[ A' , B ]} → 
          (φ : A' LV.◂ P ≤ (pull (O .Bif-homL  (σ₂ (has+ A A')) B .fst (match (has+ A A') .N-ob B (M , N)))  $ Q)) →
          (ψ : A' LV.◂ P ≤ (pull N $ Q)) → 
          Rel[ +β₂ (has+ A A') M N ][ φ , ψ ]

    Has+ᴸ : Type 
    Has+ᴸ = L∨.Has∨ LV × L∃.Has∃ LV × Has+ᴸ' 


module Reindex
  {M N : CBPVModel _ _ _ _  _ _ }
  (F : CBPVMorphism M N)
  {L : CBPVLogic N}
  (LR : CBPVRelLogic L) where 
  open import HyperDoc.Operational.TypeStructure
  private 
    module M = CBPVModelSyntax M
    module N = CBPVModelSyntax N
    module L = CBPVLogic L
    module TSM = TypeStructure M
    module TSN = TypeStructure N


  open CBPVMorphismSyntax F

  LV' : Functor (M.V ^op) (POSET ℓ-zero ℓ-zero) 
  LV' = L.LV ∘F (FV ^opF)

  LC' : Functor (M.C ^op) (POSET ℓ-zero ℓ-zero) 
  LC' = L.LC ∘F (FC ^opF)

  LSq' : NatTrans (FORGET ∘F M.OPar) (Hom^op M ∘F (LV' ×F ((LC' ^opF) ∘F to^op^op)))
  LSq' = seqTrans (FORGET ∘ʳ FO) (seqTrans F-assocl (seqTrans (L.LSq ∘ˡ ((FV ^opF) ×F FC)) dumb)) where 
    dumb : 
      NatTrans
      ((Hom^op N ∘F (L.LV ×F ((L.LC ^opF) ∘F to^op^op))) ∘F
      ((FV ^opF) ×F FC))
      (Hom^op M ∘F (LV' ×F ((LC' ^opF) ∘F to^op^op)))
    dumb .N-ob x z = z
    dumb .N-hom _ = refl

  reindex : CBPVLogic M 
  reindex .CBPVLogic.LV = LV'
  reindex .CBPVLogic.LC = LC'
  reindex .CBPVLogic.LSq = LSq'

  module L' = CBPVLogic reindex

  reindexLR : CBPVRelLogic reindex 
  reindexLR .CBPVRelLogic.LRel {M}{M'} MRM' = LR .CBPVRelLogic.LRel (N-ob (F .snd .snd) (M , M') .snd MRM')
  reindexLR .CBPVRelLogic.RelLComp 
    {A}{A'}{B}{P}{P'}{Q}{V}{M}{M'}{P≤MQ}{P≤M'P}{P'≤VP} M↦M' R[M↦M'][P≤MQ,P≤M'Q] = goal where 
      have : {!   !} 
      have = (L.proofLcomp P'≤VP P≤MQ)


      have' : {!   !} 
      have' = {! (L.proofLcomp P'≤VP P≤MQ)  !}
      goal : ⟨ LR .CBPVRelLogic.LRel
              (N-ob (F .snd .snd) (A' , B) .snd (M.O .Bif-homL V B .snd M↦M'))
              (L'.proofLcomp P'≤VP P≤MQ) 
              (L'.proofLcomp P'≤VP P≤M'P)
              ⟩
      goal = {! (L.proofLcomp P'≤VP P≤MQ)   !}

  reindexLR .CBPVRelLogic.RelRComp = {!   !}

  module LS = LogicStruct LR 
  module LS' = LogicStruct reindexLR 

  module _ (has𝟙ᴸ : LS.Has𝟙ᴸ) where
    pres𝟙ᴸ  : LS'.Has𝟙ᴸ
    pres𝟙ᴸ  = (λ c → has𝟙ᴸ .fst (F-ob (FV ^opF) c)) ,
      (λ {c} {c'} f → has𝟙ᴸ .snd (F-hom (FV ^opF) f))
  

  -- now we need stict preservation of structure ?
  module _ (hasUTy : TSN.HasUTy)(x : LS.HasUTyᴸ hasUTy) where
    -- no.. 
    presUTy : TSM.HasUTy
    presUTy = {!   !}

    presUTyᴸ : LS'.HasUTyᴸ presUTy
    presUTyᴸ .fst = {! x .fst  !}
    presUTyᴸ .snd = {!   !}



module Convert {C : Category _ _} (F : Functor (C ^op) (POSET _ _ )) where 
  open import HyperDoc.Syntax
  open import Cubical.Categories.Displayed.Base 
  open Categoryᴰ
  open HDSyntax F  

  Cᴰ : Categoryᴰ C _ _ 
  ob[ Cᴰ ] = F∣_∣
  Cᴰ .Hom[_][_,_] {x}{y} f Fx Fy = x ◂ Fx ≤ f* f Fy
  Cᴰ .idᴰ = eqTo≤  (sym f*id)
  Cᴰ ._⋆ᴰ_ {f = f} {g} = seq* f g
  Cᴰ .⋆IdLᴰ fᴰ = toPathP (isProp≤ _ fᴰ)
  Cᴰ .⋆IdRᴰ fᴰ = toPathP (isProp≤ _ fᴰ)
  Cᴰ .⋆Assocᴰ _ _ _ = toPathP (isProp≤ _ _)
  Cᴰ .isSetHomᴰ = isProp→isSet isProp≤ 
    
module ConvertLogic 
  {ℓV ℓV' ℓC ℓC' ℓG ℓG' ℓL : Level}
  {M : CBPVModel ℓV ℓV' ℓC ℓC' ℓG ℓG'}
  {L : CBPVLogic M }
  (LR : CBPVRelLogic L) where 

  open import HyperDoc.Syntax
  open import Cubical.Categories.Displayed.Base 
  open import Cubical.Categories.Displayed.Functor
  open import Cubical.Categories.Displayed.BinProduct
  open import Cubical.Categories.Bifunctor

  open Bifunctor
  open Categoryᴰ
  open Functorᴰ
  open CBPVLogic L
  open CBPVRelLogic LR 


  Vᴰ = Convert.Cᴰ (LV)
  Cᴰ = Convert.Cᴰ (LC)

    
  open CBPVModelSyntax M

  open MonFun renaming (f to fun)
  open BifunctorSepᴰ

  Oᴰ : BifunctorSepᴰ (M .snd .snd) (Vᴰ ^opᴰ) Cᴰ (GRAPHᴰ _ _ _ _ )
  Oᴰ .Bif-obᴰ {A} {B} P Q .fst M = (A LV.◂ P ≤ (pull M $ Q)) , isProp→isSet LV.isProp≤ 
  Oᴰ .Bif-obᴰ {A} {B} P Q .snd {M}{M'} M↦M' P≤MQ P≤M'Q = Rel[ M↦M' ][ P≤MQ , P≤M'Q ] , isProp→isSet (LRel M↦M' P≤MQ P≤M'Q .snd)
  Oᴰ .Bif-homLᴰ  P'≤VP _ .fst _ P≤MQ = proofLcomp P'≤VP P≤MQ 
  Oᴰ .Bif-homLᴰ {A}{A'}{V}{P}{P'} P'≤VP {B} Q .snd {M}{M'}{M↦M'} P≤MQ P≤M'Q lrel = goal where 

    have : Rel[ M↦M' ][ P≤MQ , P≤M'Q ] 
    have = lrel
    goal : Rel[ O .Bif-homL V B .snd M↦M' ][ proofLcomp P'≤VP P≤MQ , proofLcomp P'≤VP P≤M'Q ] 
    goal = RelLComp M↦M' lrel

  Oᴰ .Bif-L-idᴰ = toPathP (Σ≡Prop (λ x → isPropImplicitΠ3 λ _ _ _ → isPropΠ3 λ _ _ _ → LRel (M .snd .snd .Bif-L-id i1 .snd _) (x _ _) (x _ _) .snd) ((funExt λ _ → funExt λ _ → LV.isProp≤ _ _)))
  Oᴰ .Bif-L-seqᴰ _ _ = toPathP (Σ≡Prop (λ x → isPropImplicitΠ3 λ _ _ _ → isPropΠ3 λ _ _ _ → LRel (M .snd .snd .Bif-L-id i1 .snd _) (x _ _) (x _ _) .snd) ((funExt λ _ → funExt λ _ → LV.isProp≤ _ _)))
  Oᴰ .Bif-homRᴰ Q≤SQ' _ .fst _ P≤MQ = proofRcomp P≤MQ Q≤SQ' 
  Oᴰ .Bif-homRᴰ _ _ .snd {M}{M'}{M↦M'} _ _ lrel = RelRComp M↦M' lrel
  Oᴰ .Bif-R-idᴰ = toPathP (Σ≡Prop (λ x → isPropImplicitΠ3 λ _ _ _ → isPropΠ3 λ _ _ _ → LRel (M .snd .snd .Bif-L-id i1 .snd _) (x _ _) (x _ _) .snd) ((funExt λ _ → funExt λ _ → LV.isProp≤ _ _)))
  Oᴰ .Bif-R-seqᴰ _ _ = toPathP (Σ≡Prop (λ x → isPropImplicitΠ3 λ _ _ _ → isPropΠ3 λ _ _ _ → LRel (M .snd .snd .Bif-L-id i1 .snd _) (x _ _) (x _ _) .snd) ((funExt λ _ → funExt λ _ → LV.isProp≤ _ _)))
  Oᴰ .SepBif-RL-commuteᴰ _ _ = toPathP (Σ≡Prop (λ x → isPropImplicitΠ3 λ _ _ _ → isPropΠ3 λ _ _ _ → LRel (M .snd .snd .Bif-L-id i1 .snd _) (x _ _) (x _ _) .snd) ((funExt λ _ → funExt λ _ → LV.isProp≤ _ _)))
  
  Mᴰ : CBPVModelᴰ M  _ _ _ _ _ _ 
  Mᴰ .fst = Vᴰ
  Mᴰ .snd .fst = Cᴰ
  Mᴰ .snd .snd = Oᴰ

  open import HyperDoc.Operational.TypeStructure
  open TypeStructureᴰ Mᴰ
  open TypeStructure M
  open import Cubical.Categories.Displayed.NaturalTransformation
  open NatTransᴰ
  open LogicStruct LR
  open import Cubical.Data.Unit
  open import HyperDoc.Connectives.Connectives 

  module 𝟙TyDep (has𝟙 : Has𝟙)(has𝟙ᴸ : Has𝟙ᴸ) where 
    open L⊤
    open HA 
    has𝟙ᴰ : Has𝟙ᴰ has𝟙 
    has𝟙ᴰ .fst = top (has𝟙ᴸ .fst (has𝟙 .fst))
    has𝟙ᴰ .snd .N-obᴰ {A} P tt tt = goal where 
      goal : A LV.◂ P ≤ LV.f* (N-ob (has𝟙 .snd) A tt) (has𝟙ᴰ .fst)
      goal = LV.seq (top-top (has𝟙ᴸ .fst A)) {! has𝟙ᴸ .snd  !} -- use preservation of top by reindexing
    has𝟙ᴰ .snd .N-homᴰ {A}{A'}{V}{P}{P'} P'≤VP = toPathP (funExt λ _ → funExt λ _ → LV.isProp≤ _ _)

  module ×TyDep (has× : Has×)((has×ᴸ , has∃ᴸ) : Has×ᴸ) where 

    open ×TySyntax has× 
    open L∧ 
    open L∃ 
    open ∃Syntax {L = LV} has∃ᴸ
    open HA renaming (_∧_ to _∧ⱽ_)

    δ : {A : ob V} → V [ A , A ⊗ A ] 
    δ {A} = V .id ,p V .id

    _⋀ⱽ_ : {A : ob V} → LV.F∣ A ∣ → LV.F∣ A ∣ → LV.F∣ A ∣ 
    _⋀ⱽ_ {A} = has×ᴸ .fst A ._∧ⱽ_

    _⋀ᴰ_ : {A A' : ob V} → LV.F∣ A ∣ → LV.F∣ A' ∣ → LV.F∣ A ⊗ A' ∣ 
    _⋀ᴰ_ {A}{A'} P P' = LV.f* (δ{A ⊗ A'}) {!   !} where 
      -- ∃f {f = hrm}  (LV.f* hrm {!   !} ⋀ⱽ {!   !})  where 

      hrm : V [ (A ⊗ A') ⊗ (A ⊗ A') , A ⊗ A' ] 
      hrm =  {! ∃f {f = δ{A}}!}    

      foo : {!   !} 
      foo = {! has∃ᴸ hrm .fst  !}
      -- ∃f ({!  P !} ⋀ⱽ P')
      -- LV.f* {! ∃f ?!} P ⋀ⱽ LV.f* {!  _,p_ !} P'
      -- we don't have these maps .. V [ A ⊗ A' , A ] , V [ A ⊗ A' , A' ]
    -- need the other LR defintion using exists and eq 

    has×ᴰ : Has×ᴰ has× 
    has×ᴰ {A} {A'} P P' .fst = P ⋀ᴰ P'
    has×ᴰ {A} {A'} P P' .snd .N-obᴰ {A''} P'' (V , W) (P''≤VP , P''≤WP') = {!   !}
    has×ᴰ {A} {A'} P P' .snd .N-homᴰ {X}{Y}{V}{Xᴰ}{Yᴰ} Yᴰ≤VXᴰ = toPathP (funExt λ _ → funExt λ _ → LV.isProp≤ _ _)

  
  module +TyDep (has+ : Has+)((has+ᴸ , has∃ᴸ , anti) : Has+ᴸ has+ ) where 

    --open +TySyntax has+
    open L∨
    open L∃ 
    open ∃Syntax {L = LV} has∃ᴸ
    open HA renaming (_∨_ to _∨ⱽ_)
    open Has+'
    open Has+ᴸ'

    _⋁ⱽ_ : {A : ob V} → LV.F∣ A ∣ → LV.F∣ A ∣ →   LV.F∣ A ∣
    _⋁ⱽ_ {A} = _∨ⱽ_ {P = LV .F-ob A}(has+ᴸ .fst A) 

    ⋁ⱽ-intro₁ : {A  : ob V}{P Q : Vᴰ .ob[_] A} → 
      A LV.◂ P ≤ (P ⋁ⱽ Q)
    ⋁ⱽ-intro₁ {A}{P}{Q} = or-intro1 ((has+ᴸ .fst A)) {P = P}{P}{Q} LV.id⊢

    ⋁ⱽ-intro₂  : {A  : ob V}{P Q : Vᴰ .ob[_] A} → 
      A LV.◂ P ≤ (Q ⋁ⱽ P)
    ⋁ⱽ-intro₂ {A}{P}{Q} = or-intro2 ((has+ᴸ .fst A)) {P = P}{Q}{P} LV.id⊢


    ⋁ⱽ-elim : {A  : ob V}{P R Q : Vᴰ .ob[_] A} → 
      A LV.◂ P ≤ R  → 
      A LV.◂ Q ≤ R  →
      A LV.◂ (P ⋁ⱽ Q) ≤ R 
    ⋁ⱽ-elim {A} = or-elim  (has+ᴸ .fst A)

    _⋀ᴰ_ : {A A' : ob V} → LV.F∣ A ∣ → LV.F∣ A' ∣ → LV.F∣ A+A' (has+ A A') ∣ 
    _⋀ᴰ_ {A}{A'} P P' = ∃f {f = σ₁ ((has+ A A'))} P ⋁ⱽ ∃f {f = σ₂ ((has+ A A'))} P'

    has+ᴰ : Has+ᴰ has+
    has+ᴰ Aᴰ A'ᴰ .TypeStructureᴰ.Has+'ᴰ.Aᴰ+A'ᴰ = Aᴰ ⋀ᴰ A'ᴰ
    has+ᴰ {A}{A'} Aᴰ A'ᴰ .TypeStructureᴰ.Has+'ᴰ.matchᴰ .N-obᴰ {B} Bᴰ (M , N) (Aᴰ≤MBᴰ , A'ᴰ≤NBᴰ)  = goal where 
      module adj₁ =  AdjSyntax (has∃ᴸ (σ₁ (has+ A A')))
      module adj₂ =  AdjSyntax (has∃ᴸ (σ₂ (has+ A A')))

      sub1 : A LV.◂  Aᴰ ≤ LV.f* (σ₁ (has+ A A')) (pull (match (has+ A A') .N-ob B (M , N)) $ Bᴰ) 
      sub1 = LV.seq Aᴰ≤MBᴰ (LV.seq (anti-1 anti) VM*→V*M*)

      sub2 : A' LV.◂  A'ᴰ ≤ LV.f* (σ₂ (has+ A A')) (pull (match (has+ A A') .N-ob B (M , N)) $ Bᴰ) 
      sub2 = LV.seq A'ᴰ≤NBᴰ (LV.seq (anti-2 anti) VM*→V*M*)


      goal : (A+A' (has+ A A')) LV.◂ Aᴰ ⋀ᴰ A'ᴰ ≤ (pull (match ((has+ A A')) .N-ob  B (M , N)) $ Bᴰ)
      goal =  ⋁ⱽ-elim {TypeStructure.Has+'.A+A' (has+ A A')}{fun adj₁.L Aᴰ}{fun (pull (N-ob (TypeStructure.Has+'.match (has+ A A')) B (M , N)))
        Bᴰ}{fun adj₂.L A'ᴰ} (adj₁.RtoL sub1) (adj₂.RtoL sub2)
    has+ᴰ Aᴰ A'ᴰ .TypeStructureᴰ.Has+'ᴰ.matchᴰ .N-homᴰ _ = funExt λ _ → funExt λ _ → toPathP (LV.isProp≤ _ _)
    has+ᴰ {A}{A'} Aᴰ A'ᴰ .TypeStructureᴰ.Has+'ᴰ.σ₁ᴰ = goal where 
      open AdjSyntax (has∃ᴸ (σ₁ (has+ A A')))
      goal : A LV.◂ Aᴰ ≤ LV.f* (σ₁ (has+ A A'))  (Aᴰ ⋀ᴰ A'ᴰ) 
      goal = LtoR ⋁ⱽ-intro₁
    has+ᴰ {A}{A'} Aᴰ A'ᴰ .TypeStructureᴰ.Has+'ᴰ.σ₂ᴰ = goal where 
      open AdjSyntax (has∃ᴸ (σ₂ (has+ A A')))
      goal : A' LV.◂ A'ᴰ ≤ LV.f* (σ₂ (has+ A A')) (Aᴰ ⋀ᴰ A'ᴰ) 
      goal = LtoR ⋁ⱽ-intro₂
    has+ᴰ {A}{A'} Aᴰ A'ᴰ .TypeStructureᴰ.Has+'ᴰ.+β₁ᴰ {B}{Bᴰ}{M}{M'}{e} Aᴰ≤MBᴰ A'ᴰ≤M'Bᴰ = edge-1 {! anti  !} _ _
      -- edge-1 {! anti !} _ Aᴰ≤MBᴰ
    has+ᴰ {A}{A'} Aᴰ A'ᴰ .TypeStructureᴰ.Has+'ᴰ.+β₂ᴰ {B}{Bᴰ}{M}{M'}{e} Aᴰ≤MBᴰ A'ᴰ≤M'Bᴰ = edge-2 {!   !} _ _ 

  module UTyDep (hasUTy : HasUTy)(hasUTyᴸ : HasUTyᴸ hasUTy) where 

    open UTySyntax hasUTy
    {- holes dispatched with naturality
        force (subV V W) ≡ subC V (force W) -}
    hasUTyᴰ : HasUTyᴰ hasUTy
    hasUTyᴰ Bᴰ .WkRepresentationᴰ.repᴰ = pull (force (V .id)) $ Bᴰ
    hasUTyᴰ {B} Q .WkRepresentationᴰ.fwdᴰ .N-obᴰ {A} P V P≤!VQ = LV.seq P≤!VQ (LV.seq V*M*→VM* {!   !}) -- pull (subC V (force id)) ≡ pull (force V)
    hasUTyᴰ Bᴰ .WkRepresentationᴰ.fwdᴰ .N-homᴰ _ = toPathP (funExt λ x → funExt λ y → LV.isProp≤  _ _)
    hasUTyᴰ {B} Q .WkRepresentationᴰ.bkwdᴰ {A}{P} {M} P≤MQ = LV.seq P≤MQ (LV.seq (LV.seq (hasUTyᴸ  .fst) (LV.eqTo≤ {!   !})) VM*→V*M*)  -- pull (force (thunk M)) ≡ pull (subC (thunk M) (force id))
    hasUTyᴰ {B} Q .WkRepresentationᴰ.wkretractᴰ {A}{P}{M} P≤MQ = hasUTyᴸ .snd (hasUTyᴰ Q .WkRepresentationᴰ.fwdᴰ .N-obᴰ P
       (WkRepresentation.bkwd (hasUTy B) M)
       (hasUTyᴰ Q .WkRepresentationᴰ.bkwdᴰ P≤MQ)) P≤MQ

    {-
    hasUTyᴰ : HasUTyᴰ hasUTy
    hasUTyᴰ Bᴰ .WkRepresentationᴰ.repᴰ = pull (force (V .id)) $ Bᴰ
    hasUTyᴰ {B} Q .WkRepresentationᴰ.fwdᴰ .N-obᴰ {A} P V P≤!VQ = LV.seq P≤!VQ (LV.seq V*M*→VM* {!   !}) -- pull (subC V (force id)) ≡ pull (force V)
    {- 
  force-sub : ∀{A A' B}{V : A' ⊢v A}{W : A ⊢v U B} → 
    force (subV V W) ≡ subC V (force W) 
    -}
    hasUTyᴰ Bᴰ .WkRepresentationᴰ.fwdᴰ .N-homᴰ _ = toPathP (funExt λ x → funExt λ y → LV.isProp≤  _ _)
    hasUTyᴰ {B} Q .WkRepresentationᴰ.bkwdᴰ {A}{P} {M} P≤MQ = LV.seq P≤MQ (LV.seq (LV.seq (hasUTyᴸ  .fst) (LV.eqTo≤ {!   !})) VM*→V*M*)  -- pull (force (thunk M)) ≡ pull (subC (thunk M) (force id))
    {-
      have : A LV.◂ P ≤ fun (pull M) Q
      have = Mᴰ
      -- anti reduction
      need : A LV.◂ pull M $ Q ≤ (pull (O .Bif-homL (thunk M) B .fst (force (V .id))) $ Q) 
      need = LV.seq (hasUTyᴸ .fst) {!   !}

      goal : A LV.◂ P ≤ LV.f* (thunk M) (pull (force (V .id)) $ Q) 
      goal = LV.seq have (LV.seq need VM*→V*M*) -}
    hasUTyᴰ {B} Q .WkRepresentationᴰ.wkretractᴰ {A}{P}{M} P≤MQ = hasUTyᴸ .snd (hasUTyᴰ Q .WkRepresentationᴰ.fwdᴰ .N-obᴰ P
       (WkRepresentation.bkwd (hasUTy B) M)
       (hasUTyᴰ Q .WkRepresentationᴰ.bkwdᴰ P≤MQ)) P≤MQ
      -- lhs : A LV.◂ P ≤ fun (pull (force (thunk M))) Q
      -- lhs = hasUTyᴰ Q .WkRepresentationᴰ.fwdᴰ .N-obᴰ P (thunk M) (hasUTyᴰ Q .WkRepresentationᴰ.bkwdᴰ P≤MQ)

      --goal : Rel[ Uβ M ][ {!   !} , P≤MQ ] 
      --goal = hasUTyᴸ .snd {!   !} {!   !}
    -}

  module FTyDep (hasFTy : HasFTy)((hasFTyᴸ , anti , dumb) : HasFTyᴸ hasFTy) where
    open FTySyntax hasFTy 

    hasFTyᴰ : HasFTyᴰ hasFTy 
    hasFTyᴰ Aᴰ .WkRepresentationᴰ.repᴰ = hasFTyᴸ (ret (C .id)) .fst $ Aᴰ
    hasFTyᴰ {A} Aᴰ .WkRepresentationᴰ.fwdᴰ .N-obᴰ {B} Bᴰ S FᴰAᴰ≤retAᴰ = goal where 
      open AdjSyntax (hasFTyᴸ  (ret (C .id))) 
      goal : A  LV.◂ Aᴰ ≤ (pull (ret S) $ Bᴰ) 
      goal = LV.seq (LtoR FᴰAᴰ≤retAᴰ) (LV.eqTo≤ {!  !}) -- fun (pull (ret (C .id))) (LC.f* S Bᴰ) ≡ fun (pull (ret S)) Bᴰ
    hasFTyᴰ Aᴰ .WkRepresentationᴰ.fwdᴰ .N-homᴰ _ = toPathP (funExt λ x → funExt λ y → LV.isProp≤  _ _)
    hasFTyᴰ {A} Aᴰ .WkRepresentationᴰ.bkwdᴰ {B}{Bᴰ}{M} Aᴰ≤MBᴰ = goal where 
      open AdjSyntax (hasFTyᴸ  (ret (C .id))) 
      goal : F A  LC.◂ hasFTyᴸ (ret (C .id)) .fst $ Aᴰ ≤ LC.f* (bind M) Bᴰ 
      goal = RtoL (LV.seq Aᴰ≤MBᴰ (LV.seq anti MS*→M*S*))
    hasFTyᴰ Aᴰ .WkRepresentationᴰ.wkretractᴰ e = dumb _ e 


{-
{-       

 ktm-bind : ∀ {A  B} → (M : A ⊢c B) → F A LC.◂ hasPush ret .fst $ vty A ≤ LC.f* (bind M) (cty B)
        ktm-bind {A}{B} M = 
          pullToPush ret (
            LV.seq (ctm M) (
            LV.eqTo≤ goal)) where 

            goal  : MonFun.f (pull M) (cty B) ≡ pull ret .MonFun.f (LC.f* (bind M) (cty B))
            goal = cong (λ h → N-ob Sq (A , B) h .MonFun.f (cty B)) (sym Fβ ∙ cong₂ plug refl (sym subCId)) 
              ∙  (cong (λ h → h .MonFun.f (cty B))) (pullRComp (bind M) ret)
        

 -}


   --- (∀ {A B}{M M' : O'[ A , B ]}{MRM' : ⟨ O .Bif-ob  A B .snd  M M'  ⟩} → 
  --  ({!  LV .F-hom !} → {!   !} → hProp _ ))
{-
module CBPVLogicSyntax 
  {ℓV ℓV' ℓC ℓC' ℓG ℓG' ℓL : Level}
  {M : CBPVModel ℓV ℓV' ℓC ℓC' ℓG ℓG'}
  (L : CBPVLogic M ℓL ) where 

  open CBPVModelSyntax M

  LV = L .fst 
  LC = L .snd .fst 
  LSq = L .snd .snd .fst

  module LC = HDSyntax LC
  module LV = HDSyntax LV

  pull : {A : V .ob}{B : C .ob}(M : O'[ A , B ])  
    → MonFun (F-ob LC B .fst) (F-ob LV A .fst)
  pull {A} {B} M = LSq .N-ob (A , B) M

  pullComp : ∀ {A A' B B'}(V : V [ A' , A ])(S : C [ B , B' ])(M : O'[ A , B ]) → 
    pull (OPar .F-hom (V , S) .fst M) ≡ MonComp (LC .F-hom S) (MonComp (pull M) (LV .F-hom V))
  pullComp V S M = funExt⁻ (LSq .N-hom (V , S)) M

  pullLComp : ∀ {A A' B}(V : V [ A' , A ])(M : O'[ A , B ]) → 
    pull (O .Bif-homL V B .fst M) ≡ MonComp (pull M) (LV .F-hom V)
  pullLComp V M = {!   !}
    -- pullComp V (C .id) M  ∙ cong (λ h → MonComp h (MonComp (pull M) (LV .F-hom V))) (LC .F-id)
    -- Bif-L-id
    -- pullComp V (C .id) M  ∙ cong (λ h → MonComp h (MonComp (pull M) (LV .F-hom V))) (LC .F-id)

  pullRComp :  ∀ {A B B'}(S : C [ B , B' ])(M : O'[ A , B ]) → 
    pull (O .Bif-homR A S .fst M) ≡ MonComp (LC .F-hom S) (pull M)
  pullRComp S M = {!   !}
    -- eqMon _ _  (funExt λ Q' → λ i → {! LSq .N-hom (V .id , S) i M .MonFun.f Q'  !})
    -- pullComp (V .id) S M ∙ cong₂ MonComp refl (LV .F-id)

  V*M*→VM* : ∀ {A A' B}{V : V [ A , A' ]}{M : O'[ A' , B ]}{Q : LC.F∣ B ∣}  → 
    A LV.◂ LV.f* V (pull M $ Q) ≤ (pull (O .Bif-homL V B .fst M) $ Q) 
  V*M*→VM* = LV.eqTo≤ (cong₂ MonFun.f (sym (pullLComp _ _ )) refl)

  VM*→V*M*  : ∀ {A A' B}{V : V [ A , A' ]}{M : O'[ A' , B ]}{Q : LC.F∣ B ∣} →  
    A LV.◂ (pull (O .Bif-homL V B .fst M) $ Q) ≤ LV.f* V (pull M $ Q)
  VM*→V*M* = LV.eqTo≤ (cong₂ MonFun.f (pullLComp _ _ ) refl)

  MS*→M*S*  : ∀ {A B B'}{S : C [ B , B' ]}{M : O'[ A , B ]}{Q' : LC.F∣ B' ∣} →  
    A LV.◂ pull (O .Bif-homR A S .fst M) $ Q' ≤ MonFun.f (MonComp (LC .F-hom S) (pull M)) Q'
  MS*→M*S* = LV.eqTo≤ (cong₂ MonFun.f (pullRComp _ _ ) refl)

  M*S*→MS*  : ∀ {A B B'}{S : C [ B , B' ]}{M : O'[ A , B ]}{Q' : LC.F∣ B' ∣} →  
    A LV.◂ MonFun.f (MonComp (LC .F-hom S) (pull M)) Q' ≤ (pull (O .Bif-homR A S .fst M) $ Q')
  M*S*→MS* = LV.eqTo≤ (cong₂ MonFun.f (sym (pullRComp _ _ )) refl)


module Convert {C : Category _ _} (F : Functor (C ^op) (POSET _ _ )) where 
  open import HyperDoc.Syntax
  open import Cubical.Categories.Displayed.Base 
  open Categoryᴰ
  open HDSyntax F  

  Cᴰ : Categoryᴰ C _ _ 
  ob[ Cᴰ ] = F∣_∣
  Cᴰ .Hom[_][_,_] {x}{y} f Fx Fy = x ◂ Fx ≤ f* f Fy
  Cᴰ .idᴰ = eqTo≤  (sym f*id)
  Cᴰ ._⋆ᴰ_ {f = f} {g} = seq* f g
  Cᴰ .⋆IdLᴰ fᴰ = toPathP (isProp≤ _ fᴰ)
  Cᴰ .⋆IdRᴰ fᴰ = toPathP (isProp≤ _ fᴰ)
  Cᴰ .⋆Assocᴰ _ _ _ = toPathP (isProp≤ _ _)
  Cᴰ .isSetHomᴰ = isProp→isSet isProp≤ 

module ConvertLogic 
  {ℓV ℓV' ℓC ℓC' ℓG ℓG' ℓL : Level}
  {M : CBPVModel ℓV ℓV' ℓC ℓC' ℓG ℓG'}
  (L : CBPVLogic M ℓL ) where 

  open import HyperDoc.Syntax
  open import Cubical.Categories.Displayed.Base 
  open import Cubical.Categories.Displayed.Functor
  open import Cubical.Categories.Displayed.BinProduct
  open import Cubical.Categories.Bifunctor

  open Bifunctor
  open Categoryᴰ
  open Functorᴰ

  Vᴰ = Convert.Cᴰ (L .fst)
  Cᴰ = Convert.Cᴰ (L .snd .fst)

    
  open CBPVLogicSyntax L
  open CBPVModelSyntax M


  open MonFun renaming (f to fun)
  open BifunctorSepᴰ
  Oᴰ : BifunctorSepᴰ (M .snd .snd) (Vᴰ ^opᴰ) Cᴰ (GRAPHᴰ _ _ _ _ )
  Oᴰ .Bif-obᴰ {A} {B} P Q .fst M = (A LV.◂ P ≤ (pull M $ Q)) , isProp→isSet LV.isProp≤ 
  Oᴰ .Bif-obᴰ {A} {B} P Q .snd {M}{M'} M↦M' P≤MQ P≤M'Q = {!   !}
    -- A LV.◂ pull M' $ Q ≤ (pull M $ Q) , isProp→isSet LV.isProp≤
  Oᴰ .Bif-homLᴰ {A} {A'} {V}{P}{P'} P'≤VP {B} Q .fst M P≤MQ = 
    LV.seq  P'≤VP (
    LV.seq (LV.mon* V P≤MQ) (
    V*M*→VM*))
  Oᴰ .Bif-homLᴰ {A} {A'} {V}{P}{P'} P'≤VP {B} Q .snd {M}{M'}{M↦M'} P≤MQ P≤M'Q M'Q≤MQ = {!   !}    -- VMQ≤VMQ
  Oᴰ .Bif-L-idᴰ = toPathP (Σ≡Prop (λ x → isPropImplicitΠ3 λ _ _ _ → isPropΠ3 λ _ _ _ → LV.isProp≤)(funExt λ _ → funExt λ _ → LV.isProp≤ _ _))
  Oᴰ .Bif-L-seqᴰ _ _ = toPathP (Σ≡Prop (λ x → isPropImplicitΠ3 λ _ _ _ → isPropΠ3 λ _ _ _ → LV.isProp≤)(funExt λ _ → funExt λ _ → LV.isProp≤ _ _))
  Oᴰ .Bif-homRᴰ {B} {B'} {S}{Q}{Q'} Q≤SQ' {A} P .fst M P≤MQ = LV.seq P≤MQ ((LV.seq (pull M .isMon  Q≤SQ'))  M*S*→MS*)
  Oᴰ .Bif-homRᴰ {B} {B'} {S}{Q}{Q'} Q≤SQ' {A} P .snd = {!   !}
  Oᴰ .Bif-R-idᴰ = toPathP (Σ≡Prop (λ x → isPropImplicitΠ3 λ _ _ _ → isPropΠ3 λ _ _ _ → LV.isProp≤)(funExt λ _ → funExt λ _ → LV.isProp≤ _ _))
  Oᴰ .Bif-R-seqᴰ _ _ = toPathP (Σ≡Prop (λ x → isPropImplicitΠ3 λ _ _ _ → isPropΠ3 λ _ _ _ → LV.isProp≤)(funExt λ _ → funExt λ _ → LV.isProp≤ _ _))
  Oᴰ .SepBif-RL-commuteᴰ _ _ = toPathP (Σ≡Prop (λ x → isPropImplicitΠ3 λ _ _ _ → isPropΠ3 λ _ _ _ → LV.isProp≤)(funExt λ _ → funExt λ _ → LV.isProp≤ _ _))
  
{-}

  Oᴰ .F-homᴰ {A , B} {A' , B'} {V , S} {P , Q} {P' , Q'} (P'≤VP , Q≤SQ') .fst M P≤MQ = 
    LV.seq  P'≤VP (
    LV.seq (LV.mon* V P≤MQ)  (
    LV.seq (LV.mon* V (pull M .isMon  Q≤SQ')) (
    LV.eqTo≤ (sym (cong(λ h → h .fun Q') (funExt⁻ (LSq .N-hom (V , S)) M))))))
  Oᴰ .F-homᴰ {A , B} {A' , B'} {V , S} {P , Q} {P' , Q'} (P'≤VP , Q≤SQ') .snd {M}{M'}{M↦M'} P≤MQ P≤M'Q MQ≤M'Q = goal where 
    goal : A' LV.◂ pull (OBif .Bif-hom× V S .fst M) $ Q' ≤ (pull ((OBif .Bif-hom× V S .fst M')) $ Q') 
    goal = {!   !}
  Oᴰ .F-idᴰ = {! pGraphHomᴰ≡ ?  !}
  Oᴰ .F-seqᴰ = {!   !}
-}

  Mᴰ : CBPVModelᴰ M  _ _ _ _ _ _ 
  Mᴰ .fst = Vᴰ
  Mᴰ .snd .fst = Cᴰ
  Mᴰ .snd .snd = Oᴰ

  open import HyperDoc.Operational.TypeStructure
  open TypeStructureᴰ Mᴰ
  open TypeStructure M
  open import Cubical.Categories.Displayed.NaturalTransformation
  open NatTransᴰ

  module UTyDep (hasUTy : HasUTy) where 

    {-
      Eliminator given (lifts : ForgetfulObliqueLifts)

      also asumes 
        anti-U : 
          ∀ {A : VTy}{B : CTy}{M : A ⊢c B}
            {P : Vᴰ .ob[_] A}{Q : Cᴰ .ob[_] B} →
              Nodeᴰ[ M ][ P , Q ] →
            --------------------------------- 
              Nodeᴰ[ subC (thunk M) force ][ P , Q ]
        Uβ-fwd : 
          ∀{A : VTy}{B : CTy}{M : A ⊢c B}
          {P : Vᴰ .ob[_] A}{Q : Cᴰ .ob[_] B}
          (fᴰ : Nodeᴰ[ subC (thunk M) force ][ P , Q ])
          (gᴰ : Nodeᴰ[ M ][ P , Q ]) → 
          Edgeᴰ[ Uβ ][ fᴰ , gᴰ ]

      vty (U B) = lifts force (cty B) .fst 

      vtm (thunk {A}{B} M) = goal where 

          open CartesianLiftNotation Collageᴰ (lifts force (cty B))

          goal : Vᴰ [ thunk M ][ vty A , vty (U B) ] 
          goal = introᴰ {inl A}{vty A}{thunk M} (anti-U (ctm M))

      ctm (force {B}) = goal where 
          open CartesianLiftNotation Collageᴰ (lifts force (cty B))

          have : Oᴰ'[ subC var force ][ lifts force (cty B) .fst , cty B ]
          have = πⱽ
          
          goal : Oᴰ'[ force ][ lifts force (cty B) .fst , cty B ]
          goal = subst (λ h → Oᴰ'[ h ][ lifts force (cty B) .fst , cty B ]) subCId have

      ctmRel (Uβ {A}{B}{M}) = goal where 
          goal : Uβ ◂ ctm-subC (thunk M) force ↦Oᴰ ctm M
          goal = Uβ-fwd (ctm-subC (thunk M) force) (ctm M)

    -}
    {-
      So Given a Logic .. what do we need?
        we have the cartesian lift structure from just the logic, no assumptions
        but we still need 
        - anti reduction for the thunk case
        - the displayed edge

    -}
    {-
    ` Eliminator given (hasUTyᴰ : HasUTyᴰ hasUTy)
        
        vty (U B) = hasUTyᴰ (cty B) .repᴰ
        vtm (thunk M) = thunkᴰ (ctm M)
        ctm (force V) = forceᴰ (vtm V)
        ctm (force-sub {A}{A'}{B}{V}{W} i) = 
          hasUTyᴰ (cty B) .fwdᴰ .N-homᴰ (vtm V) i W (vtm W)
        ctmRel (Uβ {M = M}) =  Uβᴰ (ctm M) 
    -}




    open UTySyntax hasUTy
    hasUTyᴰ : HasUTyᴰ hasUTy
    hasUTyᴰ Bᴰ .WkRepresentationᴰ.repᴰ = pull (force (V .id)) $ Bᴰ
    hasUTyᴰ {B} Q .WkRepresentationᴰ.fwdᴰ .N-obᴰ {A} P V P≤!VQ = LV.seq P≤!VQ (LV.seq V*M*→VM* {!   !}) -- pull (subC V (force id)) ≡ pull (force V)
    {- 
  force-sub : ∀{A A' B}{V : A' ⊢v A}{W : A ⊢v U B} → 
    force (subV V W) ≡ subC V (force W) 
    -}
    hasUTyᴰ Bᴰ .WkRepresentationᴰ.fwdᴰ .N-homᴰ _ = toPathP (funExt λ x → funExt λ y → LV.isProp≤  _ _)
    hasUTyᴰ {B} Q .WkRepresentationᴰ.bkwdᴰ {A}{P} {M} Mᴰ = goal where 
      have : A LV.◂ P ≤ fun (pull M) Q
      have = Mᴰ
      -- anti reduction
      need : A LV.◂ pull M $ Q ≤ (pull (O .Bif-homL (thunk M) B .fst (force (V .id))) $ Q) 
      need = {!   !}
      goal : A LV.◂ P ≤ LV.f* (thunk M) (pull (force (V .id)) $ Q) 
      goal = LV.seq have (LV.seq need VM*→V*M*)
    hasUTyᴰ {B} Q .WkRepresentationᴰ.wkretractᴰ {A}{P}{M} P≤MQ = {!   !}


-}

{-




  Oᴰ : Functorᴰ O ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) (ALGᴰ {Σ})
  Oᴰ .Functorᴰ.F-obᴰ {A , B} (P , Q) .Carrierᴰ M = A VL.◂ P ≤ (pull M $ Q) , isProp→isSet VL.isProp≤
  Oᴰ .Functorᴰ.F-obᴰ {A , B} (P , Q) .interpᴰ op args dargs = pullOp op args P Q dargs 
  Oᴰ .Functorᴰ.F-homᴰ {A , B} {A' , B'} {f , g} {P , Q} {P' , Q'} (P'≤f*P , Q≤g*Q') .carmapᴰ h P≤h*Q = 
    VL.seq  P'≤f*P (
    VL.seq (VL.mon* f P≤h*Q)  (
    VL.seq (VL.mon* f (pull h .isMon  Q≤g*Q')) (
    VL.eqTo≤ (sym (cong(λ h → h .fun Q') (funExt⁻ (Sq .N-hom (f , g)) h))))))
  Oᴰ .Functorᴰ.F-homᴰ {A , B} {A' , B'} {f , g} {P , Q} {P' , Q'} (P'≤f*P , Q≤g*Q') .presᴰ op args dargs = toPathP (VL.isProp≤ _ _)
  Oᴰ .Functorᴰ.F-idᴰ = toPathP (AlgHomᴰ≡Prop λ _ → VL.isProp≤)
  Oᴰ .Functorᴰ.F-seqᴰ _ _ = toPathP (AlgHomᴰ≡Prop λ _ → VL.isProp≤)

  private 
    module VL = HDSyntax VH
    module CL = HDSyntax CH
      
  pull : {A : V .ob}{B : C .ob}(M : O'[ A , B ])  
    → MonFun (F-ob CH B .fst) (F-ob VH A .fst)
  pull {A} {B} M = Sq .N-ob (A , B) M

open Categoryᴰ
module Convert {C : Category _ _} (F : Functor (C ^op) (POSET _ _ )) where 
  open HDSyntax F  

  Cᴰ : Categoryᴰ C _ _ 
  ob[ Cᴰ ] = F∣_∣
  Cᴰ .Hom[_][_,_] {x}{y} f Fx Fy = x ◂ Fx ≤ f* f Fy
  Cᴰ .idᴰ = eqTo≤  (sym f*id)
  Cᴰ ._⋆ᴰ_ {f = f} {g} = seq* f g
  Cᴰ .⋆IdLᴰ fᴰ = toPathP (isProp≤ _ fᴰ)
  Cᴰ .⋆IdRᴰ fᴰ = toPathP (isProp≤ _ fᴰ)
  Cᴰ .⋆Assocᴰ _ _ _ = toPathP (isProp≤ _ _)
  Cᴰ .isSetHomᴰ = isProp→isSet isProp≤ 

-}
-}
-}