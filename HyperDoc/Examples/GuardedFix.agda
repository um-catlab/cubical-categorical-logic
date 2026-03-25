{-# OPTIONS --type-in-type #-}

module HyperDoc.Examples.GuardedFix where
-- fix level issues
-- reorder imports, etc


open import Cubical.Data.FinData
open import Cubical.Data.Unit
open import Cubical.Data.Sum

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor 
open import Cubical.Categories.Presheaf.Morphism.Alt hiding (_∘ˡ_)
open import Cubical.Categories.NaturalTransformation

open import HyperDoc.Algebra.Algebra
open import HyperDoc.CBPV.Model.Base
open import HyperDoc.CBPV.TypeStructure

open Alg
open AlgHom
open Category
open Functor
open PshHom
open PshIso
open Signature

module _ (Σ : Signature) where 
  
  Σ+δ : Signature
  Σ+δ .Op = Unit ⊎ Σ .Op
  Σ+δ .arity (inl tt) = 1
  Σ+δ .arity (inr op) = Σ .arity op

module Syntax (Σ : Signature) where 

  Σδ : Signature
  Σδ = Σ+δ Σ

  mutual 
    data VTy : Type where 
      𝟙 : VTy
      U : CTy → VTy

    data CTy : Type where 
      Ans : CTy

  data _⊢v_ : (A A' : VTy) → Type 
  data _⊢c_ : (A : VTy)(B : CTy) → Type 
  data _⊢k_ : (B B' : CTy) → Type 

  subC' : ∀ {A A' B} → A ⊢v A' → A' ⊢c B → A ⊢c B
  force' :  ∀{B} → U B ⊢c B
  δ' : ∀ {A B} → (Fin 1 → A ⊢c B) → A ⊢c B

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
    thunk : {A : VTy}{B : CTy} → (M : A ⊢c B) → A ⊢v U B
    Uη : ∀{A B}{V : A ⊢v U B} →  thunk (subC' V force') ≡ V
    tt : ∀{A} → A ⊢v 𝟙
    η𝟙 : ∀{A} → (V : A ⊢v 𝟙) → tt ≡ V

  data _⊢k_ where
    -- category 
    kcomp : ∀ {B B' B''} → B ⊢k B' → B' ⊢k B'' → B ⊢k B''
    hole : ∀ {B} → B ⊢k B
    kcompIdl : ∀ {B B'} → (M : B ⊢k B') → kcomp (hole {B}) M ≡ M
    kcompIdr : ∀ {B B'} → (M : B ⊢k B') → kcomp M (hole {B'}) ≡ M
    kcompAssoc : ∀ {B₁ B₂ B₃ B₄}(M : B₁ ⊢k B₂)(N : B₂ ⊢k B₃)(P : B₃ ⊢k B₄) → 
      kcomp(kcomp M N) P ≡  kcomp M (kcomp N P)
    isSet⊢k : ∀{B B'} → isSet (B ⊢k B')

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

    -- algebra structure
    ops : ∀(A : VTy)(B : CTy)(op : Σδ .Op) →  
      (Fin (Σδ .arity op) → A ⊢c B) → A ⊢c B
    opsSub : ∀{A A' : VTy}{B : CTy}(V : A ⊢v A')(op : Σδ .Op) →  
      (args : Fin (Σδ .arity op) → A' ⊢c B) → 
      subC V (ops A' B op args) ≡ ops A B op (λ x → subC V (args x))
    opsPlug :  ∀{A : VTy}{B B' : CTy}(S : B ⊢k B')(op : Σδ .Op) →  
      (args : Fin (Σδ .arity op) → A ⊢c B) → 
      plug S (ops  A B op args) ≡ ops A B' op (λ x → plug S (args x))

    -- type structure
    force : {B : CTy} → U B ⊢c B      
    yes : ∀{A} → A ⊢c Ans 
    no : ∀{A} → A ⊢c Ans 
    Uβ : ∀ {A B} → {M : A ⊢c B} → subC (thunk M) force ≡ M

    -- recursion 
    fix : {B : CTy} → U B ⊢c B → 𝟙 ⊢c B
    -- special equation that our notion of model is too weak to express 
    -- it would require knowledge of the syntax
    unfold : {B : CTy}{M : U B ⊢c B} → 
      fix M ≡  subC (thunk (δ' (λ _ → fix M))) M

  subC' = subC
  force' = force
  δ' {A}{B} = ops A B (inl tt)

 


module SyntacticModel (Σ : Signature)  where 
  open Syntax Σ


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

  FreeCompAlg : VTy → CTy → Alg Σδ
  FreeCompAlg A B .Carrier = A ⊢c B , isSet⊢c
  FreeCompAlg A B .interp = ops A B
  
  O : Functor (V ^op ×C C) (ALG Σδ) 
  O .F-ob (A , B) = FreeCompAlg A B
  O .F-hom (V , S) .carmap M = plug S (subC V M)
  O .F-hom (V , S) .pres op args = cong (λ h →  plug S h) (opsSub V op args) ∙ opsPlug S op λ x → subC V (args x)
  O .F-id = AlgHom≡ (funExt λ M → plugId ∙ subCId)
  O .F-seq (V , S)(V' , S') = AlgHom≡ (funExt λ M → sym plugDist ∙ cong₂ plug refl (sym plugSub ∙ sym subDist ∙ cong₂ subC refl plugSub))

  SynModel : CBPVModel Σδ
  SynModel .CBPVModel.V = V
  SynModel .CBPVModel.C = C
  SynModel .CBPVModel.O = O 

  open TypeStructure SynModel

  has𝟙 : HasV𝟙 
  has𝟙 .fst = 𝟙
  has𝟙 .snd .trans .N-ob = λ c _ → tt
  has𝟙 .snd .trans .N-hom _ _ _ _ = refl
  has𝟙 .snd .nIso A .fst tt = tt
  has𝟙 .snd .nIso A .snd .fst tt = refl
  has𝟙 .snd .nIso A .snd .snd = η𝟙

  hasUTy : HasUTy
  hasUTy B .fst = U B
  hasUTy B .snd .trans .N-ob A V = subC V force
  hasUTy B .snd .trans .N-hom A A' V W = sym subDist ∙ sym plugId
  hasUTy B .snd .nIso A .fst = thunk
  hasUTy B .snd .nIso A .snd .fst M = Uβ
  hasUTy B .snd .nIso A .snd .snd V = Uη

open import HyperDoc.Logic.Base 
open import HyperDoc.Syntax
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Displayed.Section.Base

module _ {Σ : Signature} where
  open SyntacticModel Σ  

  record InterpGen 
        (L : Logic SynModel) : Type where 
      open Logic L
      open Syntax Σ 
      private
        module LV = HDSyntax VH 
        module LC = HDSyntax CH 
      field 
        interpAns : LC.F∣ Ans ∣
        interpYes : {A : VTy}{P : LV.F∣ A ∣} → A  LV.◂ P ≤ (pull yes $ interpAns)
        interpNo : {A : VTy}{P : LV.F∣ A ∣} → A  LV.◂ P ≤ (pull no $ interpAns)


open import Cubical.Categories.Displayed.Base 
open Categoryᴰ 
open import HyperDoc.Connectives.Connectives
open import Cubical.Categories.NaturalTransformation 
open NatTrans
module Eliminator 
    (Σ : Signature) where 
  open Syntax Σ
  open SyntacticModel Σ
  open Section
  module _ 
    (L : Logic SynModel ) where

    module L = Logic L
    open Logic L
    module LV = HDSyntax L.VH 
    module LC = HDSyntax L.CH
    open ConvertLogic SynModel L 
    open TypeStructure SynModel

    open L▷

    module _ 
      (V⊤ : HasV𝟙 ) 
      (later : Has▷ L.VH)
      (hasΘᴰ : {A : VTy}{B : CTy}(M : Fin 1 → A ⊢c B)(Q : LC.F∣ B ∣) → 
        -- ▷ (M^*Q) ≤ δ(M)^* Q
        A LV.◂ L▷.LaterStr.▷_ (later .snd .fst A) (pull (M zero) $ Q) ≤ (pull (δ' M) $ Q)) where

      ⊤ : L⊤.Has⊤ VH 
      ⊤ = later .fst
      
      open L⊤.HA 
      mutual
        vty : (A : VTy) → LV.F∣ A ∣
        vty 𝟙 = top (⊤ .fst 𝟙)
        vty (U B) = pull force $ cty B 
   
        cty : (B : CTy) → LC.F∣ B ∣
        cty Ans = {!   !} -- interpAns


      mutual 
        vtm : {A A' : VTy} → (V : A ⊢v A') → A LV.◂ vty A ≤ LV.f* V (vty A')
        vtm (subV V V') = Vᴰ ._⋆ᴰ_  (vtm V) (vtm V')
        vtm var = Vᴰ .idᴰ
        vtm (subVIdl V i) = Vᴰ .⋆IdLᴰ (vtm V) i
        vtm (subVIdr V i) = Vᴰ .⋆IdRᴰ (vtm V) i
        vtm (subVAssoc V₁ V₂ V₃ i) = Vᴰ .⋆Assocᴰ (vtm V₁) (vtm V₂) (vtm V₃) i
        vtm (isSet⊢v V V' x y i j) = 
          isOfHLevel→isOfHLevelDep 2 
            (λ x → Vᴰ .isSetHomᴰ) 
            (vtm V) (vtm V') 
            (cong vtm x) (cong vtm y) 
            (isSet⊢v V V' x y) i j
        vtm (thunk M) = {!   !}
        vtm (Uη i) = {!   !}
        vtm tt = {!   !}
        vtm (η𝟙 V₁ i) = {!   !}

        ktm : {B B' : CTy} → (S : B ⊢k B') → B LC.◂ cty B ≤ LC.f* S (cty B')
        ktm (kcomp S S') = Cᴰ ._⋆ᴰ_  (ktm S) (ktm S')
        ktm hole = Cᴰ .idᴰ
        ktm (kcompIdl S i) = Cᴰ .⋆IdLᴰ (ktm S) i
        ktm (kcompIdr S i) = Cᴰ .⋆IdRᴰ (ktm S) i
        ktm (kcompAssoc S₁ S₂ S₃ i) =  Cᴰ .⋆Assocᴰ (ktm S₁) (ktm S₂) (ktm S₃) i
        ktm (isSet⊢k S S' x y i j) = 
          isOfHLevel→isOfHLevelDep 2 
            (λ x → Cᴰ .isSetHomᴰ) 
            (ktm S) (ktm S') 
            (cong ktm x) (cong ktm y) 
            (isSet⊢k S S' x y) i j

        ctm : ∀{A B} → (M : A ⊢c B) → A LV.◂ vty A ≤ (pull M $ cty B)
        ctm (subC V M) = {!   !}
        ctm (plug S M) = {!   !}
        ctm (plugId i) = {!   !}
        ctm (subCId i) = {!   !}
        ctm (plugDist i) = {!   !}
        ctm (subDist i) = {!   !}
        ctm (plugSub i) = {!   !}
        ctm (isSet⊢c M M₁ x y i i₁) = {!   !}
        -- δ
        ctm (ops A B (inl tt) M) = goal where 
          open LaterStr (later .snd .fst A)
          goal : A LV.◂ vty A ≤ (pull (δ' M) $ cty B) 
          goal = LV.seq ▷-intro (LV.seq (▷-mono (ctm (M zero))) (hasΘᴰ M (cty B)))
        ctm (ops A B (inr op) args) = pullOp (inr op) args (vty A) (cty B) (λ x → ctm (args x))
        ctm (opsSub V (inl tt) args i) = {!   !}
        ctm (opsSub V (inr op) args i) = {!   !}
        ctm (opsPlug S (inl tt) args i) = {!   !}
        ctm (opsPlug S (inr op) args i) = {!   !}
        ctm force = {!   !}
        ctm yes = {!   !}
        ctm no = {!   !}
        ctm (Uβ i) = {!   !}
        ctm (fix {B} M) = goal where 
          open LaterStr (later .snd .fst 𝟙)
          Q = cty B 
          fixM* = pull (fix M)

          ▷toδ : 𝟙 LV.◂ ▷ (fixM* $ Q) ≤ ((pull (δ' (λ _ → fix M))) $ Q)
          ▷toδ = (hasΘᴰ (λ _ → fix M) Q)

          Uη-exp : 𝟙 LV.◂ ((pull (δ' (λ _ → fix M))) $ Q) ≤ LV.f* (thunk (δ' (λ _ → fix M))) ((pull force) $ Q)
          Uη-exp = LV.seq (LV.eqTo≤ (cong(λ h → (pull h) $ Q) (sym Uβ ∙ sym plugId))) VM*→V*M*

          use-IH : 𝟙 LV.◂ LV.f* (thunk (δ' (λ _ → fix M))) (pull force $ Q) ≤ LV.f* (thunk (δ' (λ _ → fix M))) ((pull M) $ Q) 
          use-IH = LV.mon* (thunk (δ' (λ _ → fix M))) (ctm M)   

          unfold-fix : 𝟙 LV.◂ LV.f* (thunk (δ' (λ _ → fix M))) (pull M $ Q) ≤ (fixM* $ Q) 
          unfold-fix = LV.seq (LV.seq (V*M*→VM* {V = thunk (δ' (λ _ → fix M))}{M}{Q}) (LV.eqTo≤ ((cong (λ h → (N-ob Sq (𝟙 , B) h) $ Q) plugId)))) (LV.eqTo≤ (cong( λ h → pull h $ Q) (sym unfold)))

          sub : 𝟙 LV.◂ ▷ ((fixM* $ Q)) ≤ (fixM* $ Q) 
          sub = LV.seq  ▷toδ (LV.seq (LV.seq Uη-exp use-IH) unfold-fix)

          goal : 𝟙 LV.◂ top (⊤ .fst 𝟙) ≤ (fixM* $ Q) 
          goal = lob sub

        ctm (unfold i) = {!   !}

      SV : Section Id Vᴰ 
      SV .F-obᴰ = vty
      SV .F-homᴰ = vtm
      SV .F-idᴰ = LV.isProp≤  _ _
      SV .F-seqᴰ _ _ = LV.isProp≤  _ _

      SC : Section Id Cᴰ 
      SC .F-obᴰ = cty
      SC .F-homᴰ = ktm
      SC .F-idᴰ = LC.isProp≤  _ _
      SC .F-seqᴰ _ _ = LC.isProp≤  _ _

      M-elim : CBPVGlobalSection L
      M-elim .fst = SV
      M-elim .snd .fst = SC
      M-elim .snd .snd = ctm
