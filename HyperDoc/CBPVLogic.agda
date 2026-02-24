module HyperDoc.CBPVLogic where 

open import Cubical.Data.Sigma
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure 

open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Category 
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets

open import Cubical.Data.List using (_∷_ ; [])

open import HyperDoc.CBPVModel 
open import HyperDoc.Syntax
open import HyperDoc.Lib
open import HyperDoc.Connectives.Connectives
open Functor
open Category
open NatTrans
open MonFun renaming (f to fun)

Hom^op : {ℓP ℓP' : Level} → Functor ((POSET ℓP ℓP') ×C (POSET ℓP ℓP')^op) (SET (ℓ-max ℓP ℓP'))
Hom^op {ℓP}{ℓP'} .F-ob (P , Q) = (POSET ℓP ℓP') [ Q , P ] , (POSET ℓP ℓP') .isSetHom
Hom^op .F-hom {(A , B)}{(A' , B')} (f , g) h = MonComp g (MonComp h f)
Hom^op .F-id = funExt λ _ → eqMon _ _ refl
Hom^op .F-seq _ _ = funExt λ _ → eqMon _ _ refl

open import Cubical.Categories.NaturalTransformation
record Logic 
  {ℓV ℓV' ℓC ℓC' ℓP ℓP'  : Level}
  (M : Model ℓV ℓV' ℓC ℓC' (ℓ-max ℓP ℓP')) : Type (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓ-suc ℓP ∷ ℓ-suc ℓP' ∷ [])) where 
  open Model M
  field 
    VH : Functor (V ^op) (POSET ℓP ℓP')
    CH : Functor (C ^op) (POSET ℓP ℓP')
    Sq : NatTrans O (Hom^op ∘F (VH ×F ((CH ^opF) ∘F to^op^op)))
    
  private 
    module VL = HDSyntax VH
      
  pull : {A : V .ob}{B : C .ob}(M : O[ A , B ])  
    → MonFun (F-ob CH B .fst) (F-ob VH A .fst)
  pull {A} {B} M = Sq .N-ob (A , B) M

  pullComp : ∀ {A A' B B'}(V : V [ A' , A ])(S : C [ B , B' ])(M : O[ A , B ]) → 
    pull (lrcomp V S M) ≡ MonComp (CH .F-hom S) (MonComp (pull M) (VH .F-hom V))
  pullComp V S M = funExt⁻ (Sq .N-hom (V , S)) M

  pullLComp : ∀ {A A' B}(V : V [ A' , A ])(M : O[ A , B ]) → 
    pull (lcomp V M) ≡ MonComp (pull M) (VH .F-hom V)
  pullLComp V M = 
    pullComp V (C .id) M 
    ∙ cong (λ h → MonComp h (MonComp (pull M) (VH .F-hom V))) (CH .F-id) 

  pullRComp :  ∀ {A B B'}(S : C [ B , B' ])(M : O[ A , B ]) → 
    pull (rcomp S M) ≡ MonComp (CH .F-hom S) (pull M)
  pullRComp S M = pullComp (V .id) S M ∙ cong₂ MonComp refl (VH .F-id)

module _ 
  {ℓV ℓV' ℓC ℓC'  ℓP ℓP'  : Level}
  {M : Model ℓV ℓV' ℓC ℓC' (ℓ-max ℓP ℓP' )} 
  (L : Logic {ℓP = ℓP} {ℓP'} M) where 
  private 
    module L = Logic L
    module VL = HDSyntax L.VH
    module CL = HDSyntax L.CH
    module M = Model M


  module Products (prod : HasO× M) where 
    open import Cubical.Categories.Presheaf.Morphism.Alt
    open PshIso
    open PshHom
    _&_ : ob M.C → ob M.C → ob M.C
    _&_ B B' = prod B B' .fst

    π₁ : ∀{A B B'} → (M : M.O[ A , B & B' ]) → M.O[ A , B ]
    π₁ {A}{B}{B'} M = prod B B' .snd .trans .N-ob A M .fst

    π₂ : ∀{A B B'} → (M : M.O[ A , B & B' ]) → M.O[ A , B' ]
    π₂ {A}{B}{B'} M = prod B B' .snd .trans .N-ob A M .snd

    〈_,_〉 : ∀{A B B'} → M.O[ A , B ] → M.O[ A , B' ] → M.O[ A , B & B' ]
    〈_,_〉 {A}{B}{B'} M N = prod B B' .snd .nIso A .fst (M , N)

    {- 
    This is exactly the data of 
      hasComp : Type _ 
      hasComp = ∀(B B' : ob C) → Σ[ B&B' ∈ ob C ] PshIso O[-, B&B' ] (O[-, B ] ×Psh O[-, B' ])

      hasCompᴰ : hasComp → Type _ 
      hasCompᴰ prod = ∀(B B' : ob C)(bᴰ : ob[ Cᴰ ] B)(bᴰ' : ob[ Cᴰ ] B') → 
        Σ[ b&b' ∈ ob[ Cᴰ ] (prod B  B' .fst) ] 
          PshIsoᴰ (prod B B' .snd) (Oᴰ[-,  b&b' ] ) (Oᴰ[-, bᴰ ] ×ᴰPsh Oᴰ[-, bᴰ' ])
    -}
    -- If C has products and F
    -- then this should be derivable
    record O⋀ (B B' : ob M.C) : Type {!   !} where 
      field 
        _⋀_ : CL.F∣ B ∣ → CL.F∣ B' ∣ → CL.F∣ B & B' ∣

        ⋀-elim1 : ∀ {A M P Q R} → 
          A VL.◂ P ≤ L.pull M .fun  (Q ⋀ R) → 
          -------------------------------------
          A VL.◂ P ≤ L.pull (π₁ M) .fun  Q

        ⋀-elim2 : ∀ {A M P Q R} → 
          A VL.◂ P ≤ L.pull M .fun  (Q ⋀ R) →
          -------------------------------------
          A VL.◂ P ≤ L.pull (π₂ M) .fun  R

        ⋀-intro : ∀ {A M N P Q R} →  
          A VL.◂ P ≤ L.pull M .fun Q → 
          A VL.◂ P ≤ L.pull N .fun R →
          ----------------------------
          A VL.◂ P ≤ L.pull 〈 M , N 〉 .fun (Q ⋀ R)

    has⋀ : Type _ 
    has⋀ = (B B' : ob M.C) → O⋀ B B'

  -- dont need existentials.?
  module Coproducts (cprod : HasO+ M) where 
    open import Cubical.Categories.Presheaf.Morphism.Alt
    open PshIso
    open PshHom

    _+_ : ob M.V → ob M.V → ob M.V 
    _+_ A A' = cprod A A' .fst

    σ₁ : ∀{A A' B} → (M : M.O[ A + A' , B ]) → M.O[ A , B ]
    σ₁ {A}{A'}{B} M = cprod A A' .snd .trans .N-ob B M .fst

    σ₂ : ∀{A A' B} → (M : M.O[ A + A' , B ]) → M.O[ A' , B ]
    σ₂ {A}{A'}{B} M = cprod A A' .snd .trans .N-ob B M .snd

    case : ∀{A A' B} → M.O[ A , B ] → M.O[ A' , B ] → M.O[ A + A' , B ]
    case {A}{A'}{B} M N = cprod A A' .snd .nIso B .fst (M , N)

    record O⋁ (A A' : ob M.V): Type _ where 
      field 
        _⋁_ : VL.F∣ A ∣ → VL.F∣ A' ∣ → VL.F∣ A + A' ∣

        ⋁-intro : ∀{B P Q R } → 
          {M : M.O[ A  , B  ]}{N : M.O[ A' , B  ]} → 
          A  VL.◂ P ≤  (L.pull M $ R) → 
          A' VL.◂ Q ≤  (L.pull N $ R) → 
          ------------------------------
         (A + A') VL.◂ (P ⋁ Q) ≤  (L.pull (case M N) $ R)

        ⋁-elim1 : ∀{B P Q R }{M : M.O[ A + A'  , B  ]} → 
          (A + A') VL.◂ (P ⋁ Q) ≤  (L.pull M $ R) → 
          ------------------------------
          A VL.◂ P ≤ (L.pull (σ₁ M) $ R)

        ⋁-elim2 : ∀{B P Q R }{M : M.O[ A + A'  , B  ]} → 
          (A + A') VL.◂ (P ⋁ Q) ≤  (L.pull M $ R) → 
          ------------------------------
          A' VL.◂ Q ≤ (L.pull (σ₂ M) $ R)
    has⋁ : Type _ 
    has⋁ = (A A' : ob M.V) → O⋁ A A'

  hasPush : Type (ℓ-max (ℓ-max (ℓ-max ℓV ℓC) ℓP) ℓP') 
  hasPush = 
    ∀ {A : Model.V M .ob}
      {B : Model.C M .ob}
      (M : Model.O M .F-ob (A , B) .fst) → 
      HasLeftAdj (L.pull M)


  module _ (pp : hasPush) where 
    open import Cubical.Foundations.Isomorphism
    open Iso
    open _⊣_ 
    pushToPull : 
      ∀ {A : Model.V M .ob}
      {B : Model.C M .ob}
      (M : Model.O M .F-ob (A , B) .fst)
      {P : VL.F∣ A ∣}
      {Q : CL.F∣ B ∣}→ 
      B CL.◂ pp M .fst .MonFun.f P ≤ Q  → 
      A VL.◂ P ≤ L.pull M .MonFun.f Q
    pushToPull M  = adjIff (pp M .snd) .fun 

    pullToPush : 
      ∀ {A : Model.V M .ob}
      {B : Model.C M .ob}
      (M : Model.O M .F-ob (A , B) .fst)
      {P : VL.F∣ A ∣}
      {Q : CL.F∣ B ∣}→ 
      A VL.◂ P ≤ L.pull M .MonFun.f Q → 
      B CL.◂ pp M .fst .MonFun.f P ≤ Q 
    pullToPush M  = adjIff (pp M .snd) .inv 

    pullPush :       
      ∀ {A : Model.V M .ob}
      {B : Model.C M .ob}
      (M : Model.O M .F-ob (A , B) .fst)
      {Q : CL.F∣ B ∣}
      → A VL.◂ L.pull M .MonFun.f Q ≤ L.pull M .MonFun.f Q
    pullPush M = pushToPull M (pullToPush M VL.id⊢)

  WithConnectives : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓV ℓV') ℓC) ℓP) ℓP')
  WithConnectives = L⊤.Has⊤ L.VH × hasPush
