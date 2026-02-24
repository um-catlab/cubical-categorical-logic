  module HyperDoc.Models.Free where 

  -- Free model with 
  -- 1 , + , U for value type 
  -- & , F for computation types

  open import Cubical.Data.List 
  open import Cubical.Data.Sigma 
  open import Cubical.Data.Unit hiding (terminal)

  open import Cubical.Foundations.HLevels
  open import Cubical.Foundations.Prelude
  open import Cubical.Foundations.Structure
  open import Cubical.Data.Graph.Base 
  open import Cubical.Relation.Binary.Preorder

  open import Cubical.Categories.Category 
  open import Cubical.Categories.Functor
  open import Cubical.Categories.Constructions.BinProduct
  open import Cubical.Categories.Instances.Sets
  open import Cubical.Categories.Presheaf.Morphism.Alt
  open import Cubical.Categories.Instances.Preorders.Monotone

  open import HyperDoc.Lib
  open import HyperDoc.CBPVModel
  open import HyperDoc.CBPVLogic
  open import HyperDoc.Section
  open import HyperDoc.Syntax
  open import HyperDoc.Connectives.Connectives

  open Category
  open Functor
  open PshHom
  open PshIso
  open PreorderStr
  open MonFun renaming (f to fun)

  module Syntax
    {ℓV ℓV' ℓC ℓC' ℓS : Level } where

    mutual 
      data VTy : Type (levels (ℓV ∷ ℓC ∷ [])) where 
        one : VTy 
        _+_ : VTy → VTy → VTy
        U : CTy → VTy 

      data CTy : Type (levels (ℓV ∷ ℓC ∷ [])) where
        _&_ : CTy → CTy → CTy 
        F : VTy → CTy    

    data _⊢v_ : (A A' : VTy) → Type (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ []))
    data _⊢c_ : (A : VTy)(B : CTy) → Type (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ []))
    data _⊢k_ : (B B' : CTy) → Type (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ []))
    force' :  ∀{B} → U B ⊢c B
    hole' : ∀ {B} → B ⊢k B
    kcomp' : ∀ {B B' B''} → B ⊢k B' → B' ⊢k B'' → B ⊢k B''
    ret' : ∀{A } → A ⊢c F A
    bind' : ∀{A B} → A ⊢c B → F A ⊢k B
    subC' : ∀ {A A' B} → A ⊢v A' → A' ⊢c B → A ⊢c B

    data _⊢v_   where
      -- category 
      subV : ∀ {A A' A''} → A ⊢v A' → A' ⊢v A'' → A ⊢v A''
      var : ∀ {A} → A ⊢v A
      subVIdl : ∀ {A A'} → (V : A ⊢v A') → subV (var {A}) V ≡ V
      subVIdr : ∀ {A A'} → (V : A ⊢v A') → subV V (var {A'}) ≡ V
      subVAssoc : ∀ {A₁ A₂ A₃ A₄}(V : A₁ ⊢v A₂)(W : A₂ ⊢v A₃)(Y : A₃ ⊢v A₄) → 
        subV (subV V W) Y ≡ subV V (subV W Y)
      isSet⊢v : ∀{A A'} → isSet (A ⊢v A')

      -- 1
      tt : ∀{A} → A ⊢v one
      oneη : ∀{A}{V : A ⊢v one} → tt ≡ V

      -- U
      thunk : ∀{A B} → A ⊢c B → A ⊢v U B
      Uη : ∀{A B}{V : A ⊢v U B} →  thunk (subC' V force') ≡ V



    data _⊢c_ where 
      -- profunctor      
      subC : ∀ {A A' B} → A ⊢v A' → A' ⊢c B → A ⊢c B
      plug : ∀ {A B B'} → B ⊢k B' → A ⊢c B → A ⊢c B'
      plugId : ∀ {A B}{M : A ⊢c B} → plug (hole' {B}) M ≡ M
      subCId : ∀ {A B}{M : A ⊢c B} → subC (var {A}) M ≡ M
      plugDist : ∀ {A B B' B''}{S : B ⊢k B'}{S' : B' ⊢k B''}{M : A ⊢c B} → --rcomp
        plug S' (plug S M) ≡ plug (kcomp' S S') M
      subDist : ∀ {A A' A'' B}{V : A ⊢v A'}{V' : A' ⊢v A''}{M : A'' ⊢c B} → --lcomp
        subC V (subC V' M) ≡ subC (subV V V') M
      plugSub : ∀ {A A' B B'}{V : A ⊢v A'}{M : A' ⊢c B}{S : B ⊢k B'} → 
        subC V (plug S M) ≡ plug S (subC V M)
      isSet⊢c : ∀{A B} → isSet (A ⊢c B)

      -- &
      _,,_ : ∀{A B B'} → A ⊢c B → A ⊢c B' → A ⊢c (B & B')
      π₁ :  ∀{A B B'} → A ⊢c (B & B') → A ⊢c B
      π₂ : ∀{A B B'} → A ⊢c (B & B') → A ⊢c B'

      &β₁ : ∀{A B B'}{M : A ⊢c B}{N : A ⊢c B'} → π₁ (M ,, N) ≡ M
      &β₂ : ∀{A B B'}{M : A ⊢c B}{N : A ⊢c B'} → π₂ (M ,, N) ≡ N
      &η : ∀{A B B'}{P : A  ⊢c (B & B')} → (π₁ P ,, π₂ P) ≡ P

      π₁Sub : ∀{A A' B B'}{V : A ⊢v A'}{p : A' ⊢c (B & B')} 
        →  π₁ (subC V p) ≡ subC V (π₁ p)
      π₂Sub : ∀{A A' B B'}{V : A ⊢v A'}{p : A' ⊢c (B & B')} 
        →  π₂ (subC V p) ≡ subC V (π₂ p)

      -- +
      σ₁ : ∀ {A A' B} → (A + A') ⊢c B → (A ⊢c B) 
      σ₂ : ∀ {A A' B} → (A + A') ⊢c B → (A' ⊢c B) 
      case : ∀ {A A' B} → (A ⊢c B) → (A' ⊢c B) → (A + A') ⊢c B

      +β₁ : ∀{A A' B}{M : A ⊢c B}{N : A' ⊢c B} → σ₁ (case M N) ≡ M
      +β₂ : ∀{A A' B}{M : A ⊢c B}{N : A' ⊢c B} → σ₂ (case M N) ≡ N
      +η : ∀{A A' B}{P : (A + A') ⊢c B} → case (σ₁ P) (σ₂ P) ≡ P 

      σ₁Sub : ∀{A A' B B'}{S : B ⊢k B'}{p : (A + A') ⊢c B} → σ₁ (plug S p) ≡ plug S (σ₁ p)
      σ₂Sub : ∀{A A' B B'}{S : B ⊢k B'}{p : (A + A') ⊢c B} → σ₂ (plug S p) ≡ plug S (σ₂ p)

      -- F
      ret : ∀{A } → A ⊢c F A
      Fβ : ∀{A B}{M : A ⊢c B} → M ≡ plug (bind' M) ret

      -- U
      force : ∀{B} → U B ⊢c B
      Uβ : ∀ {A B} → {M : A ⊢c B} → subC (thunk M) force ≡ M

      -- just encode effect
      beep : one ⊢c F one

    force' = force

    data _⊢k_ where 
      -- category 
      kcomp : ∀ {B B' B''} → B ⊢k B' → B' ⊢k B'' → B ⊢k B''
      hole : ∀ {B} → B ⊢k B
      kcompIdl : ∀ {B B'} → (M : B ⊢k B') → kcomp (hole {B}) M ≡ M
      kcompIdr : ∀ {B B'} → (M : B ⊢k B') → kcomp M (hole {B'}) ≡ M
      kcompAssoc : ∀ {B₁ B₂ B₃ B₄}(M : B₁ ⊢k B₂)(N : B₂ ⊢k B₃)(P : B₃ ⊢k B₄) → 
        kcomp(kcomp M N) P ≡  kcomp M (kcomp N P)
      isSet⊢k : ∀{B B'} → isSet (B ⊢k B')

      -- F
      bind : ∀{A B} → A ⊢c B → F A ⊢k B
      Fη : ∀ {A B}{S : F A ⊢k B} → S ≡ bind (plug S ret)

    hole' = hole
    kcomp' = kcomp
    ret' = ret
    bind' = bind
    subC' = subC


  module FreeModel 
    {ℓV ℓV' ℓC ℓC' ℓS : Level } where 

    open Syntax {ℓV}{ℓV'}{ℓC}{ℓC'}{ℓS}

    V : Category (ℓ-max ℓV ℓC) (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ []))
    V .ob = VTy
    V .Hom[_,_] = _⊢v_
    V .id = var
    V ._⋆_ = subV
    V .⋆IdL = subVIdl
    V .⋆IdR = subVIdr
    V .⋆Assoc = subVAssoc
    V .isSetHom = isSet⊢v

    C : Category (ℓ-max ℓV ℓC) (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ []))
    C .ob = CTy
    C .Hom[_,_] = _⊢k_
    C .id = hole
    C ._⋆_ = kcomp
    C .⋆IdL = kcompIdl
    C .⋆IdR = kcompIdr
    C .⋆Assoc = kcompAssoc
    C .isSetHom = isSet⊢k

    O : Functor (V ^op ×C C) (SET (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ []))) 
    O .F-ob (A , B) = (A ⊢c B) , isSet⊢c
    O .F-hom (V , S) M = subC V (plug S M)
    O .F-id = funExt λ M → cong (λ h → subC var h) plugId ∙ subCId
    O .F-seq (V , S) (V' , S') = 
      funExt λ M → 
        sym subDist 
        ∙ cong₂ subC refl (cong₂ subC refl (sym plugDist) ∙ plugSub)

    M : Model (ℓ-max ℓV ℓC) (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ [])) (ℓ-max ℓV ℓC) (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ [])) (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ []))
    M .Model.V = V
    M .Model.C = C
    M .Model.O = O

    terminal : HasV⊤ M 
    terminal .fst = one
    terminal .snd .trans .N-ob B V = tt*
    terminal .snd .trans .N-hom A A' V _ = refl
    terminal .snd .nIso A .fst _ =  tt
    terminal .snd .nIso A .snd .fst tt* = refl
    terminal .snd .nIso A .snd .snd V = oneη

    utype : HasUTy M
    utype B .fst = U B
    utype B .snd .trans .N-ob A V = subC V force
    utype B .snd .trans .N-hom A A' V W = sym subDist ∙ cong₂ subC refl (sym plugId)
    utype B .snd .nIso A .fst = thunk
    utype B .snd .nIso A .snd .fst M = Uβ
    utype B .snd .nIso A .snd .snd V = Uη

    ftype : HasFTy M 
    ftype A .fst = F A
    ftype A .snd .trans .N-ob B S = plug S ret
    ftype A .snd .trans .N-hom B B' S S' = sym plugDist ∙ sym subCId
    ftype A .snd .nIso B .fst = bind
    ftype A .snd .nIso B .snd .fst M = sym Fβ
    ftype A .snd .nIso B .snd .snd S = sym Fη

    coproducts : HasO+ M 
    coproducts A A' .fst = A + A'
    coproducts A A' .snd .trans .N-ob B P = σ₁ P , σ₂ P
    coproducts A A' .snd .trans .N-hom B B' S p = 
      ΣPathP (
        cong σ₁ subCId ∙ σ₁Sub ∙ sym subCId , 
        cong σ₂ subCId ∙ σ₂Sub ∙ sym subCId)
    coproducts A A' .snd .nIso B .fst (M , N) = case M N
    coproducts A A' .snd .nIso B .snd .fst (M , N) = ΣPathP (+β₁ , +β₂)
    coproducts A A' .snd .nIso B .snd .snd P = +η

    products : HasO× M
    products B B' .fst = B & B'
    products B B' .snd .trans .N-ob A P = π₁ P , π₂ P
    products B B' .snd .trans .N-hom A A' V p = 
      ΣPathP (
        (cong (λ h → π₁ (subC V h)) plugId 
          ∙  π₁Sub 
          ∙ cong₂ subC refl (sym plugId)) , 
        (cong (λ h → π₂ (subC V h)) plugId 
          ∙  π₂Sub 
          ∙ cong₂ subC refl (sym plugId)))
    products B B' .snd .nIso A .fst (M , N) = M ,, N
    products B B' .snd .nIso A .snd .fst (M , N) = ΣPathP (&β₁ , &β₂)
    products B B' .snd .nIso A .snd .snd P = &η

    module _ 
      (L : Logic {ℓP = ℓV}{(ℓ-max (ℓ-max (ℓ-max ℓV' ℓC) ℓC') ℓS)} M)
      (Top : L⊤.Has⊤ (Logic.VH L))
      (prod : Products.has⋀ L products)
      (cprod : Coproducts.has⋁ L coproducts)
      (push : hasPush L) where 

      open import Cubical.Categories.Displayed.Section
      open import HyperDoc.AsDisplayed
      open import Cubical.Categories.NaturalTransformation
      open import Cubical.Categories.Displayed.Base
      open import Cubical.Categories.Displayed.Functor
      open import Cubical.Categories.Displayed.BinProduct
      open import Cubical.Categories.Displayed.Instances.Sets
      open import Cubical.Categories.Displayed.Bifunctor
      open import Cubical.Categories.Bifunctor
      open import Cubical.Categories.Limits.Terminal.More
      open import Cubical.Categories.Displayed.Limits.Terminal


      open Categoryᴰ
      open Functorᴰ
      open NatTrans
      open Bifunctorᴰ
      open Logic L  

      private 
        module LV = HDSyntax VH
        module LC = HDSyntax CH

      open Modelᴰ M L
      open Products L products
      open O⋀
      open Coproducts L coproducts
      open O⋁
      open TerminalⱽNotation Vᴰ one (Vᴰtermⱽ Top terminal one) 


      mutual
        vty : (A : VTy) → LV.F∣ A ∣
        vty one = 𝟙ⱽ
        vty (A + A') = _⋁_ (cprod A A') (vty A) (vty A')
        vty (U B) = pull force $ (cty B)

        cty : (B : CTy) → LC.F∣ B ∣
        cty (B & B') = _⋀_ (prod B B') (cty B) (cty B')
        cty (F A) = push ret .fst $ (vty A)

      mutual

        vtm-thunk : ∀ {A  B} → (M : A ⊢c B) →  A LV.◂ vty A ≤ LV.f* (thunk M) (pull force $ cty B) 
        vtm-thunk {A}{B} M = LV.seq (ctm M) (LV.eqTo≤  ((cong (λ h → h $ (cty B))) ((cong pull (sym Uβ ∙ cong₂ subC refl (sym plugId))) ∙ pullLComp (thunk M) force)))

        vtm : {A A' : VTy} → (V : A ⊢v A') → A LV.◂ vty A ≤ LV.f* V (vty A')
        vtm (subV V₁ V₂) = Vᴰ ._⋆ᴰ_  (vtm V₁) (vtm V₂)
        vtm var = Vᴰ .idᴰ
        vtm (subVIdl V i) = Vᴰ .⋆IdLᴰ (vtm V) i
        vtm (subVIdr V i) = Vᴰ .⋆IdRᴰ (vtm V) i
        vtm (subVAssoc V₁ V₂ V₃ i) = Vᴰ .⋆Assocᴰ (vtm V₁) (vtm V₂) (vtm V₃) i
        vtm (isSet⊢v {A}{A'} V₁ V₂ x y i j) = {!   !} -- Vᴰ .isSetHomᴰ {! vtm V₁ !} {!   !} {!  x !} {!   !} i j
        
        vtm (tt {A}) = !tⱽ tt (vty A)
        vtm (oneη {A}{V} i) = VL.eq*PathP (oneη {A}{V}) (!tⱽ tt (vty A)) (vtm V) i
        vtm (thunk M) = vtm-thunk M
        vtm (Uη {A}{B}{V} i) = 
          isProp→PathP 
            ((λ i → LV.isProp≤{q = LV.f* (Uη i) (pull force $ cty B)})) 
            (vtm-thunk (subC' V force')) 
            (vtm V) 
            i

        ktm-bind : ∀ {A  B} → (M : A ⊢c B) → F A LC.◂ push ret .fst $ vty A ≤ LC.f* (bind M) (cty B)
        ktm-bind {A}{B}M = pullToPush L push ret (LV.seq (ctm M) (LV.eqTo≤ (cong (λ h → h .MonFun.f (cty B)) (cong (λ h → Sq .N-ob (A , B) h ) (sym subCId ∙ cong₂ subC refl Fβ) ∙ pullRComp (bind M) ret))))
        
        ktm : {B B' : CTy} → (S : B ⊢k B') → B LC.◂ cty B ≤ LC.f* S (cty B')
        ktm (kcomp S S₁) = Cᴰ ._⋆ᴰ_  (ktm S) (ktm S₁)
        ktm hole = Cᴰ .idᴰ
        ktm (kcompIdl S i) = Cᴰ .⋆IdLᴰ (ktm S) i
        ktm (kcompIdr S i) = Cᴰ .⋆IdRᴰ (ktm S) i
        ktm (kcompAssoc S S₁ S₂ i) = Cᴰ .⋆Assocᴰ (ktm S) (ktm S₁) (ktm S₂) i
        ktm (isSet⊢k S S₁ x y i i₁) = {!   !}
        ktm (bind M) = ktm-bind M
        ktm (Fη {A}{B}{S} i) = 
          isProp→PathP 
            ((λ i → LC.isProp≤{q =  LC.f* (Fη i) (cty B)})) 
            (ktm S)
            (ktm-bind (plug S ret))
            i

        ctm-subC : ∀{A A' B}(V : A ⊢v A')(M : A' ⊢c B) →  A LV.◂ vty A ≤ (pull (subC V M) $ cty B)
        ctm-subC {A}{A'}{B} V M = subst (λ h → A LV.◂ vty A ≤ (pull h $ cty B)) (cong₂ subC refl plugId) have where 
          have : A LV.◂ vty A ≤ (pull (subC V (plug hole M)) $ cty B)
          have = OᴰBif .Bif-homLᴰ (vtm V) (cty B) M (ctm M)

        ctm-plug : ∀{A B B'}(S : B ⊢k B')(M : A ⊢c B) → A LV.◂ vty A ≤ (pull (plug S M) $ cty B')
        ctm-plug {A}{B}{B'} S M = subst (λ h → A LV.◂ vty A ≤ (pull h $ cty B')) subCId have where 
          have : A LV.◂ vty A ≤ (pull (subC var (plug S M)) $ cty B')
          have = OᴰBif .Bif-homRᴰ (vty A) (ktm S) M (ctm M)

        {-# TERMINATING #-}
        -- Idk why.. but this termination pragma is needed for plugDist
        -- which is just showing that the PathP is a prop.. 
        -- there should be NO interesting recursion in the proof of equality
        ctm : ∀{A B} → (M : A ⊢c B) → A LV.◂ vty A ≤ (pull M $ cty B)
        ctm (subC {A}{A'}{B} V M) = ctm-subC V M
        ctm (plug {A}{B}{B'} S M) = ctm-plug S M
        ctm (plugId {A}{B}{M} i) = 
          isProp→PathP 
            (λ i → LV.isProp≤{q = (pull (plugId i) $ cty B)})
            (ctm-plug hole M) 
            (ctm M) 
            i
        ctm (subCId {A}{B}{M} i) = 
          isProp→PathP  
            (λ i → LV.isProp≤{q = (pull (subCId i) $ cty B)}) 
            (ctm-subC var M)
            (ctm M) 
            i
        ctm (plugDist {A}{A'}{B}{B'}{S}{S'}{M} i) = 
          isProp→PathP 
            (λ i → LV.isProp≤{q = (pull (plugDist i) $ cty B')}) 
            (ctm-plug S' (plug S M)) 
            (ctm-plug (kcomp' S S') M)
            i
        ctm (subDist {A}{A'}{A''}{B}{V}{V'}{M} i) = 
          isProp→PathP 
            (λ i → LV.isProp≤{q = (pull (subDist i) $ cty B)}) 
            (ctm-subC V (subC V' M)) 
            (ctm-subC (subV V V') M)
            i
        ctm (plugSub {A}{A'}{B}{B'}{V}{M}{S} i) =           
          isProp→PathP 
            (λ i → LV.isProp≤{q = (pull (plugSub i) $ cty B')}) 
            (ctm-subC V (plug S M)) 
            (ctm-plug S (subC V M))
            i
        ctm (isSet⊢c M₁ M₂ x y i i₁) = {!   !}
        ctm (M ,, M') = ⋀-intro (prod _ _) (ctm M) (ctm M')
        ctm (π₁ M) = ⋀-elim1 (prod _ _) (ctm M)
        ctm (π₂ M) = ⋀-elim2 (prod _ _) (ctm M)
        ctm (&β₁ {A}{B}{B'}{M}{N} i) = 
          isProp→PathP 
            (λ i → LV.isProp≤{q = (pull (&β₁ i) $ cty B)}) 
            (⋀-elim1 (prod B B') (⋀-intro (prod B B') (ctm M) (ctm N)))
            (ctm M)
            i
        ctm (&β₂ {A}{B}{B'}{M}{N} i) = 
          isProp→PathP 
            (λ i → LV.isProp≤{q = (pull (&β₂ i) $ cty B')}) 
            (⋀-elim2 (prod B B') (⋀-intro (prod B B') (ctm M) (ctm N)))
            (ctm N)
            i
        ctm (&η {A}{B}{B'}{P} i) = 
          isProp→PathP 
            (λ i → LV.isProp≤{q = (pull (&η i) $ (prod B B' ⋀ cty B) (cty B'))}) 
            (⋀-intro (prod B B') (⋀-elim1 (prod B B') (ctm P)) (⋀-elim2 (prod B B') (ctm P)))
            (ctm P)
            i
        ctm (π₁Sub {A}{A'}{B}{B'}{V}{P} i) = 
          isProp→PathP 
            (λ i → LV.isProp≤{q = (pull (π₁Sub i) $ cty B)}) 
            (⋀-elim1 (prod B B') (ctm-subC V P))
            (ctm-subC V (_⊢c_.π₁ P))
            i
        ctm (π₂Sub {A}{A'}{B}{B'}{V}{P} i) = 
          isProp→PathP 
            (λ i → LV.isProp≤{q = (pull (π₂Sub i) $ cty B')}) 
            (⋀-elim2 (prod B B') (ctm-subC V P))
            (ctm-subC V (_⊢c_.π₂ P))
            i 

        -- no exists?
        ctm (σ₁ M) = ⋁-elim1 (cprod _ _) (ctm M)
        ctm (σ₂ M) = ⋁-elim2 (cprod _ _) (ctm M)
        ctm (case M M') = ⋁-intro (cprod _ _) (ctm M) (ctm M')
        ctm (+β₁ {A}{A'}{B}{M}{N} i) = 
          isProp→PathP 
            (λ i → LV.isProp≤{q = (pull (+β₁ i) $ cty B)}) 
            (⋁-elim1 (cprod A A') (⋁-intro (cprod A A') (ctm M) (ctm N)))
            (ctm M)
            i
        ctm (+β₂ {A}{A'}{B}{M}{N} i) = 
          isProp→PathP 
            (λ i → LV.isProp≤{q = (pull (+β₂ i) $ cty B)}) 
            (⋁-elim2 (cprod A A') (⋁-intro (cprod A A') (ctm M) (ctm N)))
            (ctm N)
            i
        ctm (+η {A}{A'}{B}{P} i) = 
          isProp→PathP 
            (λ i → LV.isProp≤{q = (pull (+η i) $ cty B)}) 
            (⋁-intro (cprod A A') (⋁-elim1 (cprod A A') (ctm P)) (⋁-elim2 (cprod A A') (ctm P)))
            (ctm P)
            i
        ctm (σ₁Sub {A}{A'}{B}{B'}{S}{P} i) = 
          isProp→PathP 
            (λ i → LV.isProp≤{q = (pull (σ₁Sub i) $ cty B')}) 
            (⋁-elim1 (cprod A A') (ctm-plug S P))
            (ctm-plug S (_⊢c_.σ₁ P))
            i
        ctm (σ₂Sub {A}{A'}{B}{B'}{S}{P} i) = 
          isProp→PathP 
            (λ i → LV.isProp≤{q = (pull (σ₂Sub i) $ cty B')}) 
            (⋁-elim2 (cprod A A') (ctm-plug S P))
            (ctm-plug S (_⊢c_.σ₂ P))
            i
        ctm ret = pushToPull L push ret LC.id⊢
        ctm (Fβ {A}{B}{M} i) = 
          isProp→PathP 
            (λ i → LV.isProp≤{q = (pull (Fβ i) $ cty B)}) 
            (ctm M) 
            (ctm-plug (bind' M) ret)
            i
        ctm force = LV.id⊢
        ctm (Uβ {A}{B}{M} i) = 
          isProp→PathP 
            ((λ i → LV.isProp≤{q = (pull (Uβ i) $ cty B)})) 
            (ctm-subC (thunk M) force) 
            (ctm M) 
            i
        ctm beep = {!   !}

      SV : Section Id (Modelᴰ.Vᴰ M L)
      SV .Section.F-obᴰ = vty
      SV .Section.F-homᴰ = vtm
      SV .Section.F-idᴰ = LV.isProp≤ _ _
      SV .Section.F-seqᴰ _ _ = LV.isProp≤ _ _

      SC : Section Id (Modelᴰ.Cᴰ M L) 
      SC .Section.F-obᴰ = cty
      SC .Section.F-homᴰ = ktm
      SC .Section.F-idᴰ = LC.isProp≤ _ _
      SC .Section.F-seqᴰ _ _ = LC.isProp≤ _ _

      M-elim : MSection {M = M}{M} (idModelMorphism M) L 
      M-elim .fst = SV
      M-elim .snd .fst = SC
      M-elim .snd .snd = ctm
