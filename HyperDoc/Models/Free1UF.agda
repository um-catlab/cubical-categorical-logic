  {-# OPTIONS --allow-unsolved-metas #-}
  {-# OPTIONS --type-in-type #-}
  module HyperDoc.Models.Free1UF where 

  -- Free model with 
  -- 1 , U for value type 
  -- F for computation types

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
  open import Cubical.Categories.Displayed.Section.Base
  open import Cubical.Categories.Displayed.Base
  open import Cubical.Categories.Displayed.Limits.Terminal
  open import Cubical.Categories.Displayed.Functor
  open import Cubical.Categories.NaturalTransformation.Base


  open import HyperDoc.Lib
  open import HyperDoc.CBPVModel
  open import HyperDoc.CBPVLogic
  open import HyperDoc.Section
  open import HyperDoc.Syntax
  open import HyperDoc.Connectives.Connectives

  open Category
  open Categoryᴰ
  open Functor
  open Functorᴰ
  open PshHom
  open PshIso
  open PreorderStr
  open NatTrans

  record Raw (ℓV ℓV' ℓC ℓC' ℓS : Level) : Type (levels (ℓsuc (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ []))) where 
    field 
      VG : Graph ℓV ℓV' 
      CG : Graph ℓC ℓC' 
      OF : VG .Node → CG .Node → Type ℓS

  module Syntax
    {ℓV ℓV' ℓC ℓC' ℓS : Level }
    (R : Raw ℓV ℓV' ℓC ℓC' ℓS) where

    open Raw R 

    mutual 
      data VTy : Type (levels (ℓV ∷ ℓC ∷ [])) where 
        inV : VG .Node → VTy
       -- _+_ : VTy → VTy → VTy
        one : VTy 
        U : CTy → VTy 

      data CTy : Type (levels (ℓV ∷ ℓC ∷ [])) where
        inC : CG .Node →  CTy
        F : VTy → CTy    

    -- TODO
    -- adjust the syntax so naturality comes "for free"
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
      -- include generators
      incVal : ∀{A A'} → VG .Edge A A' → inV A ⊢v inV A'

      -- category 
      subV : ∀ {A A' A''} → A ⊢v A' → A' ⊢v A'' → A ⊢v A''
      var : ∀ {A} → A ⊢v A
      subVIdl : ∀ {A A'} → (V : A ⊢v A') → subV (var {A}) V ≡ V
      subVIdr : ∀ {A A'} → (V : A ⊢v A') → subV V (var {A'}) ≡ V
      subVAssoc : ∀ {A₁ A₂ A₃ A₄}(V : A₁ ⊢v A₂)(W : A₂ ⊢v A₃)(Y : A₃ ⊢v A₄) → 
        subV (subV V W) Y ≡ subV V (subV W Y)

      -- type structure
      tt : ∀{A} → A ⊢v one
      oneη : ∀{A}{V : A ⊢v one} → tt ≡ V

      thunk : ∀{A B} → A ⊢c B → A ⊢v U B
      Uη : ∀{A B}{V : A ⊢v U B} →  thunk (subC' V force') ≡ V

      isSet⊢v : ∀{A A'} → isSet (A ⊢v A')


    data _⊢c_ where 
      ret : ∀{A } → A ⊢c F A
      incOb : ∀{A B} → OF A B → inV A ⊢c inC B
      
      subC : ∀ {A A' B} → A ⊢v A' → A' ⊢c B → A ⊢c B
      plug : ∀ {A B B'} → B ⊢k B' → A ⊢c B → A ⊢c B'

    

      Fβ : ∀{A B}{M : A ⊢c B} → M ≡ plug (bind' M) ret
      force : ∀{B} → U B ⊢c B
      Uβ : ∀ {A B} → {M : A ⊢c B} → subC (thunk M) force ≡ M

      -- interaction laws (profunctor action)
      plugId : ∀ {A B}{M : A ⊢c B} → plug (hole' {B}) M ≡ M
      subCId : ∀ {A B}{M : A ⊢c B} → subC (var {A}) M ≡ M
      plugDist : ∀ {A B B' B''}{S : B ⊢k B'}{S' : B' ⊢k B''}{M : A ⊢c B} → --rcomp
        plug S' (plug S M) ≡ plug (kcomp' S S') M
      subDist : ∀ {A A' A'' B}{V : A ⊢v A'}{V' : A' ⊢v A''}{M : A'' ⊢c B} → --lcomp
        subC V (subC V' M) ≡ subC (subV V V') M
      plugSub : ∀ {A A' B B'}{V : A ⊢v A'}{M : A' ⊢c B}{S : B ⊢k B'} → 
        subC V (plug S M) ≡ plug S (subC V M)

      -- just encode effect
      beep : one ⊢c F one

      isSet⊢c : ∀{A B} → isSet (A ⊢c B)

    force' = force

    data _⊢k_ where 
      incComp : ∀{B B'} → CG .Edge B B' → inC B ⊢k inC B'

      -- category 
      kcomp : ∀ {B B' B''} → B ⊢k B' → B' ⊢k B'' → B ⊢k B''
      hole : ∀ {B} → B ⊢k B
      kcompIdl : ∀ {B B'} → (M : B ⊢k B') → kcomp (hole {B}) M ≡ M
      kcompIdr : ∀ {B B'} → (M : B ⊢k B') → kcomp M (hole {B'}) ≡ M
      kcompAssoc : ∀ {B₁ B₂ B₃ B₄}(M : B₁ ⊢k B₂)(N : B₂ ⊢k B₃)(P : B₃ ⊢k B₄) → 
        kcomp(kcomp M N) P ≡  kcomp M (kcomp N P)

      -- type structure 
      bind : ∀{A B} → A ⊢c B → F A ⊢k B
      Fη : ∀ {A B}{S : F A ⊢k B} → S ≡ bind (plug S ret)

      isSet⊢k : ∀{B B'} → isSet (B ⊢k B')

    hole' = hole
    kcomp' = kcomp
    ret' = ret
    bind' = bind
    subC' = subC

  module FreeModel 
    {ℓV ℓV' ℓC ℓC' ℓS : Level }
    (R : Raw ℓV ℓV' ℓC ℓC' ℓS) where 

    open Syntax R

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


  module Interp where 


  module Initiality where 

    asGraph : ∀{ℓ ℓ'} → Category ℓ ℓ' → Graph ℓ ℓ' 
    asGraph C = record { Node = C .ob ; Edge = C .Hom[_,_] }

    record ModelInterpretation
      {ℓVS ℓV'S ℓCS ℓC'S ℓSS ℓVT ℓV'T ℓCT ℓC'T ℓST : Level}
      (R : Raw ℓVS ℓV'S ℓCS ℓC'S ℓSS)
      (M : Model ℓVT ℓV'T ℓCT ℓC'T ℓST )
      : Type (levels (ℓsuc (ℓVS ∷ ℓV'S ∷ ℓCS ∷ ℓC'S ∷ ℓSS ∷ ℓVT ∷ ℓV'T ∷ ℓCT ∷ ℓC'T ∷ ℓST ∷ []))) where
      open Raw R
      
      open Syntax R
      open GraphHom
      private
        module M = Model M
      field 
        interpV : GraphHom VG (asGraph M.V)
        interpC : GraphHom CG (asGraph M.C)
        interpO : ∀ (A : VG .Node)(B : CG .Node) → inV A ⊢c inC B → ⟨ M.O .F-ob ((interpV $g A) , (interpC $g B) ) ⟩ 


    module _     
      {ℓVS ℓV'S ℓCS ℓC'S ℓSS ℓVT ℓV'T ℓCT ℓC'T ℓST : Level}
      {R : Raw ℓVS ℓV'S ℓCS ℓC'S ℓSS}
      {(M , V⊤  , UTy , FTy ) : ModelWithTypeStructure ℓVS ℓV'S ℓCS ℓC'S ℓSS}
      (interp : ModelInterpretation R M) where

      open FreeModel R renaming (M to Free) hiding (V ; C ; O)
      open ModelMorphism 
      open Syntax R
      open ModelInterpretation interp

      private 
        module Free = Model Free
        module M = Model M
        module Syn = TypeSyntax (M , V⊤  , UTy , FTy ) 


      module _ (interpBeep : ⟨ M.O .F-ob (Syn.⊤ , Syn.F Syn.⊤) ⟩) where 

        mutual 
          vty : VTy → M.V .ob
          vty (inV N) = interpV $g  N
          -- vty (A + A') = vty A Syn.+ vty A'
          vty one = Syn.⊤
          vty (U B) = Syn.U (cty B)

          cty : CTy → M.C .ob
          cty (inC N) = interpC $g N
          cty (F A) = Syn.F (vty A) 

        mutual 
          vterm : ∀{A A'} → A ⊢v A' →  M.V .Hom[_,_] (vty A) (vty A') 
          vterm (incVal V) = interpV <$g> V
          vterm (subV V W) = vterm V ⋆⟨ M.V ⟩ vterm W
          vterm (var {A = A})  = M.V .id {vty A}
          vterm (subVIdl V i) = M.V .⋆IdL (vterm V) i
          vterm (subVIdr V i) = M.V .⋆IdR (vterm V) i
          vterm (subVAssoc V W Y i) = M.V .⋆Assoc (vterm V) (vterm W) (vterm Y)  i
          vterm tt = Syn.tt
          vterm (oneη {A}{V} i) = Syn.⊤η  {A = vty A}{t = vterm V} i
          vterm (thunk x) = Syn.thunk (cterm x)
          vterm (Uη {A}{B}{V} i) = Syn.Uη {vty A}{cty B}{vterm V} i
          vterm (isSet⊢v V W x y i i₁) = M.V .isSetHom (vterm V) (vterm W) (cong vterm x) (cong vterm y)  i i₁

          kterm : ∀{B B'} → B ⊢k B' →  M.C .Hom[_,_] (cty B) (cty B')
          kterm (incComp M) = interpC <$g> M
          kterm (kcomp S S') = kterm S ⋆⟨ M.C ⟩ kterm S'
          kterm (hole {B}) = M.C .id {cty B}
          kterm (kcompIdl S i) = M.C .⋆IdL (kterm S) i
          kterm (kcompIdr S i) = M.C .⋆IdR (kterm S) i
          kterm (kcompAssoc S R T i) = M.C .⋆Assoc (kterm S) (kterm R) (kterm T)  i
          kterm (bind M) = Syn.bind (cterm M)
          kterm (Fη i) = {!   !}
          kterm (isSet⊢k S S' x y i i₁) = M.C .isSetHom (kterm S) (kterm S') (cong kterm x) (cong kterm y)  i i₁ 

          cterm : {A : VTy}{B : CTy}(M : A ⊢c B) → ⟨ M.O .F-ob ((vty A) , (cty B)) ⟩
          cterm ret = Syn.ret
          cterm (incOb {A}{B} M) = interpO A B (incOb M)
          cterm (subC V M) = M.lcomp (vterm V) (cterm M)
          cterm (plug S M) = M.rcomp (kterm S) (cterm M)
          cterm (Fβ {A}{B}{M} i) = {!   !}
          cterm force = Syn.force
          cterm (Uβ {A}{B}{M} i) = Syn.Uβ {vty A}{cty B}{cterm M} i
          cterm (plugId {A}{B}{M} i) = M.rcompId {vty A}{cty B}{cterm M} i 
          cterm (subCId {A}{B}{M} i) = M.lcompId {vty A}{cty B}{cterm M} i
          cterm (plugDist {A}{B}{B'}{B''}{S}{S'}{M} i) = M.rcompSeq {vty A }{cty B}{cty B'}{cty B''}{kterm S}{kterm S'}{cterm M} i
          cterm (subDist {A}{A'}{A''}{B}{V}{V'}{M} i) = M.lcompSeq {vty A }{vty A'}{vty A''}{cty B}{vterm V}{vterm V'}{cterm M} i
          cterm (plugSub {A}{A'}{B}{B'}{V}{M}{S} i) =  M.lrSeq {vty A}{vty A'}{cty B}{cty B'}{vterm V}{cterm M}{kterm S} i
          cterm beep = interpBeep
          cterm (isSet⊢c {A}{B}M N x y i j) = 
            (SET ℓSS) .isSetHom 
              {M.O .F-ob (vty A , cty B)}
              {M.O .F-ob (vty A , cty B)}
              (λ x → cterm M) 
              (λ x → cterm N) 
              (funExt (λ _ → cong cterm x)) 
              (funExt (λ _ → cong cterm y)) 
              i j (cterm M)

        M-rec : ModelMorphism _ _ _ _ _ _ _ _ _ _  Free M 
        M-rec .FV .F-ob = vty
        M-rec .FV .F-hom = vterm
        M-rec .FV .F-id = refl
        M-rec .FV .F-seq _ _ = refl

        M-rec .FC .F-ob = cty
        M-rec .FC .F-hom = kterm
        M-rec .FC .F-id = refl
        M-rec .FC .F-seq _ _ = refl

        M-rec .FO .N-ob (A , B) M = cterm M
        M-rec .FO .N-hom (A , B)(A' , B') (f , g) h = {!   !}
          -- funExt⁻ (sym (M.O .F-seq _ _)) _ ∙ cong₂ (M.O .F-hom) (ΣPathP ((M.V .⋆IdR _) , M.C .⋆IdR _)) refl

    module _ 
      {ℓV ℓV' ℓC ℓC' ℓP ℓP'  : Level} 
      {R : Raw ℓV ℓV' ℓC ℓC' (ℓ-max ℓP ℓP')} where 
            
            
      open FreeModel R renaming (M to Free)

      module _
        (L : Logic Free) 
        (Top : L⊤.Has⊤ (Logic.VH L))
        (push : hasPush L)
        where 

        open import HyperDoc.AsDisplayed

        open Logic L
        
        open Syntax R --  hiding (F)

        open import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
        module LV = HDSyntax VH
        module LC = HDSyntax CH


        open Model Free
        open Modelᴰ Free L
        open Modelᴰstruct (terminal , utype , ftype) Top
        open TerminalᴰNotation _ Vᴰtermᴰ
        open import Cubical.Categories.Limits.Terminal.More
        open TerminalNotation Vterm

        open TerminalⱽNotation Vᴰ one (Vᴰtermⱽ one)
        

        -- ? Vᴰtermⱽ




        mutual 
          lvty : (A : VTy) → ob[ Vᴰ ] A
          lvty (inV x) = {!   !}
          lvty one = 𝟙ᴰ
          lvty (U B) = pull force .MonFun.f (lcty B)

          lcty : (B : CTy) → ob[ Cᴰ ] B
          lcty (inC x) = {!   !}
          lcty (F A) = push ret .fst .MonFun.f (lvty A)

        mutual 
          lsubC : ∀ {A A' B}→ (t : (Model.V Free) .Hom[_,_] A A' )(M : O[ A' , B ]) → A LV.◂ lvty A ≤ pull (subC t M) .MonFun.f (lcty B)
          lsubC {A}{A'}{B} V M  = VL.seq (lvtm V) (VL.seq (VL.mon* V (lctm M)) (VL.eqTo≤ ((cong (λ h → h .MonFun.f (lcty B)) (sym (cong pull (cong₂ subC refl (sym plugId)) ∙ pullLComp V M))))))

          lthunk : ∀ {A  B}→ (M : O[ A , B ]) → Hom[ Vᴰ ][ thunk M , lvty A ] (pull force .MonFun.f (lcty B))
          lthunk {A}{B} M = LV.seq (lctm M) (LV.eqTo≤ ((cong (λ h → h .MonFun.f (lcty B))) (cong pull (sym Uβ ∙ cong₂ subC refl (sym plugId)) ∙ pullLComp (thunk M) force)))

          {-# TERMINATING #-} -- WHY
          lvtm : {A A' : VTy} → (f : A ⊢v A') → Hom[ Vᴰ ][ f , lvty A ] (lvty A')
          -- (VH .F-ob A .fst .snd ≤ lvty A) (VH .F-hom f .MonFun.f (lvty A'))
          lvtm (incVal x) = {!   !}
          lvtm (subV f g) = Categoryᴰ._⋆ᴰ_  Vᴰ (lvtm f) (lvtm g)
          lvtm var = Categoryᴰ.idᴰ Vᴰ 
          lvtm (subVIdl f i) = Categoryᴰ.⋆IdLᴰ Vᴰ  (lvtm f) i
          lvtm (subVIdr f i) = Categoryᴰ.⋆IdRᴰ Vᴰ  (lvtm f) i
          lvtm (subVAssoc f g h i) = Categoryᴰ.⋆Assocᴰ Vᴰ  (lvtm f) (lvtm g) (lvtm h) i
          lvtm (tt {A}) = !tⱽ tt (lvty A)
          lvtm (oneη {A}{V} i) = VL.eq*PathP (oneη {A}{V}) (!tⱽ tt (lvty A)) (lvtm V) i
            -- VL.eq*PathP (oneη {A}{V}) (!tⱽ tt (lvty A)) (lvtm V) i
          lvtm (thunk {A}{B} M) = lthunk M
           --  LV.seq (lctm M) (LV.eqTo≤ ((cong (λ h → h .MonFun.f (lcty B))) (cong pull (sym Uβ ∙ cong₂ subC refl (sym plugId)) ∙ pullLComp (thunk M) force)))
            {-goal where 

            have : A LV.◂ lvty A ≤ pull M .MonFun.f (lcty B)
            have = lctm M

            have' : pull M ≡ MonComp (pull force) (VH .F-hom (thunk M))
            have' = cong pull (sym Uβ ∙ cong₂ subC refl (sym plugId)) ∙ pullLComp (thunk M) force

            goal : A LV.◂ lvty A ≤ LV.f* (thunk M) (pull force .MonFun.f (lcty B))
            goal = LV.seq have (LV.eqTo≤ ((cong (λ h → h .MonFun.f (lcty B))) have'))
            -}

          lvtm (Uη {A}{B}{V} i) = isProp→PathP {B = λ i → Hom[ Vᴰ ][ Uη i , lvty A ] (pull force .MonFun.f (lcty B))}(λ i₁ →
                  IsPreorder.is-prop-valued (isPreorder (VH .F-ob A .fst .snd))
                  (lvty A) (HDSyntax.f* VH (Uη i₁) (pull force .MonFun.f (lcty B)))) (lthunk (subC' V force')) (lvtm V) i 
          {-
          
          Hom[ Vᴰ ][ Uη i , lvty A ] (pull force .MonFun.f (lcty B))
———— Boundary (wanted) —————————————————————————————————————
i = i0 ⊢ lthunk (subC' V force')
i = i1 ⊢ lvtm V
          -}
            --.≡out {fᴰ = lvtm (Uη {A}{B}{V} i)}{gᴰ = lvtm V} (ΣPathP ({! refl  !} , {!   !})) i --  VL.eq*PathP (Uη {A}{B}{V})  {! lsubC {A} V ? !} (lvtm V) i
            {-}
             isProp→PathP {B = λ i → Hom[ Vᴰ ][ Uη i , lvty A ] (pull force .MonFun.f (lcty B))}(λ i₁ →
                  IsPreorder.is-prop-valued (isPreorder (VH .F-ob A .fst .snd))
                  (lvty A) (HDSyntax.f* VH (Uη i₁) (pull force .MonFun.f (lcty B)))) {! lthunk ?  !} (lvtm V) i 
                  -}
            {-}
            VL.eq*PathP 
              (Uη {A}{B}{V}) 
              (transport wtf (lvtm V)) 
              -- (LV.seq (lctm (subC V {! force  !})) (LV.isProp≤ {!   !} {!   !} i))
              -- (LV.seq (lctm (subC' V force')) (LV.eqTo≤ ((cong (λ h → h .MonFun.f (lcty B))) (cong pull (sym Uβ ∙ cong₂ subC refl (sym plugId)) ∙ pullLComp (thunk (subC' V force')) force)))) 
              (lvtm V) 
              i where 

            wtf : (VH .F-ob A .fst .snd ≤ lvty A)
              (VH .F-hom V .MonFun.f
              (N-ob Sq (U B , B) force .MonFun.f (lcty B)))
              ≡
              (VH .F-ob A .fst .snd ≤ lvty A)
              (VH .F-hom (thunk (subC V force)) .MonFun.f
              (N-ob Sq (U B , B) force .MonFun.f (lcty B))) 
            wtf i = {! d !}-}
              

          lvtm (isSet⊢v f f₁ x y i j) = {! VL.isProp  !}

          lktm : {B B' : CTy} → (S : B ⊢k B') → Hom[ Cᴰ  ][ S , lcty B ] (lcty B')
          lktm (incComp x) = {!   !}
          lktm (kcomp S S') = Categoryᴰ._⋆ᴰ_ Cᴰ (lktm S) (lktm S')
          lktm hole = Categoryᴰ.idᴰ Cᴰ
          lktm (kcompIdl S i) = Categoryᴰ.⋆IdLᴰ Cᴰ (lktm S) i
          lktm (kcompIdr S i) = Categoryᴰ.⋆IdRᴰ Cᴰ (lktm S) i
          lktm (kcompAssoc S S₁ S₂ i) = Categoryᴰ.⋆Assocᴰ Cᴰ (lktm S) (lktm S₁) (lktm S₂) i
          lktm (bind {A}{B} M) = goal where 

            have : pull M ≡ MonComp (CH .F-hom (bind M)) (pull ret)
            have = cong (λ h → Sq .N-ob (A , B) h ) (sym subCId ∙ cong₂ subC refl Fβ) ∙ pullRComp (bind M) ret

            goal' : A LV.◂ lvty A ≤ pull ret .MonFun.f (CL.f* (bind M) (lcty B))
            goal' = LV.seq (lctm M) (LV.eqTo≤ (cong (λ h → h .MonFun.f (lcty B)) have))

            goal : (F A) CL.◂ push ret .fst .MonFun.f (lvty A) ≤ CL.f* (bind M) (lcty B)
            goal = pullToPush L push ret goal'

          lktm (Fη {A}{B}{S} i) = 
            LC.eq*PathP 
              (Fη {A}{B}{S}) 
              (lktm S) 
              _ 
              i
          lktm (isSet⊢k S S₁ x y i i₁) = {! Model.lcomp Free V M  !}

          lctm : {A : VTy}{B : CTy} → (M : A ⊢c B) → A LV.◂ lvty A ≤ pull M  .MonFun.f (lcty B) 
          lctm (ret {A}) = pushToPull L push ret LC.id⊢

          lctm (incOb x) = {!   !}
          lctm (subC {A}{A'}{B} V M) = lsubC V M where 
            alt : A LV.◂ lvty A ≤ pull (Model.O Free .F-hom (V , hole) M) .MonFun.f {!   !}
            alt = Oᴰ  .F-homᴰ  {f = V , hole}(lvtm V , CL.id⊢) M {! lctm M  !}

          --   VL.seq (lvtm V) (VL.seq (VL.mon* V (lctm M)) (VL.eqTo≤ ((cong (λ h → h .MonFun.f (lcty B)) (sym (cong pull (cong₂ subC refl (sym plugId)) ∙ pullLComp V M))))))
            {-goal where 

            have : A VL.◂ lvty A ≤ VL.f* V (lvty A') 
            have = lvtm V

            have' : A' VL.◂ lvty A' ≤ pull M .MonFun.f (lcty B) 
            have' = lctm M

            have'' : pull (subC V M) ≡ MonComp (pull M) (VH .F-hom V)
            have'' = cong pull (cong₂ subC refl (sym plugId)) ∙ pullLComp V M
            
            goal : A VL.◂ lvty A ≤ pull (subC V M) .MonFun.f (lcty B)
            goal = VL.seq have (VL.seq (VL.mon* V have') (VL.eqTo≤ ((cong (λ h → h .MonFun.f (lcty B)) (sym have'')))))
-}
          lctm (plug {A}{B}{B'} S M) = goal where 
            alt : A LV.◂ VH .F-hom var .MonFun.f (lvty A) ≤ pull (subC var (plug S M)) .MonFun.f (lcty B')
            --N-ob Sq (A , B') (Model.O Free .F-hom (var , S) M) .MonFun.f
            --   (lcty B')
            atl = Oᴰ  .F-homᴰ {f = var , S} (VL.id⊢ , lktm S) M (lctm M)

            have : A LV.◂ lvty A ≤ pull M .MonFun.f (lcty B)
            have = lctm  M

            have' : B CL.◂ lcty B ≤ CL.f* S (lcty B') 
            have' = lktm S

            have'' : pull M .MonFun.f (CL.f* S (lcty B')) ≡ pull (plug S M) .MonFun.f (lcty B')
            have'' = 
              cong (λ h → h .MonFun.f (lcty B')) 
                (sym (cong (λ h → Sq .N-ob (A , B') h) (sym subCId) ∙ pullRComp S M))

            goal : A VL.◂ lvty A ≤ pull (plug S M) .MonFun.f (lcty B')
            goal = VL.seq have (VL.seq (pull M .MonFun.isMon have') (VL.eqTo≤ have''))
          lctm (Fβ i) = {!   !}
          lctm (force {B}) = LV.id⊢
            -- IsPreorder.is-refl (isPreorder (VH .F-ob (U _) .fst .snd)) (lvty (U _))
          lctm (Uβ i) = {!  VL.eq*PathP ? ? ? i  !}
          lctm (plugId i) = {! VL.eq*PathP ? ? ? i !}
            -- plug hole M ≡ M
          lctm (subCId {A}{B}{M} i) =
            
              isProp→PathP 
                {B = λ i → A LV.◂ lvty A ≤ pull (subCId i) .MonFun.f (lcty B)} 
                (λ i₁ →
                     IsPreorder.is-prop-valued (isPreorder (VH .F-ob A .fst .snd))
                     (lvty A) (pull (subCId i₁) .MonFun.f (lcty B))) 
                (lsubC var M)
                (lctm M) 
                i 
                
          lctm (plugDist i) = {! d !}
          lctm (subDist i) = {!   !}
          lctm (plugSub i) = {!   !}
          lctm beep = {!   !}
          lctm (isSet⊢c M M₁ x y i i₁) = {!   !}


        SV : Section Id (Modelᴰ.Vᴰ Free L) 
        SV .Section.F-obᴰ = lvty
        SV .Section.F-homᴰ = lvtm
        SV .Section.F-idᴰ = VL.isProp≤  _ _
        SV .Section.F-seqᴰ _ _ = VL.isProp≤  _ _

        SC : Section Id (Modelᴰ.Cᴰ Free L) 
        SC .Section.F-obᴰ = lcty
        SC .Section.F-homᴰ = lktm
        SC .Section.F-idᴰ = CL.isProp≤  _ _
        SC .Section.F-seqᴰ _ _ = CL.isProp≤  _ _

        M-elim : MSection {M = Free}{Free} (idModelMorphism Free) L
        M-elim .fst = SV
        M-elim .snd .fst = SC
        M-elim .snd .snd = lctm

