{-# OPTIONS --type-in-type #-}

module HyperDoc.Operational.Initial where

open import Cubical.Data.Maybe

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor


open Category
open Functor

mutual 
  data VTy : Type where 
    𝟙 Ans : VTy
    U : CTy → VTy 

  data CTy : Type where 
    F : VTy → CTy

data _⊢v_ : (A A' : VTy) → Type 
data _⊢c_ : (A : VTy)(B : CTy) → Type 
data _⊢k_ : (B B' : CTy) → Type 

subC' : ∀ {A A' B} → A ⊢v A' → A' ⊢c B → A ⊢c B

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
  tt : ∀{A} → A ⊢v 𝟙
  yes : ∀{A} → A ⊢v Ans 
  no : ∀{A} → A ⊢v Ans 
  thunk : ∀{A B} → A ⊢c B → A ⊢v U B


data _⊢k_ where
  -- category 
  kcomp : ∀ {B B' B''} → B ⊢k B' → B' ⊢k B'' → B ⊢k B''
  hole : ∀ {B} → B ⊢k B
  kcompIdl : ∀ {B B'} → (M : B ⊢k B') → kcomp (hole {B}) M ≡ M
  kcompIdr : ∀ {B B'} → (M : B ⊢k B') → kcomp M (hole {B'}) ≡ M
  kcompAssoc : ∀ {B₁ B₂ B₃ B₄}(M : B₁ ⊢k B₂)(N : B₂ ⊢k B₃)(P : B₃ ⊢k B₄) → 
    kcomp(kcomp M N) P ≡  kcomp M (kcomp N P)
  isSet⊢k : ∀{B B'} → isSet (B ⊢k B')

  bind : {A : VTy}{B : CTy} → A ⊢c B → F A ⊢k B

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

  -- type structure
  ret : ∀{A A'} → A ⊢v A' → A ⊢c F A'
  force : ∀{A B} →  A ⊢v U B → A ⊢c B   
  force-sub : ∀{A A' B}{V : A' ⊢v A}{W : A ⊢v U B} → 
    subC V (force W) ≡ force (subV V W)

subC' = subC

import  Cubical.Data.Equality as Eq

data _↦_ : {A : VTy}{B : CTy} → A ⊢c B → A ⊢c B → Type where 
  Fβ : ∀{A A' B}{V : A ⊢v A'}{M : A' ⊢c B} → 
    ------------------------------------
    plug (bind M) (ret V) ↦ (subC V M)

  Uβ : ∀ {A B} {M : A ⊢c B} → 
    ---------------------
    force (thunk M) ↦ M
  
  subC-cong : ∀ {A A' B}{V : A' ⊢v A}{M M' : A ⊢c B}  →  
    M ↦ M' → 
    --------- 
    subC V M  ↦ subC V M'

  plug-cong : ∀ {A B B'}{S : B ⊢k B'}{M M' : A ⊢c B}  →  
    M ↦ M' → 
    --------- 
    plug S M ↦ plug S M'

  isProp↦ : ∀ {A B} {M M' : A ⊢c B} → isProp (M ↦ M')


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

open import HyperDoc.Operational.TransitionSystemAltAlt 

TSys : VTy → CTy → ob TSysCat
TSys A B .fst = A ⊢c B
TSys A B .snd = _↦_ {A}{B}

open import Cubical.Data.Sigma 
O :  Functor ((V ^op) ×C C) TSysCat
O .F-ob (A , B) = TSys A B
O .F-hom (V , S) .fst M = subC V (plug S M)
O .F-hom (V , S) .snd {M}{M'} M↦M' = subC-cong (plug-cong M↦M')
O .F-id = Σ≡Prop (λ f → isPropImplicitΠ  λ M → isPropImplicitΠ  λ M' → isProp→ isProp↦) 
  (funExt λ M → subCId ∙ plugId)
O .F-seq (V , S)(V' , S') = 
  Σ≡Prop (λ f → isPropImplicitΠ  λ M → isPropImplicitΠ  λ M' → isProp→ isProp↦)  
    (funExt (λ M → sym (subDist )  ∙ cong₂ subC refl (cong₂ subC refl (sym plugDist) ∙  plugSub)))


open import HyperDoc.Operational.ModelAlt
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open NatTrans 

Syn : CBPVModel
Syn .CBPVModel.V = V
Syn .CBPVModel.C = C
Syn .CBPVModel.O = O

open CBPVModel using (O[_,-])


CL : CBPVMorphism Syn SetModel 
CL .CBPVMorphism.FV = V [ 𝟙 ,-]
CL .CBPVMorphism.FC = O[_,-] Syn 𝟙
CL .CBPVMorphism.FO .N-ob (A , B) .fst M V = subC V M
CL .CBPVMorphism.FO .N-ob (A , B) .snd {M}{M'} M↦M' V = subC-cong M↦M' 
CL .CBPVMorphism.FO .N-hom {A , B}{A' , B'} (V , S) = 
  ΣPathP ((funExt λ M → funExt λ V' → (subDist ∙ plugSub) ∙ sym subCId) ,
     toPathP (implicitFunExt λ {N} → implicitFunExt λ {N'} → funExt λ N↦N' → funExt λ V' → isProp↦ _ _))


open import HyperDoc.Syntax
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Functor 
open Functorᴰ

idCBPVMorphism : {M : CBPVModel} → CBPVMorphism M M 
idCBPVMorphism {M} .CBPVMorphism.FV = Id
idCBPVMorphism {M} .CBPVMorphism.FC = Id
idCBPVMorphism {M} .CBPVMorphism.FO .N-ob = λ x → (λ z → z) , (λ {a} {a'} z → z)
idCBPVMorphism {M} .CBPVMorphism.FO .N-hom _ = refl

open import Cubical.Categories.Displayed.Base
open Categoryᴰ

module CBPVSection 
  {M N : CBPVModel} 
  {F : CBPVMorphism M N}
  {Nᴰ : CBPVModelᴰ N}
    where

  private
    module Nᴰ = CBPVModelᴰ Nᴰ 
    module F = CBPVMorphism F 
    module M = CBPVModel M
    module N = CBPVModel N 

  module _ 
    (SV : Section F.FV Nᴰ.Vᴰ)
    (SC : Section F.FC Nᴰ.Cᴰ) where 
    private
      module SV = Section SV 
      module SC = Section SC 


    record SectionNat : Type where 
      field 
        N-obᴰ : {A : ob M.V}{B : ob M.C} → (M : M.O'[ A , B ]) → Nᴰ.Oᴰ'[ F.FO .N-ob _ .fst M ][ SV.F-obᴰ A , SC.F-obᴰ B ]
        -- needs to be a tsystem morphism, maps rel to displayed rel
        N-obᴰRel :{A : ob M.V}{B : ob M.C}{M M' : M.O'[ A , B ]}{M↦M' : M._↦O_ M M' } → 
          Nᴰ.Oᴰ .F-obᴰ (SV.F-obᴰ A , SC.F-obᴰ B) .snd (N-ob F.FO (A , B) .snd M↦M') (N-obᴰ M) (N-obᴰ M')

        -- ^ map into a displayed transition system
        -- naturality, morphism component 
        N-homᴰ : {A A' : ob M.V}{B B' : ob M.C}(V : M.V [ A' , A ])(S : M.C [ B , B' ])(M : M.O'[ A , B ]) →  
          PathP  
            (λ i → F-obᴰ Nᴰ.Oᴰ (SV.F-obᴰ A' , SC.F-obᴰ B') .fst (N-hom F.FO (V , S) i .fst M)) 
            (N-obᴰ  (M.O .F-hom (V , S) .fst M)) 
            (F-homᴰ Nᴰ.Oᴰ (SV.F-homᴰ V , SC.F-homᴰ S) .fst (N-ob F.FO (A , B) .fst M) (N-obᴰ M))
        -- naturality, relation component
        -- this is .. yuck
        N-homᴰRel : {A A' : ob M.V}{B B' : ob M.C}(V : M.V [ A' , A ])(S : M.C [ B , B' ])  → 
          PathP 
            (λ i → 
              {M M' : M.O .F-ob (A , B) .fst} → 
              M._↦O_ M M'  → 
              Σ (Nᴰ.M.O .F-ob (F.FV .F-ob A' , F.FC .F-ob B') .snd (N-hom F.FO (V , S) i .fst M) (N-hom F.FO (V , S) i .fst M')) 
                λ sRs' → F-obᴰ Nᴰ.Oᴰ (SV.F-obᴰ A' , SC.F-obᴰ B') .snd sRs' (N-homᴰ V S M i) (N-homᴰ V S M' i))
             (λ M↦M' → (N-ob F.FO (A' , B') .snd (M.O .F-hom (V , S) .snd  M↦M' )) , N-obᴰRel)
              λ {M}{M'} M↦M' → Nᴰ.M.O .F-hom (F.FV .F-hom V , F.FC .F-hom S) .snd ((N-ob F.FO (A , B) .snd M↦M')) , 
                      F-homᴰ Nᴰ.Oᴰ (SV.F-homᴰ V , SC.F-homᴰ S) .snd (N-obᴰ M) (N-obᴰ M') N-obᴰRel 
  CBPVSection : Type 
  CBPVSection = 
    Σ[ SV ∈  Section F.FV Nᴰ.Vᴰ ] 
    Σ[ SC ∈  Section F.FC Nᴰ.Cᴰ ]  
    SectionNat SV SC

CBPVGlobalSection : (M : CBPVModel) → CBPVModelᴰ M →  Type 
CBPVGlobalSection M Mᴰ = CBPVSection.CBPVSection {M}{M}{idCBPVMorphism} {Mᴰ}

-- Should be able to construct a total model, and then define a map into it


module TotalConstruction'
  (M N : CBPVModel)
  (F : CBPVMorphism M N)
  (Nᴰ : CBPVModelᴰ N) where
  open import Cubical.Categories.Constructions.TotalCategory
  open import Cubical.Categories.Displayed.BinProduct

  module M = CBPVModel M 
  module N = CBPVModel N 
  module F = CBPVMorphism F
  module Nᴰ = CBPVModelᴰ Nᴰ

  ΣTSys : Functor (∫C TSysCatᴰ) (TSysCat)
  ΣTSys .F-ob (S , Sᴰ) = ∫TS S Sᴰ
  ΣTSys .F-hom {S , Sᴰ}{T , Tᴰ} (f , fᴰ) = ∫TSHom {S}{T}{Sᴰ}{Tᴰ} f  fᴰ 
  ΣTSys .F-id = refl
  ΣTSys .F-seq _ _ = refl

  conv : Functor ((∫C Nᴰ.Vᴰ ^op) ×C ∫C Nᴰ.Cᴰ) (∫C ((Nᴰ.Vᴰ ^opᴰ) ×Cᴰ Nᴰ.Cᴰ))
  conv .F-ob ((A , Aᴰ),(B , Bᴰ)) = (A , B) , Aᴰ , Bᴰ 
  conv .F-hom = λ z → (z .fst .fst , z .snd .fst) , z .fst .snd , z .snd .snd
  conv .F-id = refl
  conv .F-seq _ _ = refl

  TotalModel : CBPVModel 
  TotalModel .CBPVModel.V = ∫C Nᴰ.Vᴰ
  TotalModel .CBPVModel.C = ∫C Nᴰ.Cᴰ
  TotalModel .CBPVModel.O = ΣTSys ∘F ∫F (Nᴰ.Oᴰ) ∘F conv

  open CBPVSection {M}{N}{F} {Nᴰ}

  module _   (S : CBPVSection )  where 
    SO = S .snd .snd 
    module SV = Section (S .fst)
    module SC = Section (S .snd .fst)

    map : CBPVMorphism M TotalModel 
    map .CBPVMorphism.FV .F-ob A = (F.FV .F-ob A) , SV.F-obᴰ A
    map .CBPVMorphism.FV .F-hom f = (F.FV .F-hom f) , SV.F-homᴰ f
    map .CBPVMorphism.FV .F-id = ΣPathP ((F.FV .F-id) , SV.F-idᴰ)
    map .CBPVMorphism.FV .F-seq _ _ = ΣPathP ((F.FV .F-seq _ _) , (SV.F-seqᴰ _ _))
    map .CBPVMorphism.FC .F-ob A = (F.FC .F-ob A) , SC.F-obᴰ A
    map .CBPVMorphism.FC .F-hom f = (F.FC .F-hom f) , SC.F-homᴰ f
    map .CBPVMorphism.FC .F-id = ΣPathP ((F.FC .F-id) , SC.F-idᴰ)
    map .CBPVMorphism.FC .F-seq _ _ = ΣPathP ((F.FC .F-seq _ _) , (SC.F-seqᴰ _ _))
    {-NatTrans M.O ((ΣTSys ∘F ∫F Nᴰ.Oᴰ ∘F conv) ∘F ((CBPVMorphism.FV map ^opF) ×F CBPVMorphism.FC map)) -} 
    -- components are transition system morphisms 
    -- α_{A , B} : TSysCat [ M.O .F-ob (A , B) , ((ΣTSys ∘F ∫F Nᴰ.Oᴰ ∘F conv) ∘F ((CBPVMorphism.FV map ^opF) ×F CBPVMorphism.FC map)) .F-ob (A , B) ]
    map .CBPVMorphism.FO .N-ob (A , B).fst M = (N-ob F.FO (A , B) .fst M) , CBPVSection.SectionNat.N-obᴰ (S .snd .snd) M
    map .CBPVMorphism.FO .N-ob (A , B) .snd {M}{M'} M↦M' = N-ob F.FO (A , B) .snd M↦M' , SO .SectionNat.N-obᴰRel {M↦M' = M↦M'}
    -- naturality is equality of transition system morphisms
    -- transition system mophisms are not some function with structure 
    -- where equality of morphisms is determined by equality of the underlying maps
    -- Transition systems are defined to be proof relevant relations.. 
    map .CBPVMorphism.FO .N-hom {A , B}{A' , B'}(V , S) = 
      ΣPathP ((funExt (λ M → 
        ΣPathP (
            (λ i → (F.FO .N-hom (V , S)) i  .fst M) , 
            CBPVSection.SectionNat.N-homᴰ SO V S M))) , 
        -- could be blown away if we have prop valued relations
        CBPVSection.SectionNat.N-homᴰRel SO V S) 


module TotalConstruction
  (M : CBPVModel)
  (Mᴰ : CBPVModelᴰ M) where
  open import Cubical.Categories.Constructions.TotalCategory
  open import Cubical.Categories.Displayed.BinProduct

  open CBPVModel M 
  open CBPVModelᴰ Mᴰ


  conv : Functor ((∫C Vᴰ ^op) ×C ∫C Cᴰ) (∫C ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ))
  conv .F-ob ((A , Aᴰ),(B , Bᴰ)) = (A , B) , Aᴰ , Bᴰ 
  conv .F-hom = λ z → (z .fst .fst , z .snd .fst) , z .fst .snd , z .snd .snd
  conv .F-id = refl
  conv .F-seq _ _ = refl

  ΣTSys : Functor (∫C TSysCatᴰ) (TSysCat)
  ΣTSys .F-ob (S , Sᴰ) = ∫TS S Sᴰ
  ΣTSys .F-hom {S , Sᴰ}{T , Tᴰ} (f , fᴰ) = ∫TSHom {S}{T}{Sᴰ}{Tᴰ} f  fᴰ 
  ΣTSys .F-id = refl
  ΣTSys .F-seq _ _ = refl

  TotalModel : CBPVModel 
  TotalModel .CBPVModel.V = ∫C Vᴰ
  TotalModel .CBPVModel.C = ∫C Cᴰ
  TotalModel .CBPVModel.O = ΣTSys ∘F ∫F (Oᴰ) ∘F conv

  module _   (S : CBPVGlobalSection M Mᴰ)  where 
    SO = S .snd .snd 
    module SV = Section (S .fst)
    module SC = Section (S .snd .fst)
    open CBPVSection {M}{M}{idCBPVMorphism} {Mᴰ}

    GSFun : CBPVMorphism M TotalModel 
    GSFun .CBPVMorphism.FV .F-ob A = A , (SV.F-obᴰ A)
    GSFun .CBPVMorphism.FV .F-hom f = f , (SV.F-homᴰ f)
    GSFun .CBPVMorphism.FV .F-id = ΣPathP (refl , SV.F-idᴰ)
    GSFun .CBPVMorphism.FV .F-seq f g = ΣPathP (refl , (SV.F-seqᴰ f g))
    GSFun .CBPVMorphism.FC .F-ob B = B , (SC.F-obᴰ B)
    GSFun .CBPVMorphism.FC .F-hom f = f , (SC.F-homᴰ f)
    GSFun .CBPVMorphism.FC .F-id = ΣPathP (refl , SC.F-idᴰ)
    GSFun .CBPVMorphism.FC .F-seq f g = ΣPathP (refl , (SC.F-seqᴰ f g))
    GSFun .CBPVMorphism.FO .N-ob (A , B) .fst M = M , SO .SectionNat.N-obᴰ M
    GSFun .CBPVMorphism.FO .N-ob (A , B) .snd {M}{M'} M↦M' = M↦M' , SO .SectionNat.N-obᴰRel {M↦M' = M↦M'}
    GSFun .CBPVMorphism.FO .N-hom {A , B}{A' , B'}(V , S) = ΣPathP ({!   !} , {!   !})
      --ΣPathP (funExt 
    --   (λ M → 
      --    ΣPathP ({!   !} , {!   !})) ,  
            -- this part is tricky.. if our transition system relations are prop valued relations.. things are easy
      --     {!  !})

module Elim (Synᴰ : CBPVModelᴰ Syn ) where 
  open CBPVModelᴰ Synᴰ
  open import Cubical.Categories.Displayed.Bifunctor
  open import Cubical.Categories.Bifunctor

  open Bifunctorᴰ OᴰBif

  mutual 
    vty : (A : VTy) → ob[ Vᴰ ] A
    vty 𝟙 = {!   !}
    vty Ans = {!   !}
    vty (U B) = {!   !}

    cty : (B : CTy) → ob[ Cᴰ ] B
    cty (F A) = {!   !}

    vtm : {A A' : VTy} → (f : Hom[ V , A ] A') → Hom[ Vᴰ ][ f  , vty A ] (vty A')
    vtm (subV f f₁) = (Vᴰ ⋆ᴰ vtm f) (vtm f₁)
    vtm var = idᴰ Vᴰ
    vtm (subVIdl f i) = Vᴰ .⋆IdLᴰ (vtm f) i
    vtm (subVIdr f i) = Vᴰ .⋆IdRᴰ (vtm f) i
    vtm (subVAssoc f f₁ f₂ i) = Vᴰ .⋆Assocᴰ (vtm f) (vtm f₁) (vtm f₂)  i
    vtm (isSet⊢v f f₁ x y i i₁) = Vᴰ .isSetHomᴰ {! vtm f  !} {!   !} {!   !} {!   !} i i₁
    vtm tt = {!   !}
    vtm yes = {!   !}
    vtm no = {!   !}
    vtm (thunk x) = {!   !}

    ctm-sub : {A A' : VTy}{B : CTy} → (V : A' ⊢v A)(M : A ⊢c B) → Oᴰ'[ subC V M  ][ vty A' , cty B ]
    ctm-sub {A}{A'}{B} V M = subst (λ h → F-obᴰ Oᴰ (vty A' , cty B) .fst h) (cong₂ subC refl plugId) (Bif-homLᴰ{f = V} (vtm V) (cty B) .fst M (ctm M))

    ctm-plug : {A : VTy}{B B' : CTy} → (S : B ⊢k B')(M : A ⊢c B) → Oᴰ'[ plug S M  ][ vty A , cty B' ]
    ctm-plug {A}{A'}{B} S M = subst (λ h → F-obᴰ Oᴰ (vty A , cty B) .fst h) subCId (Bif-homRᴰ  (vty A) (ktm S) .fst M (ctm M))
    
    ctm : {A : VTy}{B : CTy} → (M : A ⊢c B) → Oᴰ'[ M ][ vty A , cty B ]
    ctm {A}{B} (subC V M) = ctm-sub V M 
    ctm {A}{B} (plug S M) = ctm-plug S M 
    ctm (plugId i) = {!   !}
    ctm (subCId i) = {!   !}
    ctm (plugDist i) = {!   !}
    ctm (subDist i) = {!   !}
    ctm (plugSub i) = {!   !}
    ctm (isSet⊢c f f₁ x y i i₁) = {!   !}
    ctm (ret x) = {!   !}
    ctm (force x) = {!   !}
    ctm (force-sub i) = {!   !}

    -- this is just some opaque type.. 
    -- impossible!, unless you give me the answer for all parameters! 
    
    ctmRel : {A : VTy}{B : CTy}{M M' : A ⊢c B}(M↦M' : M M.↦O M') → OᴰRel[ M↦M' ][ ctm M , ctm M' ]
    -- F-obᴰ Oᴰ (vty A , cty B) .snd M↦M' (ctm M) (ctm M')
    ctmRel (Fβ{A}{A'}{B}{V}{M}) = {!   !} -- OᴰRel[ Fβ ][ ctm-plug (bind M) (ret V) , ctm-sub V M ]  Exactly!. but this is forward reduction.. not anti reduction.., anti is used above
    ctmRel {A} {B} {M} {M'} Uβ = {!   !} -- ctmRel M↦M'
    ctmRel (subC-cong {A}{A'}{B}{V}{M}{M'} M↦M') = subst {!   !} {!   !} have where 
      have : Bif-obᴰ (vty A') (cty B) .snd
        (Bifunctor.Bif-homL (ParFunctorToBifunctor M.O) V B .snd M↦M')
        (Bif-homLᴰ (vtm V) (cty B) .fst M (ctm M))
        (Bif-homLᴰ (vtm V) (cty B) .fst M' (ctm M')) 
      have = Bif-homLᴰ{f = V} (vtm V) (cty B) .snd {M}{M'}{M↦M'} (ctm M) (ctm M') (ctmRel M↦M')
    -- {! Bif-homLᴰ{f = V} (vtm V) (cty B) .snd {M}{M'}{M↦M'} ? ? ? !} -- OᴰRel[ subC-cong M↦M' ][ ctm-sub V₁ M₁ , ctm-sub V₁ M'' ] given OᴰRel[ M↦M' ][ ctm M₁ , ctm M'' ]
    ctmRel {A} {B} {M} {M'} (plug-cong M↦M') = {!  Oᴰ .F-homᴰ ? .snd  ? ?  ? !}
    ctmRel {A} {B} {M} {M'} (isProp↦ M↦M' M↦M'' i) = {!   !}
    -- essentially 
    module _ (no : VTy → Type) where 
      hopeless : no 𝟙 
      hopeless = {!  !}
      -- unless you give me the answer for all VTy! 


    ktm : {B B' : CTy} → (f : Hom[ C , B ] B') → Hom[ Cᴰ ][ f  , cty B ] (cty B')
    ktm (kcomp g g₁) = (Cᴰ ⋆ᴰ ktm g) (ktm g₁)
    ktm hole = idᴰ Cᴰ
    ktm (kcompIdl g i) = Cᴰ .⋆IdLᴰ (ktm g) i
    ktm (kcompIdr g i) = Cᴰ .⋆IdRᴰ (ktm g) i
    ktm (kcompAssoc g g₁ g₂ i) = Cᴰ .⋆Assocᴰ (ktm g) (ktm g₁) (ktm g₂)  i
    ktm (isSet⊢k g g₁ x y i i₁) = {!   !}
    ktm (bind x) = {!   !}

  SV : Section Id Vᴰ 
  SV .Section.F-obᴰ = vty
  SV .Section.F-homᴰ = vtm
  SV .Section.F-idᴰ = {!   !}
  SV .Section.F-seqᴰ = {!   !}

  SC : Section Id Cᴰ 
  SC .Section.F-obᴰ = cty
  SC .Section.F-homᴰ = ktm
  SC .Section.F-idᴰ = {!   !}
  SC .Section.F-seqᴰ = {!   !}

  open CBPVSection {Syn}{Syn}{idCBPVMorphism}{Synᴰ}
  SO : SectionNat SV SC
  SO .CBPVSection.SectionNat.N-obᴰ = ctm
  SO .CBPVSection.SectionNat.N-obᴰRel {A}{B}{M}{M'}{M↦M'} = ctmRel M↦M'
  SO .CBPVSection.SectionNat.N-homᴰ = {!   !}
  SO .CBPVSection.SectionNat.N-homᴰRel = {!   !}



{-
module ModelSection 
  {M N : CBPVModel }
  (F : CBPVMorphism M N)
  (L : Logic N) where 

  open CBPVMorphism F
  private 
    module M = CBPVModel M 
    module N = CBPVModel N
    module L = Logic L
    module VH' = HDSyntax (L.VH ∘F (FV ^opF))
    module CH' = HDSyntax (L.CH ∘F (FC ^opF))

  open ConvertLogic N L
  module _ 
    (SV : Section FV Vᴰ) 
    (SC : Section FC Cᴰ) where 

    private 
      module SV = Section SV 
      module SC = Section SC
    
    SectionO : Type 
    SectionO = 
      ∀ 
        {A : ob M.V}
        {B : ob M.C}
        (M : M.O[ A , B ] .fst) → 
        Oᴰ .F-obᴰ {FV .F-ob A , FC .F-ob B} (SV.F-obᴰ A , SC.F-obᴰ B)  .fst (FO .N-ob (A , B) .fst M)
      
  CBPVSection : Type 
  CBPVSection = Σ[ SV ∈ Section FV Vᴰ ] Σ[ SC ∈ Section FC Cᴰ ] SectionO SV SC

CBPVGlobalSection : {M : CBPVModel } → Logic M → Type 
CBPVGlobalSection L = ModelSection.CBPVSection idCBPVMorphism L
open import Cubical.Categories.Instances.Preorders.Monotone
open NatTrans 
open MonFun
module hrm (L : Logic Syn) where 
  open Logic L
  module LV = HDSyntax VH
  module LC = HDSyntax CH

  open Push L

  module _ (hasPush : HasPush) where 
    open PushSyntax hasPush

    mutual 
      vty : (A : VTy) → LV.F∣ A ∣ 
      vty 𝟙 = {!   !}
      vty Ans = {!   !}
      vty (U B) = pull (force var) $ cty B

      cty : (B : CTy) → LC.F∣ B ∣
      cty (F A) = hasPush (ret var) .fst $  vty A 

  {-
        vtm-thunk : ∀ {A  B} → (M : A ⊢c B) →  A LV.◂ vty A ≤ LV.f* (thunk M) (pull force $ cty B) 
          vtm-thunk {A}{B} M = 
            LV.seq (ctm M) (
            LV.eqTo≤ (cong (λ h → MonFun.f (pull h) (cty B)) (sym Uβ ∙ sym plugId)
              ∙ cong (λ h → h .MonFun.f (cty B)) (pullLComp (thunk M) force))) 

  data _↦_ : {A : VTy}{B : CTy} → A ⊢c B → A ⊢c B → Type where 
    Fβ : ∀{A A' B}{V : A ⊢v A'}{M : A' ⊢c B} → 
      ------------------------------------
      plug (bind M) (ret V) ↦ (subC V M)

    Uβ : ∀ {A B} {M : A ⊢c B} → 
      ---------------------
      force (thunk M) ↦ M
    
    subC-cong : ∀ {A A' B}{V : A' ⊢v A}{M M' : A ⊢c B}  →  
      M ↦ M' → 
      --------- 
      subC V M  ↦ subC V M'

    plug-cong : ∀ {A B B'}{S : B ⊢k B'}{M M' : A ⊢c B}  →  
      M ↦ M' → 
      --------- 
      plug S M ↦ plug S M'

    isProp↦ : ∀ {A B} {M M' : A ⊢c B} → isProp (M ↦ M')


    -}
      vtm : {A A' : VTy} → (V : A ⊢v A') → A LV.◂ vty A ≤ LV.f* V (vty A')
      vtm (subV V₁ V₂) = {!   !}
      vtm var = {!   !}
      vtm (subVIdl V₁ i) = {!   !}
      vtm (subVIdr V₁ i) = {!   !}
      vtm (subVAssoc V₁ V₂ V₃ i) = {!   !}
      vtm (isSet⊢v V₁ V₂ x y i i₁) = {!   !}
      vtm tt = {!   !}
      vtm yes = {!   !}
      vtm no = {!   !}
      vtm (thunk {A}{B} M) = goal where 

        have : A LV.◂ vty A ≤ (pull (force (thunk M)) $ cty B) 
        have = LV.seq (ctm M) (antiRed Uβ)

        wat : force (thunk M) ≡ subC (thunk M) (plug hole (force var)) 
        wat = (cong force (sym (subVIdr _)) ∙ sym force-sub) ∙ cong₂ subC refl (sym plugId)
        
        goal : A LV.◂ vty A ≤ LV.f* (thunk M) (pull (force var) $ cty B) 
        goal = LV.seq (LV.seq have (LV.eqTo≤ (cong (λ h → f (pull h) (cty B)) wat))) VM*→V*M*

      ktm : {B B' : CTy} → (S : B ⊢k B') → B LC.◂ cty B ≤ LC.f* S (cty B')
      ktm (kcomp S S₁) = {!   !}
      ktm hole = {!   !}
      ktm (kcompIdl S i) = {!   !}
      ktm (kcompIdr S i) = {!   !}
      ktm (kcompAssoc S S₁ S₂ i) = {!   !}
      ktm (isSet⊢k S S₁ x y i i₁) = {!   !}
      ktm (bind {A}{B} M) = {!   !} where 

        have : A LV.◂ vty A ≤ ((pull (plug (bind M) (ret var)) $ cty B)) 
        have = LV.seq (LV.seq (ctm M) (LV.eqTo≤ (cong (λ h → f (pull h) (cty B)) (sym  subCId)))) (antiRed Fβ)

        sub : A LV.◂ vty A ≤ pull (ret var) .f (LC.f* (bind M) (cty B))
        sub = LV.seq have (LV.eqTo≤ {!  !})
        
        goal : F A LC.◂ hasPush (ret var) .fst $ vty A ≤ LC.f* (bind M) (cty B) 
        goal = pullToPush (ret var) sub

      ctm : ∀{A B} → (M : A ⊢c B) → A LV.◂ vty A ≤ (pull M $ cty B)
      ctm (subC x M) = {!   !}
      ctm (plug x M) = {!   !}
      ctm (plugId i) = {!   !}
      ctm (subCId i) = {!   !}
      ctm (plugDist i) = {!   !}
      ctm (subDist i) = {!   !}
      ctm (plugSub i) = {!   !}
      ctm (isSet⊢c M M₁ x y i i₁) = {!   !}
      ctm (ret {A} {A'} V) = {! pushToPull  !} where 
        have : A LV.◂ vty A ≤ LV.f* V (vty A') 
        have = vtm V

        goal : A LV.◂ vty A ≤ (pull (ret V) $ (hasPush (ret var) .fst $ vty A')) 
        goal = {!   !}
      --ctm (bind M M₁) = {!   !}
      ctm (force {A}{B} V) = goal where 
        have : A LV.◂ vty A ≤ LV.f* V (pull (force var) $ cty B) 
        have = vtm V
        
        goal : A LV.◂ vty A ≤ (pull (force V) $ cty B) 
        goal = LV.seq have (LV.seq V*M*→VM* (LV.eqTo≤ (cong (λ h → f (pull h) (cty B)) (cong₂ subC refl plugId ∙ force-sub ∙ cong force (subVIdr _)))))

    GS : CBPVGlobalSection L 
    GS .fst .Section.F-obᴰ = vty
    GS .fst .Section.F-homᴰ = vtm
    GS .fst .Section.F-idᴰ = LV.isProp≤ _ _
    GS .fst .Section.F-seqᴰ _ _ = LV.isProp≤ _ _
    GS .snd .fst .Section.F-obᴰ = cty
    GS .snd .fst .Section.F-homᴰ = ktm
    GS .snd .fst .Section.F-idᴰ = LC.isProp≤ _ _
    GS .snd .fst .Section.F-seqᴰ _ _ = LC.isProp≤ _ _
    GS .snd .snd = ctm
-}