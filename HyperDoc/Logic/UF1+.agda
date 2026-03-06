{-# OPTIONS --type-in-type #-}
-- fix level issues
-- reorder imports, etc

module HyperDoc.Logic.UF1+ where 

open import Cubical.Data.Sigma using (ΣPathP)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism  hiding (isIso)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Constructions.Reindex.Base renaming (reindex to reindexᴰ)

open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Functor 
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint 
open import Cubical.Categories.Instances.Posets.Base

open import HyperDoc.Algebra.Algebra
open import HyperDoc.CBPV.Syntax.UF1+
open import HyperDoc.CBPV.Model.Base
open import HyperDoc.Syntax
open import HyperDoc.Lib
open import HyperDoc.Logic.Base
open import HyperDoc.Logic.Structure
open import HyperDoc.Connectives.Connectives
open import HyperDoc.CBPV.TypeStructure

open AlgHom
open AlgHomᴰ
open Bifunctorᴰ
open Categoryᴰ
open Category
open Functor
open NatTrans
open MonFun
open _⊣_ 

module _ {Σ : Signature} where
  open SyntacticModel Σ  

module Eliminator (Σ : Signature) where 
  open Syntax Σ
  open SyntacticModel Σ
  open Section
  
  module _ (L : Logic SynModel) where

    open ConvertLogic SynModel L
    module Vᴰ = Categoryᴰ Vᴰ
    open Logic L
    module LV = HDSyntax VH
    module LC = HDSyntax CH
    open TypeStructure SynModel
    open Push L
      
    module _ 
      (⊤ : L⊤.Has⊤ VH)
      (V∨ : L∨.Has∨ VH)
      (V⊤ : HasV𝟙 )
      (hasPush : HasPush)
      (hasO+ : HasO+)
        where

      open L⊤.HA 
      open L∨.HA renaming (_∨_ to _⋁_)
      open PushSyntax hasPush
      
      -- requesting pushforwards along just σ avoids need for existentials in general
      module _ 
        (opLiftσ₁ : ((A A' : VTy) → HasLeftAdj (VH .F-hom (σ₁ {A}{A'}))))
        (opLiftσ₂ : ((A A' : VTy) → HasLeftAdj (VH .F-hom (σ₂ {A}{A'})))) where 

        _⋁ⱽ_ : {A : VTy} → Vᴰ.ob[ A ] → Vᴰ.ob[ A ] → Vᴰ.ob[ A ] 
        _⋁ⱽ_ {A} = _⋁_  (V∨ .fst  A)

        ⋁ⱽ-intro₁ : {A  : VTy}{P Q : Vᴰ.ob[ A ]} → 
          A LV.◂ P ≤ (P ⋁ⱽ Q)
        ⋁ⱽ-intro₁ {A}{P}{Q} = (or-intro1 (V∨ .fst A) {P = P}{P}{Q}LV.id⊢)

        ⋁ⱽ-intro₂ : {A  : VTy}{P Q : Vᴰ.ob[ A ]} → 
          A LV.◂ Q ≤ (P ⋁ⱽ Q)
        ⋁ⱽ-intro₂ {A}{P}{Q} = (or-intro2 (V∨ .fst A) {P = Q}{P}{Q}LV.id⊢)


        ⋁ⱽ-elim : {A  : VTy}{P R Q : Vᴰ.ob[ A ]} → 
          A LV.◂ P ≤ R  → 
          A LV.◂ Q ≤ R  →
          A LV.◂ (P ⋁ⱽ Q) ≤ R 
        ⋁ⱽ-elim {A} = or-elim (V∨ .fst A)

        _⋁ᴰ_ : {A A' : VTy} → Vᴰ.ob[ A ] → Vᴰ.ob[ A' ] → Vᴰ.ob[ A + A' ] 
        _⋁ᴰ_ {A}{A'} P Q = 
            _⋁_ 
              (V∨ .fst (A + A')) 
              (opLiftσ₁ A A' .fst $ P) 
              (opLiftσ₂ A A' .fst $ Q)
        
        ⋁ᴰ-intro₁ : {A A' : VTy}{P : Vᴰ.ob[ A ]}{Q : Vᴰ.ob[ A' ]} → 
          Vᴰ.Hom[ σ₁ ][ P , P ⋁ᴰ Q ]
        ⋁ᴰ-intro₁ {A}{A'}{P}{Q}= goal where 

          open AdjSyntax (opLiftσ₁ A A') renaming (L to push)

          -- recall  P ⋁ᴰ Q := (push $ P) ⋁ⱽ (push $ Q)
          have : (A + A') LV.◂ push $ P ≤ (P ⋁ᴰ Q)
          have = ⋁ⱽ-intro₁

          goal : A LV.◂ P ≤ (VL.f* σ₁ (P  ⋁ᴰ Q))
          goal = LV.seq unit (isMon (VH .F-hom σ₁) have)

        ⋁ᴰ-intro₂ : {A A' : VTy}{P : Vᴰ.ob[ A ]}{Q : Vᴰ.ob[ A' ]} → 
          Vᴰ.Hom[ σ₂ ][ Q , P ⋁ᴰ Q ]
        ⋁ᴰ-intro₂ {A}{A'}{P}{Q} = goal where 
          open AdjSyntax (opLiftσ₂ A A') renaming (L to push)


          have : (A + A') LV.◂ push $ Q ≤ (P ⋁ᴰ Q)
          have = ⋁ⱽ-intro₂

          goal : A' LV.◂ Q ≤ (VL.f* σ₂ (P  ⋁ᴰ Q))
          goal = LV.seq unit (isMon (VH .F-hom σ₂) have)

        ⋁ᴰ-elim : {A A' A'' : VTy}{P : Vᴰ.ob[ A ]}{Q : Vᴰ.ob[ A' ]}{R : Vᴰ.ob[ A'' ]}
          {f : V [ A , A'' ]}{g : V [ A' , A'' ]} → 
          Vᴰ.Hom[ f ][ P , R ] → 
          Vᴰ.Hom[ g ][ Q , R ] → 
          Vᴰ.Hom[ caseV f g ][ P ⋁ᴰ Q ,  R ]
        ⋁ᴰ-elim {A}{A'}{A''}{P}{Q}{R}{f}{g} prf₁ prf₂ = goal where 
          module adj₁ = AdjSyntax (opLiftσ₁ A A')
          module adj₂ = AdjSyntax (opLiftσ₂ A A')

          have : A LV.◂ P  ≤ LV.f* σ₁ (LV.f* (caseV f g) R)
          have = LV.seq prf₁ (LV.eqTo≤ (cong (λ h → LV.f* h R) (sym +β₁) ∙ LV.f*seq))

          have' : A' LV.◂ Q  ≤ LV.f* σ₂ (LV.f* (caseV f g) R)
          have' = LV.seq prf₂ ((LV.eqTo≤ (cong (λ h → LV.f* h R) (sym +β₂) ∙ LV.f*seq)))

          goal : (A + A') LV.◂ P ⋁ᴰ Q ≤ LV.f* (caseV f g) R
          goal = 
            ⋁ⱽ-elim {A + A'}{adj₁.L $ P}{LV.f* (caseV f g) R}{adj₂.L $ Q} 
              (adj₁.RtoL have) 
              (adj₂.RtoL have')


        mutual
          vty : (A : VTy) → LV.F∣ A ∣
          vty 𝟙 = top (⊤ .fst 𝟙)
          vty (A + A') =  vty A ⋁ᴰ vty A'
          vty (U B) = pull force $ cty B

          cty : (B : CTy) → LC.F∣ B ∣
          cty (F A) = hasPush ret .fst $  vty A


        mutual
          vtm-thunk : ∀ {A  B} → (M : A ⊢c B) →  A LV.◂ vty A ≤ LV.f* (thunk M) (pull force $ cty B) 
          vtm-thunk {A}{B} M = 
            LV.seq (ctm M) (
            LV.eqTo≤ (cong (λ h → MonFun.f (pull h) (cty B)) (sym Uβ ∙ sym plugId)
              ∙ cong (λ h → h .MonFun.f (cty B)) (pullLComp (thunk M) force))) 

          ctm-subC : ∀{A A' B}(V : A ⊢v A')(M : A' ⊢c B) →  A LV.◂ vty A ≤ (pull (subC V M) $ cty B)
          ctm-subC {A}{A'}{B} V M = subst (λ h → A LV.◂ vty A ≤ (pull h $ cty B)) plugId have where 
            have : A LV.◂ vty A ≤ (pull (plug hole (subC V M)) $ cty B)
            have = OᴰBif .Bif-homLᴰ  (vtm V) (cty B) .carmapᴰ M (ctm M)

          ctm-plug : ∀{A B B'}(S : B ⊢k B')(M : A ⊢c B) → A LV.◂ vty A ≤ (pull (plug S M) $ cty B')
          ctm-plug {A}{B}{B'} S M = subst (λ h → A LV.◂ vty A ≤ (pull h $ cty B')) (cong₂ plug refl subCId) have where 
            have : A LV.◂ vty A ≤ (pull (plug S (subC var M)) $ cty B') 
            have = OᴰBif .Bif-homRᴰ (vty A) (ktm S) .carmapᴰ M (ctm M)

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
  
          vtm (thunk M) = vtm-thunk M
          vtm (Uη {A}{B}{V} i) = 
            isProp→PathP 
              ((λ i → LV.isProp≤{q = LV.f* (Uη i) (pull force $ cty B)})) 
              (vtm-thunk (subC' V force')) 
              (vtm V) 
              i
          vtm tt = LV.seq (top-top (⊤ .fst _)) (LV.eqTo≤ (sym (L⊤.HAHom.f-top (⊤ .snd tt))))
          vtm (η𝟙 {A} V i) = 
            VL.eq*PathP (η𝟙 {A} V) 
              (LV.seq (top-top (⊤ .fst _)) (LV.eqTo≤ (sym (L⊤.HAHom.f-top (⊤ .snd tt))))) 
              (vtm V) 
              i

          vtm (σ₁ {A}{A'}) = ⋁ᴰ-intro₁
          vtm (σ₂ {A}{A'}) = ⋁ᴰ-intro₂
          vtm (caseV V₁ V₂) = ⋁ᴰ-elim (vtm V₁) (vtm V₂)
          vtm (+β₁ {A}{A'}{A''}{W}{V} i) =
            isProp→PathP 
              ((λ i → LV.isProp≤{q = LV.f* (+β₁ i) (vty A'')}))
              (⋁ᴰ-intro₁ Vᴰ.⋆ᴰ ⋁ᴰ-elim (vtm W) (vtm V))
              (vtm W)
              i

          vtm (+β₂ {A}{A'}{A''}{W}{V} i) = 
            isProp→PathP 
              ((λ i → LV.isProp≤{q = LV.f* (+β₂ i) (vty A'')}))
              (⋁ᴰ-intro₂ Vᴰ.⋆ᴰ ⋁ᴰ-elim (vtm W) (vtm V))
              (vtm V)
              i
          vtm (+ηV {A}{A'}{A''}{V} i) = 
            isProp→PathP 
              (λ i → LV.isProp≤{p = vty A ⋁ᴰ vty A' }{q = LV.f* (+ηV i) (vty A'')})
              (⋁ᴰ-elim (⋁ᴰ-intro₁ Vᴰ.⋆ᴰ vtm V) (⋁ᴰ-intro₂ Vᴰ.⋆ᴰ vtm V))
              (vtm V)
              i
          vtm (+ηC {A}{A'}{B}{M} i) = 
            isProp→PathP 
              (λ i → LV.isProp≤{p = vty A ⋁ᴰ vty A' }{q =  LV.f* (+ηC i) (pull force $ cty B)})
              (⋁ᴰ-elim (vtm-thunk (subC' σ₁ M)) (vtm-thunk (subC' σ₂ M)))
              (vtm-thunk M)
              i

          ktm-bind : ∀ {A  B} → (M : A ⊢c B) → F A LC.◂ hasPush ret .fst $ vty A ≤ LC.f* (bind M) (cty B)
          ktm-bind {A}{B} M = 
            pullToPush ret (
              LV.seq (ctm M) (
              LV.eqTo≤ goal)) where 

              goal  : MonFun.f (pull M) (cty B) ≡ pull ret .MonFun.f (LC.f* (bind M) (cty B))
              goal = cong (λ h → N-ob Sq (A , B) h .MonFun.f (cty B)) (sym Fβ ∙ cong₂ plug refl (sym subCId)) 
                ∙  (cong (λ h → h .MonFun.f (cty B))) (pullRComp (bind M) ret)
          

          ktm : {B B' : CTy} → (S : B ⊢k B') → B LC.◂ cty B ≤ LC.f* S (cty B')
          ktm (kcomp S S') = Cᴰ ._⋆ᴰ_  (ktm S) (ktm S')
          ktm hole = Cᴰ .idᴰ
          ktm (kcompIdl S i) = Cᴰ .⋆IdLᴰ (ktm S) i
          ktm (kcompIdr S i) = Cᴰ .⋆IdRᴰ (ktm S) i
          ktm (kcompAssoc S₁ S₂ S₃ i) = Cᴰ .⋆Assocᴰ (ktm S₁) (ktm S₂) (ktm S₃) i
          ktm (isSet⊢k S S' x y i j) = 
            isOfHLevel→isOfHLevelDep 2 
              (λ x → Cᴰ .isSetHomᴰ) 
              (ktm S) (ktm S') 
              (cong ktm x) (cong ktm y) 
              (isSet⊢k S S' x y) i j

          ktm (bind M) = ktm-bind M
          ktm (Fη {A}{B}{S} i) = 
            isProp→PathP 
              (λ i → LC.isProp≤{p = hasPush ret .fst $ vty A} {q = LC.f* (Fη i) (cty B)})
              (ktm-bind (plug S ret'))
              (ktm S)
              i
          
          {-# TERMINATING #-}
          -- Idk why.. but this termination pragma is needed for plugDist
          -- which is just showing that the PathP is a prop.. 
          -- there should be NO interesting recursion in the proof of equality
          -- need to fix
          ctm : ∀{A B} → (M : A ⊢c B) → A LV.◂ vty A ≤ (pull M $ cty B)
          ctm (subC V M) = ctm-subC V M 
          ctm (plug S M) = ctm-plug S M
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
              (ctm-plug (kcomp S S') M)
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
          ctm (isSet⊢c M M' x y i j) = 
              isOfHLevel→isOfHLevelDep 2 
                (λ x → isProp→isSet VL.isProp≤) 
                (ctm M) (ctm M') 
                (cong ctm x) (cong ctm y) 
                (isSet⊢c M M' x y) i j 

          ctm (ops A B op args) = pullOp op args (vty A) (cty B) (λ x → ctm (args x))
          ctm (opsSub {A}{A'}{B} V op args i) = 
            isProp→PathP 
              (λ i → LV.isProp≤{q = (pull (opsSub V op args i) $ cty B)}) 
              (ctm-subC V (ops A' B op args))
              (pullOp op (λ x → subC V (args x)) (vty A) (cty B) (λ x → ctm-subC V (args x)))
              i
          ctm (opsPlug {A}{B}{B'} S op args i) = 
            isProp→PathP 
              ((λ i → LV.isProp≤{q = (pull (opsPlug S op args i) $ cty B')}))
              (ctm-plug S (ops A B op args))
              (pullOp op (λ x → plug S (args x)) (vty A) (cty B')(λ x → ctm-plug S (args x)))
              i
          ctm force = LV.id⊢
          ctm (Uβ {A}{B}{M} i) = 
            isProp→PathP 
              ((λ i → LV.isProp≤{q = (pull (Uβ i) $ cty B)})) 
              (ctm-subC (thunk M) force) 
              (ctm M) 
              i
          ctm ret = pushToPull ret LC.id⊢
          ctm (Fβ {A}{B}{M} i) = 
            isProp→PathP 
              (λ i → LV.isProp≤{q = (pull (Fβ i) $ cty B)}) 
              (ctm-plug (bind M) ret) 
              (ctm M)
              i

        SV : Section Id Vᴰ 
        SV .F-obᴰ = vty
        SV .F-homᴰ = vtm
        SV .F-idᴰ = VL.isProp≤  _ _
        SV .F-seqᴰ _ _ = VL.isProp≤  _ _

        SC : Section Id Cᴰ 
        SC .F-obᴰ = cty
        SC .F-homᴰ = ktm
        SC .F-idᴰ = CL.isProp≤  _ _
        SC .F-seqᴰ _ _ = CL.isProp≤  _ _

        M-elim : CBPVGlobalSection L
        M-elim .fst = SV
        M-elim .snd .fst = SC
        M-elim .snd .snd = ctm


module Preserve∨   
  (Σ : Signature) 
  (N : CBPVModel Σ)
  (hasO+ : TypeStructure.HasO+ N)
  (L : Logic N) where 

  open L∨

  module S = SyntacticModel Σ
  module N = CBPVModel N 
  module L = Logic L
  module SynN = TypeStructure.+Syntax N hasO+
  open import Cubical.Relation.Binary.Preorder

  module _ 
    (F : CBPVMorphism S.SynModel N )
    (L∨ : Has∨ L.VH)
    (opLiftσ₁ : (A A' : N.V .ob) → HasLeftAdj (L.VH .F-hom (SynN.σ₁ {A}{A'})))
    (opLiftσ₂ : (A A' : N.V .ob) → HasLeftAdj (L.VH .F-hom (SynN.σ₂ {A}{A'}))) where 

    open CBPVMorphism F
    open Reindex F L using (reindex)
    module L' = Logic reindex
    open Syntax Σ
    open import Cubical.Categories.Presheaf.Morphism.Alt
    open import Cubical.Data.Sum
    open PshHom
    open PshIso
    module LV = HDSyntax L.VH
    module LV' = HDSyntax L'.VH
    -- mapping out of the initial model.. this is definitional.. 
    -- but i dont have a way to access that atm

    module _ 
      (A A' : VTy)
      (asm : FV .F-ob (A + A') ≡ (FV .F-ob A SynN.+ FV .F-ob A'))
      (asm2 : 
        PathP 
          (λ i → N.V [ FV .F-ob A , asm  i ]) 
          (FV .F-hom (σ₁{A}{A'})) 
          (SynN.σ₁ {FV .F-ob A}{FV .F-ob A'})) where 
       {- PathP 
          (λ i → MonFun {! L'.VH .F-hom (σ₁{A}{A'})  !} (L.VH .F-ob (FV .F-ob A) .fst)) 
          (F-hom L.VH (F-hom FV (σ₁{A}{A'}))) 
          {!  L'.VH .F-hom (σ₁{A}{A'}) !} ) where -}

      _ = subst
      _ = {! fromPathP asm  !}

      presOpLiftσ₁ : (A A' : VTy) → HasLeftAdj (L.VH .F-hom (FV .F-hom (σ₁{A}{A'})))
      presOpLiftσ₁ A A' = {! subst  !}
  
  {-}  module _ 
      (asm : ∀ (A A' : VTy) → FV .F-ob (A + A') ≡ (FV .F-ob A SynN.+ FV .F-ob A')) where
      -- (asm1 : ∀ {A A'} → FV .F-hom σ₁ ≡ {! SynN.σ₁ !}) where
      module LV = HDSyntax L.VH
      module LV' = HDSyntax L'.VH



      LP : (A : N.V .ob) → Preorder _ _ 
      LP A = L.VH .F-ob  A .fst

      L'P : (A : VTy) → Preorder _ _ 
      L'P A = L'.VH .F-ob A .fst

      opLiftNσ₁ : {A A' : N.V .ob} → MonFun (LP A) (LP (A SynN.+ A'))
      opLiftNσ₁ {A} {A'} = opLiftσ₁ A A' .fst


      eqTyp :  {A A' : VTy} → MonFun (L'P A) (L'P (A + A')) ≡ MonFun (L'P A) (LP (FV .F-ob A SynN.+ FV .F-ob A'))
      eqTyp {A}{A'} = cong₂ MonFun refl (cong (λ h → F-ob L.VH (h) .fst) (asm _ _))
{-}
      opLiftSσ₁ : {A A' : VTy} → MonFun (L'P A) (L'P (A + A'))
      opLiftSσ₁ {A} {A'} = 
        subst 
          (λ h → MonFun (L'P A) h) 
          (cong (λ h → L.VH .F-ob (h) .fst) (sym (asm _ _)))  
          have      
       where 
        have : MonFun (LP (FV .F-ob A)) (LP (FV .F-ob A SynN.+ FV .F-ob A'))
        have = opLiftNσ₁ {(FV. F-ob A)} {(FV .F-ob A')}

      liftNσ₁ : {A A' : N.V .ob} → MonFun (LP (A SynN.+ A')) (LP A)
      liftNσ₁ {A}{A'} = (L.VH .F-hom (SynN.σ₁ {A}{A'}))

      liftNσ₂ : {A A' : VTy} → MonFun (L'P (A + A')) (L'P A)
      liftNσ₂ {A}{A'} = L'.VH .F-hom σ₁

      module _ (asm1 :  {A A' : VTy} → F-hom FV (σ₁{A}{A'}) ≡ transport {!   !} {! fromPathP  !} ) where 
        presOpLiftσ₁ : (A A' : VTy) → HasLeftAdj (L'.VH .F-hom (σ₁{A}{A'}))
        presOpLiftσ₁ A A' .fst = opLiftSσ₁
        presOpLiftσ₁ A A' .snd .adjIff {P}{Q} .Iso.fun x = goal where 
          _ : (A + A') LV'.◂ opLiftSσ₁ $ P ≤ Q
            -- (L'.VH .F-ob (A + A') .fst .snd PreorderStr.≤ (opLiftSσ₁ $ P)) Q
          _ = x
          x' : {! (FV .F-ob A SynN.+ FV .F-ob A') !} LV.◂ opLiftSσ₁ $ P ≤ Q
          x' = {!  x !}
          have : A LV'.◂ P ≤ ({!   !} $ Q)
          have = opLiftσ₁ (FV .F-ob A)(FV .F-ob A') .snd .adjIff .Iso.fun {!  F-hom FV σ₁!}
          goal : A LV'.◂  P  ≤ ((L'.VH .F-hom σ₁) $ Q)
          goal = LV'.seq have {! (L'.VH .F-hom σ₁)  !}
        presOpLiftσ₁ A A' .snd .adjIff .Iso.inv = {!   !}
        presOpLiftσ₁ A A' .snd .adjIff .Iso.sec _ = LV'.isProp≤ _ _
        presOpLiftσ₁ A A' .snd .adjIff .Iso.ret _ = LV'.isProp≤ _ _

-}
-}

{-}
      _ = isContr
      _ = {! isPropHasLeftAdj _ _  ?  !}
      presOpLiftσ₁ : (A A' : VTy) → HasLeftAdj (L'.VH .F-hom (σ₁{A}{A'}))
      presOpLiftσ₁ A A' .fst = goal where 
        goal : MonFun (L'P A) (L'P (A + A'))
        goal = 
          subst 
            (λ h → MonFun (L'P A) h) (cong (λ h → L.VH .F-ob (h) .fst) (sym (asm _ _))) 
            ((opLiftσ₁' (FV. F-ob A) (FV .F-ob A'))) 
          
      presOpLiftσ₁ A A' .snd .adjIff {P}{Q} .Iso.fun  prf = goal where 

        open AdjSyntax (opLiftσ₁ (FV .F-ob A)(FV .F-ob A')) renaming (L to foo)
        have : {!   !}
        have = {! LtoR  !}
        goal : (FV .F-ob A) LV.◂ P ≤  LV'.f* σ₁  Q
        goal = LV.seq (LtoR (IsPreorder.is-refl
           (PreorderStr.isPreorder
            (L.VH .F-ob (hasO+ (FV .F-ob A) (FV .F-ob A') .fst) .fst .snd))
           (f foo P))) (LV.eqTo≤ {!   !})
      presOpLiftσ₁ A A' .snd .adjIff .Iso.inv = {!   !}
      presOpLiftσ₁ A A' .snd .adjIff .Iso.sec _  = LV'.isProp≤ _ _
      presOpLiftσ₁ A A' .snd .adjIff .Iso.ret _ = LV'.isProp≤ _ _
-}


module LocalElim 
  (Σ : Signature) 
  (N : CBPVModel Σ)
  (L : Logic N)
  (⊤ : L⊤.Has⊤ (Logic.VH L))
  (∨ : L∨.Has∨ (Logic.VH L))
  (V⊤ : TypeStructure.HasV𝟙 N)
  (push : Push.HasPush L) where

  open Syntax Σ
  open SyntacticModel Σ

  module _ (F : CBPVMorphism SynModel N) where
    
    open Reindex F L 
    open ModelSection
    open CBPVMorphism F
    open TypeStructure
    open ConvertLogic N L

    LM : Logic SynModel
    LM = reindex

    open Eliminator Σ 
    open Push
          
    module LMHV = HDSyntax (Logic.VH LM)
    module LMHC = HDSyntax (Logic.CH LM)

    pres⊤ : L⊤.Has⊤ (Logic.VH LM) 
    pres⊤ .fst = λ c → ⊤ .fst (F-ob (FV ^opF) c)
    pres⊤ .snd = λ f → ⊤ .snd (F-hom (FV ^opF) f)

    presPush : HasPush LM
    presPush M = 
      (push (N-ob FO (_ , _) .carmap M) .fst) ,
        push (N-ob FO (_ , _) .carmap M) .snd



    M-elim' : CBPVGlobalSection LM
    M-elim' = 
      M-elim 
        LM 
        pres⊤ 
        (L∨.Preserve∨ {L = Logic.VH L} FV ∨) 
        (SyntacticModel.has𝟙 Σ) 
        presPush 
        (SyntacticModel.hasO+ Σ) 
        {!   !} 
        {!   !} 
    
    FSV : Section FV Vᴰ
    FSV = GlobalSectionReindex→Section Vᴰ FV convert where 
      convert : GlobalSection (reindexᴰ Vᴰ FV)
      convert .Section.F-obᴰ = M-elim' .fst .Section.F-obᴰ
      convert .Section.F-homᴰ = M-elim' .fst .Section.F-homᴰ
      convert .Section.F-idᴰ = LMHV.isProp≤ _ _
      convert .Section.F-seqᴰ _ _ = LMHV.isProp≤ _ _

    FSC : Section FC Cᴰ 
    FSC = GlobalSectionReindex→Section Cᴰ FC convert where 
      convert : GlobalSection (reindexᴰ Cᴰ FC)
      convert .Section.F-obᴰ = M-elim' .snd .fst .Section.F-obᴰ
      convert .Section.F-homᴰ = M-elim' .snd .fst .Section.F-homᴰ
      convert .Section.F-idᴰ = LMHC.isProp≤ _ _
      convert .Section.F-seqᴰ _ _ = LMHC.isProp≤ _ _ 

    M-elim-local : CBPVSection F L 
    M-elim-local .fst = FSV
    M-elim-local .snd .fst = FSC
    M-elim-local .snd .snd = M-elim' .snd .snd
