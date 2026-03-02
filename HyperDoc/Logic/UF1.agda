{-# OPTIONS --type-in-type #-}
-- fix level issues
-- reorder imports, etc

module HyperDoc.Logic.UF1 where 

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Constructions.Reindex.Base renaming (reindex to reindexᴰ)

open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Functor 
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.NaturalTransformation

open import HyperDoc.Algebra.Algebra
open import HyperDoc.CBPV.Syntax.UF1
open import HyperDoc.CBPV.Model.Base
open import HyperDoc.Syntax
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

module _ {Σ : Signature} where
  open SyntacticModel Σ  

  record InterpGen 
      (L : Logic (SyntacticModel.SynModel Σ))
      (⊤ : L⊤.Has⊤ (Logic.VH L)): Type where 
    open Logic L
    open Syntax Σ 
    open L⊤.HA 
    private
      module LV = HDSyntax VH 
      module LC = HDSyntax CH 
    field 
      interpAns : LV.F∣ Ans ∣
      interpYes : 𝟙 LV.◂ top (⊤ .fst 𝟙) ≤ LV.f* yes interpAns
      interpNo : 𝟙 LV.◂ top (⊤ .fst 𝟙) ≤ LV.f* no interpAns

module Eliminator (Σ : Signature) where 
  open Syntax Σ
  open SyntacticModel Σ
  open Section
  
  module _ (L : Logic SynModel) where

    open ConvertLogic SynModel L
    open Logic L
    module LV = HDSyntax VH
    module LC = HDSyntax CH
    open TypeStructure SynModel
    open Push L
      

    module _ 
      (⊤ : L⊤.Has⊤ VH)
      (V⊤ : HasV𝟙 )
      (push : HasPush)
      (interpGen : InterpGen L ⊤ )
        where

      open L⊤.HA 
      open PushSyntax push
      
      open InterpGen interpGen
      
      mutual
        vty : (A : VTy) → LV.F∣ A ∣
        vty 𝟙 = top (⊤ .fst 𝟙)
        vty Ans = interpAns
        vty (U B) = pull force $ cty B

        cty : (B : CTy) → LC.F∣ B ∣
        cty (F A) = push ret .fst $  vty A


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

        vtm (yes) = interpYes 
        vtm (no) = interpNo  
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

        ktm-bind : ∀ {A  B} → (M : A ⊢c B) → F A LC.◂ push ret .fst $ vty A ≤ LC.f* (bind M) (cty B)
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
            (λ i → LC.isProp≤{p = push ret .fst $ vty A} {q = LC.f* (Fη i) (cty B)})
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

module LocalElim 
  (Σ : Signature) 
  (N : CBPVModel Σ)
  (L : Logic N)
  (⊤ : L⊤.Has⊤ (Logic.VH L))
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

    module _ (interp : InterpGen LM pres⊤) where

      M-elim' : CBPVGlobalSection LM
      M-elim' = M-elim LM pres⊤ (SyntacticModel.has𝟙 Σ) presPush interp
      
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
