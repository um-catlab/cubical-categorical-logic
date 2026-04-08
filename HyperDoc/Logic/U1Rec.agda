{-# OPTIONS --type-in-type #-}
-- fix level issues
-- reorder imports, etc

module HyperDoc.Logic.U1Rec where 

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Constructions.Reindex.Base renaming (reindex to reindexᴰ)

open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Functor 
open import Cubical.Categories.Instances.Preorders.Monotone

open import HyperDoc.Algebra.Algebra
open import HyperDoc.CBPV.Syntax.U1Rec
open import HyperDoc.CBPV.Model.Base
open import HyperDoc.Syntax
open import HyperDoc.Logic.Base
open import HyperDoc.Connectives.Connectives
open import HyperDoc.CBPV.TypeStructure
open import HyperDoc.Logics.StepIndexed

open AlgHomᴰ
open Bifunctorᴰ
open Categoryᴰ
open Functor

module _ {Σ : Signature} where
  open SyntacticModel Σ  

  record InterpGen 
        (L : Logic SynModel)
        (⊤ : L⊤.Has⊤ (Logic.VH L)): Type where 
      open Logic L
      open Syntax Σ 
      open L⊤.HA 
      private
        module LV = HDSyntax VH 
        module LC = HDSyntax CH 
      field 
        interpAns : LC.F∣ Ans ∣
        interpYes : 𝟙 LV.◂ top (⊤ .fst 𝟙) ≤ (pull yes $ interpAns)
        interpNo : 𝟙 LV.◂ top (⊤ .fst 𝟙) ≤ (pull no $ interpAns)


module Eliminator (Σ : Signature) where 
  open Syntax Σ
  open SyntacticModel Σ
  open Section
  open import Cubical.Data.Sum

  
  module _ (L : Logic SynModel) where

    open ConvertLogic SynModel L
    open Logic L
    module LV = HDSyntax VH
    module LC = HDSyntax CH
    open TypeStructure SynModel

    hasδ : Hasδ
    hasδ .fst = hasUTy
    hasδ .snd B = δ 

    module _ 
      (V⊤ : HasV𝟙 )
      (later : L▷.Has▷ VH)
      (hasΘᴰ : HasVΘᴰ.HasΘᴰ L hasδ later )
        where
      
      ⊤ : L⊤.Has⊤ VH 
      ⊤ = later .fst

      module _ (interpGen : InterpGen L ⊤ ) where 

        open L⊤.HA 
        open L▷


        open InterpGen interpGen
        
        mutual
          vty : (A : VTy) → LV.F∣ A ∣
          vty 𝟙 = top (⊤ .fst 𝟙)
          vty (U B) = pull force $ cty B

          cty : (B : CTy) → LC.F∣ B ∣
          cty Ans = interpAns

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
          open import Cubical.Categories.Displayed.HLevels.More

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
          vtm (Uη {A}{B}{V} i) = {!   !}
            {-}
            isProp→PathP 
              ((λ i → LV.isProp≤{q = LV.f* (Uη i) (pull force $ cty B)})) 
              {!  !} -- (vtm-thunk (subC' V force')) 
              (vtm V) 
              i -}
          vtm tt = LV.seq (top-top (⊤ .fst _)) (LV.eqTo≤ (sym (L⊤.HAHom.f-top (⊤ .snd tt))))
          vtm (η𝟙 {A} V i) = 
            VL.eq*PathP (η𝟙 {A} V) 
              (LV.seq (top-top (⊤ .fst _)) (LV.eqTo≤ (sym (L⊤.HAHom.f-top (⊤ .snd tt))))) 
              (vtm V) 
              i
          vtm (δ {B}) = goal where 
            open LaterStr (later .snd .fst (U B))

            P = pull force $ cty B

            goal : U B LV.◂ P ≤ LV.f* δ P
            goal = LV.seq ▷-intro hasΘᴰ 

          vtm (fix {B} V) = goal where 
            module L1 =  LaterStr (later .snd .fst 𝟙)
            module L2 =  LaterStr (later .snd .fst (U B))

            P = (pull force $ cty B) 
            fix*P = LV.f* (fix V) P

            IH : U B LV.◂ P ≤ LV.f* V P
            IH = vtm V

            have1 : 𝟙 LV.◂ fix*P ≤ LV.f* (fix V) (LV.f* V P) 
            have1 = LV.mon* ((fix V)) IH

            yosh : 𝟙 LV.◂ LV.f* (subV (fix V) δ) P ≤ LV.f* (subV (fix V) δ) (LV.f* V P)
            yosh = LV.mon* (subV (fix V) δ) IH

            know : 𝟙 LV.◂ LV.f* (subV (subV (fix V) δ) V) P ≤ fix*P 
            know = LV.eqTo≤ (cong₂ LV.f* (sym unfold) refl)
   
            comsub : 𝟙 LV.◂ L1.▷ fix*P  ≤ LV.f* (fix V) (L2.▷ P) 
            comsub = LV.eqTo≤ (sym (f-▷ P)) where 
              open HAHom (later .snd .snd (fix V))

            ye : 𝟙 LV.◂ LV.f* (fix V) (L2.▷ P) ≤ LV.f* (fix V) (LV.f* δ P) 
            ye = LV.mon* ((fix V)) hasΘᴰ

            {-
              goal: ⊤ ≤ (fix V)*P 
                where P := force^*〚B〛

              using lob
                s.t.s ▷ ((fix V)* P) ≤ (fix V)* P

              
               ▷ ((fix V)* P)
                  by preservation of later (f-▷ : f (▷ P) ≡ (▷ f P))
               ≤ (fix V)* (▷ P)
                  by monotonicity and Θᴰ
               ≤ (fix V)* (δ* P) 
               = (fix V ; δ)* P
                  by monotonicity and IH (U B ◂ P ≤ V* P)
               ≤ (fix V ; δ)* (V* P)
               = (fix V ; δ ; V)* P 
                  by unfold equation (fix V ≡ (fix V) ; δ ; V
               = (fix V)* P
            -}
            sub : 𝟙 LV.◂ L1.▷ fix*P ≤ fix*P
            sub = 
              LV.seq 
                comsub 
              (LV.seq 
                ye 
              (LV.seq 
                (LV.seq (LV.eqTo≤ (sym LV.f*seq)) (LV.seq yosh (LV.eqTo≤ (sym LV.f*seq)))) 
                know)) 

            goal : 𝟙 LV.◂ top (⊤ .fst 𝟙) ≤ fix*P
            goal = L1.lob sub

          vtm (unfold {B}{V} i) = {!    !} 
 
      
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

        --   {-# TERMINATING #-}
          -- Idk why.. but this termination pragma is needed for plugDist
          -- which is just showing that the PathP is a prop.. 
          -- there should be NO interesting recursion in the proof of equality
          -- need to fix
          -- this is NOT needed for fix or δ
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
              {!   !} -- (ctm-plug S' (plug S M)) 
              (ctm-plug (kcomp S S') M)
              i 
          ctm (subDist {A}{A'}{A''}{B}{V}{V'}{M} i) = 
            isProp→PathP 
              (λ i → LV.isProp≤{q = (pull (subDist i) $ cty B)}) 
              {!   !} -- (ctm-subC V (subC V' M)) 
              (ctm-subC (subV V V') M)
              i 
          ctm (plugSub {A}{A'}{B}{B'}{V}{M}{S} i) =           
            isProp→PathP 
              (λ i → LV.isProp≤{q = (pull (plugSub i) $ cty B')}) 
              {!   !} -- (ctm-subC V (plug S M)) 
              {!   !} -- (ctm-plug S (subC V M))
              i 
          ctm (isSet⊢c M M' x y i j) = 
              isOfHLevel→isOfHLevelDep 2 
                (λ x → isProp→isSet VL.isProp≤) 
                (ctm M) (ctm M') 
                (cong ctm x) (cong ctm y) 
                (isSet⊢c M M' x y) i j 

          -- later effect
        --  ctm (ops A B (inl _) M) = {!   !}
          -- other effects
          ctm (ops A B op args) = pullOp op args (vty A) (cty B) (λ x → ctm (args x))
            -- pullOp op args (vty A) (cty B) (λ x → ctm (args x))
          ctm (opsSub {A}{A'}{B} V op args i) = 
            isProp→PathP 
              (λ i → LV.isProp≤{q = (pull (opsSub V op args i) $ cty B)}) 
              {!   !} -- (ctm-subC V (ops A' B op args))
              (pullOp op (λ x → subC V (args x)) (vty A) (cty B) (λ x → ctm-subC V (args x)))
              i 
          ctm (opsPlug {A}{B}{B'} S op args i) = 
            isProp→PathP 
              ((λ i → LV.isProp≤{q = (pull (opsPlug S op args i) $ cty B')}))
              {!   !} -- (ctm-plug S (ops A B op args))
              (pullOp op (λ x → plug S (args x)) (vty A) (cty B')(λ x → ctm-plug S (args x)))
              i 
          ctm force = LV.id⊢
          ctm yes = interpYes
          ctm no = interpNo
          ctm (Uβ {A}{B}{M} i) = 
            isProp→PathP 
              ((λ i → LV.isProp≤{q = (pull (Uβ i) $ cty B)})) 
               {!   !} -- (ctm-subC (thunk M) force) 
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
  (NΘ : TypeStructure.Hasδ N)
  (L : Logic N)
  (has▷ : L▷.Has▷ (Logic.VH L))
  (hasΘ : HasVΘᴰ.HasΘᴰ L NΘ has▷ )where
  
  
  -- (⊤ : L⊤.Has⊤ (Logic.VH L)) where
 --  (hasV𝟙 : TypeStructure.HasV𝟙 N) where

  open Syntax Σ
  open SyntacticModel Σ

  module _ (F : CBPVMorphism SynModel N) where
    
    open Reindex F L 
    open ModelSection
    open CBPVMorphism F
    open TypeStructure
   -- open HasVΘᴰ

    open ConvertLogic N L

    LM : Logic SynModel
    LM = reindex

    open Eliminator Σ 
          
    module LMHV = HDSyntax (Logic.VH LM)
    module LMHC = HDSyntax (Logic.CH LM)

    pres⊤ : L⊤.Has⊤ (Logic.VH LM) 
    pres⊤ .fst = λ c → has▷ .fst .fst (F-ob (FV ^opF) c)
    pres⊤ .snd = λ f → has▷ .fst .snd (F-hom (FV ^opF) f) 

    pres▷ : L▷.Has▷ (Logic.VH LM) 
    pres▷ .fst = pres⊤
    pres▷ .snd .fst = λ c → has▷ .snd .fst (F-ob (FV ^opF) c)
    pres▷ .snd .snd = λ f → has▷ .snd .snd (F-hom (FV ^opF) f)

    presΘ : HasVΘᴰ.HasΘᴰ LM (hasδ LM) pres▷ 
    presΘ {B}{P} = goal where 
      open L▷.LaterStr (pres▷ .snd .fst (U B))
      
      module N = CBPVModel N
      open import Cubical.Categories.Category
      open Category

      U' : N.C .ob → N.V .ob 
      U' = USyntax.U N (NΘ .fst)

      δ' = (HasVΘᴰ.δ L NΘ has▷)

      have : {B : N.C .ob}{P : VL.F∣ USyntax.U N (NΘ .fst) B ∣} → 
        U' B VL.◂ L▷.LaterStr.▷_ (has▷ .snd .fst (U' B)) P ≤ VL.f* δ' P 
      have {B} = hasΘ {B}

      goal : U B LMHV.◂ ▷ P ≤ LMHV.f* δ P 
      goal = also where 
        also : F-ob (FV ^opF) (U B) VL.◂ ▷ P ≤ VL.f* (FV .F-hom δ) P
        -- LMHV.f* δ P 
        also = VL.seq {! have {F-ob (FC ^opF) B}{?}  !} {!   !}

    module _ (interp : InterpGen LM pres⊤) where
      
      M-elim' : CBPVGlobalSection LM
      M-elim' = M-elim LM has𝟙 pres▷ presΘ interp 
      -- LM pres⊤ (SyntacticModel.has𝟙 Σ) interp
      
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


{-
getting the recursor from the eliminator when using Logic as a parameter.. 
.. doesnt work the same way
module Recursor {Σ : Signature} (M : CBPVModel Σ)where 
  open Syntax Σ 
  open SyntacticModel Σ using (SynModel)
  open Section
  open CBPVModel
  
  open import Cubical.Categories.Category
  open import Cubical.Categories.Instances.Posets.Base
  open import Cubical.Relation.Binary.Preorder
  open Eliminator Σ

  open Category

-- we can get a functor into the target category truncated to a poset
  -- no.. 
  hack : Category _ _ → ob (POSET _ _ ) 
  hack C .fst .fst = C .ob
  hack C .fst .snd .PreorderStr._≤_ A B = C [ A , B ] 
  hack C .fst .snd .PreorderStr.isPreorder .IsPreorder.is-prop-valued = {!   !}
  hack C .fst .snd .PreorderStr.isPreorder .IsPreorder.is-refl = {!   !}
  hack C .fst .snd .PreorderStr.isPreorder .IsPreorder.is-trans = {!   !}
  hack C .snd = {!   !}

  hm : Logic SynModel 
  hm .Logic.VH = {!   !}
  hm .Logic.CH = {!   !}
  hm .Logic.Sq = {!   !}
  hm .Logic.pullOp = {!   !}

  _ : {!   !}
  _ = M-elim {!   !} {!   !} {!   !} {!   !}

  M-recV : Functor (SynModel .V) (M .V) 
  M-recV = {!   !}
  
  M-rec : CBPVMorphism SynModel M
  M-rec = {! M-elim'  !}

{-
    rec : (ı : Interpᴰ wkC) → Functor |FreeCartesianCategory| (CC .C)
    rec ı = introS⁻ (elim wkC ı)
-}
-}