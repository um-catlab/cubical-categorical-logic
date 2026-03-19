{-# OPTIONS --type-in-type #-}
-- fix level issues
-- reorder imports, etc

module HyperDoc.Examples.Conserve where 

  open import Cubical.Data.Bool
  open import Cubical.Data.Empty.Base renaming (elim to elim⊥)
  open import Cubical.Data.FinData
  open import Cubical.Data.Nat
  open import Cubical.Data.Sigma
  open import Cubical.Data.Sum renaming (map to map⊎ ; rec to rec⊎)
  open import Cubical.Relation.Nullary.Base

  open import Cubical.Foundations.HLevels
  open import Cubical.Foundations.Isomorphism hiding (section ; retract)
  open import Cubical.Foundations.Powerset
  open import Cubical.Foundations.Prelude hiding (_∧_)
  open import Cubical.Foundations.Structure
  open import Cubical.HITs.PropositionalTruncation.Base
  open import Cubical.HITs.PropositionalTruncation.Properties
    renaming (rec to hrec ; map to hmap ; map2 to hmap2 ; elim to helim)

  open import Cubical.Categories.Category
  open import Cubical.Categories.Displayed.Section.Base
  open import Cubical.Categories.Functor
  open import Cubical.Categories.NaturalTransformation

  open import HyperDoc.Algebra.Algebra hiding (Model)
  open import HyperDoc.CBPV.Model.Algebra
  open import HyperDoc.CBPV.Model.Base
  import HyperDoc.CBPV.Syntax.UF1 as SUF1
  import HyperDoc.CBPV.Syntax.UF1& as SUF1&
  open import HyperDoc.CBPV.TypeStructure
  open import HyperDoc.Connectives.Connectives
  open import HyperDoc.Lib
  open import HyperDoc.Logic.Base
  import HyperDoc.Logic.UF1& as LUF1&
  import HyperDoc.Logic.UF1 as LUF1
  open import HyperDoc.Logics.Algebra
  open import HyperDoc.Logics.SetPred

  open Alg
  open AlgHom
  open AlgHomᴰ
  open Algᴰ
  open Category
  open Functor
  open Iso renaming (ret to retract)
  open NatTrans
  open Signature
  open Theory

  module _ where 
    data Empty : Type where 
    Sig' : Signature 
    Sig' .Op = Empty
    Sig' .arity ()
    open import Cubical.Categories.Presheaf
    open import Cubical.Categories.Instances.Functors
    open import Cubical.Categories.Constructions.BinProduct


    module Lang1 = SUF1.SyntacticModel Sig'
    module Lang2 = SUF1&.SyntacticModel Sig'

    module M1 = CBPVModel Lang1.SynModel 
    module M2 = CBPVModel Lang2.SynModel 

  
    open SUF1.Recursor Lang2.SynModel 

{-
  AlgModel : CBPVModel Σ
  AlgModel .V = SET _
  AlgModel .C = ALG Σ
  AlgModel .O .F-ob (A , B) .Carrier = (SET _)[ A , B .Carrier ] , (SET _) .isSetHom
  AlgModel .O .F-ob (A , B) .interp op args = λ a → B .interp op (λ x → args x a)
  AlgModel .O .F-hom (f , h) .carmap g a = h .carmap (g (f a))
  AlgModel .O .F-hom (f , h) .pres op args = funExt λ a → h .pres op λ x → args x (f a)
  AlgModel .O .F-id = AlgHom≡ refl
  AlgModel .O .F-seq _ _ = AlgHom≡ refl
-}
    open import Cubical.Categories.Instances.Sets
    open import Cubical.Categories.Instances.Sets.Properties
    open import Cubical.Categories.Limits.Coend
    open import Cubical.Categories.Bifunctor
    open import Cubical.Categories.Presheaf.Representable
    open import Cubical.HITs.SetCoequalizer renaming(rec to srec)
    open UniversalElement
    Diag : Presheaf M2.V _ → Presheaf M2.C _ → Functor ((M2.V ×C M2.C)^op ×C (M2.V ×C M2.C)) (SET _) 
    Diag P Q .F-ob ((v- , c-) , (v+ , c+))= (P .F-ob v- .fst × Q .F-ob  c- .fst × M2.O .F-ob (v- , c+) .Carrier .fst) , {!   !}
    Diag P Q .F-hom {((v- , c-) , (v+ , c+))} {((v-' , c-') , (v+' , c+'))}((V , S) ,(V' , S'))(Pv- , Qc- , M) = 
      (P .F-hom V Pv-) , (Q .F-hom S Qc- , M2.lrcomp V S' .carmap M)
    Diag P Q .F-id = funExt λ (Pv , Qc , M) → ΣPathP (funExt⁻ (P .F-id) _ , ΣPathP ((funExt⁻ (Q .F-id ) _) , {!   !}))
    Diag P Q .F-seq f g = funExt λ (Pv , Qc , M) → ΣPathP ((funExt⁻ (P .F-seq _ _ ) _) , (ΣPathP ((funExt⁻ (Q .F-seq _ _ ) _) , {!   !})))

    coend : (P : Presheaf M2.V _) → (Q : Presheaf M2.C _) → Coend (ParFunctorToBifunctor  (Diag P Q))
    coend P Q = CoendSET (ParFunctorToBifunctor (Diag P Q))

    PshModel : CBPVModel Sig' 
    PshModel .CBPVModel.V = PresheafCategory M2.V _
    PshModel .CBPVModel.C = PresheafCategory M2.C _
    PshModel .CBPVModel.O .F-ob (P , Q) .Carrier = coend P Q .vertex
     -- (Σ[ v ∈ ob M2.V ] (Σ[ c ∈ ob M2.C ] P .F-ob v .fst × Q .F-ob c .fst × M2.O .F-ob (v , c) .Carrier .fst)) , {!   !}
    PshModel .CBPVModel.O .F-ob (P , Q) .interp ()
    PshModel .CBPVModel.O .F-hom {(P , Q)}{(P' , Q')} (f , g) .carmap  = 
      srec 
        squash 
        (λ {((v , c) , Pv , Qc , M) → inc ((v , c) , {!  f .N-ob v !} , (N-ob g c Qc , M))}) 
        {!   !} 
    -- (v , c , Pv , Qc , M) = v , (c , ({!   !} , ({!   !} , {!   !})))
    PshModel .CBPVModel.O .F-hom (f , g) .pres ()
    PshModel .CBPVModel.O .F-id = AlgHom≡ {!   !}
    PshModel .CBPVModel.O .F-seq = {!   !}

    ⊆ : CBPVMorphism Lang1.SynModel Lang2.SynModel 
    ⊆ = M-rec Lang2.has𝟙 Lang2.hasUTy Lang2.hasFTy {!   !}

    extension : CBPVMorphism Lang2.SynModel PshModel 
    extension = {!   !}

{-

  Nerve : Functor D (PRESHEAF C ℓD')
  Nerve = reindPshFStrict F ∘F YOStrict

    open Syntax Σb
    open SyntacticModel Σb using (SynModel ; FreeCompAlg)
    module Syn = CBPVModel SynModel
    open AlgLog Σb 
    open UF1
    open Model Σb 
    open LocalElim Σb AlgModel AlgLogic has⊤ hasV𝟙 hasPush using (M-elim-local ; LM ; pres⊤)
    open ModelSection CL AlgLogic using (CBPVSection)  
    open Section
    open CBPVMorphism CL
    int : InterpGen (LM CL) (pres⊤ CL)

    BoopLR : CBPVSection
    BoopLR  = M-elim-local CL int

    open Recursor AlgModel using (M-rec ; InterpGen)
    open Recursor.InterpGen

    int'  : Recursor.InterpGen AlgModel hasV𝟙 hasUTy hasFTy 

    module F = CBPVMorphism (M-rec hasV𝟙 hasUTy hasFTy int')
-}