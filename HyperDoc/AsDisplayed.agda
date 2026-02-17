module HyperDoc.AsDisplayed where 

open import Cubical.Data.Sigma
open import Cubical.Data.Unit 
open import Cubical.Relation.Binary.Preorder
open import Agda.Builtin.Cubical.Equiv

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure 
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Category 
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf.Representable 

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.BinProduct 
open import Cubical.Categories.Displayed.Instances.Sets

open import Cubical.Categories.Displayed.Fibration
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Limits.BinProduct.Base
open import Cubical.Categories.Displayed.Limits.BinProduct.Properties
open import Cubical.Categories.NaturalTransformation

open import HyperDoc.Syntax
open import HyperDoc.CBPVLogic
open import HyperDoc.CBPVModel
open import HyperDoc.Lib
open import HyperDoc.Connectives.Connectives

open Category
open Categoryᴰ
open Functorᴰ
open Functor
open Iso
open MonFun
open UniversalElement
open NatTrans
open PreorderStr
open MonFun renaming (f to fun)

-- demonstrating that our proof irrelevant model 
-- lines up with the proof relevant version
module convert 
  {ℓ ℓ' ℓP ℓP' : Level}{C : Category ℓ ℓ'}
  (F : Functor (C ^op) (POSET ℓP ℓP')) where 

  open HDSyntax F  

  Cᴰ : Categoryᴰ C ℓP ℓP' 
  ob[ Cᴰ ] = F∣_∣
  Cᴰ .Hom[_][_,_] {x}{y} f Fx Fy = x ◂ Fx ≤ f* f Fy
  Cᴰ .idᴰ = eqTo≤  (sym f*id)
  Cᴰ ._⋆ᴰ_ {f = f} {g} = seq* f g
  Cᴰ .⋆IdLᴰ fᴰ = toPathP (isProp≤ _ fᴰ)
  Cᴰ .⋆IdRᴰ fᴰ = toPathP (isProp≤ _ fᴰ)
  Cᴰ .⋆Assocᴰ _ _ _ = toPathP (isProp≤ _ _)
  Cᴰ .isSetHomᴰ = isProp→isSet isProp≤ 


module _ 
  {ℓV ℓV' ℓC ℓC' ℓP ℓP' : Level}
  (M : Model ℓV ℓV' ℓC ℓC' (ℓ-max ℓV ℓV) )
  (L : Logic {ℓV }{ℓV'} M) where 
  open Model M 
  open Logic L
  
  Vᴰ : Categoryᴰ V ℓV ℓV 
  Vᴰ = convert.Cᴰ VH

  Cᴰ : Categoryᴰ C ℓV ℓV 
  Cᴰ = convert.Cᴰ CH
  
  module VL = HDSyntax VH 
  module CL = HDSyntax CH 

  Oᴰ :  Functorᴰ O ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) (SETᴰ ℓV ℓV )
  Oᴰ .F-obᴰ {(A , B)}(P , Q) o = (A VL.◂ P ≤ (Sq .N-ob (A , B) o .fun Q) ), isProp→isSet VL.isProp≤ 
  Oᴰ .F-homᴰ {(A , B)}{(A' , B')}{(f , g)}{(P , Q)}{(P' , Q')}(P'≤f*P , Q≤g*Q' ) o  P≤o*Q = 
    VL.seq  P'≤f*P (VL.seq (VL.mon* f P≤o*Q) (VL.seq (VL.mon* f (Sq .N-ob (A , B) o .isMon  Q≤g*Q')) ?))
    -- (VL.eqTo≤ (cong (λ h → h .fun Q') {! λ i →  sym (Sq .N-hom (f , g) i o)   !})))) 

    -- foo = {! funExt⁻ (Sq .N-hom (f , g )) o _ .isMon _ !}
  Oᴰ .F-idᴰ = toPathP (funExt λ _ → funExt λ _ → VL.isProp≤ _ _)
  Oᴰ .F-seqᴰ _ _ = toPathP (funExt λ _ → funExt λ _ → VL.isProp≤ _ _)
  
{-

module _ 
  {ℓV ℓV' ℓC ℓC' ℓS ℓP ℓP' ℓR : Level}
  {(M , V⊤  , UTy , FTy , C×) : ModelWithTypeStructure ℓV ℓV' ℓC ℓC' ℓS}
  (L : Logic M ) 
  ((⊤ , ∧) : WithConnectives L)where 

  open TypeSyntax (M , V⊤  , UTy , FTy , C×) renaming(⊤ to ⊤ty ; tt to tterm)

  open Model M 
  open Logic L
  --open L⊤.HA 
  -- open L∧.HA renaming (_∧_ to and)
  open L⊤.HA 
  open L∧.HA renaming (_∧_ to and)
  module LV = HDSyntax VH
  module LC = HDSyntax CH
  open L⊤.HAHom
  open L∧.HAHom

  Vterm : Terminal' V
  Vterm .vertex = ⊤ty
  Vterm .element = tt
  Vterm .universal A .equiv-proof tt = {!   !}

  Cbp : BinProducts C 
  Cbp (a , b) .vertex = a & b
  Cbp (a , b) .element = (π₁ (C .id)) , π₂ (C .id)
  Cbp (a , b) .universal A .equiv-proof (f , g) = ({!   !} , {!   !}) , (λ y   → {!   !})


  Vᴰ : Categoryᴰ V ℓV ℓV 
  Vᴰ = convert.Cᴰ VH

  Cᴰ : Categoryᴰ C ℓV ℓV 
  Cᴰ = convert.Cᴰ CH

  VHisFibration : isFibration Vᴰ 
  VHisFibration cᴰ p .UniversalElementⱽ.vertexⱽ = VH .F-hom p .f cᴰ
  VHisFibration cᴰ p .UniversalElementⱽ.elementⱽ = LV.eqTo≤ (cong (λ h → VH .F-hom h .f cᴰ) (sym (V .⋆IdL p)))
  VHisFibration cᴰ p .UniversalElementⱽ.universalⱽ .fst prf = LV.seq prf (LV.eqTo≤ (cong (λ h → h .f cᴰ) (VH .F-seq _ _)))
  VHisFibration cᴰ p .UniversalElementⱽ.universalⱽ .snd .fst _ = LV.isProp≤ _ _
  VHisFibration cᴰ p .UniversalElementⱽ.universalⱽ .snd .snd _ = LV.isProp≤ _ _

  CHisFibration : isFibration Cᴰ 
  CHisFibration cᴰ p .UniversalElementⱽ.vertexⱽ = CH .F-hom p .f cᴰ
  CHisFibration cᴰ p .UniversalElementⱽ.elementⱽ = LC.eqTo≤ (cong (λ h → CH .F-hom h .f cᴰ) (sym (C .⋆IdL p)))
  CHisFibration cᴰ p .UniversalElementⱽ.universalⱽ .fst prf = LC.seq prf (LC.eqTo≤ (cong (λ h → h .f cᴰ) (CH .F-seq _ _)))
  CHisFibration cᴰ p .UniversalElementⱽ.universalⱽ .snd .fst _ = LC.isProp≤ _ _
  CHisFibration cᴰ p .UniversalElementⱽ.universalⱽ .snd .snd _ = LC.isProp≤ _ _

  Vᴰtermⱽ : Terminalsⱽ Vᴰ
  Vᴰtermⱽ c .UniversalElementⱽ.vertexⱽ = top (⊤ .fst c)
  Vᴰtermⱽ c .UniversalElementⱽ.elementⱽ = tt
  Vᴰtermⱽ c .UniversalElementⱽ.universalⱽ {y = c'}{f = f} .fst tt = LV.seq (top-top (⊤ .fst c')) (LV.eqTo≤ (sym (f-top (⊤ .snd f) )))
  Vᴰtermⱽ c .UniversalElementⱽ.universalⱽ .snd .fst tt = refl
  Vᴰtermⱽ c .UniversalElementⱽ.universalⱽ .snd .snd a = LV.isProp≤ _ a

  Vᴰtermᴰ : Terminalᴰ Vᴰ Vterm 
  Vᴰtermᴰ = Terminalⱽ→Terminalᴰ Vᴰ (Vᴰtermⱽ (TerminalNotation.𝟙 Vterm))

  Cᴰbpⱽ : BinProductsⱽ Cᴰ 
  Cᴰbpⱽ x (P , Q) .UniversalElementⱽ.vertexⱽ = and (∧ .fst x) P Q
  Cᴰbpⱽ x (P , Q) .UniversalElementⱽ.elementⱽ = (LC.f*id' (and-elim1 (∧ .fst x) LC.id⊢)) , LC.f*id' (and-elim2 (∧ .fst x) LC.id⊢)
  Cᴰbpⱽ x (P , Q) .UniversalElementⱽ.universalⱽ {y = y}{f = f} .fst (R≤f*P , R≤f*Q)= LC.seq (and-intro (∧ .fst y)  R≤f*P R≤f*Q) (LC.eqTo≤  (sym (f-and (∧ .snd f) _ _)))
  Cᴰbpⱽ x (P , Q) .UniversalElementⱽ.universalⱽ .snd .fst (prf , prf') = ΣPathP ((LC.isProp≤ _ _) , LC.isProp≤ _ _)
  Cᴰbpⱽ x (P , Q) .UniversalElementⱽ.universalⱽ .snd .snd _ = LC.isProp≤ _ _

  Cᴰbpᴰ : BinProductsᴰ Cᴰ Cbp
  Cᴰbpᴰ = BinProductsⱽ→BinProductsᴰ _ CHisFibration Cᴰbpⱽ Cbp

  module SETᴰ = Fibers (SETᴰ ℓS ℓV)

--  open ORelFunctor ORel

{-
-- Recommendation: implement PROPᴰ and then implement this as a composition of a ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) to PROPᴰ and a vertical functor PROPᴰ to SETᴰ
Oᴰ : Functorᴰ O ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) (SETᴰ ℓS ℓV)
Oᴰ .F-obᴰ (P , Q) o = ⟨ Rel P Q o ⟩ , isProp→isSet (Rel P Q o .snd)
Oᴰ .F-homᴰ {(v , c)}{(v' , c')}{(f , g)}{(P , Q)}{(P' , Q')}(v'P'≤f*P' , c'Q'≤g*Q) o =
  RelMono v'P'≤f*P' c'Q'≤g*Q
Oᴰ .F-idᴰ {(v , c)}{(P , Q)} =
  -- agda can't fill in these implicits because there is no canonical choice
  SETᴰ.rectifyOut {a = O ⟅ (v , c) ⟆ }{b = O ⟅ (v , c) ⟆ }
    {aᴰ = λ o → ⟨ Rel P Q o ⟩ , isProp→isSet (Rel P Q o .snd)}
    {bᴰ = λ o → ⟨ Rel P Q o ⟩ , isProp→isSet (Rel P Q o .snd)}
    (ΣPathP (O .F-id , toPathP (funExt λ o → funExt λ r → Rel P Q o .snd _ r)))
Oᴰ .F-seqᴰ {(v , c)}{(v' , c')}{(v'' , c'')}{(f , g)}{(f' , g')}{(P , Q)}{(P' , Q')}{(P'' , Q'')} fᴰ gᴰ =
  SETᴰ.rectifyOut {a = O ⟅ (v , c) ⟆}{b = O ⟅ (v'' , c'') ⟆}{aᴰ = λ o → ⟨ Rel P Q o ⟩ , isProp→isSet (Rel P Q o .snd)}{bᴰ = λ o → ⟨ Rel P'' Q'' o ⟩ , isProp→isSet (Rel P'' Q'' o .snd)}
    
    (ΣPathP (O .F-seq _ _ , toPathP (funExt λ o → funExt λ r → Rel P'' Q'' (O .F-hom (f' , g') (O .F-hom (f , g) o)) .snd _ _ )))
-}
-}