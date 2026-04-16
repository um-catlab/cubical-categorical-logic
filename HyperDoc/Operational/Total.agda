{-# OPTIONS --type-in-type #-}
-- just to define the CBPVMorphism between categories of different levels 
module HyperDoc.Operational.Total where 


open import Cubical.Data.Sigma 

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Category
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Constructions.TotalCategory

open import HyperDoc.Operational.Model 
open import HyperDoc.Operational.Graph
open import HyperDoc.Operational.Section

open Category
open Categoryᴰ
open Functor
open Functorᴰ 
open NatTrans
open Section


module _ 
  {ℓV ℓV' ℓC ℓC' ℓG ℓG' ℓVᴰ ℓVᴰ' ℓCᴰ ℓCᴰ' ℓGᴰ ℓGᴰ' : Level}
  {M N : CBPVModel ℓV ℓV' ℓC ℓC' ℓG ℓG'}
  {F : CBPVMorphism M N }
  {Nᴰ : CBPVModelᴰ N ℓVᴰ ℓVᴰ' ℓCᴰ ℓCᴰ' ℓGᴰ ℓGᴰ'} where 

  module N = CBPVModelSyntax N
  module M = CBPVModelSyntax M
  module F = CBPVMorphismSyntax F
  module Nᴰ = CBPVModelᴰSyntax {ℓCᴰ' = ℓCᴰ'} Nᴰ

  ΣGraph : Functor (∫C (pGRAPHᴰ ℓG ℓG' ℓGᴰ ℓGᴰ' ) ) (pGRAPH (ℓ-max ℓG ℓGᴰ) (ℓ-max ℓG' ℓGᴰ')) 
  ΣGraph .F-ob (G , Gᴰ)= ∫Graphᴰ (G .fst) (Gᴰ .fst) , {!   !}
  ΣGraph .F-hom {G , Gᴰ}{H , Hᴰ} (f , fᴰ)= ∫GraphHomᴰ {G = G .fst}{H .fst}{Gᴰ .fst}{Hᴰ .fst} f fᴰ
  ΣGraph .F-id {G , Gᴰ} = 
    pGraphHom≡ 
      {G = ∫Graphᴰ (G .fst) (Gᴰ .fst) , {!   !}}
      {∫Graphᴰ (G .fst) (Gᴰ .fst)  , {!   !}} 
      refl -- pGraphHom≡ refl
  ΣGraph .F-seq _ _ = {!   !} -- pGraphHom≡ refl

  conv : Functor ((∫C Nᴰ.Vᴰ ^op) ×C ∫C Nᴰ.Cᴰ) (∫C ((Nᴰ.Vᴰ ^opᴰ) ×Cᴰ Nᴰ.Cᴰ))
  conv .F-ob ((A , Aᴰ),(B , Bᴰ)) = (A , B) , Aᴰ , Bᴰ 
  conv .F-hom = λ z → (z .fst .fst , z .snd .fst) , z .fst .snd , z .snd .snd
  conv .F-id = refl
  conv .F-seq _ _ = refl

  TotalModel : CBPVModel (ℓ-max ℓV ℓVᴰ) (ℓ-max ℓV' ℓVᴰ') (ℓ-max ℓC ℓCᴰ) (ℓ-max ℓC' ℓCᴰ) (ℓ-max ℓG ℓGᴰ) (ℓ-max ℓG' ℓGᴰ') 
  TotalModel .fst = ∫C Nᴰ.Vᴰ
  TotalModel .snd .fst = ∫C Nᴰ.Cᴰ
  TotalModel .snd .snd =  {!  !}
    -- annoying bifunctor conversions.. to AND from..  
    -- ΣGraph ∘F ∫F (Nᴰ.Oᴰ) ∘F conv
  module _ 
    (S : CBPVSection {F = F}{Nᴰ}) where 

    SO = S .snd .snd 
    module SV = Section (S .fst)
    module SC = Section (S .snd .fst)
    
    ∫FV : Functor M.V (CBPVModelSyntax.V TotalModel)
    ∫FV .F-ob A = F.FV .F-ob A , SV.F-obᴰ A  
    ∫FV .F-hom f = (F.FV .F-hom f) , SV.F-homᴰ f
    ∫FV .F-id = ΣPathP ((F.FV .F-id) , SV.F-idᴰ)
    ∫FV .F-seq  _ _ = ΣPathP ((F.FV .F-seq _ _) , (SV.F-seqᴰ _ _))

    ∫FC : Functor M.C (CBPVModelSyntax.C TotalModel)
    ∫FC .F-ob A = F.FC .F-ob A , SC.F-obᴰ A  
    ∫FC .F-hom f = (F.FC .F-hom f) , SC.F-homᴰ f
    ∫FC .F-id = ΣPathP ((F.FC .F-id) , SC.F-idᴰ)
    ∫FC .F-seq  _ _ = ΣPathP ((F.FC .F-seq _ _) , (SC.F-seqᴰ _ _))

{-}
    nob : N-ob-Type M.O (CBPVModelSyntax.O TotalModel ∘F ((∫FV ^opF) ×F ∫FC))
    nob (A , B) = 
        (λ M → (F.FO .N-ob (A , B) .fst M) , SO .SectionNat.N-obᴰ M) , 
        λ {M}{M'} M↦M' → (F.FO .N-ob (A , B) .snd M↦M') , SO .SectionNat.N-obᴰRel

    ∫FO : NatTrans M.O (CBPVModelSyntax.O TotalModel ∘F ((∫FV ^opF) ×F ∫FC))
    ∫FO .N-ob = nob
    ∫FO .N-hom {A , B}{A' , B'}(V , S) = 
      -- this second part just blows away because we have prop valued relations in the base and upstairs
      Σ≡Prop (λ  f P Q → implicitFunExt λ {M} → (implicitFunExt λ {M'} → (funExt λ M↦M' → 
        ΣPathP (F-ob (∫F Nᴰ.Oᴰ ∘F conv) (F-ob ((∫FV ^opF) ×F ∫FC) (A' , B')) .fst  .snd (f M .fst) (f M' .fst) (fst (P M↦M')) (fst (Q M↦M')) , 
        toPathP (F-ob (∫F Nᴰ.Oᴰ ∘F conv) (F-ob ((∫FV ^opF) ×F ∫FC) (A' , B')) .snd .snd {f M .fst}{f M' .fst}{fst (Q M↦M')}{f M .snd}{f M' .snd} (transport
           (λ i →
              ⟨
              F-ob (∫F Nᴰ.Oᴰ ∘F conv) (F-ob ((∫FV ^opF) ×F ∫FC) (A' , B')) .snd
              .fst .snd
              (F-ob (∫F Nᴰ.Oᴰ ∘F conv) (F-ob ((∫FV ^opF) ×F ∫FC) (A' , B')) .fst
               .snd (f M .fst) (f M' .fst) (fst (P M↦M')) (fst (Q M↦M')) i)
              (f M .snd) (f M' .snd)
              ⟩)
           (snd (P M↦M'))) (snd (Q M↦M'))))))) 
        (funExt λ M → 
          ΣPathP (
            (λ i → N-hom F.FO (V , S) i .fst M) , 
            SO .SectionNat.N-homᴰ V S M))

    map : CBPVMorphism M TotalModel 
    map .fst = ∫FV 
    map .snd .fst = ∫FC
    map .snd .snd = ∫FO
-}


{-

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
-}