{-# OPTIONS --type-in-type #-}
module HyperDoc.Operational.Effects.Section where 

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Category
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Section.Base

open import HyperDoc.Algebra.Algebra
open import HyperDoc.Operational.Effects.BiAlgebra
open import HyperDoc.Operational.Effects.Model 

open BiAlg 
open BiAlgᴰ
open BiAlgHom 
open BiAlgHomᴰ
open Category
open Categoryᴰ
open Functor
open Functorᴰ 
open Section
open NatTrans

module _ 
  {Sig : Signature}
  {M N : CBPVModel Sig}
  {F : CBPVMorphism M N } 
  {Nᴰ : CBPVModelᴰ N } where 

  private 
    module M = CBPVModelSyntax M
    module F = CBPVMorphismSyntax F 
    module Nᴰ = CBPVModelᴰSyntax Nᴰ

  module _ 
    (SV : Section F.FV Nᴰ.Vᴰ)
    (SC : Section F.FC Nᴰ.Cᴰ) where 

    open BifunctorSepᴰ Nᴰ.Oᴰ

    record SectionNat : Type _ where 
      field  
        -- needs to be a bialgebra homomorphism
        F-Car : {A : ob M.V}{B : ob M.C}→ 
          (n : M.Node[ A , B ]) → Nᴰ.Nodeᴰ[ F.FO .N-ob _ .map n ][ SV .F-obᴰ A , SC .F-obᴰ B ]
          --  Nᴰ.Nodeᴰ[ F.FO .N-ob _ ? ][ SV .F-obᴰ A , SC .F-obᴰ B ] 
        F-Edge : {A : ob M.V}{B : ob M.C}{n n' : M.Node[ A , B ]}
          (n↦n' : M.Edge[ n , n' ]) → Nᴰ.Edgeᴰ[ F.FO .N-ob _ .isRelator .fst n↦n' ][ F-Car n , F-Car n' ]

        -- TODO
       -- F-ops : {A : ob M.V}{B : ob M.C} → 
      --    PathP (λ i → {! F.FO .N-ob (A , B) .isAlgHom ? ?  !}) {!   !} {!   !} 
        {-}
        F-Edge :{A : ob M.V}{B : ob M.C}{n n' : M.Node[ A , B ]}
          (n↦n' : M.Edge[ n , n' ]) → Nᴰ.Edgeᴰ[ F.FO .N-ob _ .snd n↦n' ][ F-Node n , F-Node n' ]
        -- which is natural
        F-Node-nat : {A A' : ob M.V}{B B' : ob M.C}
          (V : M.V [ A' , A ])(S : M.C [ B , B' ])(n : M.Node[ A , B ]) → 
          PathP 
            (λ i → Nᴰ.Nodeᴰ[ (F.FO .N-hom (V , S) i  .fst n) ][ (SV .F-obᴰ A') , (SC .F-obᴰ B') ]) 
            (F-Node (M.OPar .F-hom (V , S) .fst n)) 
            (Bif-homᴰ (SV .F-homᴰ V)(SC .F-homᴰ S) .fst (F.FO .N-ob _ .fst n) (F-Node n)) 
        F-Edge-nat : {A A' : ob M.V}{B B' : ob M.C}
          (V : M.V [ A' , A ])(S : M.C [ B , B' ])(n n' : M.Node[ A , B ])(n↦n' : M.Edge[ n , n' ]) → 
          PathP 
            (λ i → Nᴰ.Edgeᴰ[ (F.FO .N-hom (V , S) i .snd n↦n') ][ F-Node-nat V S n i , F-Node-nat V S n' i ]) 
            (F-Edge (M.OPar .F-hom (V , S) .snd n↦n')) 
            (Bif-homᴰ (SV .F-homᴰ V)(SC .F-homᴰ S) .snd (F-Node n) (F-Node n') (F-Edge n↦n')) 
-}
  CBPVSection : Type _
  CBPVSection = 
    Σ[ SV ∈  Section F.FV Nᴰ.Vᴰ ] 
    Σ[ SC ∈  Section F.FC Nᴰ.Cᴰ ]  
    SectionNat SV SC
{-


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


-}
