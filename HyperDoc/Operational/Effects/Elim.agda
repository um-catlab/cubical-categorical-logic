{-# OPTIONS --type-in-type #-}
module HyperDoc.Operational.Effects.Elim where


open import Cubical.Data.Sum hiding (map)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit 

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Category 
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.NaturalTransformation

open import HyperDoc.Algebra.Algebra
open import HyperDoc.Operational.Effects.Model 
open import HyperDoc.Operational.Effects.Syntax
open import HyperDoc.Operational.Effects.Logic
open import HyperDoc.Operational.Effects.Section
open import HyperDoc.Operational.Effects.TypeStructure
open import HyperDoc.Operational.Effects.BiAlgebra

open Category
open Categoryᴰ
open Functor
open Functorᴰ
open NatTrans
open NatTransᴰ
open Bifunctor
open BifunctorSepᴰ
open Algᴰ
open BiAlg 
open BiAlgᴰ hiding (Edgeᴰ[_][_,_])
open BiAlgHom
open BiAlgHomᴰ

module Elim
  {Sig : Signature} 
  (Synᴰ : CBPVModelᴰ (SynModel.Syn Sig)  )
  where
  open SynModel Sig
  open Syntax Sig
  open CBPVModelᴰSyntax Synᴰ
  open CBPVModelSyntax Syn hiding (V ; C ; O)
  open TypeStructureᴰ Synᴰ 
  open TypeStructureᴰ.Has+'ᴰ
  module _
   --  (hasAnsᴰ : HasAnsᴰ hasAns)
    (has𝟙ᴰ : Has𝟙ᴰ has𝟙)
    -- (has×ᴰ : Has×ᴰ has×)
    (has+ᴰ : Has+ᴰ has+)
    (hasUTyᴰ : HasUTyᴰ hasUTy)
    (hasFTyᴰ : HasFTyᴰ hasFTy)
     where

    open UTySyntaxᴰ hasUTyᴰ
    open FTySyntaxᴰ hasFTyᴰ

    open WkRepresentation
    open WkRepresentationᴰ

    mutual 
      vty : (A : VTy) → ob[ Vᴰ ] A 
      vty 𝟙 = has𝟙ᴰ .fst
     --  vty Ans = hasAnsᴰ .fst
      vty (U B) = Uᴰ (cty B) 
      vty (A ⊕ A₁) = has+ᴰ (vty A) (vty A₁) .Aᴰ+A'ᴰ

      cty : (B : CTy) → ob[ Cᴰ ] B 
      cty (F A) = Fᴰ (vty A) 

    mutual 
      vtm : {A A' : VTy} → (f : Hom[ V , A ] A') → Hom[ Vᴰ ][ f  , vty A ] (vty A')
      vtm (subV V₁ V₂) = (Vᴰ ⋆ᴰ vtm V₁) (vtm V₂)
      vtm var = idᴰ Vᴰ
      vtm (subVIdl V i) = Vᴰ .⋆IdLᴰ (vtm V) i
      vtm (subVIdr V i) = Vᴰ .⋆IdRᴰ (vtm V) i
      vtm (subVAssoc V₁ V₂ V₃ i) = Vᴰ .⋆Assocᴰ (vtm V₁) (vtm V₂) (vtm V₃) i
      vtm (isSet⊢v V₁ V₂ x y i j) = 
        isOfHLevel→isOfHLevelDep 2 
          (λ x → Vᴰ .isSetHomᴰ) 
          (vtm V₁) (vtm V₂) (cong vtm x) (cong vtm y) (isSet⊢v V₁ V₂ x y) i j

      vtm (tt {A}) = has𝟙ᴰ .snd .N-obᴰ (vty A) tt tt
     --  vtm yes = hasAnsᴰ .snd (vty _) .fst
     --  vtm no = hasAnsᴰ .snd (vty _) .snd
      vtm (thunk M) = thunkᴰ (ctm M)
      vtm (subtt {A}{A'}{V} i) = has𝟙ᴰ .snd .N-homᴰ (vtm V) i tt tt
      vtm (σ₁ {A}{A'})= has+ᴰ (vty A) (vty A') .σ₁ᴰ
      vtm (σ₂ {A}{A'}) = has+ᴰ (vty A) (vty A') .σ₂ᴰ

      -- for goal readability
      ctm-subC : {A A' : VTy}{B : CTy} → (V : A' ⊢v A)(M : A ⊢c B) → Oᴰ'[ subC V M ][ vty A' , cty B ] 
      ctm-subC {A}{A'}{B} V M = Oᴰ .Bif-homLᴰ (vtm V) (cty B) .mapᴰ M (ctm M)

      ctm-plug : {A : VTy}{B B' : CTy} → (S : B ⊢k B')(M : A ⊢c B) → Oᴰ'[ plug S M ][ vty A , cty B' ] 
      ctm-plug {A}{B}{B'} S M = Oᴰ .Bif-homRᴰ (ktm S)(vty A) .mapᴰ M (ctm M)

      ctm : {A : VTy}{B : CTy} → (M : A ⊢c B) → Nodeᴰ[ M ][ vty A , cty B ]
      ctm (subC V M) = ctm-subC V M 
      ctm (plug S M) = ctm-plug S M
      ctm (plugId {A}{B}{M} i) =  Oᴰ .Bif-R-idᴰ i .mapᴰ M (ctm M)
      ctm (subCId {A}{B}{M} i) =  Oᴰ .Bif-L-idᴰ i .mapᴰ M (ctm M)
      ctm (plugDist {A}{B}{B'}{B''}{S}{S'}{M} i) = Oᴰ .Bif-R-seqᴰ (ktm S) (ktm S') (~ i) .mapᴰ M (ctm M)
      ctm (subDist {A}{A'}{A''}{B} {V}{V'}{M} i) = Oᴰ .Bif-L-seqᴰ (vtm V') (vtm V) (~ i) .mapᴰ M (ctm M)
      ctm (plugSub {A}{A'}{B}{B'}{V}{M}{S} i) = Oᴰ .SepBif-RL-commuteᴰ (vtm V) (ktm S) i .mapᴰ M (ctm M)
      ctm (ops {A}{B} op args) = interpᴰ (algᴰ (Oᴰ .Bif-obᴰ {A}{B} (vty A) (cty B))) op args λ x → ctm (args x)
      ctm (opsSub V₁ op args i) = {!   !}
      ctm (opsPlug S op args i) = {!   !}
      ctm (isSet⊢c {A}{B} M M₁ x y i i₁) = {!   !}
        {-}
        isOfHLevel→isOfHLevelDep 2 {Node[ A , B ]} {λ M → Nodeᴰ[ M ][ (vty A) , (cty B) ]}
        (λ M → Oᴰ .Bif-obᴰ {A}{B} (vty A)(cty B) .fst M .snd) 
        (ctm M) (ctm M₁) (cong ctm x) (cong ctm y) (isSet⊢c M M₁ x y) i i₁
        -}

      ctm (ret S) = retᴰ (ktm S) 
      ctm (ret-sub {A}{B}{B'}{S}{S'} i) = 
        hasFTyᴰ (vty A) .fwdᴰ .N-homᴰ (ktm S) i S' (ktm S')
        -- subst (λ h → Nodeᴰ[ h ][ vty A , hasFTyᴰ (vty A) .repᴰ ] ) plugId have where 
        --have : Nodeᴰ[ plug hole ret ][ vty A , hasFTyᴰ (vty A) .repᴰ ] 
        --have = hasFTyᴰ (vty A) .fwdᴰ .N-obᴰ (cty (F A)) (C .id) (Cᴰ .idᴰ) 

      ctm (force V) = forceᴰ (vtm V)
      ctm (force-sub {A}{A'}{B}{V}{W} i) = 
        hasUTyᴰ (cty B) .fwdᴰ .N-homᴰ (vtm V) i W (vtm W)
      ctm (match {A}{A'}{B} M M') = has+ᴰ (vty A) (vty A') .matchᴰ .N-obᴰ {B} (cty B) (M , M') (ctm M , ctm M')
      ctm (plugmatch i) = {!   !}
        
        -- subst (λ h → Nodeᴰ[ h ][ hasUTyᴰ (cty B) .repᴰ , cty B ] ) subCId have where 
        
        -- have : Nodeᴰ[ subC var force ][ Uᴰ (cty B) , cty B ] 
        -- have = forceᴰ (Vᴰ .idᴰ)

      open import HyperDoc.Operational.Graph
      ctmRel : {A : VTy}{B : CTy}{M M' : A ⊢c B}
        (M↦M' : M ↦ M') → Edgeᴰ[ M↦M' ][ ctm M , ctm M' ]
      ctmRel (Fβ {A}{B}{M = M}) = {! βᴰ (ctm M)   !} where 
        _ : hasFTyᴰ (vty A) .bkwdᴰ (ctm M) ≡  ktm (bind M) 
        _ = {!   !}
      -- hasFTyᴰ (vty A) .bkwdᴰ (ctm M) != ktm (bind M) 
        _ = {!  ktm (bind M) !} -- normalized hasFTyᴰ (vty A) .bkwdᴰ (ctm M)
        goal =  Fβᴰ (ctm M)
      ctmRel (Uβ {M = M}) =  Uβᴰ (ctm M) 
      {-} have : Edgeᴰ[ Uβ ][ forceᴰ (thunkᴰ (ctm M)) , ctm M ] 
        have = Uβᴰ (ctm M)

        sub' : forceᴰ (thunkᴰ (ctm M)) ≡ Oᴰ .Bif-homLᴰ (vtm (thunk M)) _ .fst _ (ctm force) 
        -- ctm-subC (thunk M) force
        sub' = {!   !}

        goal : Edgeᴰ[ Uβ ][ ctm-subC (thunk M) force , ctm M ] 
        goal = subst (λ h → Edgeᴰ[ Uβ ][ h , ctm M ] ) sub' have
-}
        {-}
        _ = {! ctm-subC (thunk M) force  !}
        _ :  Edgeᴰ[ wkretract (hasUTy B) (subC (thunk M) force) ][ hasUTyᴰ (cty B) .fwdᴰ .N-obᴰ (vty A)
          (bkwd (hasUTy B) (subC (thunk M) force))
          (hasUTyᴰ (cty B) .bkwdᴰ (ctm (subC (thunk M) force))) , ctm (subC (thunk M) force) ]
        _ = hasUTyᴰ (cty B) .wkretractᴰ {A}{vty A}{subC (thunk M) force}(ctm (subC (thunk M) force))-}
      ctmRel (subC-cong {A}{A'}{B}{V}{M}{M'} M↦M') = 
        (Oᴰ .Bif-homLᴰ (vtm V) (cty B)) .isRelatorᴰ .fst (ctm M) (ctm M') (ctmRel M↦M')
      ctmRel (plug-cong {A}{B}{B'}{S}{M}{M'} M↦M') =
         Oᴰ .Bif-homRᴰ (ktm S) (vty A) .isRelatorᴰ .fst (ctm M) (ctm M') (ctmRel M↦M')
      ctmRel (+β₁ {A}{A'}{B}{M}{M'})  = has+ᴰ (vty A) (vty A') .+β₁ᴰ {B}{cty B}{M}{M'}{+β₁} (ctm M) (ctm M')
      ctmRel (+β₂ {A}{A'}{B}{M}{M'})  = has+ᴰ (vty A) (vty A') .+β₂ᴰ {B}{cty B}{M}{M'}{+β₂} (ctm M) (ctm M')
      ctmRel (βrefl {A}{B}{M}) = Oᴰ .Bif-obᴰ {A}{B} (vty A) (cty B) .isRGraphᴰ .snd (ctm M)
      ctmRel (alg-cong {A}{B}{op}{args}{args'} edges) = 
        Oᴰ .Bif-obᴰ {A}{B} (vty A) (cty B) .congruenceᴰ op args args' edges 
        (λ x → ctm (args x)) 
        (λ x → ctm (args' x)) 
        λ x → ctmRel {A}{B}{args x}{args' x} (edges x)
      ctmRel (isProp↦ a b  i) = {!   !}

      ktm : {B B' : CTy} → (f : Hom[ C , B ] B') → Hom[ Cᴰ ][ f  , cty B ] (cty B')
      ktm (kcomp S S₁) = (Cᴰ ⋆ᴰ ktm S) (ktm S₁)
      ktm hole = idᴰ Cᴰ
      ktm (kcompIdl S i) = Cᴰ .⋆IdLᴰ (ktm S) i
      ktm (kcompIdr S i) = Cᴰ .⋆IdRᴰ (ktm S) i
      ktm (kcompAssoc S S₁ S₂ i) = Cᴰ .⋆Assocᴰ (ktm S) (ktm S₁) (ktm S₂)  i
      ktm (isSet⊢k S S₁ x y i j) = 
        isOfHLevel→isOfHLevelDep 2 
          (λ x → Cᴰ .isSetHomᴰ) 
          (ktm S) (ktm S₁) (cong ktm x) (cong ktm y) (isSet⊢k S S₁ x y) i j
      ktm (bind {A}{B} M) = hasFTyᴰ (vty A) .bkwdᴰ (ctm M)
      
        -- bindᴰ (ctm M)
      
      SV : Section Id Vᴰ 
      SV .Section.F-obᴰ = vty
      SV .Section.F-homᴰ = vtm
      SV .Section.F-idᴰ = refl
      SV .Section.F-seqᴰ _ _ = refl

      SC : Section Id Cᴰ 
      SC .Section.F-obᴰ = cty
      SC .Section.F-homᴰ = ktm
      SC .Section.F-idᴰ = refl
      SC .Section.F-seqᴰ _ _ = refl

      -- TODO, need to fill our rest
      SO : SectionNat {F = idModelMorphsim Syn}{Nᴰ = Synᴰ} SV SC
      SO .SectionNat.F-Car = ctm
      SO .SectionNat.F-Edge = ctmRel
{-}
      SO : SectionNat {F = idModelMorphsim Syn}{Nᴰ = Synᴰ} SV SC
      SO .SectionNat.F-Node = ctm
      SO .SectionNat.F-Edge = ctmRel
      SO .SectionNat.F-Node-nat V S M = refl
      SO .SectionNat.F-Edge-nat V S M M' M↦M' = refl
-}
      Elim : CBPVSection {F = idModelMorphsim Syn}{Synᴰ} 
      Elim .fst = SV
      Elim .snd .fst = SC
      Elim .snd .snd = SO
