{-# OPTIONS --type-in-type #-}
module HyperDoc.Operational.Elim where


open import Cubical.Data.Sum
open import Cubical.Data.Sigma 

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
-- open import Cubical.Categories.Limits.Terminal.More
-- open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.NaturalTransformation

open import HyperDoc.Operational.Model 
open import HyperDoc.Operational.Initial
open import HyperDoc.Operational.Logic
open import HyperDoc.Operational.Section
open import HyperDoc.Operational.TypeStructure

open Category
open Categoryᴰ
open Functor
open Functorᴰ
open NatTrans
open NatTransᴰ
open Bifunctor
open BifunctorSepᴰ

module Elim 
  { ℓVᴰ ℓVᴰ' ℓCᴰ ℓCᴰ' ℓGᴰ ℓGᴰ' : Level}
  (Synᴰ : CBPVModelᴰ Syn ℓVᴰ ℓVᴰ' ℓCᴰ ℓCᴰ' ℓGᴰ ℓGᴰ' )
  where

  open CBPVModelᴰSyntax Synᴰ
  open CBPVModelSyntax Syn hiding (V ; C ; O)
  open TypeStructureᴰ Synᴰ 

  -- dumb displayed model 
  -- 

  -- needed assumptions
  -- TODO, specify as displayed type structures
  module _
    (𝟙ᴰ : ob[ Vᴰ ] 𝟙)
    (Ansᴰ : ob[ Vᴰ ] Ans)
    (hasUTyᴰ : HasUTyᴰ hasUTy)
    (hasFTyᴰ : HasFTyᴰ hasFTy)
   {- (propEdgeᴰ : 
      {A : VTy}{B : CTy}{M M' :  A ⊢c B}
      {Aᴰ : Vᴰ .ob[_] A}{Bᴰ : Cᴰ .ob[_] B} 
      (e : M ↦ M')
      (Mᴰ : Nodeᴰ[ M ][ Aᴰ , Bᴰ ])
      (M'ᴰ : Nodeᴰ[ M' ][ Aᴰ , Bᴰ ]) → 
      isProp (Edgeᴰ[ e ][ Mᴰ , M'ᴰ ]))-} where

    open UTySyntaxᴰ hasUTyᴰ
 

    open WkRepresentation
    open WkRepresentationᴰ

    mutual 
      vty : (A : VTy) → ob[ Vᴰ ] A 
      vty 𝟙 = 𝟙ᴰ
      vty Ans = Ansᴰ
      vty (U B) = hasUTyᴰ (cty B) .repᴰ

      cty : (B : CTy) → ob[ Cᴰ ] B 
      cty (F A) = hasFTyᴰ (vty A) .repᴰ

    module _  
      (𝟙elem : ∀{A} → Vᴰ .Hom[_][_,_] tt (vty A) 𝟙ᴰ )
      (yesᴰ : ∀{A} → Hom[ Vᴰ ][ yes , vty A ] (vty Ans))
      (noᴰ : ∀{A} → Hom[ Vᴰ ][ no , vty A ] (vty Ans)) where 

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

        vtm tt = 𝟙elem
        vtm yes = yesᴰ
        vtm no = noᴰ
        vtm (thunk M) = thunkᴰ (ctm M)

        -- for goal readability
        ctm-subC : {A A' : VTy}{B : CTy} → (V : A' ⊢v A)(M : A ⊢c B) → Oᴰ'[ subC V M ][ vty A' , cty B ] 
        ctm-subC {A}{A'}{B} V M = Oᴰ .Bif-homLᴰ (vtm V) (cty B) .fst M (ctm M)

        ctm-plug : {A : VTy}{B B' : CTy} → (S : B ⊢k B')(M : A ⊢c B) → Oᴰ'[ plug S M ][ vty A , cty B' ] 
        ctm-plug {A}{B}{B'} S M = Oᴰ .Bif-homRᴰ (ktm S)(vty A) .fst M (ctm M)

        ctm : {A : VTy}{B : CTy} → (M : A ⊢c B) → Nodeᴰ[ M ][ vty A , cty B ]
        ctm (subC V M) = ctm-subC V M 
        ctm (plug S M) = ctm-plug S M
        ctm (plugId {A}{B}{M} i) = Oᴰ .Bif-R-idᴰ i .fst M (ctm M)
        ctm (subCId {A}{B}{M} i) = Oᴰ .Bif-L-idᴰ i .fst M (ctm M)
        ctm (plugDist {A}{B}{B'}{B''}{S}{S'}{M} i) = 
          Oᴰ .Bif-R-seqᴰ (ktm S) (ktm S') (~ i) .fst M (ctm M)
        ctm (subDist {A}{A'}{A''}{B} {V}{V'}{M} i) = 
          Oᴰ .Bif-L-seqᴰ (vtm V') (vtm V) (~ i) .fst M (ctm M)
        ctm (plugSub {A}{A'}{B}{B'}{V}{M}{S} i) = 
          Oᴰ .SepBif-RL-commuteᴰ (vtm V) (ktm S) i .fst M (ctm M)
        ctm (isSet⊢c {A}{B} M M₁ x y i i₁) = 
          isOfHLevel→isOfHLevelDep 2 {Node[ A , B ]} {λ M → Nodeᴰ[ M ][ (vty A) , (cty B) ]}
          (λ M → Oᴰ .Bif-obᴰ {A}{B} (vty A)(cty B) .fst M .snd) 
          (ctm M) (ctm M₁) (cong ctm x) (cong ctm y) (isSet⊢c M M₁ x y) i i₁
  
        ctm (ret {A}) = {!   !} where 
          -- subst (λ h → Nodeᴰ[ h ][ vty A , hasFTyᴰ (vty A) .repᴰ ] ) plugId have where 
          have : Nodeᴰ[ plug hole ret ][ vty A , hasFTyᴰ (vty A) .repᴰ ] 
          have = hasFTyᴰ (vty A) .fwdᴰ .N-obᴰ (cty (F A)) (C .id) (Cᴰ .idᴰ) 

        ctm (force V) = forceᴰ (vtm V)
        ctm (force-sub {A}{A'}{B}{V}{W} i) = 
          hasUTyᴰ (cty B) .fwdᴰ .N-homᴰ (vtm V) i W (vtm W)
          
          -- subst (λ h → Nodeᴰ[ h ][ hasUTyᴰ (cty B) .repᴰ , cty B ] ) subCId have where 
          
          -- have : Nodeᴰ[ subC var force ][ Uᴰ (cty B) , cty B ] 
          -- have = forceᴰ (Vᴰ .idᴰ)

        open import HyperDoc.Operational.Graph
        ctmRel : {A : VTy}{B : CTy}{M M' : A ⊢c B}
          (M↦M' : M ↦ M') → Edgeᴰ[ M↦M' ][ ctm M , ctm M' ]
        ctmRel (Fβ {A}{B}{M}) = {!   !}
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
          Oᴰ .Bif-homLᴰ (vtm V) (cty B) .snd (ctm M) (ctm M') (ctmRel M↦M') 
        ctmRel (plug-cong {A}{B}{B'}{S}{M}{M'} M↦M') = 
          Oᴰ .Bif-homRᴰ (ktm S) (vty A) .snd (ctm M) (ctm M') (ctmRel M↦M')
        ctmRel (subC-cong-id {A}{B}{M}{M'}{M↦M'} i) = 
          Oᴰ .Bif-L-idᴰ i .snd (ctm M) (ctm M') (ctmRel M↦M')
        ctmRel (subC-cong-seq {A}{A'}{A''}{B}{V}{V'}{M}{M'}{M↦M'} i) = 
          Oᴰ .Bif-L-seqᴰ (vtm V') (vtm V) i .snd  (ctm M) (ctm M') (ctmRel M↦M')
        ctmRel (plug-cong-id {A}{B}{M}{M'}{M↦M'} i) = 
          Oᴰ .Bif-R-idᴰ i .snd (ctm M) (ctm M') (ctmRel M↦M')
        ctmRel (plug-cong-seq {A}{B}{B'}{B''}{S}{S'}{M}{M'}{M↦M'} i) = 
          Oᴰ .Bif-R-seqᴰ (ktm S) (ktm S') i .snd  (ctm M) (ctm M') (ctmRel M↦M')
        ctmRel (plug-subC-cong {A}{A'}{B}{B'}{V}{S}{M}{M'}{M↦M'} i) = 
          Oᴰ .SepBif-RL-commuteᴰ (vtm V) (ktm S) i .snd (ctm M) (ctm M') (ctmRel M↦M')
        ctmRel (isSet↦ {A}{B}{M}{M'} M↦M' M↦M'' x y i j) = 
          isOfHLevel→isOfHLevelDep 2 
            {Edge[ M , M' ]}{λ e → Edgeᴰ[ e ][ ctm M , ctm M' ]}
            (λ e → Oᴰ .Bif-obᴰ {A}{B} (vty A)(cty B) .snd e (ctm M) (ctm M') .snd) 
            (ctmRel M↦M') (ctmRel M↦M'') 
            (cong ctmRel x) (cong ctmRel y) 
            (isSet↦   M↦M' M↦M'' x y) i j

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

        SO : SectionNat {F = idModelMorphsim Syn}{Nᴰ = Synᴰ} SV SC
        SO .SectionNat.F-Node = ctm
        SO .SectionNat.F-Edge = ctmRel
        SO .SectionNat.F-Node-nat V S M = refl
        SO .SectionNat.F-Edge-nat V S M M' M↦M' = refl

        Elim : CBPVSection {F = idModelMorphsim Syn}{Synᴰ} 
        Elim .fst = SV
        Elim .snd .fst = SC
        Elim .snd .snd = SO
{-
module Elim 
  { ℓVᴰ ℓVᴰ' ℓCᴰ ℓCᴰ' ℓGᴰ ℓGᴰ' : Level}
  (Synᴰ : CBPVModelᴰ Syn ℓVᴰ ℓVᴰ' ℓCᴰ ℓCᴰ' ℓGᴰ ℓGᴰ' )
  where

  open CBPVModelᴰSyntax Synᴰ
  open CBPVModelSyntax Syn hiding (V ; C ; O)

  -- dumb displayed model 
  -- 

  -- needed assumptions
  -- TODO, specify as displayed type structures
  module _
    (𝟙ᴰ : ob[ Vᴰ ] 𝟙)
    (Ansᴰ : ob[ Vᴰ ] Ans)
    -- Q: if these were not forgetfull ..?
    (lifts : ForgetfulObliqueLifts)
    (oplifts : ForgetfulObliqueOpLifts)  where 

    mutual 
      vty : (A : VTy) → ob[ Vᴰ ] A 
      vty 𝟙 = 𝟙ᴰ
      vty Ans = Ansᴰ
      vty (U B) = lifts force (cty B) .fst 

      cty : (B : CTy) → ob[ Cᴰ ] B 
      cty (F A) = oplifts ret (vty A) .fst

    module _  
      (𝟙elem : ∀{A} → Vᴰ .Hom[_][_,_] tt (vty A) 𝟙ᴰ )
      (yesᴰ : ∀{A} → Hom[ Vᴰ ][ yes , vty A ] (vty Ans))
      (noᴰ : ∀{A} → Hom[ Vᴰ ][ no , vty A ] (vty Ans))
      {- Q: .. why do we have a map between displayed nodes.. 
          and an edge between them ..
         A: The map between displayed nodes is due to the fact that
         - We no longer have an equation Fβ : plug (bind M) ret ≡ M in the base 
           that we can use with subst.
            ex.
              subst (λ h →  Nodeᴰ[ h ][ P , Q ]) (sym Fβ) prf
            Is there a better way to capture this assumption in the model? 
        - We assumed edge  
            plug (bind M) ret ↦ M 
          in the base, and we need its displayed counterpart 
          to construct a total model
      -}
      (anti-F : 
        ∀ {A : VTy}{B : CTy}{M : A ⊢c B}
          {P : Vᴰ .ob[_] A}{Q : Cᴰ .ob[_] B} → 
            Nodeᴰ[ M ][ P , Q ] →
          --------------------------------- 
            Nodeᴰ[ plug (bind M) ret ][ P , Q ])
      (Fβ-fwd :
        ∀ {A : VTy}{B : CTy}{M : A ⊢c B}
        {P : Vᴰ .ob[_] A}{Q : Cᴰ .ob[_] B}
        (fᴰ : Nodeᴰ[ plug (bind M) ret ][ P , Q ])
        (gᴰ : Nodeᴰ[ M ][ P , Q ]) → 
        Edgeᴰ[ Fβ ][ fᴰ , gᴰ ])
      (anti-U : 
        ∀ {A : VTy}{B : CTy}{M : A ⊢c B}
           {P : Vᴰ .ob[_] A}{Q : Cᴰ .ob[_] B} →
            Nodeᴰ[ M ][ P , Q ] →
           --------------------------------- 
            Nodeᴰ[ subC (thunk M) force ][ P , Q ])
      (Uβ-fwd : 
        ∀{A : VTy}{B : CTy}{M : A ⊢c B}
        {P : Vᴰ .ob[_] A}{Q : Cᴰ .ob[_] B}
        (fᴰ : Nodeᴰ[ subC (thunk M) force ][ P , Q ])
        (gᴰ : Nodeᴰ[ M ][ P , Q ]) → 
        Edgeᴰ[ Uβ ][ fᴰ , gᴰ ])  where 

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

        vtm tt = 𝟙elem
        vtm yes = yesᴰ
        vtm no = noᴰ
        vtm (thunk {A}{B} M) = goal where 

          open CartesianLiftNotation Collageᴰ (lifts force (cty B))

          goal : Vᴰ [ thunk M ][ vty A , vty (U B) ] 
          goal = introᴰ {inl A}{vty A}{thunk M} (anti-U (ctm M))

        -- for goal readability
        ctm-subC : {A A' : VTy}{B : CTy} → (V : A' ⊢v A)(M : A ⊢c B) → Oᴰ'[ subC V M ][ vty A' , cty B ] 
        ctm-subC {A}{A'}{B} V M = Oᴰ .Bif-homLᴰ (vtm V) (cty B) .fst M (ctm M)

        ctm-plug : {A : VTy}{B B' : CTy} → (S : B ⊢k B')(M : A ⊢c B) → Oᴰ'[ plug S M ][ vty A , cty B' ] 
        ctm-plug {A}{B}{B'} S M = Oᴰ .Bif-homRᴰ (ktm S)(vty A) .fst M (ctm M)

        ctm : {A : VTy}{B : CTy} → (M : A ⊢c B) → Nodeᴰ[ M ][ vty A , cty B ]
        ctm (subC V M) = ctm-subC V M 
        ctm (plug S M) = ctm-plug S M
        ctm (plugId {A}{B}{M} i) = Oᴰ .Bif-R-idᴰ i .fst M (ctm M)
        ctm (subCId {A}{B}{M} i) = Oᴰ .Bif-L-idᴰ i .fst M (ctm M)
        ctm (plugDist {A}{B}{B'}{B''}{S}{S'}{M} i) = 
          Oᴰ .Bif-R-seqᴰ (ktm S) (ktm S') (~ i) .fst M (ctm M)
        ctm (subDist {A}{A'}{A''}{B} {V}{V'}{M} i) = 
          Oᴰ .Bif-L-seqᴰ (vtm V') (vtm V) (~ i) .fst M (ctm M)
        ctm (plugSub {A}{A'}{B}{B'}{V}{M}{S} i) = 
          Oᴰ .SepBif-RL-commuteᴰ (vtm V) (ktm S) i .fst M (ctm M)
        ctm (isSet⊢c {A}{B} M M₁ x y i i₁) = 
          isOfHLevel→isOfHLevelDep 2 {Node[ A , B ]} {λ M → Nodeᴰ[ M ][ (vty A) , (cty B) ]}
          (λ M → Oᴰ .Bif-obᴰ {A}{B} (vty A)(cty B) .fst M .snd) 
          (ctm M) (ctm M₁) (cong ctm x) (cong ctm y) (isSet⊢c M M₁ x y) i i₁
  
        ctm (ret {A}) = goal where 
          open CartesianLiftNotation (Collageᴰ ^opᴰ) (oplifts ret (vty A))

          have : Nodeᴰ[ plug hole ret ][ vty A , oplifts ret (vty A) .fst  ]
          have = πⱽ
          -- Q: .. is subst really the right thing to do here..
          -- or are we missing something fundamental ..?
          goal : Nodeᴰ[ ret ][ vty A , oplifts ret (vty A) .fst ]
          goal = subst (λ h → Nodeᴰ[ h ][ vty A , oplifts ret (vty A) .fst ]) plugId have

        ctm (force {B}) = goal where 
          open CartesianLiftNotation Collageᴰ (lifts force (cty B))

          have : Oᴰ'[ subC var force ][ lifts force (cty B) .fst , cty B ]
          have = πⱽ
          
          goal : Oᴰ'[ force ][ lifts force (cty B) .fst , cty B ]
          goal = subst (λ h → Oᴰ'[ h ][ lifts force (cty B) .fst , cty B ]) subCId have
  
        -- ah... 
        ctmRel : {A : VTy}{B : CTy}{M M' : A ⊢c B}
          (M↦M' : M ↦ M') → Edgeᴰ[ M↦M' ][ ctm M , ctm M' ]

        ctmRel (Fβ {A}{B}{M}) = goal where 
          goal : Fβ ◂ ctm-plug (bind M) ret ↦Oᴰ ctm M
          goal = Fβ-fwd (ctm-plug (bind M) ret) (ctm M)
        ctmRel (Uβ {A}{B}{M}) = goal where 
          goal : Uβ ◂ ctm-subC (thunk M) force ↦Oᴰ ctm M
          goal = Uβ-fwd (ctm-subC (thunk M) force) (ctm M)
        ctmRel (subC-cong {A}{A'}{B}{V}{M}{M'} M↦M') = 
          Oᴰ .Bif-homLᴰ (vtm V) (cty B) .snd (ctm M) (ctm M') (ctmRel M↦M') 
        ctmRel (plug-cong {A}{B}{B'}{S}{M}{M'} M↦M') = 
          Oᴰ .Bif-homRᴰ (ktm S) (vty A) .snd (ctm M) (ctm M') (ctmRel M↦M')
        ctmRel (subC-cong-id {A}{B}{M}{M'}{M↦M'} i) = 
          Oᴰ .Bif-L-idᴰ i .snd (ctm M) (ctm M') (ctmRel M↦M')
        ctmRel (subC-cong-seq {A}{A'}{A''}{B}{V}{V'}{M}{M'}{M↦M'} i) = 
          Oᴰ .Bif-L-seqᴰ (vtm V') (vtm V) i .snd  (ctm M) (ctm M') (ctmRel M↦M')
        ctmRel (plug-cong-id {A}{B}{M}{M'}{M↦M'} i) = 
          Oᴰ .Bif-R-idᴰ i .snd (ctm M) (ctm M') (ctmRel M↦M')
        ctmRel (plug-cong-seq {A}{B}{B'}{B''}{S}{S'}{M}{M'}{M↦M'} i) = 
          Oᴰ .Bif-R-seqᴰ (ktm S) (ktm S') i .snd  (ctm M) (ctm M') (ctmRel M↦M')
        ctmRel (plug-subC-cong {A}{A'}{B}{B'}{V}{S}{M}{M'}{M↦M'} i) = 
          Oᴰ .SepBif-RL-commuteᴰ (vtm V) (ktm S) i .snd (ctm M) (ctm M') (ctmRel M↦M')
        ctmRel (isSet↦ {A}{B}{M}{M'} M↦M' M↦M'' x y i j) = 
          isOfHLevel→isOfHLevelDep 2 
            {Edge[ M , M' ]}{λ e → Edgeᴰ[ e ][ ctm M , ctm M' ]}
            (λ e → Oᴰ .Bif-obᴰ {A}{B} (vty A)(cty B) .snd e (ctm M) (ctm M') .snd) 
            (ctmRel M↦M') (ctmRel M↦M'') 
            (cong ctmRel x) (cong ctmRel y) 
            (isSet↦   M↦M' M↦M'' x y) i j

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
        ktm (bind {A}{B} M) = goal where 
          -- don't 
          open CartesianLiftNotation (Collageᴰ ^opᴰ) (oplifts ret (vty A))

          goal : Hom[ Cᴰ ][ bind M , oplifts ret (vty A) .fst ] (cty B)
          goal = introᴰ {inr B}{cty B}{bind M}(anti-F (ctm M))

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

        SO : SectionNat {F = idModelMorphsim Syn}{Nᴰ = Synᴰ} SV SC
        SO .SectionNat.F-Node = ctm
        SO .SectionNat.F-Edge = ctmRel
        SO .SectionNat.F-Node-nat V S M = refl
        SO .SectionNat.F-Edge-nat V S M M' M↦M' = refl

        Elim : CBPVSection {F = idModelMorphsim Syn}{Synᴰ} 
        Elim .fst = SV
        Elim .snd .fst = SC
        Elim .snd .snd = SO
-}



{-}

module ElimLogic 
  { ℓVᴰ ℓVᴰ' ℓCᴰ ℓCᴰ' ℓGᴰ ℓGᴰ' : Level}
  (L : CBPVLogic Syn _ ) where

  open CBPVLogicSyntax L
  open import HyperDoc.Syntax

  Synᴰ : CBPVModelᴰ Syn _ _ _ _ _ _ 
  Synᴰ = ConvertLogic.Mᴰ L

  open CBPVModelᴰSyntax Synᴰ
  open CBPVModelSyntax Syn hiding (V ; C ; O)

  open import Cubical.Relation.Binary.Preorder
  open IsPreorder 

  -- needed assumptions 
  module _
    (𝟙ᴰ : ob[ Vᴰ ] 𝟙) where 

    mutual 
      vty : (A : VTy) → ob[ Vᴰ ] A 
      vty 𝟙 = 𝟙ᴰ
      vty Ans = {!   !}
      vty (U B) = pull force $ cty B

      cty : (B : CTy) → ob[ Cᴰ ] B 
      cty (F A) = {!   !}

    module _  
      (𝟙elem : ∀{A} → Vᴰ .Hom[_][_,_] tt (vty A) 𝟙ᴰ )
      (Fβ-fwd :
        ∀ {A A' : VTy}{B : CTy}{V : A' ⊢v A}{M : A ⊢c B}
        {P' : Vᴰ .ob[_] A'}{Q : Cᴰ .ob[_] B}
        (fᴰ : Oᴰ'[ plug (bind M) (ret V) ][ P' , Q ])
        (gᴰ : Oᴰ'[ subC V M ][ P' , Q ]) → 
        Fβ ◂ fᴰ ↦Oᴰ gᴰ )
      (Uβ-fwd : 
        ∀{A : VTy}{B : CTy}{M : A ⊢c B}
        {P : Vᴰ .ob[_] A}{Q : Cᴰ .ob[_] B}
        (fᴰ : Oᴰ'[ subC (thunk M) force ][ P , Q ])
        (gᴰ : Oᴰ'[ M ][ P , Q ]) → 
        Uβ ◂ fᴰ ↦Oᴰ gᴰ)
      (Uβ-bkwd : 
        ∀{A : VTy}{B : CTy}{M : A ⊢c B}
        {P : Vᴰ .ob[_] A}{Q : Cᴰ .ob[_] B}
        (fᴰ : Oᴰ'[ M ][ P , Q ])
        (gᴰ : Oᴰ'[ subC (thunk M) force ][ P , Q ]) → 
        {!   !} ◂ fᴰ ↦Oᴰ gᴰ)
      where 

      mutual 
        vtm : {A A' : VTy} → (f : Hom[ V , A ] A') → Hom[ Vᴰ ][ f  , vty A ] (vty A')
        vtm (subV V₁ V₂) = (Vᴰ ⋆ᴰ vtm V₁) (vtm V₂)
        vtm var = idᴰ Vᴰ
        vtm (subVIdl V i) = Vᴰ .⋆IdLᴰ (vtm V) i
        vtm (subVIdr V i) = Vᴰ .⋆IdRᴰ (vtm V) i
        vtm (subVAssoc V₁ V₂ V₃ i) = Vᴰ .⋆Assocᴰ (vtm V₁) (vtm V₂) (vtm V₃) i
        vtm (isSet⊢v V₁ V₂ x y i i₁) = {!   !}
        vtm tt = 𝟙elem
        vtm yes = {!   !}
        vtm no = {!   !}
        vtm (thunk {A}{B} M) = goal where

          sub : A LV.◂ pull M $ cty B ≤ (pull (subC (thunk M) force) $ cty B) 
          sub = {!   !}
          
          goal : Hom[ Vᴰ ][ thunk M , vty A ] (pull force $ cty B) 
          goal = LV.seq (ctm M) (LV.seq sub VM*→V*M*) 

        -- for readability
        ctm-subC : {A A' : VTy}{B : CTy} → (V : A' ⊢v A)(M : A ⊢c B) → Oᴰ'[ subC V M ][ vty A' , cty B ] 
        ctm-subC {A}{A'}{B} V M = Oᴰ .Bif-homLᴰ (vtm V) (cty B) .fst M (ctm M)

        ctm-plug : {A : VTy}{B B' : CTy} → (S : B ⊢k B')(M : A ⊢c B) → Oᴰ'[ plug S M ][ vty A , cty B' ] 
        ctm-plug {A}{B}{B'} S M = Oᴰ .Bif-homRᴰ (ktm S)(vty A) .fst M (ctm M)

        ctm : {A : VTy}{B : CTy} → (M : A ⊢c B) → Nodeᴰ[ M ][ vty A , cty B ]
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

        -- again with the termination issues.. 
        ctm (plugDist {A}{B}{B'}{B''}{S}{S'}{M} i) = {!   !}
          {- isProp→PathP 
            (λ i → LV.isProp≤{q = (pull (plugDist i) $ cty B'')})
            (ctm-plug S' (plug S M))
            (ctm-plug (kcomp S S') M)
            i -}

        ctm (subDist i) = {!   !}
        ctm (plugSub i) = {!   !}
        ctm (isSet⊢c M M₁ x y i i₁) = {!   !}
        ctm (ret V) = {!   !}
        ctm (force) = LV.id⊢

        -- forward reduction ?
        ctmRel : {A : VTy}{B : CTy}{M M' : A ⊢c B}
          (M↦M' : M ↦ M') → Edgeᴰ[ M↦M' ][ ctm M , ctm M' ]

        ctmRel (Fβ {A}{A'}{B}{V}{M}) = goal where 
          goal : Fβ ◂ ctm-plug (bind M) (ret V) ↦Oᴰ ctm-subC V M 
          goal = Fβ-fwd (ctm-plug (bind M) (ret V)) (ctm-subC V M)
        ctmRel (Uβ {A}{B}{M}) = goal where 
          goal : Uβ ◂ ctm-subC (thunk M) force ↦Oᴰ ctm M
          goal = Uβ-fwd (ctm-subC (thunk M) force) (ctm M)
        ctmRel (subC-cong {A}{A'}{B}{V}{M}{M'} M↦M') = 
          Oᴰ .Bif-homLᴰ (vtm V) (cty B) .snd (ctm M) (ctm M') (ctmRel M↦M') 
        ctmRel (plug-cong {A}{B}{B'}{S}{M}{M'} M↦M') = 
          Oᴰ .Bif-homRᴰ (ktm S) (vty A) .snd (ctm M) (ctm M') (ctmRel M↦M')
        ctmRel (isProp↦ M↦M' M↦M'' i) = {!   !}


        ktm : {B B' : CTy} → (f : Hom[ C , B ] B') → Hom[ Cᴰ ][ f  , cty B ] (cty B')
        ktm (kcomp S S₁) = (Cᴰ ⋆ᴰ ktm S) (ktm S₁)
        ktm hole = idᴰ Cᴰ
        ktm (kcompIdl S i) = Cᴰ .⋆IdLᴰ (ktm S) i
        ktm (kcompIdr S i) = Cᴰ .⋆IdRᴰ (ktm S) i
        ktm (kcompAssoc S S₁ S₂ i) = Cᴰ .⋆Assocᴰ (ktm S) (ktm S₁) (ktm S₂)  i
        ktm (isSet⊢k S S₁ x y i i₁) = {!   !}
        ktm (bind x) = {!   !}

        SV : Section Id Vᴰ 
        SV .Section.F-obᴰ = vty
        SV .Section.F-homᴰ = vtm
        SV .Section.F-idᴰ = LV.isProp≤  _ _
        SV .Section.F-seqᴰ _ _ = LV.isProp≤  _ _ 

        SC : Section Id Cᴰ 
        SC .Section.F-obᴰ = cty
        SC .Section.F-homᴰ = ktm
        SC .Section.F-idᴰ = LC.isProp≤  _ _
        SC .Section.F-seqᴰ _ _ = LC.isProp≤  _ _ 

        SO : SectionNat {F = idModelMorphsim Syn}{Nᴰ = Synᴰ} SV SC
        SO .SectionNat.F-Node = ctm
        SO .SectionNat.F-Edge = ctmRel
        SO .SectionNat.F-Node-nat = {!   !}
        SO .SectionNat.F-Edge-nat = {!   !}
        {-}.SectionNat.N-obᴰ = ctm
        SO .SectionNat.N-obᴰRel {A}{B}{M}{M'}{M↦M'} = ctmRel M↦M'
        SO .SectionNat.N-homᴰ {A}{A'} V S M = LV.isProp≤  _ _ -}

        Elim : CBPVSection {F = idModelMorphsim Syn}{Synᴰ} 
        Elim .fst = SV
        Elim .snd .fst = SC
        Elim .snd .snd = SO


-}
{-


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



-}