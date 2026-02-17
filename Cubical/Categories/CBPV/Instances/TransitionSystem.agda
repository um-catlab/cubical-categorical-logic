{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.CBPV.Instances.TransitionSystem where 

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma 

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.CBPV.Base
open import Cubical.Categories.Enriched.Functors.Base
open import Cubical.Categories.Enriched.Instances.FromCat
open import Cubical.Categories.Enriched.Instances.Presheaf.Self
open import Cubical.Categories.Instances.Sets 
open import Cubical.Categories.Instances.TransitionSystem
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Monoidal.Instances.Presheaf 
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Instances.Sets 
  renaming(SET to SETScwf)

open Category
open Functor
open EnrichedFunctor
open EnrichedCategory
open MonoidalCategory
open NatTrans
open TSystem
open TSystem[_,_]

module _ (ℓ : Level) where 

  set = (SET ℓ)
  V = PshMon.𝓟Mon set ℓ
  E : EnrichedCategory V (ℓ-suc ℓ) 
  E = Cat→Enriched TSysCat
  V[_,_] = V .Hom[_,_]
  E[_,_] = E .Hom[_,_]
  selfSet = self set ℓ
  self[_,_] = selfSet .Hom[_,_]

  computations : ob E → ob selfSet
  computations S .F-ob Γ = 
    (⟨ Γ ⟩ → Lift ⟨ state S ⟩) , 
    isSet→ (isOfHLevelLift 2 (state S .snd))
  computations S .F-hom γ m = m ∘S γ
  computations S .F-id = refl
  computations S .F-seq _ _ = refl

  stackhom : (X Y : ob E) → 
    V[ E[ X , Y ] , self[ computations X , computations Y ] ]
  stackhom X Y = adjL _ _ (
    natTrans 
      (λ Γ (lift tsys , s) Γ∙ → lift (tsys Γ∙ .s-map (s Γ∙ .lower)) )
      λ f → funExt λ _ → funExt λ _ → refl)

  cTm : EnrichedFunctor V E selfSet
  cTm .F-ob = computations
  cTm .F-hom {X}{Y} = stackhom X Y
  cTm .F-id = 
    helper _ _ (
      makeNatTransPath (funExt λ Γ → funExt λ (tt* , s) → funExt λ Γ∙ → refl))
    --makeNatTransPath (funExt λ Γ → funExt λ tt → makePshHomPath refl)
  cTm .F-seq = 
    helper _ _ (
      makeNatTransPath (funExt λ Γ → funExt λ ((lift tsys , lift tsys'), s) → 
        funExt λ Γ∙ → refl)
    )
   -- makeNatTransPath (funExt λ Γ → funExt λ (k , k') → makePshHomPath refl)

  TSystemModel : CBPVModel _ _ _ _ _ _
  TSystemModel .fst = SETScwf ℓ
  TSystemModel .snd .fst = E
  TSystemModel .snd .snd = cTm

