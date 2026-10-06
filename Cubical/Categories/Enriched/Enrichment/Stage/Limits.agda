{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Enriched.Enrichment.Base

module Cubical.Categories.Enriched.Enrichment.Stage.Limits
  {ℓ ℓ' ℓS : Level} {A : Category ℓ ℓ'}
  {ℓC ℓC' : Level} {C : Category ℓC ℓC'} (ℰ : Enrichment C (PshMon.𝓟Mon A ℓS)) where

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.Representable
import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Limits.AsRepresentable
open import Cubical.Categories.Enriched.Enrichment.HomFunctor
open import Cubical.Categories.Enriched.Enrichment.Limits.Conical
open import Cubical.Categories.Enriched.Enrichment.Limits.Power
open import Cubical.Categories.Enriched.Enrichment.Stage ℰ
open import Cubical.Categories.Enriched.Enrichment.Stage.Yoneda A ℓS

open Functor
open NatTrans
open PshHomStrict
open UniversalElement
open PshMon A ℓS using (𝓟 ; 𝓟Mon)

private
  module A = Category A
  module C = Category C
  module ℰ = Enrichment ℰ
  module S (c : A.ob) = Category (Stage c)

module _ {ℓJ ℓJ' : Level} {J : Category ℓJ ℓJ'} {D : Functor J C} (lm : EnrichedLimit ℰ D) where
  private
    L = lm .fst .vertex
    π = lm .fst .element

  stageCone : ∀ c → NatTrans (ΔCone ⟅ L ⟆) (at c ∘F D)
  stageCone c .N-ob j = at c ⟪ π ⟦ j ⟧ ⟫
  stageCone c .N-hom k =
    S.⋆IdL c _ ∙ cong (at c ⟪_⟫) (sym (C.⋆IdL _) ∙ π .N-hom k) ∙ at c .F-seq _ _

  private
    module _ (c : A.ob) (Y : C.ob) where
      conesIso : Iso (NatTrans (ΔCone ⟅ ŷ c ⟆) (Hom[_,-] ℰ Y ∘F D))
                     (NatTrans (ΔCone ⟅ Y ⟆) (at c ∘F D))
      conesIso .Iso.fun t .N-ob j = (t ⟦ j ⟧) .N-ob c (lift A.id)
      conesIso .Iso.fun t .N-hom k =
        S.⋆IdL c _ ∙ (λ i → t .N-hom k i .N-ob c (lift A.id))
      conesIso .Iso.inv x .N-ob j = yoneda c ℰ.VE[ Y , D ⟅ j ⟆ ] .Iso.inv (x ⟦ j ⟧)
      conesIso .Iso.inv x .N-hom k = makePshHomStrictPath (funExt λ d → funExt λ (lift g) →
        cong (res g ⟪_⟫) (sym (S.⋆IdL c _) ∙ x .N-hom k)
        ∙ res g .F-seq _ _
        ∙ cong (λ m → res g ⟪ x ⟦ _ ⟧ ⟫ ⋆⟨ Stage d ⟩ m) (at-res _ g))
      conesIso .Iso.sec x = makeNatTransPath (funExt λ j → yoneda c ℰ.VE[ Y , D ⟅ j ⟆ ] .Iso.sec (x ⟦ j ⟧))
      conesIso .Iso.ret t = makeNatTransPath (funExt λ j → yoneda c ℰ.VE[ Y , D ⟅ j ⟆ ] .Iso.ret (t ⟦ j ⟧))

  stageLimit : ∀ c → limit {C = Stage c} (at c ∘F D)
  stageLimit c .vertex = L
  stageLimit c .element = stageCone c
  stageLimit c .universal Y = isoToIsEquiv (iso _ inv
    (λ x → agree (inv x) ∙ composite .Iso.sec x)
    (λ α → cong inv (agree α) ∙ composite .Iso.ret α))
    where
    composite : Iso (Stage c [ Y , L ]) (NatTrans (ΔCone ⟅ Y ⟆) (at c ∘F D))
    composite = compIso (compIso (invIso (yoneda c ℰ.VE[ Y , L ]))
                                 (equivToIso (_ , lm .snd Y (ŷ c))))
                        (conesIso c Y)

    inv : NatTrans (ΔCone ⟅ Y ⟆) (at c ∘F D) → Stage c [ Y , L ]
    inv = composite .Iso.inv

    agree : ∀ α → (ΔCone {C = Stage c} {J = J} ⟪ α ⟫ ⋆⟨ FUNCTOR J (Stage c) ⟩ stageCone c)
      ≡ composite .Iso.fun α
    agree α = makeNatTransPath (funExt λ j →
      sym (cong (λ m → m ⋆⟨ Stage c ⟩ at c ⟪ π ⟦ j ⟧ ⟫) (res-id α)))

module _ {z : A.ob} {X : C.ob} (pw : EnrichedPower ℰ (ŷ z) X) where
  private
    P = pw .fst .vertex
    module 𝓟Mon = Cubical.Categories.Monoidal.Base.MonoidalCategory 𝓟Mon

  powEvₛ : Stage z [ P , X ]
  powEvₛ = yoneda z ℰ.VE[ P , X ] .Iso.fun (pw .fst .element)

  module _ (c : A.ob) (Y : C.ob) where
    stagePower : Iso (Stage c [ Y , P ]) (𝓟 [ ŷ c 𝓟Mon.⊗ ŷ z , ℰ.VE[ Y , X ] ])
    stagePower = compIso (invIso (yoneda c ℰ.VE[ Y , P ])) (equivToIso (_ , pw .snd Y (ŷ c)))

    stagePower-β : ∀ (α : Stage c [ Y , P ]) w g h
      → stagePower .Iso.fun α .N-ob w (lift g , lift h) ≡ res g ⟪ α ⟫ ⋆⟨ Stage w ⟩ res h ⟪ powEvₛ ⟫
    stagePower-β α w g h = cong (λ m → res g ⟪ α ⟫ ⋆⟨ Stage w ⟩ m)
      (sym (pw .fst .element .N-hom w z h (lift A.id) (lift h) (cong lift (A.⋆IdR h))))
