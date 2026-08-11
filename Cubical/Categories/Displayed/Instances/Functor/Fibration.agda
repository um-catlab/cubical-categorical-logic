{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Functor.Fibration where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.NaturalTransformation
import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base as EqPsh

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

record EqFibrationData
  {D : Category ℓD ℓD'} (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ')
  : Type (ℓ-max (ℓ-max ℓD ℓD') (ℓ-max ℓDᴰ ℓDᴰ')) where
  no-eta-equality
  field
    Eq-idL : EqPsh.EqIdL D
    Eq-idR : EqPsh.EqIdR D
    Eq-assoc : EqPsh.ReprEqAssoc D
    Eq-fibration : EqPsh.Fibration Dᴰ Eq-assoc

open EqFibrationData public

module _ (D : Category ℓD ℓD') where
  private
    module D = Category D

  pathEqIdL : EqPsh.EqIdL D
  pathEqIdL f = Eq.pathToEq (D.⋆IdL f)

  pathEqIdR : EqPsh.EqIdR D
  pathEqIdR f = Eq.pathToEq (D.⋆IdR f)

  pathReprEqAssoc : EqPsh.ReprEqAssoc D
  pathReprEqAssoc x f g h f⋆g f⋆g≡ =
    Eq.pathToEq
      (sym (D.⋆Assoc f g h)
      ∙ cong (D._⋆ h) (Eq.eqToPath f⋆g≡))

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ')
  (eqFib : EqFibrationData Dᴰ) where

  private
    module C = Category C
    module D = Category D
    module Cᴰ = Fibers Cᴰ
    module Dᴰ = Fibers Dᴰ
    D-idL = eqFib .Eq-idL
    D-idR = eqFib .Eq-idR
    D-assoc = eqFib .Eq-assoc
    D-fibration = eqFib .Eq-fibration
    module fib = EqPsh.FibrationNotation Dᴰ D-assoc D-fibration
    FUNCTOR-idL = pathEqIdL (FUNCTOR C D)
    FUNCTOR-idR = pathEqIdR (FUNCTOR C D)
    FUNCTOR-assoc = pathReprEqAssoc (FUNCTOR C D)

  module Construction {F G : Functor C D} (α : NatTrans F G)
    (Gᴰ : Functorᴰ G Cᴰ Dᴰ) where

    private
      module FD = Fibers (FUNCTORᴰ Cᴰ Dᴰ)

      π-idL : {x : C.ob} → Eq._≡_
        (D.id D.⋆ α .NatTrans.N-ob x) (α .NatTrans.N-ob x)
      π-idL = D-idL _

      α-nat : {x y : C.ob} (f : C [ x , y ]) → Eq._≡_
        (α .NatTrans.N-ob x D.⋆ G .Functor.F-hom f)
        (F .Functor.F-hom f D.⋆ α .NatTrans.N-ob y)
      α-nat f = Eq.sym (Eq.pathToEq (α .NatTrans.N-hom f))

      outer-tri : {H : Functor C D} (β : NatTrans H F) → Eq._≡_
        (seqTrans β (seqTrans (idTrans F) α)) (seqTrans β α)
      outer-tri β =
        FUNCTOR-assoc G β (idTrans F) α β (FUNCTOR-idR β)

      π : {x : C.ob} (xᴰ : Cᴰ.ob[ x ]) →
        Dᴰ.Hom[ α .NatTrans.N-ob x ][
            α .NatTrans.N-ob x fib.* Gᴰ .Functorᴰ.F-obᴰ xᴰ
          , Gᴰ .Functorᴰ.F-obᴰ xᴰ ]
      π xᴰ = Dᴰ.reindEq π-idL fib.πⱽ

      square : {x y : C.ob} {f : C [ x , y ]}
        {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
        (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ]) →
        Dᴰ.Hom[ F .Functor.F-hom f D.⋆ α .NatTrans.N-ob y ][
            α .NatTrans.N-ob x fib.* Gᴰ .Functorᴰ.F-obᴰ xᴰ
          , Gᴰ .Functorᴰ.F-obᴰ yᴰ ]
      square {f = f} {xᴰ = xᴰ} fᴰ =
        Dᴰ.reindEq (α-nat f)
          (π xᴰ Dᴰ.⋆ᴰ Gᴰ .Functorᴰ.F-homᴰ fᴰ)

    pulled : Functorᴰ F Cᴰ Dᴰ
    pulled .Functorᴰ.F-obᴰ xᴰ =
      α .NatTrans.N-ob _ fib.* Gᴰ .Functorᴰ.F-obᴰ xᴰ
    pulled .Functorᴰ.F-homᴰ fᴰ = fib.introᴰ (square fᴰ)
    pulled .Functorᴰ.F-idᴰ {x = x} {xᴰ = xᴰ} = Dᴰ.rectifyOut $
      fib.extensionalityᴰ (F .Functor.F-id)
        (fib.βᴰ {gfᴰ = square Cᴰ.idᴰ}
        ∙ Dᴰ.reindEq-filler⁻ (α-nat C.id)
        ∙ Dᴰ.⟨ refl ⟩⋆⟨ Dᴰ.≡in (Gᴰ .Functorᴰ.F-idᴰ) ⟩
        ∙ Dᴰ.⋆IdR _
        ∙ Dᴰ.reindEq-filler⁻ (π-idL {x = x})
        ∙ sym (Dᴰ.⋆IdL _))
    pulled .Functorᴰ.F-seqᴰ
      {x = x} {y = y} {z = z} {f = f} {g = g}
      {xᴰ = xᴰ} {yᴰ = yᴰ} {zᴰ = zᴰ} fᴰ gᴰ =
      Dᴰ.rectifyOut $ fib.extensionalityᴰ (F .Functor.F-seq f g)
        (fib.βᴰ {gfᴰ = square (fᴰ Cᴰ.⋆ᴰ gᴰ)}
        ∙ Dᴰ.reindEq-filler⁻ (α-nat (f C.⋆ g))
        ∙ Dᴰ.⟨ refl ⟩⋆⟨ Dᴰ.≡in (Gᴰ .Functorᴰ.F-seqᴰ fᴰ gᴰ) ⟩
        ∙ sym (Dᴰ.⋆Assoc _ _ _)
        ∙ Dᴰ.⟨ Dᴰ.reindEq-filler (α-nat f) ⟩⋆⟨ refl ⟩
        ∙ Dᴰ.⟨ sym (fib.βᴰ {gfᴰ = square fᴰ}) ⟩⋆⟨ refl ⟩
        ∙ Dᴰ.⋆Assoc _ _ _
        ∙ Dᴰ.⟨ refl ⟩⋆⟨
            Dᴰ.⟨ Dᴰ.reindEq-filler (π-idL {x = y}) ⟩⋆⟨ refl ⟩ ⟩
        ∙ Dᴰ.⟨ refl ⟩⋆⟨ Dᴰ.reindEq-filler (α-nat g) ⟩
        ∙ Dᴰ.⟨ refl ⟩⋆⟨ sym (fib.βᴰ {gfᴰ = square gᴰ}) ⟩
        ∙ sym (Dᴰ.⋆Assoc _ _ _))

    projection : NatTransᴰ α pulled Gᴰ
    projection .NatTransᴰ.N-obᴰ = π
    projection .NatTransᴰ.N-homᴰ
      {f = f} {yᴰ = yᴰ} fᴰ = Dᴰ.rectifyOut $
        Dᴰ.⟨ refl ⟩⋆⟨ Dᴰ.reindEq-filler⁻ π-idL ⟩
        ∙ fib.βᴰ {gfᴰ = square fᴰ}
        ∙ Dᴰ.reindEq-filler⁻ (α-nat f)

    rawProjection : NatTransᴰ (seqTrans (idTrans F) α) pulled Gᴰ
    rawProjection .NatTransᴰ.N-obᴰ xᴰ = fib.πⱽ
    rawProjection .NatTransᴰ.N-homᴰ {f = f} fᴰ = Dᴰ.rectifyOut $
      fib.βᴰ {gfᴰ = square fᴰ}
      ∙ Dᴰ.reindEq-filler⁻ (α-nat f)
      ∙ Dᴰ.⟨ Dᴰ.reindEq-filler⁻ π-idL ⟩⋆⟨ refl ⟩

    factor-ob : {H : Functor C D} {β : NatTrans H F}
      (Hᴰ : Functorᴰ H Cᴰ Dᴰ)
      (γᴰ : NatTransᴰ (seqTrans β α) Hᴰ Gᴰ)
      {x : C.ob} (xᴰ : Cᴰ.ob[ x ]) →
      Dᴰ.Hom[ β .NatTrans.N-ob x ][
          Hᴰ .Functorᴰ.F-obᴰ xᴰ , pulled .Functorᴰ.F-obᴰ xᴰ ]
    factor-ob Hᴰ γᴰ xᴰ = fib.introᴰ (γᴰ .NatTransᴰ.N-obᴰ xᴰ)

    factor : {H : Functor C D} {β : NatTrans H F}
      (Hᴰ : Functorᴰ H Cᴰ Dᴰ)
      (γᴰ : NatTransᴰ (seqTrans β α) Hᴰ Gᴰ) →
      NatTransᴰ β Hᴰ pulled
    factor Hᴰ γᴰ .NatTransᴰ.N-obᴰ = factor-ob Hᴰ γᴰ
    factor {β = β} Hᴰ γᴰ .NatTransᴰ.N-homᴰ
      {f = f} {xᴰ = xᴰ} {yᴰ = yᴰ} fᴰ = Dᴰ.rectifyOut $
        fib.extensionalityᴰ (β .NatTrans.N-hom f)
          (Dᴰ.⋆Assoc _ _ _
          ∙ Dᴰ.⟨ refl ⟩⋆⟨
              fib.βᴰ {gfᴰ = γᴰ .NatTransᴰ.N-obᴰ yᴰ} ⟩
          ∙ Dᴰ.≡in (γᴰ .NatTransᴰ.N-homᴰ fᴰ)
          ∙ sym
            (Dᴰ.⋆Assoc _ _ _
            ∙ Dᴰ.⟨ refl ⟩⋆⟨ fib.βᴰ {gfᴰ = square fᴰ} ⟩
            ∙ Dᴰ.⟨ refl ⟩⋆⟨ Dᴰ.reindEq-filler⁻ (α-nat f) ⟩
            ∙ Dᴰ.⟨ refl ⟩⋆⟨
                Dᴰ.⟨ Dᴰ.reindEq-filler⁻ π-idL ⟩⋆⟨ refl ⟩ ⟩
            ∙ sym (Dᴰ.⋆Assoc _ _ _)
            ∙ Dᴰ.⟨
                fib.βᴰ {gfᴰ = γᴰ .NatTransᴰ.N-obᴰ xᴰ} ⟩⋆⟨ refl ⟩))

    componentAt : {H : Functor C D} (Hᴰ : Functorᴰ H Cᴰ Dᴰ)
      {x : C.ob} (xᴰ : Cᴰ.ob[ x ]) →
      (Σ[ δ ∈ NatTrans H G ] NatTransᴰ δ Hᴰ Gᴰ) →
      Σ[ f ∈ D [ H .Functor.F-ob x , G .Functor.F-ob x ] ]
        Dᴰ.Hom[ f ][
            Hᴰ .Functorᴰ.F-obᴰ xᴰ
          , Gᴰ .Functorᴰ.F-obᴰ xᴰ ]
    componentAt Hᴰ xᴰ (δ , δᴰ) =
      δ .NatTrans.N-ob _ , δᴰ .NatTransᴰ.N-obᴰ xᴰ

    liftUE : EqPsh.CartesianLiftUE
      (FUNCTORᴰ Cᴰ Dᴰ) FUNCTOR-assoc FUNCTOR-idR α Gᴰ
    liftUE .EqPsh.UEⱽ.v = pulled
    liftUE .EqPsh.UEⱽ.e = rawProjection
    liftUE .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      (H , Hᴰ , β) .fst = factor Hᴰ
    liftUE .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      (H , Hᴰ , β) .snd .fst γᴰ =
        FD.rectifyOut $
          FD.reindEq-filler⁻ (outer-tri β)
          ∙ FD.≡in
            (makeNatTransPathᴰ Cᴰ Dᴰ
              (makeNatTransPath (funExt λ x →
                D.⟨ refl ⟩⋆⟨ Eq.eqToPath (π-idL {x = x}) ⟩))
              (implicitFunExt λ {x} → funExt λ xᴰ →
                Dᴰ.rectifyOut $
                  fib.βᴰ {gfᴰ = γᴰ .NatTransᴰ.N-obᴰ xᴰ}))
    liftUE .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      (H , Hᴰ , β) .snd .snd βᴰ =
        makeNatTransPathᴰ Cᴰ Dᴰ refl
          (implicitFunExt λ {x} → funExt λ xᴰ →
            Dᴰ.rectifyOut $ fib.extensionalityᴰ refl
              (fib.βᴰ
                {gfᴰ =
                  (FD.reindEq (outer-tri β)
                    (seqTransᴰ βᴰ rawProjection))
                  .NatTransᴰ.N-obᴰ xᴰ}
              ∙ cong
                (componentAt Hᴰ xᴰ)
                (FD.reindEq-filler⁻
                  {p = seqTransᴰ βᴰ rawProjection}
                  (outer-tri β))))

  FUNCTORᴰ-FibrationEq : EqFibrationData (FUNCTORᴰ Cᴰ Dᴰ)
  FUNCTORᴰ-FibrationEq .Eq-idL = FUNCTOR-idL
  FUNCTORᴰ-FibrationEq .Eq-idR = FUNCTOR-idR
  FUNCTORᴰ-FibrationEq .Eq-assoc = FUNCTOR-assoc
  FUNCTORᴰ-FibrationEq .Eq-fibration α Gᴰ =
    EqPsh.UEⱽ→Reprⱽ
      (EqPsh.CartesianLiftPshⱽ
        (FUNCTORᴰ Cᴰ Dᴰ) FUNCTOR-assoc α Gᴰ)
      FUNCTOR-idR
      (Construction.liftUE α Gᴰ)

  pullFunctorᴰ :
    {F G : Functor C D} (Gᴰ : Functorᴰ G Cᴰ Dᴰ) (α : NatTrans F G) →
    Functorᴰ F Cᴰ Dᴰ
  pullFunctorᴰ Gᴰ α = Construction.pulled α Gᴰ

  pullFunctorᴰπ :
    {F G : Functor C D} (Gᴰ : Functorᴰ G Cᴰ Dᴰ) (α : NatTrans F G) →
    NatTransᴰ α (pullFunctorᴰ Gᴰ α) Gᴰ
  pullFunctorᴰπ Gᴰ α = Construction.projection α Gᴰ

  private
    check-FUNCTORᴰ-FibrationEq : EqFibrationData (FUNCTORᴰ Cᴰ Dᴰ)
    check-FUNCTORᴰ-FibrationEq = FUNCTORᴰ-FibrationEq

    module _ {F G : Functor C D} (Gᴰ : Functorᴰ G Cᴰ Dᴰ)
      (α : NatTrans F G) where

      check-pullFunctorᴰ : Functorᴰ F Cᴰ Dᴰ
      check-pullFunctorᴰ = pullFunctorᴰ Gᴰ α

      check-pullFunctorᴰπ :
        NatTransᴰ α check-pullFunctorᴰ Gᴰ
      check-pullFunctorᴰπ = pullFunctorᴰπ Gᴰ α
