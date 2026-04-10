module Cubical.Categories.2Functor.Fibration where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.2Category.Base
open import Cubical.Categories.2Functor.Base
open import Cubical.Categories.Category
open import Cubical.Categories.Functor as Func
open import Cubical.Categories.NaturalTransformation

private
  variable
    ℓC ℓC' ℓC'' ℓD ℓD' ℓD'' ℓE ℓE' : Level

open 2Category
open LaxFunctor
open PseudoFunctor

module _ {ℓC ℓC'} (C : Category ℓC ℓC') ℓD ℓD' where
  OpFibration : Type _
  OpFibration = PseudoFunctor (Cat→2Cat C) (CAT {ℓC = ℓD} {ℓC' = ℓD'})

  OpFibrationEq : Type _
  OpFibrationEq = PseudoFunctor (Cat→2CatEq C) (CAT {ℓC = ℓD} {ℓC' = ℓD'})

module _ {ℓC ℓC'} (C : Category ℓC ℓC') ℓD ℓD' where
  Fibration : Type _
  Fibration = OpFibration (C ^op) ℓD ℓD'

  FibrationEq : Type _
  FibrationEq = OpFibrationEq (C ^op) ℓD ℓD'

module _ {ℓC ℓC'} (C : Category ℓC ℓC') ℓD ℓD' where
  module _ (F : Fibration C ℓD ℓD') {E : Category ℓE ℓE'} (G : Functor E C) where
    private
      module C = Category C
      module E = Category E
      module F = PseudoFunctor F
      module G = Functor G
      module CAT = 2Category (CAT {ℓC = ℓD} {ℓC' = ℓD'})

    open isPseudo
    open isIso2Cell

    private
      -- F's F₂ applied to any path is an iso 2-cell in CAT, with inverse
      -- obtained by flipping the path.
      F₂PathIsIso : ∀ {x y : C.ob} {f g : C.Hom[ y , x ]} (p : f ≡ g)
                  → isIso2Cell (CAT {ℓC = ℓD} {ℓC' = ℓD'}) (F.F₂ p)
      F₂PathIsIso p .inv = F.F₂ (sym p)
      F₂PathIsIso p .sec =
          sym (F.F-seqⱽ p (sym p))
        ∙ cong F.F₂ (rCancel p)
        ∙ F.F-id₂
      F₂PathIsIso p .ret =
          sym (F.F-seqⱽ (sym p) p)
        ∙ cong F.F₂ (lCancel p)
        ∙ F.F-id₂

      -- Vertical composition of iso 2-cells in CAT is iso.
      ⋆ⱽIsIso : ∀ {x y : CAT.ob} {f g h : CAT.Hom₁[ x , y ]}
                  {α : CAT.Hom₂[ f , g ]} {β : CAT.Hom₂[ g , h ]}
                → isIso2Cell (CAT {ℓC = ℓD} {ℓC' = ℓD'}) α
                → isIso2Cell (CAT {ℓC = ℓD} {ℓC' = ℓD'}) β
                → isIso2Cell (CAT {ℓC = ℓD} {ℓC' = ℓD'}) (α CAT.⋆ⱽ β)
      ⋆ⱽIsIso {α = α} {β = β} isα isβ .inv = isβ .inv CAT.⋆ⱽ isα .inv
      ⋆ⱽIsIso {α = α} {β = β} isα isβ .sec =
          CAT.⋆ⱽAssoc α β (isβ .inv CAT.⋆ⱽ isα .inv)
        ∙ cong (α CAT.⋆ⱽ_)
               (sym (CAT.⋆ⱽAssoc β (isβ .inv) (isα .inv))
                ∙ cong (CAT._⋆ⱽ isα .inv) (isβ .sec)
                ∙ CAT.⋆ⱽIdL (isα .inv))
        ∙ isα .sec
      ⋆ⱽIsIso {α = α} {β = β} isα isβ .ret =
          CAT.⋆ⱽAssoc (isβ .inv) (isα .inv) (α CAT.⋆ⱽ β)
        ∙ cong (isβ .inv CAT.⋆ⱽ_)
               (sym (CAT.⋆ⱽAssoc (isα .inv) α β)
                ∙ cong (CAT._⋆ⱽ β) (isα .ret)
                ∙ CAT.⋆ⱽIdL β)
        ∙ isβ .ret

    reindex : Fibration E ℓD ℓD'
    reindex .lax = seqLaxFunctor (Functor→LaxFunctor (G ^opF)) (F .lax)
    reindex .pseudo .F-id-iso =
      ⋆ⱽIsIso (F .pseudo .F-id-iso)
              (F₂PathIsIso (Functor→LaxFunctor (G ^opF) .F-id))
    reindex .pseudo .F-seq-iso f g =
      ⋆ⱽIsIso (F .pseudo .F-seq-iso _ _)
              (F₂PathIsIso (Functor→LaxFunctor (G ^opF) .F-seq f g))
