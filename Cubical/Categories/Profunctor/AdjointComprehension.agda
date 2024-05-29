{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Profunctor.AdjointComprehension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More
open import Cubical.Data.Unit

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Functors.More
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Displayed.Constructions.PropertyOver
open import Cubical.Categories.Isomorphism.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Properties hiding (L)
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.KanExtension
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Profunctor.General

open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Profunctor.FunctorComprehension

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓS ℓR : Level

open Category
open Functor
open NatIso
open UniversalElement
open NatTrans
open NaturalBijection

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  (L : Functor C D)
    where

  -- D[ L - , = ]
  LProf : Profunctor D C ℓD'
  LProf = CurryBifunctor (Sym ((HomBif D) ∘Fl (L ^opF)))

  module _ (ues : UniversalElements LProf) where
    R : Functor D C
    R = FunctorComprehension {P = LProf} ues

    the-prof-iso = ProfIso {P = LProf} ues
    the-prof-iso-inv = symNatIso (ProfIso {P = LProf} ues)

    open _⊣_
    open NatElt
    -- TODO create a universe polymorphic definition of adjoint
    -- then whisker with a lift natiso
    L⊣R : L ⊣ R
    L⊣R .adjIso {c}{d} .Iso.fun x =
      lower (the-prof-iso-inv .trans .N-ob d .N-ob c (lift x))
    L⊣R .adjIso {c}{d} .Iso.inv x =
      lower (the-prof-iso .trans .N-ob d .N-ob c (lift x))
    L⊣R .adjIso {c}{d} .Iso.rightInv b =
      cong (λ a → lower (a .N-ob c (lift b))) (the-prof-iso .nIso d .isIsoC.ret)
    L⊣R .adjIso {c}{d} .Iso.leftInv a =
      cong (λ z → lower (z .N-ob c (lift a))) (the-prof-iso .nIso d .isIsoC.sec)
    L⊣R .adjNatInD {c}{d}{d'} f k =
      cong (λ a → lower ((a .N-ob c) (lift f))) (the-prof-iso-inv .trans .N-hom k)
    L⊣R .adjNatInC {c'}{c}{d} g h =
      cong (λ a → lower (a (lift g))) (the-prof-iso .trans .N-ob d .N-hom h)

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  (F : Functor C D)
  ℓS
  where

  F* = precomposeF (SET (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD') ℓS)) (F ^opF)

  open Ran ℓS F

  the-ues : UniversalElements (LProf F*)
  the-ues P .vertex = RanOb P
  the-ues P .element .N-ob c x =
    x .Ran.End.fun c (D .id)
  the-ues P .element .N-hom {c}{c'} g =
    funExt λ x →
    cong
      (x .End.fun c')
      (D .⋆IdL _ ∙ sym (D .⋆IdR _)) ∙ x .End.coh g (D .id)
  the-ues P .universal A .equiv-proof y .fst .fst .N-ob d x .Ran.End.fun c g =
    y .N-ob c (action D A g x)
  the-ues P .universal A .equiv-proof y .fst .fst .N-ob d x
    .Ran.End.coh {c}{c'} f g =
    cong (λ a → y .N-ob c a) (cong (λ a → a x) (A .F-seq _ _)) ∙
    cong (λ a → a (action D A g x)) (y .N-hom f)
  the-ues P .universal A .equiv-proof y .fst .fst .N-hom {d}{d'} f =
    funExt (λ x →
      end≡
        P
        (λ c g →
          cong (λ a → y .N-ob c a) (cong (λ a → a x) (sym (A .F-seq _ _))))
    )
  the-ues P .universal A .equiv-proof y .fst .snd =
    makeNatTransPath (funExt (λ c → funExt (λ x →
      cong (λ a → y .N-ob c a) (cong (λ a → a x) (A .F-id)))))
  the-ues P .universal A .equiv-proof y .snd z =
    Σ≡Prop
      (λ x → isSetHom
        (FUNCTOR (C ^op) (SET (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD') ℓS)))
        (action (FUNCTOR (D ^op) (SET (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD') ℓS)))
        (LProf F* ⟅ P ⟆) x (the-ues P .element)) y)
      (makeNatTransPath (funExt (λ d → funExt (λ x →
        end≡
          P
          (λ c g →
            cong (λ a → a .N-ob c (action D A g x)) (sym (z .snd)) ∙
            cong (λ a → a x .End.fun c (D .id)) (z .fst .N-hom g) ∙
            cong (λ a → z .fst .N-ob d x .Ran.End.fun c a)
              (cong (λ a → a ⋆⟨ D ⟩ g) (sym (F .F-id))) ∙
            z .fst .N-ob d x .End.coh (C .id) g ∙
            (sym (z .fst .N-ob d x .Ran.End.coh (C .id) g)) ∙
            cong (λ a → z .fst .N-ob d x .Ran.End.fun c a)
              (cong (λ a → a ⋆⟨ D ⟩ g) (F .F-id) ∙ D .⋆IdL g))
      ))))

  -- Define the right Kan-extension of preseheaves along F
  -- via FunctorComprehension
  --
  -- As written, this still requires the Presheaf.KanExtension definitions of
  -- RanOb
  Ran' :
    Functor
      (FUNCTOR (C ^op) (SET (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD') ℓS)))
      (FUNCTOR (D ^op) (SET (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD') ℓS)))
  Ran' = R F* the-ues

  _ : ∀ P → Ran ⟅ P ⟆ ≡ Ran' ⟅ P ⟆
  _ = λ P → refl

  F*⊣Ran' : F* ⊣ Ran'
  F*⊣Ran' = L⊣R F* the-ues

  test : ∀ {P}{Q}(f : FUNCTOR (C ^op) (SET _) [ P , Q ]) →
    Ran ⟪ f ⟫ ≡ Ran' ⟪ f ⟫
  test {P}{Q} f =
    makeNatTransPath (funExt (λ x → funExt (λ x →
      end≡ Q
        (λ c g →
          cong
            (λ a → f .N-ob c (x .End.fun c a))
            (sym (D .⋆IdL g))))))


  {--
  --          P
  -- C^op -----------> SET
  --  |              __/
  --  | F ^op    ___/
  --  V    _____/ Ran' P
  -- D^op /
  --
  -- M : D^op → SET and μ : MF → X
  -- then ∃! δ : M → Ran' X such that
  --
  --       δF
  -- MF -----> RF
  --   \_       |
  --     \      |
  --  μ   \_    | ε
  --        \   |
  --         \  v
  --            P
  --}

  module _
    {E : Category ℓE ℓE'}
    (P : Functor (C ^op) (SET _))
    (M : Functor (D ^op) (SET _))
    (μ : (FUNCTOR (C ^op) (SET _)) [ M ∘F (F ^opF) , P ] )
    where

    ε' :
      (FUNCTOR (C ^op) (SET _))
        [ Ran' .F-ob P ∘F (F ^opF) , P ]
    ε' = the-ues P .element

    δ : (FUNCTOR (D ^op) (SET  _))
      [ M , Ran' .F-ob P ]
    δ = the-ues P .universal M .equiv-proof μ .fst .fst

    δ' : (FUNCTOR (C ^op) (SET  _))
      [ M ∘F (F ^opF) , Ran' .F-ob P ∘F (F ^opF) ]
    δ' = δ ∘ˡ (F ^opF)

    ε∘δ : NatTrans (M ∘F (F ^opF)) P
    ε∘δ = seqTrans δ' ε'

    _ : ε∘δ ≡ μ
    _ = makeNatTransPath (funExt (λ c → funExt (λ x →
      cong (μ .N-ob c) (cong (λ a → a x) (M .F-id)))))
