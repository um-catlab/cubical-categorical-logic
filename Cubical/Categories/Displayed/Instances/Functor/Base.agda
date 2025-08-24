module Cubical.Categories.Displayed.Instances.Functor.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.NaturalTransformation

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')(Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ') where

  open Category
  open Functorᴰ
  open Categoryᴰ
  open NatTransᴰ
  open NatTrans
  open Functor

  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ
    module C = Category C
    module D = Category D
    import Cubical.Categories.Displayed.Reasoning Dᴰ as R

  idTransᴰ : (F : Functor C D)(Fᴰ : Functorᴰ F Cᴰ Dᴰ) →
    NatTransᴰ (idTrans F) Fᴰ Fᴰ
  idTransᴰ F Fᴰ .N-obᴰ {x = c} cᴰ = Dᴰ .idᴰ
  idTransᴰ F Fᴰ .N-homᴰ {x = c} {y = c'} {f = f} {xᴰ = cᴰ} {yᴰ = c'ᴰ} fᴰ =
    R.rectify (R.≡out (R.⋆IdR _ ∙ (sym (R.⋆IdL _))))

  makeNatTransPathᴰ : {F G : Functor C D}{α β : NatTrans F G}
      {Fᴰ : Functorᴰ F Cᴰ Dᴰ}{Gᴰ : Functorᴰ G Cᴰ Dᴰ}
      {αᴰ : NatTransᴰ α Fᴰ Gᴰ}{βᴰ : NatTransᴰ β Fᴰ Gᴰ} →
    (α≡β : α ≡ β) →
    (aoc : PathP (λ i → {c : C .ob}(cᴰ : Cᴰ.ob[ c ]) →
        Dᴰ.Hom[ (α≡β i) .N-ob c ][ Fᴰ .F-obᴰ cᴰ , Gᴰ .F-obᴰ cᴰ ])
      (αᴰ .N-obᴰ) (βᴰ .N-obᴰ)) →
    PathP (λ i → NatTransᴰ (α≡β i) Fᴰ Gᴰ) αᴰ βᴰ
  makeNatTransPathᴰ α≡β aoc i .N-obᴰ {x = c} cᴰ = (aoc i) cᴰ
  makeNatTransPathᴰ {F} {G} {α} {β} {Fᴰ} {Gᴰ} {αᴰ} {βᴰ}
    α≡β aoc i .N-homᴰ {x = c} {y = c'} {f = f} {xᴰ = cᴰ} {yᴰ = c'ᴰ} fᴰ = remᴰ i
    where
    left : PathP (λ j → Dᴰ [ α .N-hom f j ][ Fᴰ .F-obᴰ cᴰ , Gᴰ .F-obᴰ c'ᴰ ])
            ((Fᴰ .F-homᴰ fᴰ) Dᴰ.⋆ᴰ (αᴰ .N-obᴰ c'ᴰ))
            ((αᴰ .N-obᴰ cᴰ) Dᴰ.⋆ᴰ (Gᴰ .F-homᴰ fᴰ))
    left = αᴰ .N-homᴰ fᴰ
    right : PathP (λ j → Dᴰ [ β .N-hom f j ][ Fᴰ .F-obᴰ cᴰ , Gᴰ .F-obᴰ c'ᴰ ])
            ((Fᴰ .F-homᴰ fᴰ) Dᴰ.⋆ᴰ (βᴰ .N-obᴰ c'ᴰ))
            ((βᴰ .N-obᴰ cᴰ) Dᴰ.⋆ᴰ (Gᴰ .F-homᴰ fᴰ))
    right = βᴰ .N-homᴰ fᴰ
    top : PathP _
          ((Fᴰ .F-homᴰ fᴰ) Dᴰ.⋆ᴰ (αᴰ .N-obᴰ c'ᴰ))
          ((Fᴰ .F-homᴰ fᴰ) Dᴰ.⋆ᴰ (βᴰ .N-obᴰ c'ᴰ))
    top = congP (λ _ x → (Fᴰ .F-homᴰ fᴰ) Dᴰ.⋆ᴰ (x c'ᴰ)) aoc
    bottom : PathP _
             ((αᴰ .N-obᴰ cᴰ) Dᴰ.⋆ᴰ (Gᴰ .F-homᴰ fᴰ))
             ((βᴰ .N-obᴰ cᴰ) Dᴰ.⋆ᴰ (Gᴰ .F-homᴰ fᴰ))
    bottom = congP (λ _ x → (x cᴰ) Dᴰ.⋆ᴰ (Gᴰ .F-homᴰ fᴰ)) aoc
    remᴰ : PathP (λ k →
             PathP (λ j →
              Dᴰ.Hom[ (α≡β k) .N-hom f j ][ Fᴰ .F-obᴰ cᴰ , Gᴰ .F-obᴰ c'ᴰ ])
               ((Fᴰ .F-homᴰ fᴰ) Dᴰ.⋆ᴰ ((aoc k) c'ᴰ))
               ((aoc k) cᴰ Dᴰ.⋆ᴰ Gᴰ .F-homᴰ fᴰ))
           (αᴰ .N-homᴰ fᴰ)
           (βᴰ .N-homᴰ fᴰ)
    remᴰ = isSet→SquareP (λ _ _ → Dᴰ.isSetHomᴰ) left right top bottom

  idLTransᴰ : {F G : Functor C D}{α : NatTrans F G}
    {Fᴰ : Functorᴰ F Cᴰ Dᴰ}{Gᴰ : Functorᴰ G Cᴰ Dᴰ}(αᴰ : NatTransᴰ α Fᴰ Gᴰ) →
    PathP (λ i → NatTransᴰ (FUNCTOR C D .⋆IdL α i) Fᴰ Gᴰ)
    (seqTransᴰ (idTransᴰ F Fᴰ) αᴰ) αᴰ
  idLTransᴰ {F} {G} {α} {Fᴰ} {Gᴰ} αᴰ =
    makeNatTransPathᴰ (FUNCTOR C D .⋆IdL α) goal
    where
    goal : PathP (λ i → {c : C .ob} (cᴰ : Cᴰ.ob[ c ]) →
        Dᴰ.Hom[ D .⋆IdL (α .N-ob c) i ][ Fᴰ .F-obᴰ cᴰ , Gᴰ .F-obᴰ cᴰ ])
      (λ xᴰ → (Dᴰ .idᴰ) Dᴰ.⋆ᴰ (αᴰ .N-obᴰ xᴰ)) (αᴰ .N-obᴰ)
    goal = implicitFunExt (λ {x} → funExt (λ xᴰ → Dᴰ.⋆IdLᴰ _))

  idRTransᴰ : {F G : Functor C D}{α : NatTrans F G}
    {Fᴰ : Functorᴰ F Cᴰ Dᴰ}{Gᴰ : Functorᴰ G Cᴰ Dᴰ}(αᴰ : NatTransᴰ α Fᴰ Gᴰ) →
    PathP (λ i → NatTransᴰ (FUNCTOR C D .⋆IdR α i) Fᴰ Gᴰ)
    (seqTransᴰ αᴰ (idTransᴰ G Gᴰ)) αᴰ
  idRTransᴰ {F} {G} {α} {Fᴰ} {Gᴰ} αᴰ =
    makeNatTransPathᴰ (FUNCTOR C D .⋆IdR α) goal
    where
    goal : PathP (λ i → {c : C .ob} (cᴰ : Cᴰ.ob[ c ]) →
      Dᴰ.Hom[ D .⋆IdR (α .N-ob c) i ][ Fᴰ .F-obᴰ cᴰ , Gᴰ .F-obᴰ cᴰ ])
      (λ xᴰ → (αᴰ .N-obᴰ xᴰ) Dᴰ.⋆ᴰ (Dᴰ .idᴰ)) (αᴰ .N-obᴰ)
    goal = implicitFunExt (λ {x} → funExt (λ xᴰ → Dᴰ.⋆IdRᴰ _))

  module _ {F G : Functor C D}{α : NatTrans F G}
    {Fᴰ : Functorᴰ F Cᴰ Dᴰ}{Gᴰ : Functorᴰ G Cᴰ Dᴰ} where

    open import Cubical.Foundations.Isomorphism
    open Iso

    NatTransᴰΣ : Type _
    NatTransᴰΣ = Σ[ ob ∈ ({c : C .ob} (cᴰ : Cᴰ.ob[ c ]) →
        Dᴰ.Hom[ α .N-ob c ][ (Fᴰ .F-obᴰ cᴰ) , (Gᴰ .F-obᴰ cᴰ) ]) ]
      ({c : C.ob} {c' : C.ob} {f : C [ c , c' ]}
      {cᴰ : Cᴰ.ob[ c ] } {c'ᴰ : Cᴰ.ob[ c' ] } (fᴰ : Cᴰ.Hom[ f ][ cᴰ , c'ᴰ ]) →
      PathP (λ i → Dᴰ.Hom[ α .N-hom f i ][ Fᴰ .F-obᴰ cᴰ , Gᴰ .F-obᴰ c'ᴰ ])
      (Fᴰ .F-homᴰ fᴰ Dᴰ.⋆ᴰ ob c'ᴰ) (ob cᴰ Dᴰ.⋆ᴰ Gᴰ .F-homᴰ fᴰ))

    NatTransIsoᴰΣ : Iso (NatTransᴰ α Fᴰ Gᴰ) NatTransᴰΣ
    NatTransIsoᴰΣ .fun αᴰ = αᴰ .N-obᴰ , αᴰ .N-homᴰ
    NatTransIsoᴰΣ .inv (ob , hom) .N-obᴰ = ob
    NatTransIsoᴰΣ .inv (ob , hom) .N-homᴰ = hom
    NatTransIsoᴰΣ .rightInv _ = refl
    NatTransIsoᴰΣ .leftInv _ = refl

    isSetNatTransᴰ : isSet (NatTransᴰ α Fᴰ Gᴰ)
    isSetNatTransᴰ = isSetRetract (NatTransIsoᴰΣ .fun)
      (NatTransIsoᴰΣ .inv) (NatTransIsoᴰΣ .leftInv)
      (isSetΣSndProp (isSetImplicitΠ (λ c → isSetΠ (λ cᴰ → Dᴰ .isSetHomᴰ)))
        λ α-components → isPropImplicitΠ3 λ c c' f →
        isPropImplicitΠ2 (λ cᴰ c'ᴰ →
          isPropΠ λ fᴰ → λ p q → isSet→SquareP (λ _ _ → Dᴰ .isSetHomᴰ) _ _ _ _))

  FUNCTORᴰ : Categoryᴰ (FUNCTOR C D)  _ _
  FUNCTORᴰ .ob[_] F = Functorᴰ F Cᴰ Dᴰ
  FUNCTORᴰ .Hom[_][_,_] {x = F} {y = G} α Fᴰ Gᴰ = NatTransᴰ α Fᴰ Gᴰ
  FUNCTORᴰ .idᴰ {x = F} {p = Fᴰ} = idTransᴰ F Fᴰ
  FUNCTORᴰ ._⋆ᴰ_ {x = F} {y = G} {z = H} {f = α} {g = β}
    {xᴰ = Fᴰ} {yᴰ = Gᴰ} {zᴰ = Hᴰ} αᴰ βᴰ = seqTransᴰ αᴰ βᴰ
  FUNCTORᴰ .⋆IdLᴰ {x = F} {y = G} {f = α} {xᴰ = Fᴰ} {yᴰ = Gᴰ} αᴰ = idLTransᴰ αᴰ
  FUNCTORᴰ .⋆IdRᴰ {x = F} {y = G} {f = α} {xᴰ = Fᴰ} {yᴰ = Gᴰ} αᴰ = idRTransᴰ αᴰ
  FUNCTORᴰ .⋆Assocᴰ {x = F} {y = G} {z = H} {w = E} {f = α} {g = β} {h = γ}
    {xᴰ = Fᴰ} {yᴰ = Gᴰ} {zᴰ = Hᴰ} {wᴰ = Eᴰ} αᴰ βᴰ γᴰ =
    makeNatTransPathᴰ (FUNCTOR C D .⋆Assoc α β γ)
    (implicitFunExt (λ {x} → funExt (λ xᴰ →  Dᴰ .⋆Assocᴰ _ _ _)))
  FUNCTORᴰ .isSetHomᴰ {x = F} {y = G} {f = α} {xᴰ = Fᴰ} {yᴰ = Gᴰ} =
    isSetNatTransᴰ

-- TODO: precompose/postcompose/compose are really just the three
-- operations of a compose bifunctor
module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (E : Category ℓE ℓE')
  {F : Functor C D}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ') (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  where
  open Functorᴰ
  open NatTransᴰ
  import Cubical.Categories.Displayed.Reasoning Dᴰ as R
  precomposeFᴰ : Functorᴰ (precomposeF E F) (FUNCTORᴰ Dᴰ Eᴰ) (FUNCTORᴰ Cᴰ Eᴰ)
  precomposeFᴰ .F-obᴰ Gᴰ = Gᴰ ∘Fᴰ Fᴰ
  precomposeFᴰ .F-homᴰ αᴰ .N-obᴰ xᴰ = αᴰ .N-obᴰ (Fᴰ .F-obᴰ xᴰ)
  precomposeFᴰ .F-homᴰ αᴰ .N-homᴰ fᴰ = αᴰ .N-homᴰ (Fᴰ .F-homᴰ fᴰ)
  precomposeFᴰ .F-idᴰ = refl
  precomposeFᴰ .F-seqᴰ fᴰ gᴰ = refl

  postcomposeFᴰ : Functorᴰ (postcomposeF E F) (FUNCTORᴰ Eᴰ Cᴰ) (FUNCTORᴰ Eᴰ Dᴰ)
  postcomposeFᴰ .F-obᴰ Gᴰ = Fᴰ ∘Fᴰ Gᴰ
  postcomposeFᴰ .F-homᴰ αᴰ .N-obᴰ xᴰ = F-homᴰ Fᴰ (αᴰ .N-obᴰ xᴰ)
  postcomposeFᴰ .F-homᴰ αᴰ .N-homᴰ fᴰ = R.rectify $ R.≡out $
    (sym $ R.≡in $ Fᴰ .F-seqᴰ _ _)
    ∙ (R.≡in $ (λ i → Fᴰ .F-homᴰ (αᴰ .N-homᴰ fᴰ i)))
    ∙ (R.≡in $ Fᴰ .F-seqᴰ _ _)
  postcomposeFᴰ .F-idᴰ = makeNatTransPathᴰ _ _ _ λ i _ → Fᴰ .F-idᴰ i
  postcomposeFᴰ .F-seqᴰ fᴰ gᴰ = makeNatTransPathᴰ _ _ _ λ i _ →
    Fᴰ .F-seqᴰ (fᴰ .N-obᴰ _) (gᴰ .N-obᴰ _) i

module _
  {C : Category ℓC ℓC'} (E : Category ℓE ℓE')
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ'}
  (Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ') (Fⱽ : Functorⱽ Cᴰ Dᴰ)
  where
  open Functorᴰ
  open NatTransᴰ
  precomposeFⱽ : Functorⱽ (FUNCTORᴰ Dᴰ Eᴰ) (FUNCTORᴰ Cᴰ Eᴰ)
  precomposeFⱽ .F-obᴰ Gᴰ = Gᴰ ∘Fᴰⱽ Fⱽ
  precomposeFⱽ .F-homᴰ αᴰ .N-obᴰ xᴰ = αᴰ .N-obᴰ (Fⱽ .F-obᴰ xᴰ)
  precomposeFⱽ .F-homᴰ αᴰ .N-homᴰ fᴰ = αᴰ .N-homᴰ (Fⱽ .F-homᴰ fᴰ)
  precomposeFⱽ .F-idᴰ = refl
  precomposeFⱽ .F-seqᴰ _ _ = refl

  import Cubical.Categories.Displayed.Reasoning Dᴰ as R
  postcomposeFⱽ : Functorⱽ (FUNCTORᴰ Eᴰ Cᴰ) (FUNCTORᴰ Eᴰ Dᴰ)
  postcomposeFⱽ .F-obᴰ Gᴰ = Fⱽ ∘Fⱽᴰ Gᴰ
  postcomposeFⱽ .F-homᴰ αᴰ .N-obᴰ xᴰ = F-homᴰ Fⱽ (αᴰ .N-obᴰ xᴰ)
  postcomposeFⱽ .F-homᴰ αᴰ .N-homᴰ fᴰ = R.rectify $ R.≡out $
    (sym $ R.≡in $ Fⱽ .F-seqᴰ _ _)
    ∙ (R.≡in $ (λ i → Fⱽ .F-homᴰ (αᴰ .N-homᴰ fᴰ i)))
    ∙ (R.≡in $ Fⱽ .F-seqᴰ _ _)
  postcomposeFⱽ .F-idᴰ = makeNatTransPathᴰ _ _ _ (λ i _ → Fⱽ .F-idᴰ i)
  postcomposeFⱽ .F-seqᴰ fᴰ gᴰ = makeNatTransPathᴰ _ _ _ λ i _ →
    Fⱽ .F-seqᴰ (fᴰ .N-obᴰ _) (gᴰ .N-obᴰ _) i
