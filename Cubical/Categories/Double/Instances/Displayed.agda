{-# OPTIONS --lossy-unification --allow-unsolved-metas #-}
module Cubical.Categories.Double.Instances.Displayed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets hiding (PullbacksSET)
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Instances.Fiber

open import Cubical.Categories.Displayed.Base

open import Cubical.Categories.Double.Base
open import Cubical.Categories.Double.Functor.Base

open import Cubical.Categories.Double.Instances.1Category
open import Cubical.Categories.Double.Instances.Prof
open import Cubical.Categories.Double.Instances.Span
open import Cubical.Categories.Double.Instances.Span.Base

open import Cubical.Categories.Functors.Strict.Base
open import Cubical.Categories.Functors.Strict.Presheaf
open import Cubical.Categories.Functors.Strict.Bifunctor
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Presheaf.Constructions.Tensor as ⊗

open DoubleCategory
open LaxDoubleFunctor
open Categoryᴰ

module _ ℓ where
  SPANSET : DoubleCategory _ _ _ _
  SPANSET = SPAN (SET ℓ) PullbacksSET

module _ {ℓ ℓ'} (C : Category ℓ ℓ') (ℓF : Level)
  (F : LaxDoubleFunctor (1Cat→DoubleCatᴴEq C) (SPANSET ℓF))
  where

  private
    module C = Category C
    module F = LaxDoubleFunctor F

    -- Extract components of spans
    module SpanOf {x y : C.ob} (f : C [ x , y ]) where
      span = F.Fᴴ f
      apex : hSet ℓF
      apex = span .fst
      leg-l : ⟨ apex ⟩ → ⟨ F.F₀ x ⟩
      leg-l = span .snd .fst
      leg-r : ⟨ apex ⟩ → ⟨ F.F₀ y ⟩
      leg-r = span .snd .snd

    -- Fiber hom type: elements of the span apex mapping to given endpoints
    FiberHom : ∀ {x y} (f : C [ x , y ])
      → ⟨ F.F₀ x ⟩ → ⟨ F.F₀ y ⟩ → Type ℓF
    FiberHom f xᴰ yᴰ =
      Σ[ a ∈ ⟨ SpanOf.apex f ⟩ ]
        (SpanOf.leg-l f a ≡ xᴰ) × (SpanOf.leg-r f a ≡ yᴰ)

    isSetFiberHom : ∀ {x y} (f : C [ x , y ]) xᴰ yᴰ
      → isSet (FiberHom f xᴰ yᴰ)
    isSetFiberHom f xᴰ yᴰ =
      isSetΣ (SpanOf.apex f .snd) λ _ →
        isProp→isSet (isProp×
          (F.F₀ _ .snd _ _)
          (F.F₀ _ .snd _ _))

  toCatᴰ-Span : Categoryᴰ C ℓF ℓF
  toCatᴰ-Span .ob[_] c = ⟨ F.F₀ c ⟩
  toCatᴰ-Span .Hom[_][_,_] f xᴰ yᴰ = FiberHom f xᴰ yᴰ
  toCatᴰ-Span .idᴰ {x} {xᴰ} =
    F.F-idᴴ .fst xᴰ ,
    sym (funExt⁻ (F.F-idᴴ .snd .fst) xᴰ) ,
    sym (funExt⁻ (F.F-idᴴ .snd .snd) xᴰ)
  toCatᴰ-Span ._⋆ᴰ_ {f = f} {g = g} (a , pa-l , pa-r) (b , pb-l , pb-r) =
     F.F-seqᴴ f g .fst x ,
     sym (funExt⁻ (F.F-seqᴴ f g .snd .fst) x) ∙ pa-l ,
     sym (funExt⁻ (F.F-seqᴴ f g .snd .snd) x) ∙ pb-r
    where
    x : Σ[ (p , q) ∈ ⟨ SpanOf.apex f ⟩ × ⟨ SpanOf.apex g ⟩ ]
           SpanOf.leg-r f p ≡ SpanOf.leg-l g q
    x = ((a , b) , pa-r ∙ sym pb-l)
  toCatᴰ-Span .⋆IdLᴰ {f = f} {xᴰ = xᴰ} {yᴰ = yᴰ} fᴰ = {!!}
  toCatᴰ-Span .⋆IdRᴰ {f = f} fᴰ = {!!}
  toCatᴰ-Span .⋆Assocᴰ {f = f} {g = g} {h = h} fᴰ gᴰ hᴰ = {!!}
  toCatᴰ-Span .isSetHomᴰ {f = f} = isSetFiberHom f _ _

module _ {ℓ ℓ'} (C : Category ℓ ℓ') (ℓP : Level)
  (F : LaxDoubleFunctor (1Cat→DoubleCatᴴEq C) (PROF ℓP ℓP))
  (F-idᴴ-iso : ∀ {x} → SPshIso
    (StrictRelator→Psh (PROF ℓP ℓP .idᴴ {x = F .LaxDoubleFunctor.F₀ x}))
    (StrictRelator→Psh (F .LaxDoubleFunctor.Fᴴ
      (1Cat→DoubleCatᴴ C .idᴴ {x = x}))))
  where

  private
    module C = Category C
    module F = LaxDoubleFunctor F

  toCatᴰ-Prof : Categoryᴰ C _ _
  toCatᴰ-Prof .ob[_] c = F.F₀ c .Category.ob
  toCatᴰ-Prof .Hom[_][_,_] f xᴰ yᴰ = ⟨ F.Fᴴ f .StrictBifunctor.Bif-ob xᴰ yᴰ ⟩
  toCatᴰ-Prof .idᴰ = F.F-idᴴ .SPshHom.N-ob _ (Category.id (F.F₀ _))
  toCatᴰ-Prof ._⋆ᴰ_ {f = f}{g = g} fᴰ gᴰ = F.F-seqᴴ f g .SPshHom.N-ob _ (fᴰ Tensor.,⊗ gᴰ)
  toCatᴰ-Prof .⋆IdLᴰ {f = f} {xᴰ = xᴰ} {yᴰ = yᴰ} fᴰ = {!!}
  toCatᴰ-Prof .⋆IdRᴰ = {!!}
  toCatᴰ-Prof .⋆Assocᴰ = {!!}
  toCatᴰ-Prof .isSetHomᴰ {f = f}{xᴰ = xᴰ}{yᴰ = yᴰ} = F.Fᴴ f .StrictBifunctor.Bif-ob xᴰ yᴰ .snd


module _ {ℓ ℓ' ℓᴰ} (C : Category ℓ ℓ') (Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ) where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module _ (isSetObᴰ : ∀ c → isSet Cᴰ.ob[ c ]) where
    private
      module S = SpanDefs (SET ℓᴰ) PullbacksSET

    fromCatᴰ-Span : LaxDoubleFunctor (1Cat→DoubleCatᴴEq C) (SPANSET ℓᴰ)
    fromCatᴰ-Span .F₀ c = Cᴰ.ob[ c ] , isSetObᴰ c
    fromCatᴰ-Span .Fⱽ Eq.refl = λ z → z
    fromCatᴰ-Span .Fᴴ {x = x}{y = y} f =
      ((Σ[ xᴰ ∈ Cᴰ.ob[ x ] ] Σ[ yᴰ ∈ Cᴰ.ob[ y ] ] Cᴰ.Hom[ f ][ xᴰ , yᴰ ]) ,
      isSetΣ (isSetObᴰ x) (λ _ → isSetΣ (isSetObᴰ y) λ _ → Cᴰ.isSetHomᴰ)) ,
      (λ z → z .fst) ,
      λ z → z .snd .fst
    fromCatᴰ-Span .Fˢ {fⱽ = Eq.refl} {gⱽ = Eq.refl} Eq.refl = (λ z → z) , (refl , refl)
    fromCatᴰ-Span .F-idⱽ = refl
    fromCatᴰ-Span .F-seqⱽ Eq.refl Eq.refl = refl
    fromCatᴰ-Span .F-idᴴ = (λ z → z , z , Cᴰ.idᴰ) , (refl , refl)
    fromCatᴰ-Span .F-seqᴴ {y = y} f g =
      (λ (((xᴰ , yᴰ , fᴰ) , (yᴰ' , zᴰ , gᴰ)) , yᴰ≡yᴰ') →
        xᴰ , zᴰ ,
        (fᴰ Cᴰ.⋆ᴰ
          subst (λ a → Cᴰ.Hom[ g ][ a , zᴰ ]) (sym yᴰ≡yᴰ') gᴰ)) ,
      refl , refl
    fromCatᴰ-Span .F-idⱽSq =
      S.makeSpanSquarePathP refl
    fromCatᴰ-Span .F-seqⱽSq
      {←f = Eq.refl}{→f = Eq.refl}{←f' = Eq.refl}{→f' = Eq.refl} Eq.refl Eq.refl =
      S.makeSpanSquarePathP refl
    fromCatᴰ-Span .F-idᴴ-nat Eq.refl =
      S.makeSpanSquarePathP refl
    fromCatᴰ-Span .F-seqᴴ-nat = {!!}
    fromCatᴰ-Span .F-unit-l f =
      S.makeSpanSquarePathP (funExt λ _ → {!!})
    fromCatᴰ-Span .F-unit-r f =
      S.makeSpanSquarePathP (funExt λ _ → {!!})
    fromCatᴰ-Span .F-assoc f g h =
      S.makeSpanSquarePathP (funExt λ _ → {!!})

  fromCatᴰ-Prof : LaxDoubleFunctor (1Cat→DoubleCatᴴEq C) (PROF ℓᴰ ℓᴰ)
  fromCatᴰ-Prof .F₀ c = Cᴰ.v[ c ]
  fromCatᴰ-Prof .Fⱽ Eq.refl = SId
  fromCatᴰ-Prof .Fᴴ f .StrictBifunctor.Bif-ob xᴰ yᴰ =
    Cᴰ.Hom[ f ][ xᴰ , yᴰ ] , Cᴰ.isSetHomᴰ
  fromCatᴰ-Prof .Fᴴ f .StrictBifunctor.Bif-homL fⱽ yᴰ hᴰ = fⱽ Cᴰ.⋆ⱽᴰ hᴰ
  fromCatᴰ-Prof .Fᴴ f .StrictBifunctor.Bif-L-id fⱽ e =
    funExt λ hᴰ → cong (Cᴰ._⋆ⱽᴰ hᴰ) (sym e) ∙ Cᴰ.⋆IdLⱽᴰ hᴰ
  fromCatᴰ-Prof .Fᴴ f .StrictBifunctor.Bif-L-seq fⱽ fⱽ' h e =
    funExt λ hᴰ → cong (Cᴰ._⋆ⱽᴰ hᴰ) (sym e) ∙ Cᴰ.⋆Assocⱽⱽᴰ
  fromCatᴰ-Prof .Fᴴ f .StrictBifunctor.Bif-homR xᴰ gⱽ hᴰ = hᴰ Cᴰ.⋆ᴰⱽ gⱽ
  fromCatᴰ-Prof .Fᴴ f .StrictBifunctor.Bif-R-id gⱽ e =
    funExt λ hᴰ → cong (hᴰ Cᴰ.⋆ᴰⱽ_) (sym e) ∙ Cᴰ.⋆IdRᴰⱽ
  fromCatᴰ-Prof .Fᴴ f .StrictBifunctor.Bif-R-seq gⱽ gⱽ' h e =
    funExt λ hᴰ → cong (hᴰ Cᴰ.⋆ᴰⱽ_) (sym e) ∙ sym Cᴰ.⋆Assocᴰⱽⱽ
  fromCatᴰ-Prof .Fᴴ f .StrictBifunctor.Bif-hom× fⱽ gⱽ hᴰ =
    fⱽ Cᴰ.⋆ⱽᴰ (hᴰ Cᴰ.⋆ᴰⱽ gⱽ)
  fromCatᴰ-Prof .Fᴴ f .StrictBifunctor.Bif-LR-fuse fⱽ gⱽ =
    funExt λ hᴰ → Cᴰ.⋆Assocⱽᴰⱽ
  fromCatᴰ-Prof .Fᴴ f .StrictBifunctor.Bif-RL-fuse fⱽ gⱽ = refl
  fromCatᴰ-Prof .Fˢ {fⱽ = Eq.refl}{gⱽ = Eq.refl} Eq.refl =
    PROF ℓᴰ ℓᴰ .idⱽSq
  fromCatᴰ-Prof .F-idⱽ = refl
  fromCatᴰ-Prof .F-seqⱽ Eq.refl Eq.refl = refl
  fromCatᴰ-Prof .F-idᴴ = {!!}
  fromCatᴰ-Prof .F-seqᴴ = {!!}
  fromCatᴰ-Prof .F-idⱽSq = refl
  fromCatᴰ-Prof .F-seqⱽSq {←f = Eq.refl}{→f = Eq.refl}
                          {←f' = Eq.refl}{→f' = Eq.refl} Eq.refl Eq.refl = refl
  fromCatᴰ-Prof .F-idᴴ-nat = {!!}
  fromCatᴰ-Prof .F-seqᴴ-nat = {!!}
  fromCatᴰ-Prof .F-unit-l f = {!!}
  fromCatᴰ-Prof .F-unit-r f = {!!}
  fromCatᴰ-Prof .F-assoc f g h = {!!}
