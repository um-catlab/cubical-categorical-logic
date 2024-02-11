{-

  The comma category of two functors viewed as a displayed category
  over one or both of the projections.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Displayed.Constructions.Comma where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.FullSubcategory
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Constructions.BinProduct as BinProduct
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More as Displayed
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Preorder
open import Cubical.Categories.Displayed.Constructions.Graph

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' : Level

open Category
open Categoryᴰ
open Preorderᴰ
open Functor
open NatTrans

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}{E : Category ℓE ℓE'}
         (F : Functor C E) (G : Functor D E) where

  Commaᴰ : Categoryᴰ (C ×C D) ℓE' ℓE'
  Commaᴰ = Graph {C = C} (HomBif E ∘Fl (F ^opF) ∘Fr G)

  hasPropHomsCommaᴰ : hasPropHoms Commaᴰ
  hasPropHomsCommaᴰ = hasPropHomsGraph _

  -- Universal Property: a functor into the comma category is
  -- equivalent to a natural transformation
  Comma : Category _ _
  Comma = ∫C Commaᴰ

  π1 : Functor Comma C
  π1 = BinProduct.Fst C D ∘F Displayed.Fst {Cᴰ = Commaᴰ}

  π2 : Functor Comma D
  π2 = BinProduct.Snd C D ∘F Displayed.Fst {Cᴰ = Commaᴰ}

  π⇒ : NatTrans (F ∘F π1) (G ∘F π2)
  π⇒ .N-ob  = snd
  π⇒ .N-hom = snd

  Commaᴰ₁ : Categoryᴰ C (ℓ-max ℓD ℓE') (ℓ-max ℓD' ℓE')
  Commaᴰ₁ = ∫Cᴰs Commaᴰ

  IsoCommaᴰ : Categoryᴰ (C ×C D) (ℓ-max ℓE' ℓE') ℓE'
  IsoCommaᴰ = ∫Cᴰ Commaᴰ (Preorderᴰ→Catᴰ IsoCommaᴰ') where
    IsoCommaᴰ' : Preorderᴰ Comma ℓE' ℓ-zero
    IsoCommaᴰ' .ob[_] ((c , d) , f)= isIso E f
    IsoCommaᴰ' .Hom[_][_,_] _ _ _ = Unit
    IsoCommaᴰ' .idᴰ = tt
    IsoCommaᴰ' ._⋆ᴰ_ _ _ = tt
    IsoCommaᴰ' .isPropHomᴰ = isPropUnit

  IsoComma : Category _ _
  IsoComma = ∫C IsoCommaᴰ

  IsoCommaᴰ₁ : Categoryᴰ C (ℓ-max ℓD ℓE') (ℓ-max ℓD' ℓE')
  IsoCommaᴰ₁ = ∫Cᴰs IsoCommaᴰ

  -- Characterization of HLevel of Commaᴰ₁ homs
  hasPropHomsIsoCommaᴰ₁ : isFaithful G → hasPropHoms IsoCommaᴰ₁
  hasPropHomsIsoCommaᴰ₁ G-faithful f (d , iso) (d' , iso') =
    isPropRetract {!!} {!!} {!!}
      (isEmbedding→hasPropFibers (injEmbedding (E .isSetHom) (λ {g} {g'} → G-faithful d d' g g'))
      {!!})

  hasContrHomsIsoCommaᴰ₁ : isFullyFaithful G → hasContrHoms IsoCommaᴰ₁
  hasContrHomsIsoCommaᴰ₁ Gff f (d , e) (d' , e') =
    inhProp→isContr
      {!!}
      (hasPropHomsIsoCommaᴰ₁ (isFullyFaithful→Faithful Gff) f (d , e) (d' , e'))


  πⁱ1 : Functor IsoComma C
  πⁱ1 = BinProduct.Fst C D ∘F Displayed.Fst {Cᴰ = IsoCommaᴰ}

  πⁱ2 : Functor IsoComma D
  πⁱ2 = BinProduct.Snd C D ∘F Displayed.Fst {Cᴰ = IsoCommaᴰ}

  π≅ : NatIso (F ∘F πⁱ1) (G ∘F πⁱ2)
  π≅ .NatIso.trans .N-ob (_ , f , _) = f
  π≅ .NatIso.trans .N-hom (_ , sq , _) = sq
  π≅ .NatIso.nIso (_ , _ , isIso) = isIso

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}{E : Category ℓE ℓE'}
         {F : Functor C E} {G : Functor D E}
         {B : Category ℓB ℓB'}
         (H : Functor B C)
         (K : Functor B D)
         (α : NatTrans (F ∘F H) (G ∘F K))
         where
  open Functorᴰ
  mkCommaFunctor : Functor B (Comma F G)
  mkCommaFunctor = mk∫Functor (H ,F K) αF where
    αF : Functorᴰ (H ,F K) _ _
    αF = mkP→CᴰFunctorᴰ _ _ _
      (λ {b} _ → α ⟦ b ⟧ )
      λ {_}{_}{f} _ → α .N-hom f

  mkCommaFunctorβ₁ : (π1 _ _ ∘F mkCommaFunctor) ≡ H
  mkCommaFunctorβ₁ = Functor≡ (λ _ → refl) (λ _ → refl)

  mkCommaFunctorβ₂ : (π2 _ _ ∘F mkCommaFunctor) ≡ K
  mkCommaFunctorβ₂ = Functor≡ (λ _ → refl) (λ _ → refl)

  private
    β⇒-boundary₁ : (F ∘F π1 F G) ∘F mkCommaFunctor ≡ F ∘F H
    β⇒-boundary₁ =
      sym F-assoc
      ∙ cong (F ∘F_) mkCommaFunctorβ₁
    β⇒-boundary₂ : (G ∘F π2 F G) ∘F mkCommaFunctor ≡ G ∘F K
    β⇒-boundary₂ =
      sym F-assoc
      ∙ cong (G ∘F_) mkCommaFunctorβ₂

  -- Morally this hole is refl but it's a PathP so...
  -- mkCommaFunctorβ⇒ :
  --   PathP (λ i → NatTrans (β⇒-boundary₁ i) (β⇒-boundary₂ i))
  --         (π⇒ F G ∘ˡ mkCommaFunctor)
  --         α
  -- mkCommaFunctorβ⇒ = makeNatTransPathP _ _
  --   (funExt (λ x → {!λ i → α ⟦ x ⟧!}))

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}{E : Category ℓE ℓE'}
         {F : Functor C E} {G : Functor D E}
         {B : Category ℓB ℓB'}
         (H : Functor B C)
         (K : Functor B D)
         (α : NatIso (F ∘F H) (G ∘F K))
         where
  open NatIso

  mkIsoCommaFunctor : Functor B (IsoComma F G)
  mkIsoCommaFunctor = mk∫Functor (H ,F K)
    (mk∫ᴰFunctorᴰ _ _
      (mkP→CᴰFunctorᴰ _ _ _
       ((λ {b} _ → α .trans ⟦ b ⟧ ))
       λ {_}{_}{f} _ → α .trans .N-hom f)
      (mkP→CᴰFunctorᴰ _ _ _
       (λ x → α .nIso _)
       λ x → _))
