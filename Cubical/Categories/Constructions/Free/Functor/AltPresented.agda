-- Free functor between categories generated from base objects and generators
-- this time based on Quiver and freely adding in the functor
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Constructions.Free.Functor.AltPresented where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum hiding (rec; elim)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Displayed.Section

open import Cubical.Categories.Constructions.Presented as Presented
  hiding (rec; elim)
open import Cubical.Categories.Constructions.Free.Category.Quiver as FreeCat
  hiding (rec; elim)

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓh ℓh' ℓj ℓ : Level

open Category
open Categoryᴰ
open Functor
open Functorᴰ
open Section
open QuiverOver
open Axioms
open Interpᴰ

-- We are going to generate a category G as well as a category H
-- equipped with a functor G -> H G has ordinary generating objects
-- and morphisms H has generating objects from the quiver, but also a
-- "type constructor" mapping objects from G. morphisms can be
-- between either type
module _ (G : Quiver ℓg ℓg') where
  HQuiver : ∀ ℓh ℓh' → Type _
  HQuiver ℓh ℓh' = Σ[ ob ∈ Type ℓh ] QuiverOver (G .fst ⊎ ob) ℓh'

  module _ (H : HQuiver ℓh ℓh') where
    private
      GCat = FreeCat G

      HOb = (G .fst ⊎ H .fst)

    HQ : Quiver (ℓ-max ℓg ℓh) (ℓ-max (ℓ-max ℓg ℓg') ℓh')
    HQ .fst = HOb
    HQ .snd .mor = CatQuiver GCat .snd .mor ⊎ H .snd .mor
    HQ .snd .dom (inl x) = inl (CatQuiver GCat .snd .dom x)
    HQ .snd .dom (inr x) = H .snd .dom x
    HQ .snd .cod (inl x) = inl (CatQuiver GCat .snd .cod x)
    HQ .snd .cod (inr x) = H .snd .cod x

    PreHCat = FreeCat HQ

    FunctorEquation =
    --   F⟪id⟫≡id
      GCat .ob
    --   F⟪⋆⟫≡⋆F⟪⟫
      ⊎ (Σ[ A ∈ G .fst ] Σ[ B ∈ G .fst ] Σ[ C ∈ G .fst ]
        GCat [ A , B ] × GCat [ B , C ])
    FunctorAxioms : Axioms HQ _
    FunctorAxioms = mkAx HQ FunctorEquation (Sum.rec
      (λ A → inl A , inl A
      , (↑ inl (_ , _ , GCat .id)) -- F ⟪ G .id ⟫
      , PreHCat .id)                 -- H .id
      (λ (A , B , C , f , g) → inl A , inl C
      , (↑ (inl (_ , _ , f ⋆⟨ GCat ⟩ g)))
      , ↑ (inl (_ , _ , f)) ⋆⟨ PreHCat ⟩ (↑ (inl (_ , _ , g)))))

    HCat = PresentedCat HQ FunctorAxioms
    ηHCat = ηP HQ FunctorAxioms
    ηHEq  = ηEq HQ FunctorAxioms

    FFctor : Functor GCat HCat
    FFctor .F-ob = inl
    FFctor .F-hom e = ηHCat .I-hom (inl (_ , _ , e))
    FFctor .F-id = ηHEq (inl _)
    FFctor .F-seq f g = ηHEq (inr (_ , _ , _ , f , g))

    module _ {𝓒 : Categoryᴰ GCat ℓc ℓc'}
             {𝓓 : Categoryᴰ HCat ℓd ℓd'}
             (ıG : Interpᴰ G 𝓒)
             (𝓕 : Functorᴰ FFctor 𝓒 𝓓)
             where

      private
        elimG : Section 𝓒
        elimG = FreeCat.elim G ıG

      record HInterpᴰ : Type (ℓ-max (ℓ-max ℓd ℓd') (ℓ-max ℓg (ℓ-max ℓh ℓh')))
        where
        field
          I-obH : ∀ (A : H .fst) → 𝓓 .ob[_] (inr A)
        I-ob-full : ∀ (A : HOb) → 𝓓 .ob[_] A
        I-ob-full = Sum.elim (λ A → 𝓕 .F-obᴰ (elimG .F-ob A)) I-obH

        field
          I-homH : ∀ e → 𝓓 [ ηP HQ FunctorAxioms .I-hom (inr e) ][
                             I-ob-full (H .snd .dom e)
                           , I-ob-full (H .snd .cod e)
                           ]
      open HInterpᴰ

      module _ (ıH : HInterpᴰ) where
        elim : Section 𝓓
        elim = Presented.elim HQ FunctorAxioms 𝓓 ıHgen satisfies-axioms where
          ıHgen : Interpᴰ HQ _
          ıHgen .I-ob = I-ob-full ıH
          ıHgen .I-hom (inl (_ , _ , e)) = 𝓕 .F-homᴰ (elimG .F-hom e)
          ıHgen .I-hom (inr f) = ıH .I-homH f

          satisfies-axioms : ∀ (eq : FunctorAxioms .equation) → _
          -- F⟪ id A ⟫ ≡ id (F ⟅ A ⟆)
          satisfies-axioms (inl A) = 𝓕 .F-idᴰ
          -- F⟪ f ⋆ g ⟫ ≡ F⟪ f ⟫ ⋆ F⟪ g ⟫
          satisfies-axioms (inr (_ , _ , _ , f , g)) = 𝓕 .F-seqᴰ _ _
