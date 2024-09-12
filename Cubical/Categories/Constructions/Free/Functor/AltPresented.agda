-- This module defines the free category H equipped with a functor
-- from a given category 𝓒
{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.Free.Functor.AltPresented where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum hiding (rec; elim)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Functor.Base

open import Cubical.Data.Quiver.Base

open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Constructions.Presented as Presented
open import Cubical.Categories.Constructions.BinProduct as BinProduct
open import Cubical.Categories.Displayed.Constructions.Weaken as Weaken
open import Cubical.Categories.Displayed.Constructions.Reindex.Base as Reindex
open import Cubical.Categories.Displayed.Instances.Path as PathC
open import Cubical.Categories.Constructions.Free.Category.Quiver as FreeCat
  hiding (rec; elim; elimLocal)

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓh ℓh' ℓj ℓ ℓcᴰ ℓcᴰ' ℓdᴰ ℓdᴰ' ℓe ℓe' : Level

open Category
open Categoryᴰ
open Functor
open Functorᴰ
open Section
open QuiverOver
open HetQG
open Axioms

module _ (𝓒 : Category ℓc ℓc') where
  HQuiver : ∀ ℓh ℓh' → Type _
  HQuiver ℓh ℓh' = Σ[ Hgen ∈ Type ℓh ] QuiverOver (𝓒 .ob ⊎ Hgen) ℓh'

  module FreeFunctor (H : HQuiver ℓh ℓh') where
    private
      HOb = (𝓒 .ob ⊎ H .fst)

    HQ : Quiver (ℓ-max ℓc ℓh) (ℓ-max (ℓ-max ℓc ℓc') ℓh')
    HQ .fst = HOb
    HQ .snd .mor = Cat→Quiver 𝓒 .snd .mor ⊎ H .snd .mor
    HQ .snd .dom (inl (A , B , _)) = inl A
    HQ .snd .cod (inl (A , B , _)) = inl B
    HQ .snd .dom (inr g) = H .snd .dom g
    HQ .snd .cod (inr g) = H .snd .cod g

    PreHCat = FreeCat HQ
    ηPre = η HQ

    FunctorEquation =
    --   F⟪id⟫≡id
      𝓒 .ob
    --   F⟪⋆⟫≡⋆F⟪⟫
      ⊎ (Σ[ A ∈ 𝓒 .ob ] Σ[ B ∈ 𝓒 .ob ] Σ[ C ∈ 𝓒 .ob ]
        𝓒 [ A , B ] × 𝓒 [ B , C ])
    FunctorAxioms : Axioms PreHCat _
    FunctorAxioms = mkAx PreHCat FunctorEquation (Sum.rec
      (λ A → inl A , inl A
      , (↑ inl (_ , _ , 𝓒 .id)) -- F ⟪ G .id ⟫
      , PreHCat .id)                 -- H .id
      (λ (A , B , C , f , g) → inl A , inl C
      , (↑ (inl (_ , _ , f ⋆⟨ 𝓒 ⟩ g)))
      , ↑ (inl (_ , _ , f)) ⋆⟨ PreHCat ⟩ (↑ (inl (_ , _ , g)))))

    module PresentH = QuoByAx PreHCat FunctorAxioms
    HCat = PresentH.PresentedCat
    moduloAx = PresentH.ToPresented
    ηHEq  = PresentH.ηEq

    FreeFunctor : Functor 𝓒 HCat
    FreeFunctor .F-ob = inl
    FreeFunctor .F-hom e = moduloAx .F-hom (ηPre <$g> inl (_ , _ , e))
    FreeFunctor .F-id = ηHEq (inl _)
    FreeFunctor .F-seq f g = ηHEq (inr (_ , _ , _ , f , g))

    module _ {𝓓ᴰ : Categoryᴰ HCat ℓdᴰ ℓdᴰ'}
             (s : Section FreeFunctor 𝓓ᴰ)
             (ıOb : ∀ (A : H .fst) → 𝓓ᴰ .ob[_] (inr A))
             where
      private
        ıOb' : ∀ (A : HOb) → 𝓓ᴰ .ob[_] A
        ıOb' = Sum.elim (s .F-obᴰ) ıOb
      module _ (ıHom : ∀ e
             → 𝓓ᴰ [ moduloAx .F-hom (ηPre <$g> inr e) ][
                    ıOb' (H .snd .dom e)
                  , ıOb' (H .snd .cod e) ]) where
        open Section
        open HetSection
        elim : GlobalSection 𝓓ᴰ
        elim = PresentH.elim 𝓓ᴰ (FreeCat.elim HQ _ ıHgen) satisfies-axioms
          where
          ıHgen : Interpᴰ HQ _ _
          ıHgen ._$gᴰ_ = ıOb'
          ıHgen <$g>ᴰ inl (_ , _ , e) = s .F-homᴰ e
          ıHgen <$g>ᴰ inr f = ıHom f

          satisfies-axioms : ∀ (eq : FunctorAxioms .equation) → _
          -- F⟪ id A ⟫ ≡ id (F ⟅ A ⟆)
          satisfies-axioms (inl A) = s .F-idᴰ
          -- F⟪ f ⋆ g ⟫ ≡ F⟪ f ⟫ ⋆ F⟪ g ⟫
          satisfies-axioms (inr (_ , _ , _ , f , g)) = s .F-seqᴰ _ _

    -- elimination principle for Local Sections
    module _ {𝓔 : Category ℓe ℓe'}
             {𝓕 : Functor HCat 𝓔}
             {𝓓ᴰ : Categoryᴰ 𝓔 ℓdᴰ ℓdᴰ'}
             (s : Section (𝓕 ∘F FreeFunctor) 𝓓ᴰ)
             (ıOb : (A : H .fst) → 𝓓ᴰ .ob[_] (𝓕 .F-ob (inr A)))
           where
      private
        ıOb' : ∀ (A : HOb) → 𝓓ᴰ .ob[_] (𝓕 .F-ob A)
        ıOb' = Sum.elim (s .F-obᴰ) ıOb
      module _ (ıHom : ∀ e
             → 𝓓ᴰ [ 𝓕 .F-hom (moduloAx .F-hom (ηPre <$g> inr e)) ][
                    ıOb' (H .snd .dom e)
                  , ıOb' (H .snd .cod e) ]) where
        elimLocal : Section 𝓕 𝓓ᴰ
        elimLocal = GlobalSectionReindex→Section _ _
          (elim (Reindex.introS _ s) ıOb ıHom)
    module _ {𝓔 : Category ℓe ℓe'}
             (𝓕 : Functor 𝓒 𝓔)
             (ıOb : H .fst → 𝓔 .ob)
           where
      private
        ıOb' : ∀ (A : HOb) → 𝓔 .ob
        ıOb' = Sum.elim (𝓕 .F-ob) ıOb
      module _ (ıHom : ∀ e → 𝓔 [ ıOb' (H .snd .dom e) , ıOb' (H .snd .cod e) ])
               where
        rec : Functor HCat 𝓔
        rec = Weaken.introS⁻ {F = Id}
          (elim (Weaken.introS FreeFunctor 𝓕) ıOb ıHom)

    module _ {𝓔 : Category ℓe ℓe'}
             (F G : Functor HCat 𝓔)
             (agree-on-𝓒 : Section ((F ,F G) ∘F FreeFunctor) (PathC 𝓔))
             (agree-on-objects : ∀ (A : H .fst)
               → F-ob F (inr A) ≡ F-ob G (inr A))
           where
      private
          ıOb' : ∀ (A : HOb) → F ⟅ A ⟆ ≡ G ⟅ A ⟆
          ıOb' = Sum.elim (agree-on-𝓒 .F-obᴰ) agree-on-objects
      module _ (agree-on-morphisms : ∀ e →
                 PathP ((λ i → 𝓔 [ ıOb' (H .snd .dom e) i
                                 , ıOb' (H .snd .cod e) i ]))
                   (F ⟪ moduloAx .F-hom (ηPre <$g> inr e) ⟫)
                   (G ⟪ moduloAx .F-hom (ηPre <$g> inr e) ⟫))
        where
        extensionalityF : F ≡ G
        extensionalityF = PathC.PathReflection
          (elimLocal agree-on-𝓒 agree-on-objects agree-on-morphisms)

    -- todo: extensionality for (local) sections

module CoUnit {C : Category ℓc ℓc'} {D : Category ℓd ℓd'} (F : Functor C D)
  where

  DGenOb = C .ob ⊎ D .ob

  asDob : DGenOb → D .ob
  asDob = Sum.rec (F .F-ob) λ z → z

  DGen = Σ[ A ∈ DGenOb ] Σ[ B ∈ DGenOb ] (D [ asDob A , asDob B ])

  DQuiver : HQuiver C _ _
  DQuiver .fst = D .ob
  DQuiver .snd .mor = DGen
  DQuiver .snd .dom (A , B , f) = A
  DQuiver .snd .cod (A , B , f) = B

  open FreeFunctor (FreeCat (Cat→Quiver C)) DQuiver public
