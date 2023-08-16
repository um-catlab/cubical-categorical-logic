-- Free functor between categories generated from base objects and generators
-- this time based on Quiver and freely adding in the functor
{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.Free.Functor.Alt where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum hiding (rec)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Preorder as Preorder hiding (Section)

open import Cubical.Categories.Constructions.Free.Category.Quiver as FreeCat
  hiding (rec)

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓh ℓh' ℓj ℓ : Level

open Category
open Functor
open QuiverOver
module _ (G : Quiver ℓg ℓg') where
  HQuiver : ∀ ℓh ℓh' → Type _
  HQuiver ℓh ℓh' = Σ[ ob ∈ Type ℓh ] QuiverOver (G .fst ⊎ ob) ℓh'

  module _ (H : HQuiver ℓh ℓh') where
    Hob = G .fst ⊎ H .fst
    data HExp : Hob → Hob → Type (((ℓ-max ℓg (ℓ-max ℓg' (ℓ-max ℓh ℓh'))))) where
      ↑_ : ∀ (m : H .snd .mor) → HExp (H .snd .dom m) (H .snd .cod m)
      idₑ : ∀ {A} → HExp A A
      _⋆ₑ_ : ∀ {A B C} → HExp A B → HExp B C → HExp A C
      F⟪_⟫ : ∀ {A B} → Exp G A B → HExp (inl A) (inl B)

      ⋆ₑIdL : ∀ {A B} (e : HExp A B) → idₑ ⋆ₑ e ≡ e
      ⋆ₑIdR : ∀ {A B} (e : HExp A B) → e ⋆ₑ idₑ ≡ e
      ⋆ₑAssoc : ∀ {A B C D} (e : HExp A B)(f : HExp B C)(g : HExp C D)
              → (e ⋆ₑ f) ⋆ₑ g ≡ e ⋆ₑ (f ⋆ₑ g)
      F-idₑ : ∀ {A} → F⟪ idₑ {A = A} ⟫ ≡ idₑ
      F-seqₑ : ∀ {A B C} (f : Exp G A B)(g : Exp G B C)
             → F⟪ f ⋆ₑ g ⟫ ≡ (F⟪ f ⟫ ⋆ₑ F⟪ g ⟫)

      isSetHExp : ∀ {A B} → isSet (HExp A B)

    HCat : Category _ _
    HCat .ob = Hob
    HCat .Hom[_,_] = HExp
    HCat .id = idₑ
    HCat ._⋆_ = _⋆ₑ_
    HCat .⋆IdL = ⋆ₑIdL
    HCat .⋆IdR = ⋆ₑIdR
    HCat .⋆Assoc = ⋆ₑAssoc
    HCat .isSetHom = isSetHExp

    F : Functor (FreeCat G) HCat
    F .F-ob = inl
    F .F-hom = F⟪_⟫
    F .F-id = F-idₑ
    F .F-seq = F-seqₑ

    module _ {𝓒 : Category ℓc ℓc'}{𝓓 : Category ℓd ℓd'} {𝓕 : Functor 𝓒 𝓓} where
      module _ (ıG : Interp G 𝓒) where
        recG = FreeCat.rec _ ıG
        open Interpᴰ

        HInterp : Type _
        HInterp = Σ[ ıHgen ∈ (H .fst → 𝓓 .ob) ]
          let ıHob : Hob → 𝓓 .ob
              ıHob = Sum.rec (λ x → 𝓕 .F-ob (ıG .I-ob x)) ıHgen
          in ∀ (m : H .snd .mor)
            → 𝓓 [ ıHob (H .snd .dom m) , ıHob (H .snd .cod m) ]
        module _ (ıH : HInterp) where
          ıHob : Hob → 𝓓 .ob
          ıHob = Sum.rec (λ x → 𝓕 .F-ob (ıG .I-ob x)) (ıH .fst)

          recH-hom : ∀ {A B} → HExp A B → 𝓓 [ ıHob A , ıHob B ]
          recH-hom (↑ m) = ıH .snd m
          recH-hom idₑ = 𝓓 .id
          recH-hom (e ⋆ₑ e') = recH-hom e ⋆⟨ 𝓓 ⟩ recH-hom e'
          recH-hom F⟪ e ⟫ = 𝓕 ⟪ recG ⟪ e ⟫ ⟫
          recH-hom (⋆ₑIdL e i) = 𝓓 .⋆IdL (recH-hom e) i
          recH-hom (⋆ₑIdR e i) = 𝓓 .⋆IdR (recH-hom e) i
          recH-hom (⋆ₑAssoc e e₁ e₂ i) =
            𝓓 .⋆Assoc (recH-hom e) (recH-hom e₁) (recH-hom e₂) i
          recH-hom (F-idₑ i) = 𝓕 .F-id i
          recH-hom (F-seqₑ f g i) = 𝓕 .F-seq (recG ⟪ f ⟫) (recG ⟪ g ⟫) i
          recH-hom (isSetHExp e e' p q i j) =
            𝓓 .isSetHom (recH-hom e) (recH-hom e')
              (cong recH-hom p) (cong recH-hom q) i j

          rec : Functor HCat 𝓓
          rec .F-ob = ıHob
          rec .F-hom = recH-hom
          rec .F-id = refl
          rec .F-seq = λ f g → refl

          rec-commutes : rec ∘F F ≡ 𝓕 ∘F recG
          rec-commutes = Functor≡ (λ c → refl) (λ f → refl)

    -- TODO: an elim version would have
    -- 𝓒 a cat displayed over (FreeCat G)
    -- 𝓓 a cat displayed over HCat
    -- 𝓕 a functor from 𝓒 to F^* 𝓓
    -- interpretation of G in 𝓒
    -- interpretation of H in 𝓓
    -- and get out a section of 𝓓 that makes the diagram commute

-- self interpretation
module _ {𝓒 : Category ℓc ℓc'} {𝓓 : Category ℓd ℓd'} (𝓕 : Functor 𝓒 𝓓) where
  private
    G = CatQuiver 𝓒
    Hrec : 𝓒 .ob ⊎ 𝓓 .ob → 𝓓 .ob
    Hrec = Sum.rec (𝓕 .F-ob) (λ z → z)
    HGen = Σ[ A ∈ 𝓒 .ob ⊎ 𝓓 .ob ] Σ[ B ∈ 𝓒 .ob ⊎ 𝓓 .ob ] (𝓓 [ Hrec A , Hrec B ])

    H : HQuiver G ℓd (ℓ-max (ℓ-max ℓc ℓd) ℓd')
    H .fst = 𝓓 .ob
    H .snd .mor = HGen
    H .snd .dom e = e .fst
    H .snd .cod e = e .snd .fst

  selfInterp : Functor (HCat G H) 𝓓
  selfInterp = rec G H {𝓕 = 𝓕}
    (record { I-ob = λ c → c ; I-hom = (λ e → e .snd .snd) })
    ((λ z → z) , λ e → e .snd .snd)
