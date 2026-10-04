{-# OPTIONS --lossy-unification #-}
-- The coherence proofs follow Cruttwell, "Normed Spaces and the Change of Base for Enriched
-- Categories" (2008), §4.1–4.2. In particular his "apply N monoidally" idiom and his interaction
-- lemmas 4.1.1 (unit) and 4.1.3 (associativity).
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Functor

module Cubical.Categories.Enriched.BaseChange.Base
  {ℓV ℓV' ℓU ℓU' : Level}
  {V : MonoidalCategory ℓV ℓV'} {U : MonoidalCategory ℓU ℓU'}
  (Fl : LaxMonoidalFunctor V U)
   where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Reasoning.Core
import Cubical.Categories.Monoidal.Reasoning as MonRes

private
  module V = MonoidalCategory V
  module U = MonoidalCategory U
  open LaxMonoidalFunctor Fl
open NatTrans
open Reasoning U.C
open MonRes U

{-
 Cruttwell Lemma 4.1.1, left unitality
 Given a commuting triangle in V witnessing that some composite
 realises the left unitor of A, applying F monoidally yields the
 corresponding triangle in U for F(A).
 Cruttwell leaves implicit that, to instantiate for unitality, you need
 to post-compose with `F-hom V.id ≡ U.id` in the result
-}
lem-411-L : ∀ {A B C : V.ob}
            (f : V.C [ V.unit , B ]) (g : V.C [ A , C ])
            (h : V.C [ B V.⊗ C , A ])
          → V.η⟨ A ⟩ ≡ (f V.⊗ₕ g) V.⋆ h
          → U.η⟨ F-ob A ⟩
            ≡ (ε̂ f U.⊗ₕ F-hom g) U.⋆ μ̂ h
lem-411-L {A}{B}{C} f g h eq =
    U.η⟨ F-ob A ⟩
      -- ηε-law, then left-whisker the (μ-nat with F(eq) glued on the right).
      ≡⟨ sym (ηε-law A)
       ∙ extendˡ (glueTriR (sym (μ .N-hom (f , g)))
                           (sym (cong F-hom eq ∙ F-seq _ _))) ⟩
    ((ε U.⊗ₕ U.id) U.⋆ (F-hom f U.⊗ₕ F-hom g)) U.⋆ μ̂ h
      -- Cruttwell leaves this step implicit
      ≡⟨ cong (U._⋆ μ̂ h) merge₁ˡ ⟩
    (ε̂ f U.⊗ₕ F-hom g) U.⋆ μ̂ h
      ∎

-- Right-unit mirror of Lemma 4.1.1.
lem-411-R : ∀ {A B C : V.ob}
            (f : V.C [ A , B ]) (g : V.C [ V.unit , C ])
            (h : V.C [ B V.⊗ C , A ])
          → V.ρ⟨ A ⟩ ≡ (f V.⊗ₕ g) V.⋆ h
          → U.ρ⟨ F-ob A ⟩
            ≡ (F-hom f U.⊗ₕ ε̂ g) U.⋆ μ̂ h
lem-411-R {A}{B}{C} f g h eq =
    U.ρ⟨ F-ob A ⟩
      ≡⟨ sym (ρε-law A)
       ∙ extendˡ (glueTriR (sym (μ .N-hom (f , g)))
                           (sym (cong F-hom eq ∙ F-seq _ _))) ⟩
    ((U.id U.⊗ₕ ε) U.⋆ (F-hom f U.⊗ₕ F-hom g)) U.⋆ μ̂ h
      ≡⟨ cong (U._⋆ μ̂ h) merge₂ˡ ⟩
    (F-hom f U.⊗ₕ ε̂ g) U.⋆ μ̂ h
      ∎

{-
  Cruttwell Lemma 4.1.3, associativity
  Note that the ⋆Assoc pentagon is mirrored compared to Cruttwell
  bc `α` goes the opposite direction
-}
lem-413 : ∀ {A B C D E F' : V.ob}
          (f : V.C [ A V.⊗ B , D ]) (g : V.C [ B V.⊗ C , E ])
          (h : V.C [ D V.⊗ C , F' ]) (k : V.C [ A V.⊗ E , F' ])
        → (V.α⟨ A , B , C ⟩ V.⋆ (f V.⊗ₕ V.id)) V.⋆ h
          ≡ (V.id V.⊗ₕ g) V.⋆ k
        → (U.α⟨ F-ob A , F-ob B , F-ob C ⟩ U.⋆ (μ̂ f U.⊗ₕ U.id))
            U.⋆ μ̂ h
          ≡ (U.id U.⊗ₕ μ̂ g) U.⋆ μ̂ k
lem-413 {A}{B}{C}{D}{E}{F'} f g h k eq =
  let α    = U.α⟨ F-ob A , F-ob B , F-ob C ⟩
      μab  = μ⟨ A , B ⟩
      μdc  = μ⟨ D , C ⟩
      μbc  = μ⟨ B , C ⟩
      μab-c = μ⟨ A V.⊗ B , C ⟩
      μa-bc = μ⟨ A , B V.⊗ C ⟩
      μae  = μ⟨ A , E ⟩

      -- *left parallelogram*: μ-naturality at (f, V.id),
      -- with Ff• id -> Ff • Fid -> F(f⊗id) (this part is elided by Cruttwell)
      nat-f : (F-hom f U.⊗ₕ U.id) U.⋆ μdc
              ≡ μab-c U.⋆ F-hom (f V.⊗ₕ V.id)
      nat-f = cong (λ z → (F-hom f U.⊗ₕ z) U.⋆ μdc) (sym F-id)
              ∙ μ .N-hom (f , V.id)

      -- *right parallelogram*: μ-naturality at (V.id, g).
      nat-g : (U.id U.⊗ₕ F-hom g) U.⋆ μae
              ≡ μa-bc U.⋆ F-hom (V.id V.⊗ₕ g)
      nat-g = cong (λ z → (z U.⊗ₕ F-hom g) U.⋆ μae) (sym F-id)
              ∙ μ .N-hom (V.id , g)

      -- *bottom pentagon*: F applied to the V-pentagon eq.
      F-eq : F-hom V.α⟨ A , B , C ⟩ U.⋆ (F-hom (f V.⊗ₕ V.id) U.⋆ F-hom h)
           ≡ F-hom (V.id V.⊗ₕ g) U.⋆ F-hom k
      F-eq = cong (F-hom V.α⟨ A , B , C ⟩ U.⋆_) (sym (F-seq _ _))
           ∙ sym (F-seq _ _)
           ∙ cong F-hom (sym (V.⋆Assoc _ _ _) ∙ eq)
           ∙ F-seq _ _
  in
    (α U.⋆ (μ̂ f U.⊗ₕ U.id)) U.⋆ μ̂ h
      -- LEFT: bifunctoriality split of μ̂ f ⊗ U.id, then reassoc.
      ≡⟨ cong (U._⋆ μ̂ h) (pushʳ split₁ˡ) ∙ U.⋆Assoc _ _ _ ⟩
    (α U.⋆ (μab U.⊗ₕ U.id))
      U.⋆ ((F-hom f U.⊗ₕ U.id) U.⋆ (μdc U.⋆ F-hom h))
      -- MIDDLE: paste four Cruttwell regions, each visible as a single cong.
      ≡⟨   cong ((α U.⋆ (μab U.⊗ₕ U.id)) U.⋆_) (extendʳ nat-f)   -- LEFT parallelogram
         ∙ sym (U.⋆Assoc _ _ _)
         ∙ cong (U._⋆ (F-hom (f V.⊗ₕ V.id) U.⋆ F-hom h))
                (αμ-law A B C)                                    -- TOP hexagon
         ∙ U.⋆Assoc _ _ _
         ∙ cong (((U.id U.⊗ₕ μbc) U.⋆ μa-bc) U.⋆_) F-eq           -- BOTTOM pentagon
         ∙ sym (U.⋆Assoc _ _ _)
         ∙ cong (U._⋆ F-hom k) (extendˡ (sym nat-g)) ⟩            -- RIGHT parallelogram
    (((U.id U.⊗ₕ μbc) U.⋆ (U.id U.⊗ₕ F-hom g)) U.⋆ μae) U.⋆ F-hom k
      -- RIGHT: bifunctoriality merge (U.id ⊗ μbc) ⋆ (U.id ⊗ F(g)) = U.id ⊗ μ̂ g, then reassoc.
      ≡⟨ cong (λ z → (z U.⋆ μae) U.⋆ F-hom k) (sym split₂ˡ)
         ∙ U.⋆Assoc _ _ _ ⟩
    (U.id U.⊗ₕ μ̂ g) U.⋆ (μae U.⋆ F-hom k)
      ∎

-- Compatibility of ε̂ with the "pairing-then-H" shape used by the
-- underlying ordinary category.  The structure mirrors UniMath's
-- `change_of_base_enrichment_laws` for `enriched_from_arr`
-- (`UniMath/CategoryTheory/EnrichedCats/Examples/ChangeOfBase.v`):
-- use `η⁻ε-law` (= `mon_functor_linvunitor`), `sqLL` of U.η
-- (= `tensor_linvunitor`), μ-naturality (= `tensor_mon_functor_tensor`),
-- and ⊗-F-seq.
lem-⌜⋆⌝ : ∀ {X Y Z : V.ob}
          (A : V.C [ V.unit , X ]) (B : V.C [ V.unit , Y ])
          (H : V.C [ X V.⊗ Y , Z ])
        → ε̂ (V.η⁻¹⟨ V.unit ⟩ V.⋆ (A V.⊗ₕ B) V.⋆ H)
          ≡ U.η⁻¹⟨ U.unit ⟩ U.⋆ (ε̂ A U.⊗ₕ ε̂ B) U.⋆ μ̂ H
lem-⌜⋆⌝ {X}{Y}{Z} A B H =
    -- Target reshape: convert RHS to canonical form via μ-nat + ⊗-F-seq, then
    -- apply F to the equation `(ε ⋆ F(η⁻¹) ⋆ F(A⊗B)) ⋆ F H ≡ ...`.
    front ∙ cong (U._⋆ F-hom H) rearrange ∙ U.⋆Assoc _ _ _
    ∙ cong (U.η⁻¹⟨ U.unit ⟩ U.⋆_) (U.⋆Assoc _ _ _)
  where
    -- `ε̂ (η⁻¹ ⋆ (A ⊗ B) ⋆ H) = (ε ⋆ F η⁻¹ ⋆ F (A ⊗ B)) ⋆ F H`.
    front :
        ε U.⋆ F-hom (V.η⁻¹⟨ V.unit ⟩ V.⋆ (A V.⊗ₕ B) V.⋆ H)
      ≡ (ε U.⋆ F-hom V.η⁻¹⟨ V.unit ⟩ U.⋆ F-hom (A V.⊗ₕ B)) U.⋆ F-hom H
    front =
        cong (ε U.⋆_) (F-seq _ _)
      ∙ cong (λ q → ε U.⋆ (F-hom V.η⁻¹⟨ V.unit ⟩ U.⋆ q)) (F-seq _ _)
      ∙ cong (ε U.⋆_) (sym (U.⋆Assoc _ _ _))
      ∙ sym (U.⋆Assoc _ _ _)

    -- `ε ⋆ F η⁻¹ ⋆ F (A ⊗ B) ≡ η⁻¹⟨U⟩ ⋆ (ε̂ A ⊗ ε̂ B) ⋆ μ⟨X, Y⟩`.
    rearrange :
        ε U.⋆ F-hom V.η⁻¹⟨ V.unit ⟩ U.⋆ F-hom (A V.⊗ₕ B)
      ≡ U.η⁻¹⟨ U.unit ⟩ U.⋆ (ε̂ A U.⊗ₕ ε̂ B) U.⋆ μ⟨ X , Y ⟩
    rearrange =
        cong (λ q → ε U.⋆ q U.⋆ F-hom (A V.⊗ₕ B)) (sym (η⁻ε-law V.unit))
      ∙ step-sqLL
      ∙ step-merge
      ∙ step-μ-nat
      ∙ step-collect
      where
        sqLL-ε : ε U.⋆ U.η⁻¹⟨ F-ob V.unit ⟩
               ≡ U.η⁻¹⟨ U.unit ⟩ U.⋆ (U.id U.⊗ₕ ε)
        sqLL-ε = NatIso.sqLL U.η {f = ε}

        step-sqLL :
            ε U.⋆ ((U.η⁻¹⟨ F-ob V.unit ⟩ U.⋆ (ε U.⊗ₕ U.id)) U.⋆ μ⟨ V.unit , V.unit ⟩)
              U.⋆ F-hom (A V.⊗ₕ B)
          ≡ U.η⁻¹⟨ U.unit ⟩ U.⋆ (U.id U.⊗ₕ ε) U.⋆ ((ε U.⊗ₕ U.id)
              U.⋆ μ⟨ V.unit , V.unit ⟩ U.⋆ F-hom (A V.⊗ₕ B))
        step-sqLL =
            ε U.⋆ ((U.η⁻¹⟨ F-ob V.unit ⟩ U.⋆ (ε U.⊗ₕ U.id)) U.⋆ μ⟨ V.unit , V.unit ⟩)
              U.⋆ F-hom (A V.⊗ₕ B)
          ≡⟨ cong (λ q → ε U.⋆ q U.⋆ F-hom (A V.⊗ₕ B)) (U.⋆Assoc _ _ _) ⟩
            ε U.⋆ (U.η⁻¹⟨ F-ob V.unit ⟩ U.⋆ ((ε U.⊗ₕ U.id) U.⋆ μ⟨ V.unit , V.unit ⟩))
              U.⋆ F-hom (A V.⊗ₕ B)
          ≡⟨ cong (ε U.⋆_) (U.⋆Assoc _ _ _) ⟩
            ε U.⋆ (U.η⁻¹⟨ F-ob V.unit ⟩
              U.⋆ ((ε U.⊗ₕ U.id) U.⋆ μ⟨ V.unit , V.unit ⟩) U.⋆ F-hom (A V.⊗ₕ B))
          ≡⟨ sym (U.⋆Assoc _ _ _) ⟩
            (ε U.⋆ U.η⁻¹⟨ F-ob V.unit ⟩)
              U.⋆ ((ε U.⊗ₕ U.id) U.⋆ μ⟨ V.unit , V.unit ⟩) U.⋆ F-hom (A V.⊗ₕ B)
          ≡⟨ cong (U._⋆ (((ε U.⊗ₕ U.id) U.⋆ μ⟨ V.unit , V.unit ⟩)
                           U.⋆ F-hom (A V.⊗ₕ B)))
                  sqLL-ε ⟩
            (U.η⁻¹⟨ U.unit ⟩ U.⋆ (U.id U.⊗ₕ ε))
              U.⋆ ((ε U.⊗ₕ U.id) U.⋆ μ⟨ V.unit , V.unit ⟩) U.⋆ F-hom (A V.⊗ₕ B)
          ≡⟨ U.⋆Assoc _ _ _ ⟩
            U.η⁻¹⟨ U.unit ⟩ U.⋆ ((U.id U.⊗ₕ ε)
              U.⋆ ((ε U.⊗ₕ U.id) U.⋆ μ⟨ V.unit , V.unit ⟩) U.⋆ F-hom (A V.⊗ₕ B))
          ≡⟨ cong (λ q → U.η⁻¹⟨ U.unit ⟩ U.⋆ ((U.id U.⊗ₕ ε) U.⋆ q))
                  (U.⋆Assoc _ _ _) ⟩
            U.η⁻¹⟨ U.unit ⟩ U.⋆ (U.id U.⊗ₕ ε) U.⋆ ((ε U.⊗ₕ U.id)
              U.⋆ μ⟨ V.unit , V.unit ⟩ U.⋆ F-hom (A V.⊗ₕ B)) ∎

        step-merge :
            U.η⁻¹⟨ U.unit ⟩ U.⋆ (U.id U.⊗ₕ ε) U.⋆ ((ε U.⊗ₕ U.id)
              U.⋆ μ⟨ V.unit , V.unit ⟩ U.⋆ F-hom (A V.⊗ₕ B))
          ≡ U.η⁻¹⟨ U.unit ⟩ U.⋆ (ε U.⊗ₕ ε) U.⋆
              (μ⟨ V.unit , V.unit ⟩ U.⋆ F-hom (A V.⊗ₕ B))
        step-merge =
            cong (U.η⁻¹⟨ U.unit ⟩ U.⋆_)
              (  sym (U.⋆Assoc _ _ _)
              ∙ cong (U._⋆ (μ⟨ V.unit , V.unit ⟩ U.⋆ F-hom (A V.⊗ₕ B)))
                  (  sym (U.─⊗─ .Functor.F-seq (U.id , ε) (ε , U.id))
                  ∙ cong₂ U._⊗ₕ_ (U.⋆IdL _) (U.⋆IdR _)))

        step-μ-nat :
            U.η⁻¹⟨ U.unit ⟩ U.⋆ (ε U.⊗ₕ ε) U.⋆
              (μ⟨ V.unit , V.unit ⟩ U.⋆ F-hom (A V.⊗ₕ B))
          ≡ U.η⁻¹⟨ U.unit ⟩ U.⋆ (ε U.⊗ₕ ε) U.⋆
              ((F-hom A U.⊗ₕ F-hom B) U.⋆ μ⟨ X , Y ⟩)
        step-μ-nat =
          cong (λ q → U.η⁻¹⟨ U.unit ⟩ U.⋆ (ε U.⊗ₕ ε) U.⋆ q) (sym (μ .N-hom (A , B)))

        step-collect :
            U.η⁻¹⟨ U.unit ⟩ U.⋆ (ε U.⊗ₕ ε) U.⋆
              ((F-hom A U.⊗ₕ F-hom B) U.⋆ μ⟨ X , Y ⟩)
          ≡ U.η⁻¹⟨ U.unit ⟩ U.⋆ (ε̂ A U.⊗ₕ ε̂ B) U.⋆ μ⟨ X , Y ⟩
        step-collect =
            cong (U.η⁻¹⟨ U.unit ⟩ U.⋆_)
              (  sym (U.⋆Assoc _ _ _)
              ∙ cong (U._⋆ μ⟨ X , Y ⟩)
                  (sym (U.─⊗─ .Functor.F-seq (ε , ε) (F-hom A , F-hom B))))

module _ {ℓC : Level} (C : EnrichedCategory V ℓC) where
  private module C = EnrichedCategory C
  open EnrichedCategory

  BaseChange : EnrichedCategory U ℓC
  BaseChange .ob = C.ob
  BaseChange .Hom[_,_] x y = F-ob C.Hom[ x , y ]
  BaseChange .id = ε̂ C.id
  BaseChange .seq x y z = μ̂ (C.seq x y z)
  BaseChange .⋆IdL x y =
    lem-411-L C.id V.id (C.seq x x y) (C.⋆IdL x y)
    ∙ cong (λ k → (ε̂ C.id U.⊗ₕ k) U.⋆ μ̂ (C.seq x x y)) F-id
  BaseChange .⋆IdR x y =
    lem-411-R V.id C.id (C.seq x y y) (C.⋆IdR x y)
    ∙ cong (λ k → (k U.⊗ₕ ε̂ C.id) U.⋆ μ̂ (C.seq x y y)) F-id
  BaseChange .⋆Assoc x y z w =
    sym (U.⋆Assoc _ _ _)
    ∙ lem-413 (C.seq x y z) (C.seq y z w) (C.seq x z w) (C.seq x y w)
        (V.⋆Assoc _ _ _ ∙ C.⋆Assoc x y z w)
