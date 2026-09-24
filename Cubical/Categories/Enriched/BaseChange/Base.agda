{-# OPTIONS --lossy-unification #-}
-- The coherence proofs follow Cruttwell, "Normed Spaces and the Change of Base for Enriched
-- Categories" (2008), §4.1–4.2. In particular his "apply N monoidally" idiom and his interaction
-- lemmas 4.1.1 (unit) and 4.1.3 (associativity).
module Cubical.Categories.Enriched.BaseChange.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Reasoning.Core
import Cubical.Categories.Monoidal.Reasoning as MonRes

module _
  {ℓV ℓV' ℓU ℓU' : Level}
  {V : MonoidalCategory ℓV ℓV'} {U : MonoidalCategory ℓU ℓU'}
  (Fl : LaxMonoidalFunctor V U)
  where

  private
    module V = MonoidalCategory V
    module U = MonoidalCategory U
    open LaxMonoidalFunctor Fl
  open NatTrans
  open Reasoning U.C
  open MonRes U

  {-
   Cruttwell §4.1: applying the lax monoidal F "monoidally".
   F: (V,⊗,I) → (U,•,J)
   For f : I → A,    ε̂ f  := ε ⋆ F(f)      : J → F(A)
   For h : A⊗B → C,  μ̂ h  := μ⟨A,B⟩ ⋆ F(h) : F(A)•F(B) → F(C)
  -}
  ε̂ : ∀ {A : V.ob} → V.C [ V.unit , A ] → U.C [ U.unit , F-ob A ]
  ε̂ f = ε U.⋆ F-hom f

  μ̂ : ∀ {A B C : V.ob}
    → V.C [ A V.⊗ B , C ]
    → U.C [ F-ob A U.⊗ F-ob B , F-ob C ]
  μ̂ {A}{B} h = μ⟨ A , B ⟩ U.⋆ F-hom h


  {-
   Cruttwell Lemma 4.1.1, left unitality
   Given a commuting triangle in V witnessing that some composite
   realises the left unitor of A, applying F monoidally yields the
   corresponding triangle in U for F(A).
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
        -- with F(V.id) absorbed into U.id.
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
