{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Enriched.Enrichment.HomFunctor where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation using (NatTrans ; NatIso ; symNatIso)
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Properties using (ρ⟨⊗⟩ ; ρ⁻¹⟨unit⟩≡η⁻¹⟨unit⟩)
open import Cubical.Categories.Reasoning.Core
open import Cubical.Categories.Enriched.Enrichment.Base
open import Cubical.Categories.Enriched.Enrichment.Opposite

open Functor

private
  variable
    ℓV ℓV' ℓC ℓC' : Level

private
  module _ (V : MonoidalCategory ℓV ℓV') where
    module M = MonoidalCategory V
    open Reasoning M.C
    open import Cubical.Categories.Monoidal.Reasoning V

    α-nat : ∀ {x x' y y' z z'} (f : M.Hom[ x , x' ]) (g : M.Hom[ y , y' ]) (h : M.Hom[ z , z' ])
      → (f M.⊗ₕ (g M.⊗ₕ h)) M.⋆ M.α⟨ x' , y' , z' ⟩ ≡ M.α⟨ x , y , z ⟩ M.⋆ ((f M.⊗ₕ g) M.⊗ₕ h)
    α-nat f g h = M.α .NatIso.trans .NatTrans.N-hom (f , g , h)

    ρ⁻¹-nat : ∀ {x y} (f : M.Hom[ x , y ]) → f M.⋆ M.ρ⁻¹⟨ y ⟩ ≡ M.ρ⁻¹⟨ x ⟩ M.⋆ (f M.⊗ₕ M.id)
    ρ⁻¹-nat f = symNatIso M.ρ .NatIso.trans .NatTrans.N-hom f

    unitor-collapse : ∀ x y
      → (M.id {x} M.⊗ₕ M.η⁻¹⟨ y ⟩) M.⋆ M.α⟨ x , M.unit , y ⟩
        ≡ M.ρ⁻¹⟨ x ⟩ M.⊗ₕ M.id {y}
    unitor-collapse x y =
      (M.id M.⊗ₕ M.η⁻¹⟨ y ⟩) M.⋆ M.α⟨ x , M.unit , y ⟩
        ≡⟨ introʳ k ⟩
      ((M.id M.⊗ₕ M.η⁻¹⟨ y ⟩) M.⋆ M.α⟨ x , M.unit , y ⟩)
        M.⋆ ((M.ρ⟨ x ⟩ M.⊗ₕ M.id) M.⋆ (M.ρ⁻¹⟨ x ⟩ M.⊗ₕ M.id))
        ≡⟨ M.⋆Assoc _ _ _
         ∙ cong ((M.id M.⊗ₕ M.η⁻¹⟨ y ⟩) M.⋆_) (pullˡ (M.triangle x y)) ⟩
      (M.id M.⊗ₕ M.η⁻¹⟨ y ⟩) M.⋆ ((M.id M.⊗ₕ M.η⟨ y ⟩) M.⋆ (M.ρ⁻¹⟨ x ⟩ M.⊗ₕ M.id))
        ≡⟨ pullˡ (merge₂ʳ ∙ cong (M.id M.⊗ₕ_) (M.η .NatIso.nIso y .isIso.sec) ∙ M.─⊗─ .F-id) ⟩
      M.id M.⋆ (M.ρ⁻¹⟨ x ⟩ M.⊗ₕ M.id)
        ≡⟨ M.⋆IdL _ ⟩
      M.ρ⁻¹⟨ x ⟩ M.⊗ₕ M.id ∎
      where
      k : (M.ρ⟨ x ⟩ M.⊗ₕ M.id {y}) M.⋆ (M.ρ⁻¹⟨ x ⟩ M.⊗ₕ M.id) ≡ M.id
      k = sym (M.─⊗─ .F-seq _ _)
        ∙ cong₂ M._⊗ₕ_ (M.ρ .NatIso.nIso x .isIso.ret) (M.⋆IdL _)
        ∙ M.─⊗─ .F-id

    ρ⁻¹-collapse : ∀ x y
      → (M.id {x} M.⊗ₕ M.ρ⁻¹⟨ y ⟩) M.⋆ M.α⟨ x , y , M.unit ⟩ ≡ M.ρ⁻¹⟨ x M.⊗ y ⟩
    ρ⁻¹-collapse x y =
      (M.id M.⊗ₕ M.ρ⁻¹⟨ y ⟩) M.⋆ M.α⟨ x , y , M.unit ⟩
        ≡⟨ introʳ (M.ρ .NatIso.nIso (x M.⊗ y) .isIso.ret) ⟩
      ((M.id M.⊗ₕ M.ρ⁻¹⟨ y ⟩) M.⋆ M.α⟨ x , y , M.unit ⟩) M.⋆ (M.ρ⟨ x M.⊗ y ⟩ M.⋆ M.ρ⁻¹⟨ x M.⊗ y ⟩)
        ≡⟨ M.⋆Assoc _ _ _ ∙ cong ((M.id M.⊗ₕ M.ρ⁻¹⟨ y ⟩) M.⋆_) (pullˡ (ρ⟨⊗⟩ V)) ⟩
      (M.id M.⊗ₕ M.ρ⁻¹⟨ y ⟩) M.⋆ ((M.id M.⊗ₕ M.ρ⟨ y ⟩) M.⋆ M.ρ⁻¹⟨ x M.⊗ y ⟩)
        ≡⟨ pullˡ (merge₂ʳ ∙ cong (M.id M.⊗ₕ_) (M.ρ .NatIso.nIso y .isIso.sec) ∙ M.─⊗─ .F-id) ⟩
      M.id M.⋆ M.ρ⁻¹⟨ x M.⊗ y ⟩
        ≡⟨ M.⋆IdL _ ⟩
      M.ρ⁻¹⟨ x M.⊗ y ⟩ ∎

    interchange : ∀ {a b c d d'} (f : M.Hom[ a M.⊗ b , c ]) (g : M.Hom[ d , d' ])
      → ((M.id {a} M.⊗ₕ M.id {b}) M.⊗ₕ g) M.⋆ (f M.⊗ₕ M.id) ≡ (f M.⊗ₕ M.id) M.⋆ (M.id M.⊗ₕ g)
    interchange f g =
      sym ⊗-distrib-over-⋆
      ∙ cong₂ M._⊗ₕ_ (cong (M._⋆ f) ⊗-id ∙ M.⋆IdL f ∙ sym (M.⋆IdR f)) (M.⋆IdR g ∙ sym (M.⋆IdL g))
      ∙ ⊗-distrib-over-⋆

module _ {V : MonoidalCategory ℓV ℓV'} {C : Category ℓC ℓC'} (ℰ : Enrichment C V) where
  private
    module V = MonoidalCategory V
    module C = Category C
    module ℰ = Enrichment ℰ
  open Reasoning V.C
  open import Cubical.Categories.Monoidal.Reasoning V

  module _ (W : C.ob) where
    post : ∀ {X Y} → C [ X , Y ] → V.Hom[ ℰ.VE[ W , X ] , ℰ.VE[ W , Y ] ]
    post f = V.ρ⁻¹⟨ _ ⟩ V.⋆ ((V.id V.⊗ₕ ℰ.⌜ f ⌝) V.⋆ ℰ.seq _ _ _)

    Hom[_,-] : Functor C V.C
    Hom[_,-] .Functor.F-ob X = ℰ.VE[ W , X ]
    Hom[_,-] .Functor.F-hom = post
    Hom[_,-] .Functor.F-id {X} =
        cong (λ m → V.ρ⁻¹⟨ _ ⟩ V.⋆ ((V.id V.⊗ₕ m) V.⋆ ℰ.seq _ _ _)) ℰ.⌜id⌝
      ∙ cong (V.ρ⁻¹⟨ _ ⟩ V.⋆_) (sym (ℰ.⋆IdR W X))
      ∙ V.ρ .NatIso.nIso _ .isIso.sec
    Hom[_,-] .Functor.F-seq {X} {Y} {Z} f g = lhs ∙ sym rhs
      where
      N = V.ρ⁻¹⟨ _ ⟩ V.⋆ (V.ρ⁻¹⟨ _ ⟩ V.⋆ (((V.id V.⊗ₕ ℰ.⌜ f ⌝) V.⊗ₕ ℰ.⌜ g ⌝)
            V.⋆ ((ℰ.seq W X Y V.⊗ₕ V.id) V.⋆ ℰ.seq W Y Z)))

      lhs : post (f C.⋆ g) ≡ N
      lhs =
        V.ρ⁻¹⟨ _ ⟩ V.⋆ ((V.id V.⊗ₕ ℰ.⌜ f C.⋆ g ⌝) V.⋆ ℰ.seq W X Z)
          ≡⟨ cong (λ m → V.ρ⁻¹⟨ _ ⟩ V.⋆ ((V.id V.⊗ₕ m) V.⋆ ℰ.seq W X Z)) (ℰ.⌜⋆⌝ f g) ⟩
        V.ρ⁻¹⟨ _ ⟩ V.⋆ ((V.id V.⊗ₕ (V.η⁻¹⟨ V.unit ⟩ V.⋆ ((ℰ.⌜ f ⌝ V.⊗ₕ ℰ.⌜ g ⌝) V.⋆ ℰ.seq X Y Z)))
          V.⋆ ℰ.seq W X Z)
          ≡⟨ cong (λ m → V.ρ⁻¹⟨ _ ⟩ V.⋆ (m V.⋆ ℰ.seq W X Z)) (split₂ʳ ∙ cong ((V.id V.⊗ₕ V.η⁻¹⟨ V.unit ⟩) V.⋆_) split₂ʳ) ⟩
        V.ρ⁻¹⟨ _ ⟩ V.⋆ (((V.id V.⊗ₕ V.η⁻¹⟨ V.unit ⟩)
          V.⋆ ((V.id V.⊗ₕ (ℰ.⌜ f ⌝ V.⊗ₕ ℰ.⌜ g ⌝)) V.⋆ (V.id V.⊗ₕ ℰ.seq X Y Z)))
          V.⋆ ℰ.seq W X Z)
          ≡⟨ cong (V.ρ⁻¹⟨ _ ⟩ V.⋆_)
               (V.⋆Assoc _ _ _
               ∙ cong ((V.id V.⊗ₕ V.η⁻¹⟨ V.unit ⟩) V.⋆_)
                   (V.⋆Assoc _ _ _
                   ∙ cong ((V.id V.⊗ₕ (ℰ.⌜ f ⌝ V.⊗ₕ ℰ.⌜ g ⌝)) V.⋆_) (sym (ℰ.⋆Assoc W X Y Z)))) ⟩
        V.ρ⁻¹⟨ _ ⟩ V.⋆ ((V.id V.⊗ₕ V.η⁻¹⟨ V.unit ⟩)
          V.⋆ ((V.id V.⊗ₕ (ℰ.⌜ f ⌝ V.⊗ₕ ℰ.⌜ g ⌝))
          V.⋆ (V.α⟨ _ , _ , _ ⟩ V.⋆ ((ℰ.seq W X Y V.⊗ₕ V.id) V.⋆ ℰ.seq W Y Z))))
          ≡⟨ cong (λ m → V.ρ⁻¹⟨ _ ⟩ V.⋆ ((V.id V.⊗ₕ V.η⁻¹⟨ V.unit ⟩) V.⋆ m))
               (extendʳ (α-nat V V.id ℰ.⌜ f ⌝ ℰ.⌜ g ⌝)) ⟩
        V.ρ⁻¹⟨ _ ⟩ V.⋆ ((V.id V.⊗ₕ V.η⁻¹⟨ V.unit ⟩)
          V.⋆ (V.α⟨ _ , _ , _ ⟩ V.⋆ (((V.id V.⊗ₕ ℰ.⌜ f ⌝) V.⊗ₕ ℰ.⌜ g ⌝)
          V.⋆ ((ℰ.seq W X Y V.⊗ₕ V.id) V.⋆ ℰ.seq W Y Z))))
          ≡⟨ cong (V.ρ⁻¹⟨ _ ⟩ V.⋆_) (pullˡ (unitor-collapse V _ _)) ⟩
        V.ρ⁻¹⟨ _ ⟩ V.⋆ ((V.ρ⁻¹⟨ _ ⟩ V.⊗ₕ V.id) V.⋆ (((V.id V.⊗ₕ ℰ.⌜ f ⌝) V.⊗ₕ ℰ.⌜ g ⌝)
          V.⋆ ((ℰ.seq W X Y V.⊗ₕ V.id) V.⋆ ℰ.seq W Y Z)))
          ≡⟨ pullˡ (sym (ρ⁻¹-nat V V.ρ⁻¹⟨ _ ⟩)) ∙ V.⋆Assoc _ _ _ ⟩
        N ∎

      rhs : post f V.⋆ post g ≡ N
      rhs =
          V.⋆Assoc _ _ _
        ∙ cong (V.ρ⁻¹⟨ _ ⟩ V.⋆_)
            ( extendʳ (ρ⁻¹-nat V _)
            ∙ cong (V.ρ⁻¹⟨ _ ⟩ V.⋆_) (pullˡ (sym ⊗-distrib-over-⋆ ∙ cong₂ V._⊗ₕ_ (V.⋆IdR _) (V.⋆IdL _) ∙ split₁ʳ)))
        ∙ cong (λ m → V.ρ⁻¹⟨ _ ⟩ V.⋆ (V.ρ⁻¹⟨ _ ⟩ V.⋆ m)) (V.⋆Assoc _ _ _)


  post-β : ∀ {W X Y} (g : C [ W , X ]) (f : C [ X , Y ])
    → ℰ.⌜ g ⌝ V.⋆ post W f ≡ ℰ.⌜ g C.⋆ f ⌝
  post-β {W} {X} {Y} g f =
      sym (V.⋆Assoc _ _ _)
    ∙ cong (V._⋆ ((V.id V.⊗ₕ ℰ.⌜ f ⌝) V.⋆ ℰ.seq W X Y)) (ρ⁻¹-nat V ℰ.⌜ g ⌝)
    ∙ V.⋆Assoc _ _ _
    ∙ cong (V.ρ⁻¹⟨ V.unit ⟩ V.⋆_) (pullˡ (merge₁ˡ ∙ cong (V._⊗ₕ ℰ.⌜ f ⌝) (V.⋆IdR _)))
    ∙ cong (V._⋆ ((ℰ.⌜ g ⌝ V.⊗ₕ ℰ.⌜ f ⌝) V.⋆ ℰ.seq _ _ _)) (ρ⁻¹⟨unit⟩≡η⁻¹⟨unit⟩ V)
    ∙ sym (ℰ.⌜⋆⌝ g f)

  seq-post : ∀ {W X Y Y'} (f : C [ Y , Y' ])
    → ℰ.seq W X Y V.⋆ post W f ≡ (V.id V.⊗ₕ post X f) V.⋆ ℰ.seq W X Y'
  seq-post {W} {X} {Y} {Y'} f = sym (
    (V.id V.⊗ₕ (V.ρ⁻¹⟨ _ ⟩ V.⋆ ((V.id V.⊗ₕ ℰ.⌜ f ⌝) V.⋆ ℰ.seq X Y Y'))) V.⋆ ℰ.seq W X Y'
      ≡⟨ cong (V._⋆ ℰ.seq W X Y') (split₂ʳ ∙ cong ((V.id V.⊗ₕ V.ρ⁻¹⟨ _ ⟩) V.⋆_) split₂ʳ)
       ∙ V.⋆Assoc _ _ _
       ∙ cong ((V.id V.⊗ₕ V.ρ⁻¹⟨ _ ⟩) V.⋆_)
           (V.⋆Assoc _ _ _
           ∙ cong ((V.id V.⊗ₕ (V.id V.⊗ₕ ℰ.⌜ f ⌝)) V.⋆_) (sym (ℰ.⋆Assoc W X Y Y'))) ⟩
    (V.id V.⊗ₕ V.ρ⁻¹⟨ _ ⟩) V.⋆ ((V.id V.⊗ₕ (V.id V.⊗ₕ ℰ.⌜ f ⌝))
      V.⋆ (V.α⟨ _ , _ , _ ⟩ V.⋆ ((ℰ.seq W X Y V.⊗ₕ V.id) V.⋆ ℰ.seq W Y Y')))
      ≡⟨ cong ((V.id V.⊗ₕ V.ρ⁻¹⟨ _ ⟩) V.⋆_) (extendʳ (α-nat V V.id V.id ℰ.⌜ f ⌝))
       ∙ pullˡ (ρ⁻¹-collapse V _ _) ⟩
    V.ρ⁻¹⟨ _ ⟩ V.⋆ (((V.id V.⊗ₕ V.id) V.⊗ₕ ℰ.⌜ f ⌝) V.⋆ ((ℰ.seq W X Y V.⊗ₕ V.id) V.⋆ ℰ.seq W Y Y'))
      ≡⟨ cong (V.ρ⁻¹⟨ _ ⟩ V.⋆_) (pullˡ (interchange V (ℰ.seq W X Y) ℰ.⌜ f ⌝) ∙ V.⋆Assoc _ _ _) ⟩
    V.ρ⁻¹⟨ _ ⟩ V.⋆ ((ℰ.seq W X Y V.⊗ₕ V.id) V.⋆ ((V.id V.⊗ₕ ℰ.⌜ f ⌝) V.⋆ ℰ.seq W Y Y'))
      ≡⟨ pullˡ (sym (ρ⁻¹-nat V (ℰ.seq W X Y))) ∙ V.⋆Assoc _ _ _ ⟩
    ℰ.seq W X Y V.⋆ post W f ∎)

module _ {V : MonoidalCategory ℓV ℓV'} {C : Category ℓC ℓC'} (ℰ : Enrichment C V) where
  private
    module V = MonoidalCategory V
    module C = Category C
    module ℰ = Enrichment ℰ
  open Reasoning V.C
  open import Cubical.Categories.Monoidal.Reasoning V

  Hom[-,_] : C.ob → Functor (C ^op) V.C
  Hom[-,_] X = Hom[_,-] (ℰ ^opᴱ) X

  seq-extranatural : ∀ {W U' U X} (f : C [ U' , U ])
    → (V.id V.⊗ₕ Hom[-,_] X ⟪ f ⟫) V.⋆ ℰ.seq W U' X
      ≡ (Hom[_,-] ℰ W ⟪ f ⟫ V.⊗ₕ V.id) V.⋆ ℰ.seq W U X
  seq-extranatural {W} {U'} {U} {X} f =
    (V.id V.⊗ₕ (V.η⁻¹⟨ _ ⟩ V.⋆ ((ℰ.⌜ f ⌝ V.⊗ₕ V.id) V.⋆ ℰ.seq U' U X))) V.⋆ ℰ.seq W U' X
      ≡⟨ cong (V._⋆ ℰ.seq W U' X) (split₂ʳ ∙ cong ((V.id V.⊗ₕ V.η⁻¹⟨ _ ⟩) V.⋆_) split₂ʳ)
       ∙ V.⋆Assoc _ _ _
       ∙ cong ((V.id V.⊗ₕ V.η⁻¹⟨ _ ⟩) V.⋆_)
           (V.⋆Assoc _ _ _
           ∙ cong ((V.id V.⊗ₕ (ℰ.⌜ f ⌝ V.⊗ₕ V.id)) V.⋆_) (sym (ℰ.⋆Assoc W U' U X))) ⟩
    (V.id V.⊗ₕ V.η⁻¹⟨ _ ⟩) V.⋆ ((V.id V.⊗ₕ (ℰ.⌜ f ⌝ V.⊗ₕ V.id))
      V.⋆ (V.α⟨ _ , _ , _ ⟩ V.⋆ ((ℰ.seq W U' U V.⊗ₕ V.id) V.⋆ ℰ.seq W U X)))
      ≡⟨ cong ((V.id V.⊗ₕ V.η⁻¹⟨ _ ⟩) V.⋆_) (extendʳ (α-nat V V.id ℰ.⌜ f ⌝ V.id))
       ∙ pullˡ (unitor-collapse V _ _) ⟩
    (V.ρ⁻¹⟨ _ ⟩ V.⊗ₕ V.id) V.⋆ (((V.id V.⊗ₕ ℰ.⌜ f ⌝) V.⊗ₕ V.id)
      V.⋆ ((ℰ.seq W U' U V.⊗ₕ V.id) V.⋆ ℰ.seq W U X))
      ≡⟨ sym (cong (V._⋆ ℰ.seq W U X) (split₁ˡ ∙ cong ((V.ρ⁻¹⟨ _ ⟩ V.⊗ₕ V.id) V.⋆_) split₁ˡ)
             ∙ V.⋆Assoc _ _ _ ∙ cong ((V.ρ⁻¹⟨ _ ⟩ V.⊗ₕ V.id) V.⋆_) (V.⋆Assoc _ _ _)) ⟩
    (Hom[_,-] ℰ W ⟪ f ⟫ V.⊗ₕ V.id) V.⋆ ℰ.seq W U X ∎

  pre-β : ∀ {U' U X} (g : C [ U , X ]) (f : C [ U' , U ])
    → ℰ.⌜ g ⌝ V.⋆ Hom[-,_] X ⟪ f ⟫ ≡ ℰ.⌜ f C.⋆ g ⌝
  pre-β g f = post-β (ℰ ^opᴱ) g f

  seq-pre : ∀ {U' U Y X} (f : C [ U' , U ])
    → ℰ.seq U Y X V.⋆ Hom[-,_] X ⟪ f ⟫ ≡ (Hom[-,_] Y ⟪ f ⟫ V.⊗ₕ V.id) V.⋆ ℰ.seq U' Y X
  seq-pre f = seq-post (ℰ ^opᴱ) f

  pre-post : ∀ {W' W Y Y'} (f : C [ W' , W ]) (g : C [ Y , Y' ])
    → Hom[-,_] Y ⟪ f ⟫ V.⋆ Hom[_,-] ℰ W' ⟪ g ⟫ ≡ Hom[_,-] ℰ W ⟪ g ⟫ V.⋆ Hom[-,_] Y' ⟪ f ⟫
  pre-post {W'} {W} {Y} {Y'} f g =
      V.⋆Assoc _ _ _
    ∙ cong (V.η⁻¹⟨ _ ⟩ V.⋆_)
        ( V.⋆Assoc _ _ _
        ∙ cong ((ℰ.⌜ f ⌝ V.⊗ₕ V.id) V.⋆_) (seq-post ℰ g)
        ∙ pullˡ (sym serialize₁₂ ∙ serialize₂₁)
        ∙ V.⋆Assoc _ _ _)
    ∙ pullˡ (sym (symNatIso V.η .NatIso.trans .NatTrans.N-hom _))
    ∙ V.⋆Assoc _ _ _
