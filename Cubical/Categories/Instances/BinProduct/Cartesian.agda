-- The product of two cartesian categories is cartesian
module Cubical.Categories.Instances.BinProduct.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma.Properties

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Instances.BinProduct

open import Cubical.Categories.Instances.TotalCategory.Cartesian

open import Cubical.Categories.Displayed.Instances.Weaken.Properties

open Category

private
  variable ℓB ℓB' ℓC ℓC' ℓD ℓD' : Level

module _
  (C : CartesianCategory ℓC ℓC')
  (D : CartesianCategory ℓD ℓD')
  where
  _×_ : CartesianCategory _ _
  _×_ = ∫C (weakenCartesianCategory C D)

pairCF :
  {B : CartesianCategory ℓB ℓB'}
  {C : CartesianCategory ℓC ℓC'}
  {D : CartesianCategory ℓD ℓD'}
  → CartesianFunctor B (C .CartesianCategory.C)
  → CartesianFunctor B (D .CartesianCategory.C)
  → CartesianFunctor B
      ((C .CartesianCategory.C) ×C (D .CartesianCategory.C))
pairCF F G .fst = F .fst ,F G .fst
pairCF F G .snd c c' Γ =
  compEquiv
    (Σ-cong-equiv
      (_ , F .snd c c' (Γ .fst))
      (λ _ → _ , G .snd c c' (Γ .snd)))
    (isoToEquiv
      (iso
        (λ z → (z .fst .fst , z .snd .fst) ,
               (z .fst .snd , z .snd .snd))
        (λ z → (z .fst .fst , z .snd .fst) ,
               (z .fst .snd , z .snd .snd))
        (λ _ → refl)
        (λ _ → refl)))
    .snd

module _ (C : CartesianCategory ℓC ℓC') where
  private
    module C = CartesianCategory C

  private
    shuffle : ∀ {Γ a b c d} →
      C.C [ Γ , ((a C.× c) C.× (b C.× d)) ] →
      Σ (C.C [ Γ , (a C.× b) ]) (λ _ → C.C [ Γ , (c C.× d) ])
    shuffle {a = a} {b = b} {c = c} {d = d} h =
      ab._,p_
        ((h C.⋆ outer.π₁) C.⋆ ac.π₁)
        ((h C.⋆ outer.π₂) C.⋆ bd.π₁) ,
      cd._,p_
        ((h C.⋆ outer.π₁) C.⋆ ac.π₂)
        ((h C.⋆ outer.π₂) C.⋆ bd.π₂)
      where
      module ac = BinProductNotation (C.bp (a , c))
      module bd = BinProductNotation (C.bp (b , d))
      module ab = BinProductNotation (C.bp (a , b))
      module cd = BinProductNotation (C.bp (c , d))
      module outer =
        BinProductNotation (C.bp ((a C.× c) , (b C.× d)))

    unshuffle : ∀ {Γ a b c d} →
      Σ (C.C [ Γ , (a C.× b) ]) (λ _ → C.C [ Γ , (c C.× d) ]) →
      C.C [ Γ , ((a C.× c) C.× (b C.× d)) ]
    unshuffle {a = a} {b = b} {c = c} {d = d} (f , g) =
      outer._,p_
        (ac._,p_ (f C.⋆ ab.π₁) (g C.⋆ cd.π₁))
        (bd._,p_ (f C.⋆ ab.π₂) (g C.⋆ cd.π₂))
      where
      module ac = BinProductNotation (C.bp (a , c))
      module bd = BinProductNotation (C.bp (b , d))
      module ab = BinProductNotation (C.bp (a , b))
      module cd = BinProductNotation (C.bp (c , d))
      module outer =
        BinProductNotation (C.bp ((a C.× c) , (b C.× d)))

    shuffle-unshuffle : ∀ {Γ a b c d}
      (fg : Σ (C.C [ Γ , (a C.× b) ]) (λ _ → C.C [ Γ , (c C.× d) ])) →
      shuffle (unshuffle fg) ≡ fg
    shuffle-unshuffle {a = a} {b = b} {c = c} {d = d} (f , g) =
      ΣPathP
        ( ab.,p-extensionality
            (ab.×β₁ ∙ C.⟨ outer.×β₁ ⟩⋆⟨ refl ⟩ ∙ ac.×β₁)
            (ab.×β₂ ∙ C.⟨ outer.×β₂ ⟩⋆⟨ refl ⟩ ∙ bd.×β₁)
        , cd.,p-extensionality
            (cd.×β₁ ∙ C.⟨ outer.×β₁ ⟩⋆⟨ refl ⟩ ∙ ac.×β₂)
            (cd.×β₂ ∙ C.⟨ outer.×β₂ ⟩⋆⟨ refl ⟩ ∙ bd.×β₂))
      where
      module ac = BinProductNotation (C.bp (a , c))
      module bd = BinProductNotation (C.bp (b , d))
      module ab = BinProductNotation (C.bp (a , b))
      module cd = BinProductNotation (C.bp (c , d))
      module outer =
        BinProductNotation (C.bp ((a C.× c) , (b C.× d)))

    unshuffle-shuffle : ∀ {Γ a b c d}
      (h : C.C [ Γ , ((a C.× c) C.× (b C.× d)) ]) →
      unshuffle (shuffle h) ≡ h
    unshuffle-shuffle {a = a} {b = b} {c = c} {d = d} h =
      outer.,p-extensionality
        (outer.×β₁ ∙
         ac.,p-extensionality
           (ac.×β₁ ∙ ab.×β₁)
           (ac.×β₂ ∙ cd.×β₁))
        (outer.×β₂ ∙
         bd.,p-extensionality
           (bd.×β₁ ∙ ab.×β₂)
           (bd.×β₂ ∙ cd.×β₂))
      where
      module ac = BinProductNotation (C.bp (a , c))
      module bd = BinProductNotation (C.bp (b , d))
      module ab = BinProductNotation (C.bp (a , b))
      module cd = BinProductNotation (C.bp (c , d))
      module outer =
        BinProductNotation (C.bp ((a C.× c) , (b C.× d)))

  ×CF : CartesianFunctor (C × C) C.C
  ×CF .fst = C.×F
  ×CF .snd (a , b) (c , d) Γ =
    subst isEquiv
      (sym (funExt λ h →
        ΣPathP
          ( ab.×ue.intro-natural ∙
            cong ab.×ue.intro
              (ΣPathP
                (sym (C.⋆Assoc _ _ _) , sym (C.⋆Assoc _ _ _)))
          , cd.×ue.intro-natural ∙
            cong cd.×ue.intro
              (ΣPathP
                (sym (C.⋆Assoc _ _ _) , sym (C.⋆Assoc _ _ _))))))
      (isoToIsEquiv
        (iso
          shuffle
          unshuffle
          shuffle-unshuffle
          unshuffle-shuffle))
    where
    module ab = BinProductNotation (C.bp (a , b))
    module cd = BinProductNotation (C.bp (c , d))
