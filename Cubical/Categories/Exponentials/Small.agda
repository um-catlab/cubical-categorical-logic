module Cubical.Categories.Exponentials.Small where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation hiding (_⇒_)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.Presheaf.Constructions hiding (π₁; π₂)
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Profunctor.General

private
  variable
    ℓC ℓC' ℓD ℓD' : Level
    C D : Category ℓC ℓC'

open Category
open Functor
open isIso

module _ (C : Category ℓC ℓC') where
  Exponential : (c d : C .ob) → (BinProductsWith C c) → Type _
  Exponential c d -×c = UniversalElement C (((C [-, c ]) , -×c) ⇒PshSmall (C [-, d ]))

  Exponentiable : ∀ c → (_×c : BinProductsWith C c) → Type _
  Exponentiable c _×c = ∀ d → Exponential c d _×c

  module _ (bp : BinProducts C) where
    AllExponentiable : Type _
    AllExponentiable = ∀ c → Exponentiable c λ d → bp (d , c)

module ExponentialNotation {C : Category ℓC ℓC'}{c d} -×c (exp : Exponential C c d -×c) where
  private
    module C = Category C
  module ⇒ue = UniversalElementNotation exp
  open ⇒ue
  open BinProductsWithNotation -×c

  vert : C .ob
  vert = vertex

  app : C [ vert ×a , d ]
  app = element

  app' : ∀ {Γ} → C [ Γ , vert ] → C [ Γ , c ] → C [ Γ , d ]
  app' f x = (f ,p x) C.⋆ app

  lda : ∀ {Γ} → C [ Γ ×a , d ] → C [ Γ , vert ]
  lda = intro

module ExponentiableNotation {C : Category ℓC ℓC'}{c}
  -×c
  (c⇒- : Exponentiable C c -×c) where
  c⇒_ : C .ob → C .ob
  c⇒ d = c⇒- d .UniversalElement.vertex

  module _ {c d : C .ob} where
    open ExponentialNotation -×c (c⇒- d) hiding (vert; module ⇒ue) public
  module ⇒ue d = ExponentialNotation.⇒ue -×c (c⇒- d)

module ExponentialsNotation {C : Category ℓC ℓC'} (bp : BinProducts C)
  (exps : AllExponentiable C bp) where
  open BinProductsNotation bp
  _⇒_ : C .ob → C .ob → C .ob
  c ⇒ d = exps c d .UniversalElement.vertex

  module _ {c d : C .ob} where
    open ExponentialNotation (λ d' → bp (d' , c)) (exps c d) hiding (vert; module ⇒ue) public
  module ⇒ue c d = ExponentialNotation.⇒ue (λ d' → bp (d' , c)) (exps c d)

module _ (C : Category ℓC ℓC') where
  module _ (bp : BinProducts C) where
    private
      module C = Category C
      module bp = BinProductsNotation bp
    module _ (exp : AllExponentiable C bp) where
      private
        module exp = ExponentialsNotation bp exp
      module _ {a b c d : C.ob} (f : CatIso C a c) (g : CatIso C b d) where
        private
          module a⇒b = ExponentialNotation (λ d₁ → bp (d₁ , a)) (exp a b)
          module c⇒d = ExponentialNotation (λ d₁ → bp (d₁ , c)) (exp c d)

        ExpProf : C.ob → Profunctor C C _
        ExpProf x .F-ob d = (C [-, d ]) ∘F (LRPsh→Functor ((C [-, x ]) , (λ d₁ → bp (d₁ , x))) ^opF)
        ExpProf x .F-hom f = natTrans (λ x₁ z → z C.⋆ f) λ _ → funExt λ _ → C.⋆Assoc _ _ _
        ExpProf x .F-id = makeNatTransPath (funExt₂ λ _ _ → C.⋆IdR _)
        ExpProf x .F-seq _ _ = makeNatTransPath (funExt₂ λ _ _ → sym $ C.⋆Assoc _ _ _)

        ⇒F : C.ob → Functor C C
        ⇒F x = FunctorComprehension (ExpProf x) (exp x)

        ⇒Iso : CatIso C (a exp.⇒ b) (c exp.⇒ d)
        ⇒Iso = ⋆Iso (preserveIsosF {F = ⇒F a} g) a⇒d≅c⇒d
          where

          p : ∀ {x} →
            bp.×F ⟪ C.id {x = x} , f .snd .inv ⟫ C.⋆ bp.×F ⟪ C.id , f .fst ⟫ ≡ C.id
          p = (sym $ bp.×F .F-seq _ _)
              ∙ cong (bp.×F .F-hom) (ΣPathP ((C.⋆IdL _) , (f .snd .sec)))
              ∙ bp.×F .F-id

          q : ∀ {x} →
            bp.×F ⟪ C.id {x = x} , f .fst ⟫ C.⋆ bp.×F ⟪ C.id , f .snd .inv ⟫ ≡ C.id
          q = (sym $ bp.×F .F-seq _ _)
              ∙ cong (bp.×F .F-hom) (ΣPathP ((C.⋆IdL _) , (f .snd .ret)))
              ∙ bp.×F .F-id

          a⇒F≅c⇒F : NatIso (⇒F a) (⇒F c)
          a⇒F≅c⇒F = FunctorComprehension-NatIso (ExpProf a) (ExpProf c) (exp a) (exp c)
                      (Isos→PshIso (λ _ → iso (λ x → bp.×F ⟪ C.id , f .snd .inv ⟫ C.⋆ x)
                                              (λ x → bp.×F ⟪ C.id , f .fst ⟫ C.⋆ x)
                                              (λ x → sym (C.⋆Assoc _ _ _)
                                                     ∙ C.⟨ p ⟩⋆⟨ refl ⟩
                                                     ∙ C.⋆IdL _)
                                              (λ x → sym (C.⋆Assoc _ _ _)
                                                     ∙ C.⟨ q ⟩⋆⟨ refl ⟩
                                                     ∙ C.⋆IdL _))
                                   (λ x y g p →
                                     (sym $ C.⋆Assoc _ _ _)
                                      ∙ C.⟨ (sym $ C.⋆Assoc _ _ _)
                                            ∙ C.⟨ bp.,p-extensionality
                                                    (C.⋆Assoc _ _ _
                                                    ∙ C.⟨ refl ⟩⋆⟨ bp.×β₁ ⟩
                                                    ∙ sym (C.⋆Assoc _ _ _)
                                                    ∙ C.⟨ bp.×β₁ ∙ C.⋆IdR _ ⟩⋆⟨ refl ⟩
                                                    ∙ sym bp.×β₁
                                                    ∙ C.⟨ refl ⟩⋆⟨ (sym $ C.⋆IdR _)
                                                                   ∙ sym bp.×β₁ ⟩
                                                    ∙ (sym $ C.⋆Assoc _ _ _))
                                                    (C.⋆Assoc _ _ _
                                                    ∙ C.⟨ refl ⟩⋆⟨ bp.×β₂ ⟩
                                                    ∙ bp.×β₂
                                                    ∙ C.⟨ sym bp.×β₂ ⟩⋆⟨ refl ⟩
                                                    ∙ C.⋆Assoc _ _ _
                                                    ∙ C.⟨ refl ⟩⋆⟨ sym bp.×β₂ ⟩
                                                    ∙ (sym $ C.⋆Assoc _ _ _))
                                                ⟩⋆⟨ refl ⟩
                                            ∙ C.⋆Assoc _ _ _ ⟩⋆⟨ refl ⟩))

          a⇒d≅c⇒d : CatIso C (a exp.⇒ d) (c exp.⇒ d)
          a⇒d≅c⇒d = _ , (a⇒F≅c⇒F .NatIso.nIso d)
