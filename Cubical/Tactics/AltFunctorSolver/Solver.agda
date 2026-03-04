module Cubical.Tactics.AltFunctorSolver.Solver where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sum as Sum
open import Cubical.Data.Quiver.Base as Quiver

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Power
open import Cubical.Categories.Functor renaming (Id to IdF)
open import Cubical.Categories.Instances.Sets

open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Instances.Free.Category.Quiver as FreeCat
open import Cubical.Categories.Instances.Free.Functor.AltPresented

private
  variable
    ℓc ℓc' ℓd ℓd' ℓb ℓb' : Level
open Category
open Functor
open HetSection

module Eval (𝓒 : Category ℓc ℓc') (𝓓 : Category ℓd ℓd')  (𝓕 : Functor 𝓒 𝓓) where
  module Self = CoUnit 𝓕
  open Self

  Free𝓒 = FreeCat (Cat→Quiver 𝓒)
  η𝓒 = FreeCat.η (Cat→Quiver 𝓒)
  Free𝓓 = Self.HCat
  η𝓓 = Self.ηPre
  Free𝓕 = Self.FreeFunctor
  𝓒Q = Cat→Quiver 𝓒

  sem𝓒 : Functor Free𝓒 𝓒
  sem𝓒 = FreeCat.rec 𝓒Q ı where
    ı : FreeCat.Interp _ 𝓒
    ı $g u = u
    ı <$g> e = e .snd .snd

  sem𝓓 : Functor Free𝓓 𝓓
  sem𝓓 = Self.rec (𝓕 ∘F sem𝓒) (λ A → A) ıHom where
    ıHom : ∀ (e : DGen) → _
    ıHom (inl x , inl x₁ , e) = e
    ıHom (inl x , inr x₁ , e) = e
    ıHom (inr x , inl x₁ , e) = e
    ıHom (inr x , inr x₁ , e) = e

  module sem𝓓 = Functor sem𝓓

  -- Normalization is by interpretation into the presheaf category
  𝓟F𝓓 = PowerCategory (Free𝓓 .ob) (SET (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓd) ℓd'))
  Y : Functor Free𝓓 𝓟F𝓓
  Y = PseudoYoneda {C = Free𝓓}

  module Y = Functor Y
  open HetQG

  selfFree𝓒 : Functor Free𝓒 𝓟F𝓓
  selfFree𝓒 = FreeCat.rec 𝓒Q ı where
    ı : FreeCat.Interp 𝓒Q 𝓟F𝓓
    ı ._$g_ = (Y ∘F Self.FreeFunctor) .F-ob
    ı <$g> e = (Y ∘F Self.FreeFunctor) .F-hom (η𝓒 <$g> e)

  Normalize : Functor Free𝓓 𝓟F𝓓
  Normalize = Self.rec selfFree𝓒 (λ A → Y.F-ob (inr A)) ı where
    ı : ∀ (e : DGen) → _
    ı (inl x , inl x₁ , e) =
      Y.F-hom (Self.moduloAx ⟪ η𝓓 <$g> (inr (_ , _ , e)) ⟫)
    ı (inl x , inr x₁ , e) =
      Y.F-hom (Self.moduloAx ⟪ η𝓓 <$g> (inr (_ , _ , e)) ⟫)
    ı (inr x , inl x₁ , e) =
      Y.F-hom (Self.moduloAx ⟪ η𝓓 <$g> (inr (_ , _ , e)) ⟫)
    ı (inr x , inr x₁ , e) =
      Y.F-hom (Self.moduloAx ⟪ η𝓓 <$g> (inr (_ , _ , e)) ⟫)
  module Normalize = Functor Normalize

  -- Normalization is equivalent to Yoneda because they agree on generators
  N≡Y : Normalize ≡ Y
  N≡Y = Self.extensionalityF _ _ agree-on-Free𝓒 (λ A → refl) ıHom where
    agree-on-Free𝓒 : Section _ _
    agree-on-Free𝓒 = FreeCat.elimLocal _ _ _ ı where
      ı : Interpᴰ _ _ _
      ı $gᴰ u = refl
      ı <$g>ᴰ e = refl

    ıHom : ∀ (e : DGen) → _
    ıHom (inl x , inl x₁ , e) = refl
    ıHom (inl x , inr x₁ , e) = refl
    ıHom (inr x , inl x₁ , e) = refl
    ıHom (inr x , inr x₁ , e) = refl

  solve : ∀ {A B}
        → (e e' : Free𝓓 [ A , B ])
        → (Normalize.F-hom e ≡ Normalize.F-hom e')
        → (sem𝓓.F-hom e ≡ sem𝓓.F-hom e')
  solve e e' p =
    cong sem𝓓.F-hom
    -- suffices to show e ≡ e'
    (isFaithfulPseudoYoneda {C = Free𝓓} _ _ e e'
    -- suffices to show Y e ≡ Y e'
    (transport (λ i → Path _ (N≡Y i .F-hom e) (N≡Y i .F-hom e'))
      p))

-- -- Do we need any of this??
--   readBack : ∀ {A B} → 𝓟F𝓓 [ Normalize.F-ob A , Normalize.F-ob B ]
--                      → Free𝓓 [ A , B ]
--   readBack {inl x} {inl x₁} f = f _ (Free𝓓 .id)
--   readBack {inl x} {inr x₁} f = f _ (Free𝓓 .id)
--   readBack {inr x} {inl x₁} f = f _ (Free𝓓 .id)
--   readBack {inr x} {inr x₁} f = f _ (Free𝓓 .id)

--   -- TODO: prove this
--   -- normalise : ∀ {A B } → ∀ (e : Free𝓓 [ A , B ]) → singl e
--   -- normalise e = readBack (Normalize .F-hom e) ,
--   --   {!!} ∙ cong readBack (λ i → {!Normalize≡Y (~ i) .F-hom e!})

--   -- nf : ∀ {A B} → (e : Free𝓓 [ A , B ])
--   --    → sem .F-hom e ≡ sem .F-hom (normalise e .fst)
--   -- nf e = cong (sem .F-hom) (normalise e .snd)

  private
    module _ (A A' A'' : 𝓒 .ob) (B B' B'' : 𝓓 .ob)
             (f : 𝓓 [ B , B' ])
             (g : 𝓓 [ 𝓕 ⟅ A ⟆ , B ])


             (h : 𝓒 [ A' , A ])
             (k : 𝓒 [ A'' , A' ])
             where
      fgen = Self.moduloAx ⟪ η𝓓 <$g> inr (inr B , inr B' , f) ⟫
      ggen = Self.moduloAx ⟪ η𝓓 <$g> inr (inl A , inr B , g) ⟫
      hgen = η𝓒 <$g> (A' , A , h)
      kgen = η𝓒 <$g> (A'' , A' , k)

      tst' : 𝓓 .id ≡ 𝓓 .id ⋆⟨ 𝓓 ⟩ 𝓓 .id
      tst' = solve (Free𝓓 .id) (Free𝓓 .id {x = inr B} ⋆⟨ Free𝓓 ⟩ Free𝓓 .id) refl

      tst2 : g ≡ ((𝓓 .id ⋆⟨ 𝓓 ⟩ g) ⋆⟨ 𝓓 ⟩ 𝓓 .id)
      tst2 = solve ggen ((Free𝓓 .id ⋆⟨ Free𝓓 ⟩ ggen) ⋆⟨ Free𝓓 ⟩ Free𝓓 .id) refl

      tst : 𝓕 ⟪ 𝓒 .id ⟫ ≡ 𝓓 .id
      tst = solve (Self.FreeFunctor ⟪ Free𝓒 .id {A} ⟫) (Free𝓓 .id) refl

      tst'' : 𝓕 ⟪ k ⟫ ⋆⟨ 𝓓 ⟩ 𝓕 ⟪ h ⟫ ≡ 𝓕 ⟪ k ⋆⟨ 𝓒 ⟩ h ⟫
      tst'' = solve
        (Self.FreeFunctor ⟪ kgen ⟫ ⋆⟨ Free𝓓 ⟩ Self.FreeFunctor ⟪ hgen ⟫)
        (Self.FreeFunctor ⟪ kgen ⋆⟨ Free𝓒 ⟩ hgen ⟫)
        refl

solve = Eval.solve
