{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.TotalCategory as ∫
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Bifunctor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Presheaf.Constructions
private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓP ℓPᴰ ℓQᴰ : Level

module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'} {ℓA ℓB ℓAᴰ ℓBᴰ : Level}
  where
  private
    𝓟 = PresheafCategory C ℓA
    𝓟ᴰ = PRESHEAFᴰ Cᴰ ℓA ℓAᴰ
    𝓠 = PresheafCategory C ℓB
    𝓠ᴰ = PRESHEAFᴰ Cᴰ ℓB ℓBᴰ
    𝓡 = PresheafCategory C (ℓ-max ℓA ℓB)
    𝓡ᴰ = PRESHEAFᴰ Cᴰ (ℓ-max ℓA ℓB) (ℓ-max ℓAᴰ ℓBᴰ)

  -- External product: (Pᴰ ×ᴰ Qᴰ) over (P × Q)
  PshProd'ᴰ : Functorᴰ PshProd' (𝓟ᴰ ×Cᴰ 𝓠ᴰ) 𝓡ᴰ
  PshProd'ᴰ = postcomposeFᴰ (C ^op) (Cᴰ ^opᴰ) ×Setsᴰ ∘Fᴰ ,Fᴰ-functorᴰ

  PshProdᴰ : Bifunctorᴰ PshProd 𝓟ᴰ 𝓠ᴰ 𝓡ᴰ
  PshProdᴰ = ParFunctorᴰToBifunctorᴰ PshProd'ᴰ

module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'} {ℓA ℓAᴰ ℓBᴰ : Level}
  where
  private
    𝓟 = PresheafCategory C ℓA
    𝓟ᴰ = PRESHEAFᴰ Cᴰ ℓA ℓAᴰ
    𝓠ᴰ = PRESHEAFᴰ Cᴰ ℓA ℓBᴰ
    𝓡ᴰ = PRESHEAFᴰ Cᴰ ℓA (ℓ-max ℓAᴰ ℓBᴰ)
  -- Internal product: Pᴰ ×ⱽ Qᴰ over P
  PshProdⱽ : Functorⱽ (𝓟ᴰ ×ᴰ 𝓠ᴰ) 𝓡ᴰ
  PshProdⱽ = postcomposeFⱽ (C ^op) (Cᴰ ^opᴰ) ×Setsⱽ ∘Fⱽ ,Fⱽ-functorⱽ

module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
  {P : Presheaf C ℓP}
  (Pᴰ : Presheafᴰ Cᴰ P ℓPᴰ)
  (Qᴰ : Presheafᴰ Cᴰ P ℓQᴰ)
  where
  private
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
    module ∫C = Category (∫C Cᴰ)

  -- Heuristic:
  --   if Cᴰ = Unit and P = Unit, then this should be the exponential ?
  --   if C = Unit and Cᴰ = weaken Unit C and P = Unit then this should be the exponential

  -- Psh⇒ⱽ-fail0 : Presheafᴰ Cᴰ P (ℓ-max ℓPᴰ ℓQᴰ)
  -- Psh⇒ⱽ-fail0 .Functorᴰ.F-obᴰ {x} xᴰ p .fst = Pᴰ.p[ p ][ xᴰ ] → Qᴰ.p[ p ][ xᴰ ]
  -- Psh⇒ⱽ-fail0 .Functorᴰ.F-obᴰ {x} xᴰ p .snd = isSet→ Qᴰ.isSetPshᴰ
  -- -- cannot refine because α only knows how to transform things Pᴰ.p[ p ][ xᴰ ], not Pᴰ.p[ f P.⋆ p ][ yᴰ ]
  -- Psh⇒ⱽ-fail0 .Functorᴰ.F-homᴰ fᴰ p α pᴰ = {!α ?!}
  -- Psh⇒ⱽ-fail0 .Functorᴰ.F-idᴰ = {!!}
  -- Psh⇒ⱽ-fail0 .Functorᴰ.F-seqᴰ = {!!}

  -- this doesn't work because we can't prove F-seqᴰ
  -- Psh⇒ⱽ-fail1 : Presheafᴰ Cᴰ P _
  -- Psh⇒ⱽ-fail1 .Functorᴰ.F-obᴰ {x} xᴰ p .fst =
  --   ∀ y (yᴰ : Cᴰ.ob[ y ]) -- This is an object of ∫C {C} Cᴰ
  --     (f : C [ y , x ]) (fᴰ : Cᴰ [ f ][ yᴰ , xᴰ ]) -- This is an element of ∫P (Cᴰ [-][-, xᴰ ])
  --     → Pᴰ.p[ f P.⋆ p ][ yᴰ ] → Qᴰ.p[ f P.⋆ p ][ yᴰ ]

  -- Psh⇒ⱽ-fail1 .Functorᴰ.F-obᴰ {x} xᴰ p .snd = {!∫P Pᴰ!}
  -- Psh⇒ⱽ-fail1 .Functorᴰ.F-homᴰ {x} {y} {f} {xᴰ} {yᴰ} fᴰ p α z zᴰ g gᴰ =
  --   subst (λ p' → Pᴰ.p[ p' ][ zᴰ ] → Qᴰ.p[ p' ][ zᴰ ])
  --     (P.⋆Assoc g f p) (α z zᴰ (g C.⋆ f) (gᴰ Cᴰ.⋆ᴰ fᴰ))
  -- -- probably provable
  -- Psh⇒ⱽ-fail1 .Functorᴰ.F-idᴰ = funExt (λ p → funExt λ α → funExt (λ z → funExt λ zᴰ → funExt λ g → funExt λ gᴰ →
  --   {!!}
  --   ))
  -- -- not provable without naturality of α right?
  -- Psh⇒ⱽ-fail1 .Functorᴰ.F-seqᴰ fᴰ gᴰ = ?

  -- what does it even mean for such a thing to be "natural?"
  -- before it was α (g C.⋆ f) (g P.⋆ p) ≡ g Q.⋆ α f p
  --
  -- for this? α (g C.⋆ f) (gᴰ Cᴰ.⋆ᴰ fᴰ) (gᴰ Pᴰ.⋆ᴰ fpᴰ) ≡[ ? ] gᴰ Q.⋆ᴰ α f fᴰ fpᴰ
--   Psh⇒ⱽ-fun : ∀ {x} (xᴰ : Cᴰ.ob[ x ]) (p : P.p[ x ]) → Type _
--   Psh⇒ⱽ-fun xᴰ p = (∀ ((y , yᴰ) : ∫C Cᴰ .Category.ob) ((f , fᴰ) : ⟨ ∫P (Cᴰ [-][-, xᴰ ]) ⟅ y , yᴰ ⟆ ⟩)
--       → Pᴰ.p[ f P.⋆ p ][ yᴰ ] → Qᴰ.p[ f P.⋆ p ][ yᴰ ])

--   isSetPsh⇒ⱽ-fun : ∀ {x} {xᴰ : Cᴰ.ob[ x ]} {p : P.p[ x ]} → isSet (Psh⇒ⱽ-fun xᴰ p)
--   isSetPsh⇒ⱽ-fun = isSetΠ (λ _ → isSetΠ λ _ → isSetΠ (λ _ → Qᴰ.isSetPshᴰ))

--   Psh⇒ⱽ-fun-is-natural : ∀ {x} {xᴰ : Cᴰ.ob[ x ]} {p : P.p[ x ]}
--     → Psh⇒ⱽ-fun xᴰ p → Type _
--   Psh⇒ⱽ-fun-is-natural {x} {xᴰ} {p} α = (∀ (yyᴰ zzᴰ : ∫C Cᴰ .Category.ob)
--        (ggᴰ : ∫C Cᴰ [ zzᴰ , yyᴰ ])
--        (ffᴰ : ⟨ ∫P (Cᴰ [-][-, xᴰ ]) ⟅ yyᴰ ⟆ ⟩)
--        → (pᴰ : Pᴰ.p[ (ffᴰ .fst) P.⋆ p ][ yyᴰ .snd ])
--        → α _ (ggᴰ ⋆⟨ ∫C Cᴰ ⟩ ffᴰ) (Pᴰ.reind (sym $ P.⋆Assoc _ _ _) $ ggᴰ .snd Pᴰ.⋆ᴰ pᴰ)
--          ≡ Qᴰ.reind (sym $ P.⋆Assoc _ _ _) (ggᴰ .snd Qᴰ.⋆ᴰ α _ ffᴰ pᴰ))

--   isProp-Psh⇒ⱽ-fun-is-natural : ∀ {x} {xᴰ : Cᴰ.ob[ x ]} {p : P.p[ x ]} {α : Psh⇒ⱽ-fun xᴰ p}
--     → isProp (Psh⇒ⱽ-fun-is-natural α)
--   isProp-Psh⇒ⱽ-fun-is-natural = isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → Qᴰ.isSetPshᴰ _ _

--   Psh⇒ⱽ-ob :  ∀ {x} (xᴰ : Cᴰ.ob[ x ]) (p : P.p[ x ]) → Type _
--   Psh⇒ⱽ-ob xᴰ p = Σ (Psh⇒ⱽ-fun xᴰ p) Psh⇒ⱽ-fun-is-natural

--   Psh⇒ⱽ : Presheafᴰ Cᴰ P _
--   Psh⇒ⱽ .Functorᴰ.F-obᴰ {x} xᴰ p .fst =
--     -- This fundamentally cannot be stated as a natural transformation (or naturaltransformationᴰ)
--     -- because the Pᴰ,Qᴰ parts are *dependent* on the ffᴰ part.
--     Psh⇒ⱽ-ob xᴰ p
--   Psh⇒ⱽ .Functorᴰ.F-obᴰ {x} xᴰ p .snd = isSetΣ isSetPsh⇒ⱽ-fun λ _ → isProp→isSet isProp-Psh⇒ⱽ-fun-is-natural
--   Psh⇒ⱽ .Functorᴰ.F-homᴰ {x} {y} {f} {xᴰ} {yᴰ} fᴰ p α .fst zzᴰ ggᴰ gpᴰ =
--     Qᴰ.reind (P.⋆Assoc _ _ _) $ α .fst _ (ggᴰ ∫C.⋆ (f , fᴰ)) (Pᴰ.reind (sym $ P.⋆Assoc _ _ _) $ gpᴰ)
--   Psh⇒ⱽ .Functorᴰ.F-homᴰ {x} {y} {f} {xᴰ} {yᴰ} fᴰ p α .snd yyᴰ zzᴰ hhᴰ ggᴰ pᴰ = Qᴰ.rectify $ Qᴰ.≡out $
--     (sym $ Qᴰ.reind-filler _ _) --        (seq' (∫C Cᴰ) ggᴰ ffᴰ .fst C.⋆ f , seq' (∫C Cᴰ) ggᴰ ffᴰ .snd Cᴰ.⋆ᴰ fᴰ)
--     -- (Pᴰ.reind-filler (P.⋆Assoc (hhᴰ .fst C.⋆ ggᴰ .fst) f p) {!!} {!~ i!} .snd)
--     ∙ (Qᴰ.≡in $ (λ i → α .fst (zzᴰ .fst , zzᴰ .snd) ((hhᴰ ∫C.⋆ ggᴰ) ∫C.⋆ (f , fᴰ))
--     -- (Pᴰ.rectify (Pᴰ.≡out $ Pᴰ.reind-filler (sym $ P.⋆Assoc (hhᴰ .fst C.⋆ ggᴰ .fst) f p) (Pᴰ.reind (sym $ P.⋆Assoc (hhᴰ .fst) _ _) (hhᴰ .snd Pᴰ.⋆ᴰ pᴰ))) i)
--         {!(Pᴰ.rectify (Pᴰ.≡out $ Pᴰ.reind-filler (sym $ P.⋆Assoc (hhᴰ .fst C.⋆ ggᴰ .fst) f p) (Pᴰ.reind (sym $ P.⋆Assoc (hhᴰ .fst) _ _) (hhᴰ .snd Pᴰ.⋆ᴰ pᴰ))) i)!}  )) -- (Pᴰ.rectify {!!} i)
-- -- i = i0 ⊢ (transp
-- --           (λ i₁ →
-- --              Pᴰ.p[ P.⋆Assoc (seq' (∫C Cᴰ) hhᴰ ggᴰ .fst) f p (~ i₁) ][ zzᴰ .snd
-- --              ])
-- --           i0
-- --           (Pᴰ.reind
-- --            (λ i₁ →
-- --               P.⋆Assoc (hhᴰ .fst) (ggᴰ .fst) (P .Functor.F-hom f p) (~ i₁))
-- --            (hhᴰ .snd Pᴰ.⋆ᴰ pᴰ)))

--     ∙ {!!}
--     ∙ Qᴰ.⟨ refl ⟩⋆⟨ Qᴰ.reind-filler _ _ ⟩
--     ∙ Qᴰ.reind-filler _ _
--   Psh⇒ⱽ .Functorᴰ.F-idᴰ = {!!}
--   Psh⇒ⱽ .Functorᴰ.F-seqᴰ = {!!}
