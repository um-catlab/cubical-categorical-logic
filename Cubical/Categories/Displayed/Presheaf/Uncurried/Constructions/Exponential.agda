{-

  Let Cᴰ displayed over C

-- Given an object Aᴰ over A such that for all γ : Γ → A and Γᴰ over
-- Γ, the product/pullback Γᴰ ×ⱽ γ*Aᴰ exists, then given any object Bᴰ
-- over A, the vertical exponential Aᴰ ⇒ⱽ Bᴰ is specified by the
-- universal property that
--
-- Cᴰ [-][-, Aᴰ ⇒ⱽ Bᴰ ] ≅ reindPsh (×ⱽ* Aᴰ) Cᴰ [-][-, Bᴰ ]
--
-- where (×ⱽ* Aᴰ) : Cᴰ / C [-, A ] → Cᴰ / C [-, A ]
-- is defined as (Γ , Γᴰ , f) ×ⱽ* Aᴰ = (Γ , f*Γᴰ , f)
-- Note: this is the product of (Γ , Γᴰ , f) with (Γ , f*Aᴰ , f)

-- TODO: This means that the restriction operation
-- (×ⱽ* Aᴰ)* : 𝓟 (Cᴰ / C [-, A ]) → 𝓟 (Cᴰ / C [-, A ])
-- is equivalent to the product with Cᴰ [-][-, Aᴰ ]
--
-- meaning Qᴰ → (×ⱽ* Aᴰ)*Pᴰ ≅ Qᴰ → Pᴰ ×ⱽ Cᴰ [-][-, Aᴰ ] ≅ (Qᴰ → Pᴰ) × (Qᴰ → Cᴰ [-][-, Aᴰ ])
-}

{-# OPTIONS --lossy-unification #-}

-- This should probably be UniversalProperties.Exponential, not Constructions.Exponential
module Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Exponential where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open PshHom
open PshIso
open UniversalElement
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

-- Representability condition to get UMP for ⇒ⱽSmall
module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  where
  private
    module Cᴰ = Fibers Cᴰ using (ob[_])
    module P = PresheafNotation P using (p[_])

  LocallyRepresentableⱽ : Presheafᴰ P Cᴰ ℓPᴰ → Type _
  LocallyRepresentableⱽ Pᴰ = ∀ {x} (xᴰ : Cᴰ.ob[ x ])(p : P.p[ x ])
    → Representableⱽ Cᴰ x ((Cᴰ [-][-, xᴰ ]) ×Psh reindPshᴰNatTrans (yoRec P p) Pᴰ)

  LocallyRepresentableⱽ→LocallyRepresentable : {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
    → LocallyRepresentableⱽ Pᴰ
    → LocallyRepresentable Pᴰ
  LocallyRepresentableⱽ→LocallyRepresentable {Pᴰ = Pᴰ} _×ⱽ_*Pᴰ (Γ , Γᴰ , p) =
    RepresentationPshIso→UniversalElement (((Cᴰ / P) [-, Γ , Γᴰ , p ]) ×Psh Pᴰ)
      ((_ , (Γᴰ ×ⱽ p *Pᴰ) .fst , p) ,
      -- Cᴰ / P [-, Γ , (Γᴰ ×ⱽ p *Pᴰ) , p ]
      push-repr
      -- pushⱽ p (Cᴰ [-][-, (Γᴰ ×ⱽ p *Pᴰ) ])
      ⋆PshIso push-PshIsoⱽ (yoRec P p) ((Γᴰ ×ⱽ p *Pᴰ) .snd)
      -- pushⱽ p (Cᴰ [-][-, Γᴰ ] ×ⱽ (reindPshᴰNatTrans (yoRec p) Pᴰ))
      ⋆PshIso FrobeniusReciprocity (yoRec P p) (Cᴰ [-][-, Γᴰ ]) Pᴰ
      -- pushⱽ p (Cᴰ [-][-, Γᴰ ]) ×ⱽ Pᴰ
      ⋆PshIso ×PshIso (invPshIso push-repr) idPshIso
      -- (Cᴰ / P [-][-, Γ , Γᴰ , p ]) ×ⱽ Pᴰ
      )

LRⱽPresheafᴰ : {C : Category ℓC ℓC'}(P : Presheaf C ℓP) (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (ℓPᴰ : Level) → Type _
LRⱽPresheafᴰ P Cᴰ ℓPᴰ = Σ (Presheafᴰ P Cᴰ ℓPᴰ) LocallyRepresentableⱽ


module LRⱽPresheafᴰNotation {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') {P : Presheaf C ℓP} (Pᴰ : LRⱽPresheafᴰ P Cᴰ ℓPᴰ) where
  private
    module C = Category C using (id; _⋆_; ob; ⋆IdL)
    module Cᴰ = Fibers Cᴰ using (ob[_]; Hom[_][_,_]; ⋆IdR; Hom[_,_]; idᴰ; _≡[_]_; _∫≡_; ≡in; ≡out; rectify; _⋆ᴰ_; reind; reind-filler)
    module P = PresheafNotation P using (p[_]; _⋆_)
  open PresheafᴰNotation Cᴰ P (Pᴰ .fst)
  _×ⱽ_* : ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ])(p : P.p[ Γ ]) → Cᴰ.ob[ Γ ]
  Γᴰ ×ⱽ p * = Pᴰ .snd Γᴰ p .fst

  introᴰ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
    → (γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ])
    → p[ γ P.⋆ p ][ Δᴰ ]
    → Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ]
  introᴰ {Δ} {Δᴰ} {Γ} {Γᴰ} {γ} {p} γᴰ γpᴰ = Pᴰ .snd Γᴰ p .snd .nIso (Δ , Δᴰ , γ) .fst
    (γᴰ , γpᴰ)

  _⋆π₁ⱽ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
    → Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ]
    → Cᴰ [ γ ][ Δᴰ , Γᴰ ]
  γᴰ ⋆π₁ⱽ = Pᴰ .snd _ _ .snd .trans .N-ob (_ , _ , _) γᴰ .fst


  π₁ⱽ : ∀ {Γ Γᴰ p} → Cᴰ [ C.id {Γ} ][ Γᴰ ×ⱽ p * , Γᴰ ]
  π₁ⱽ = Cᴰ.idᴰ ⋆π₁ⱽ

  _⋆π₂ⱽ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
    → Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ]
    → p[ γ P.⋆ p ][ Δᴰ ]
  γᴰ ⋆π₂ⱽ = Pᴰ .snd _ _ .snd .trans .N-ob (_ , _ , _) γᴰ .snd

  π₂ⱽ : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{p} → p[ C.id P.⋆ p ][ Γᴰ ×ⱽ p * ]
  π₂ⱽ = Cᴰ.idᴰ ⋆π₂ⱽ

  opaque
    congP-introᴰ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ γ'}{p : P.p[ Γ ]}
      {γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ]}
      {γᴰ' : Cᴰ.Hom[ γ' ][ Δᴰ , Γᴰ ]}
      {γpᴰ : p[ γ P.⋆ p ][ Δᴰ ]}
      {γ'pᴰ : p[ γ' P.⋆ p ][ Δᴰ ]}
      (γ≡γ' : γ ≡ γ')
      (γᴰ≡γᴰ' : γᴰ Cᴰ.≡[ γ≡γ' ] γᴰ')
      (γpᴰ≡γ'pᴰ : γpᴰ ≡[ (λ i → γ≡γ' i P.⋆ p) ] γ'pᴰ)
      → introᴰ γᴰ γpᴰ Cᴰ.≡[ γ≡γ' ] introᴰ γᴰ' γ'pᴰ
    congP-introᴰ γ≡γ' γᴰ≡γᴰ' γpᴰ≡γ'pᴰ = λ i → introᴰ (γᴰ≡γᴰ' i) (γpᴰ≡γ'pᴰ i)

    cong-introᴰ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ γ'}{p : P.p[ Γ ]}
      {γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ]}
      {γᴰ' : Cᴰ.Hom[ γ' ][ Δᴰ , Γᴰ ]}
      {γpᴰ : p[ γ P.⋆ p ][ Δᴰ ]}
      {γ'pᴰ : p[ γ' P.⋆ p ][ Δᴰ ]}
      (γᴰ≡γᴰ' : γᴰ Cᴰ.∫≡ γᴰ')
      (γpᴰ≡γ'pᴰ : γpᴰ ∫≡ γ'pᴰ)
      → Path (Cᴰ.Hom[ _ , _ ]) (_ , introᴰ γᴰ γpᴰ) (_ , introᴰ γᴰ' γ'pᴰ)
    cong-introᴰ γᴰ≡γᴰ' γpᴰ≡γ'pᴰ =
      Cᴰ.≡in $ congP-introᴰ (PathPΣ γᴰ≡γᴰ' .fst) (Cᴰ.≡out γᴰ≡γᴰ') (rectify $ ≡out $ γpᴰ≡γ'pᴰ)

    ⟨_⟩⋆π₁ⱽ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ γ'}{p : P.p[ Γ ]}
      → {γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ]}
      → {γᴰ' : Cᴰ [ γ' ][ Δᴰ , Γᴰ ×ⱽ p * ]}
      → (Path (Cᴰ.Hom[ _ , _ ]) (_ , γᴰ) (_ , γᴰ'))
      → (Path (Cᴰ.Hom[ _ , _ ]) (_ , γᴰ ⋆π₁ⱽ) (_ , γᴰ' ⋆π₁ⱽ))
    ⟨ γᴰ≡γᴰ' ⟩⋆π₁ⱽ i = (γᴰ≡γᴰ' i .fst) , (γᴰ≡γᴰ' i .snd ⋆π₁ⱽ)

    ⋆π₁ⱽ-natural : ∀ {Θ Δ Γ}{Θᴰ : Cᴰ.ob[ Θ ]}{Δᴰ : Cᴰ.ob[ Δ ]}{Γᴰ : Cᴰ.ob[ Γ ]}{δ γ}{p : P.p[ Γ ]}
      → (δᴰ : Cᴰ [ δ ][ Θᴰ , Δᴰ ])
      → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ])
      → Path Cᴰ.Hom[ _ , _ ] (_ , (δᴰ Cᴰ.⋆ᴰ γᴰ) ⋆π₁ⱽ) (_ , δᴰ Cᴰ.⋆ᴰ (γᴰ ⋆π₁ⱽ))
    ⋆π₁ⱽ-natural {Θ} {Δ} {Γ} {Θᴰ} {Δᴰ} {Γᴰ} {δ} {γ} {p} δᴰ γᴰ =
      ⟨ Cᴰ.reind-filler refl ⟩⋆π₁ⱽ ∙ Cᴰ.≡in (cong fst (Pᴰ .snd Γᴰ p .snd .trans .N-hom _ _ (δ , δᴰ , (λ i → δ C.⋆ γ)) _))
      ∙ (sym $ Cᴰ.reind-filler _)

    β₁ⱽ' : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
      → (γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ])
      → (γpᴰ : p[ γ P.⋆ p ][ Δᴰ ])
      → Path Cᴰ.Hom[ _ , _ ] (_ , (introᴰ γᴰ γpᴰ ⋆π₁ⱽ)) (_ , γᴰ)
    β₁ⱽ' {Δ} {Δᴰ} {Γ} {Γᴰ} {γ} {p} γᴰ γpᴰ =
      Cᴰ.≡in $ cong fst $ Pᴰ .snd Γᴰ p .snd .nIso (Δ , Δᴰ , γ) .snd .fst (γᴰ , γpᴰ)

    β₁ⱽ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
      → (γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ])
      → (γpᴰ : p[ γ P.⋆ p ][ Δᴰ ])
      → Path Cᴰ.Hom[ _ , _ ] (_ , (introᴰ γᴰ γpᴰ Cᴰ.⋆ᴰ π₁ⱽ)) (_ , γᴰ)
    β₁ⱽ {Δ} {Δᴰ} {Γ} {Γᴰ} {γ} {p} γᴰ γpᴰ =
      (sym $ ⋆π₁ⱽ-natural (introᴰ γᴰ γpᴰ) Cᴰ.idᴰ) ∙ ⟨ Cᴰ.⋆IdR _ ⟩⋆π₁ⱽ ∙ β₁ⱽ' γᴰ γpᴰ

    ⟨_⟩⋆π₂ⱽ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ γ'}{p : P.p[ Γ ]}
      → {γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ]}
      → {γᴰ' : Cᴰ [ γ' ][ Δᴰ , Γᴰ ×ⱽ p * ]}
      → (Path (Cᴰ.Hom[ _ , _ ]) (_ , γᴰ) (_ , γᴰ'))
      → (γᴰ ⋆π₂ⱽ) ∫≡ (γᴰ' ⋆π₂ⱽ)
    ⟨ γᴰ≡γᴰ' ⟩⋆π₂ⱽ i = (γᴰ≡γᴰ' i .fst P.⋆ _) , (γᴰ≡γᴰ' i .snd ⋆π₂ⱽ)

    ⋆π₂ⱽ-natural : ∀ {Θ Δ Γ}{Θᴰ : Cᴰ.ob[ Θ ]}{Δᴰ : Cᴰ.ob[ Δ ]}{Γᴰ : Cᴰ.ob[ Γ ]}{δ γ}{p : P.p[ Γ ]}
      → (δᴰ : Cᴰ [ δ ][ Θᴰ , Δᴰ ])
      → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ])
      → ((δᴰ Cᴰ.⋆ᴰ γᴰ) ⋆π₂ⱽ) ∫≡ (δᴰ ⋆ᴰ (γᴰ ⋆π₂ⱽ))
    ⋆π₂ⱽ-natural {Θ} {Δ} {Γ} {Θᴰ} {Δᴰ} {Γᴰ} {δ} {γ} {p} δᴰ γᴰ =
      ⟨ Cᴰ.reind-filler _ ⟩⋆π₂ⱽ
      ∙ (≡in $ (PathPΣ (Pᴰ .snd Γᴰ p .snd .trans .N-hom _ _ (δ , δᴰ , refl) _)) .snd)
      ∙ ⋆ᴰ-reind _ _ _

    β₂ⱽ' : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
      → (γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ])
      → (γpᴰ : p[ γ P.⋆ p ][ Δᴰ ])
      → (introᴰ γᴰ γpᴰ ⋆π₂ⱽ) ∫≡ γpᴰ
    β₂ⱽ' {Δ} {Δᴰ} {Γ} {Γᴰ} {γ} {p} γᴰ γpᴰ =
      ≡in $ snd $ PathPΣ (Pᴰ .snd Γᴰ p .snd .nIso (Δ , Δᴰ , γ) .snd .fst (γᴰ , γpᴰ))

    -- Because this is the presheaf composition ⋆ᴰ we get a reind on
    -- the left here yuck
    β₂ⱽ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
      → (γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ])
      → (γpᴰ : p[ γ P.⋆ p ][ Δᴰ ])
      → (introᴰ γᴰ γpᴰ ⋆ᴰ π₂ⱽ) ∫≡ γpᴰ
    β₂ⱽ γᴰ γpᴰ =
      sym (⋆π₂ⱽ-natural (introᴰ γᴰ γpᴰ) Cᴰ.idᴰ)
      ∙ ⟨ Cᴰ.⋆IdR _ ⟩⋆π₂ⱽ
      ∙ β₂ⱽ' γᴰ γpᴰ

    ηⱽ' : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ}{p : P.p[ Γ ]}
      → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ×ⱽ p * ])
      → Path Cᴰ.Hom[ _ , _ ] (_ , introᴰ (γᴰ ⋆π₁ⱽ) (γᴰ ⋆π₂ⱽ)) (_ , γᴰ)
    ηⱽ' {Δ} {Δᴰ} {Γ} {Γᴰ} {γ} {p} γᴰ =
      Cᴰ.≡in $ Pᴰ .snd Γᴰ p .snd .nIso (Δ , Δᴰ , γ) .snd .snd γᴰ

    introᴰ≡ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ γ'}{p : P.p[ Γ ]}
      → {γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ]}
      → {γpᴰ : p[ γ P.⋆ p ][ Δᴰ ]}
      → {γᴰ' : Cᴰ [ γ' ][ Δᴰ , Γᴰ ×ⱽ p * ]}
      → Path Cᴰ.Hom[ _ , _ ] (_ , γᴰ) (_ , (γᴰ' ⋆π₁ⱽ))
      → (γpᴰ ∫≡ (γᴰ' ⋆π₂ⱽ))
      → Path Cᴰ.Hom[ _ , _ ] (_ , introᴰ γᴰ γpᴰ) (_ , γᴰ')
    introᴰ≡ {Δ} {Δᴰ} {Γ} {Γᴰ} {γ} {γ'} {p} {γᴰ} {γpᴰ} {γᴰ'} γᴰ≡γᴰ'⋆π₁ γpᴰ≡γᴰ'⋆π₂ =
      cong-introᴰ γᴰ≡γᴰ'⋆π₁ γpᴰ≡γᴰ'⋆π₂
      ∙ ηⱽ' γᴰ'

    extensionalityᴰ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{γ γ'}{p : P.p[ Γ ]}
      → {γᴰ : Cᴰ.Hom[ γ ][ Δᴰ , Γᴰ ×ⱽ p * ]}
      → {γᴰ' : Cᴰ [ γ' ][ Δᴰ , Γᴰ ×ⱽ p * ]}
      → (γᴰ ⋆π₁ⱽ Cᴰ.∫≡ γᴰ' ⋆π₁ⱽ)
      → (γᴰ ⋆π₂ⱽ ∫≡ γᴰ' ⋆π₂ⱽ)
      → γᴰ Cᴰ.∫≡ γᴰ'
    extensionalityᴰ γᴰ1≡ γᴰ2≡ = (sym $ introᴰ≡ (sym $ γᴰ1≡) (sym $ γᴰ2≡)) ∙ ηⱽ' _

    asLR : LRPresheaf (Cᴰ / P) ℓPᴰ
    asLR = (Pᴰ .fst) , (LocallyRepresentableⱽ→LocallyRepresentable (Pᴰ .snd))
module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} (Pᴰ : LRⱽPresheafᴰ P Cᴰ ℓPᴰ) where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Cᴰ P (Pᴰ .fst)
    module ×ⱽPᴰ = LRⱽPresheafᴰNotation Cᴰ Pᴰ
    -- module ⇒ⱽPshSmall = P⇒Large-cocontinuous-repr (-×Psh (Pᴰ .fst)) (-×Psh (Pᴰ .fst) -cocontinuous)
    --   (λ Γ → LocallyRepresentableⱽ→LocallyRepresentable (Pᴰ .snd) Γ
    --     ◁PshIso eqToPshIso (F-ob ((-×Psh Pᴰ .fst) ∘F (CurryBifunctorL $ HomBif (Cᴰ / P))) Γ) Eq.refl Eq.refl)
  ×LRⱽPshᴰ : Functor (Cᴰ / P) (Cᴰ / P)
  ×LRⱽPshᴰ = LRPsh→Functor (Pᴰ .fst , LocallyRepresentableⱽ→LocallyRepresentable (Pᴰ .snd))

  private
    test-ob : ∀ ((Γ , Γᴰ , p) : (Cᴰ / P) .Category.ob) →
      ×LRⱽPshᴰ .Functor.F-ob (Γ , Γᴰ , p) ≡ (Γ , ((Γᴰ ×ⱽPᴰ.×ⱽ p *) , p))
    test-ob (Γ , Γᴰ , p) = refl

  -- -- this would be a preferable definition but it's very slow to typecheck and use. Why?
  -- ×LRⱽPshᴰ : Functor (Cᴰ / P) (Cᴰ / P)
  -- ×LRⱽPshᴰ = improveF-hom ×LRⱽPshᴰ'
  --   (λ {(Δ , Δᴰ , f) (Γ , Γᴰ , f')} (γ , γᴰ , γf'≡f) →
  --     (γ , (×ⱽPᴰ.introᴰ (Cᴰ.reind (C.⋆IdL γ) (×ⱽPᴰ.π₁ⱽ Cᴰ.⋆ᴰ γᴰ)) (Pᴰ.reind (P.⋆IdL _ ∙ sym γf'≡f) ×ⱽPᴰ.π₂ⱽ) , γf'≡f)) ,
  --     (ΣPathP ((C.⋆IdL _) , ΣPathPProp (λ _ → P.isSetPsh _ _)
  --       (Cᴰ.rectify $ Cᴰ.≡out $
  --         ×ⱽPᴰ.cong-introᴰ (sym (Cᴰ.reind-filler _) ∙ Cᴰ.cong-reind _ _ refl)
  --         (sym (Pᴰ.reind-filler _) ∙ sym (Pᴰ.reind-filler _) ∙ sym (Pᴰ.reind-filler _) ∙ (sym (Pᴰ.reind-filler _))
  --         ∙ Pᴰ.reind-filler _)))))

  -- ×LRⱽPshᴰ≅⇒ⱽPshSmallP-F : NatIso ×LRⱽPshᴰ ⇒ⱽPshSmall.P-F
  -- ×LRⱽPshᴰ≅⇒ⱽPshSmallP-F = record { trans = natTrans (λ x → (Cᴰ / P) .id)
  --   λ f → (Cᴰ / P) .⋆IdR _
  --   ∙ ΣPathP ((sym $ C.⋆IdL _ ∙ C.⋆IdL _) , (ΣPathPProp (λ _ → P.isSetPsh _ _)
  --   (Cᴰ.rectify $ Cᴰ.≡out $
  --   sym $ Cᴰ.⋆IdL _ ∙ Cᴰ.⋆IdL _)))
  --   ∙ (Cᴰ / P) .⋆IdL _
  --   ; nIso = λ x → idCatIso {C = Cᴰ / P} .snd }

  module _ (Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ) where

    _⇒ⱽPshSmall_ : Presheafᴰ P Cᴰ ℓQᴰ
    _⇒ⱽPshSmall_ = reindPsh ×LRⱽPshᴰ Qᴰ

    -- ⇒ⱽPshSmall-UMP : ∀ {Rᴰ : Presheafᴰ P Cᴰ ℓRᴰ}
    --   → Iso (PshHom Rᴰ _⇒ⱽPshSmall_) (PshHom (Rᴰ ×Psh Pᴰ .fst) Qᴰ)
    -- ⇒ⱽPshSmall-UMP =
    --   compIso (postcomp⋆PshHom-Iso (reindNatIsoPsh ×LRⱽPshᴰ≅⇒ⱽPshSmallP-F Qᴰ))
    --           (⇒ⱽPshSmall.P⇒Small-UMP Qᴰ _)


module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} (Pᴰ : LRⱽPresheafᴰ P Cᴰ ℓPᴰ) (Qᴰ : LRⱽPresheafᴰ P Cᴰ ℓQᴰ) where
  ×LRⱽPshᴰ-Iso : (α : PshIsoⱽ (Pᴰ .fst) (Qᴰ .fst))
    → NatIso (×LRⱽPshᴰ Pᴰ) (×LRⱽPshᴰ Qᴰ)
  ×LRⱽPshᴰ-Iso α = LRPshIso→NatIso _ _ α

module _
  {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf D ℓQ}
  (F : Functor (Cᴰ / P) (Dᴰ / Q))
  (Pᴰ : LRⱽPresheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : LRⱽPresheafᴰ Q Dᴰ ℓQᴰ)
  (αᴰ : PshHomⱽ (Pᴰ .fst) (reindPsh F (Qᴰ .fst)))
  where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module D = Category D
    module Dᴰ = Fibers Dᴰ
    module ×ⱽPᴰ = LRⱽPresheafᴰNotation Cᴰ Pᴰ
    module ×ⱽQᴰ = LRⱽPresheafᴰNotation Dᴰ Qᴰ
    module Qᴰ = PresheafᴰNotation Dᴰ Q (Qᴰ .fst)
    module F = Functor F
  open Category
  open PresheafNotation renaming (p[_] to [_]p[_])

  strictPresLRⱽ→NatIso :
    (F⟅c×P⟆≡Fc×Q : (c : Category.ob (Cᴰ / P)) →
      F ⟅ LocallyRepresentableⱽ→LocallyRepresentable (Pᴰ .snd) c .vertex
      ⟆
      Eq.≡
      LocallyRepresentableⱽ→LocallyRepresentable (Qᴰ .snd) (F ⟅ c ⟆)
      .vertex)
    → (((c : Category.ob (Cᴰ / P)) →
      Eq.mixedHEq
      (Eq.ap
       (λ Fc×Q →
          ((Dᴰ / Q) [ Fc×Q , F ⟅ c ⟆ ]) × PresheafNotation.p[ Qᴰ .fst ] Fc×Q)
       (F⟅c×P⟆≡Fc×Q c))
      (F ⟪
       LocallyRepresentableⱽ→LocallyRepresentable (Pᴰ .snd) c .element
       .fst
       ⟫
       ,
       αᴰ .N-ob
       (LocallyRepresentableⱽ→LocallyRepresentable (Pᴰ .snd) c .vertex)
       (LocallyRepresentableⱽ→LocallyRepresentable (Pᴰ .snd) c .element
        .snd))
      (LocallyRepresentableⱽ→LocallyRepresentable (Qᴰ .snd) (F ⟅ c ⟆)
       .element)))
    → NatIso ((×LRⱽPshᴰ Qᴰ) ∘F F) (F ∘F (×LRⱽPshᴰ Pᴰ))
  strictPresLRⱽ→NatIso F⟅c×P⟆≡Fc×Q F⟅π⟆≡π = strictPresLR→NatIso F
    (Pᴰ .fst , LocallyRepresentableⱽ→LocallyRepresentable (Pᴰ .snd))
    (Qᴰ .fst , LocallyRepresentableⱽ→LocallyRepresentable (Qᴰ .snd))
    αᴰ
    F⟅c×P⟆≡Fc×Q
    F⟅π⟆≡π

module _ {C : Category ℓC ℓC'}(Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  isLRⱽObᴰ : ∀ {x} (xᴰ : Cᴰ.ob[ x ]) → Type _
  isLRⱽObᴰ {x} xᴰ = LocallyRepresentableⱽ (Cᴰ [-][-, xᴰ ])

  LRⱽObᴰ : ∀ (x : C.ob) → Type _
  LRⱽObᴰ x = Σ[ xᴰ ∈ Cᴰ.ob[ x ] ] isLRⱽObᴰ xᴰ

  LRⱽObᴰ→LRⱽ : ∀ {x} → (xᴰ : LRⱽObᴰ x) → LRⱽPresheafᴰ (C [-, x ]) Cᴰ _
  LRⱽObᴰ→LRⱽ xᴰ = (Cᴰ [-][-, xᴰ .fst ]) , (xᴰ .snd)

  AllLRⱽ : Type _
  AllLRⱽ = ∀ {x} xᴰ → isLRⱽObᴰ {x} xᴰ

  LargeExponentialⱽ : ∀ {x} → (xᴰ yᴰ : Cᴰ.ob[ x ]) → Type _
  LargeExponentialⱽ {x} xᴰ yᴰ = Representableⱽ Cᴰ x ((Cᴰ [-][-, xᴰ ]) ⇒ⱽPshLarge (Cᴰ [-][-, yᴰ ]))

  LargeExponentialsⱽ : Type _
  LargeExponentialsⱽ = ∀ {x} xᴰ yᴰ → LargeExponentialⱽ {x} xᴰ yᴰ

  -- The one without the qualifier represents the *small* exponential
  Exponentialⱽ : ∀ {x} ((xᴰ , _×ⱽxᴰ) : LRⱽObᴰ x) (yᴰ : Cᴰ.ob[ x ]) → Type _
  Exponentialⱽ {x} xᴰ yᴰ =
    Representableⱽ Cᴰ x (LRⱽObᴰ→LRⱽ xᴰ ⇒ⱽPshSmall (Cᴰ [-][-, yᴰ ]))
  -- TODO: make an explicit definition for the functor you get out of an LRⱽ

  BinProductsⱽ+Fibration→AllLRⱽ : BinProductsⱽ Cᴰ → isFibration Cᴰ
    → AllLRⱽ
  BinProductsⱽ+Fibration→AllLRⱽ bpⱽ lifts {x} xᴰ {Γ} Γᴰ f =
    (bpⱽ Γᴰ (lifts xᴰ Γ f .fst))
    ◁PshIsoⱽ ×PshIso idPshIso (lifts xᴰ Γ f .snd)

  Exponentialsⱽ : AllLRⱽ → Type _
  Exponentialsⱽ lrⱽ = ∀ {x} (xᴰ yᴰ : Cᴰ.ob[ x ]) → Exponentialⱽ (xᴰ , lrⱽ xᴰ) yᴰ
