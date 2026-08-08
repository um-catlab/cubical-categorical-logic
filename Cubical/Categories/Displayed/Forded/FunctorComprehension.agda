{-# OPTIONS --lossy-unification #-}
{-

  FORDED DISPLAYED FUNCTOR COMPREHENSION.

  Cubical.Categories.Displayed.FunctorComprehension builds a `Functorᴰ`
  by first building `Functor (∫C Cᴰ) (∫C Dᴰ)` and then projecting `.snd`
  off both the object and the hom part; its `F-idᴰ` and `F-seqᴰ` are
  `rectify $ ≡out $ (the total functor's law)`.  That roundtrip exists
  only because `Functorᴰ`'s laws are PathPs over the BASE functor's
  laws, and the cheapest way to produce such a PathP is to prove the
  law in the total category.

  With forded displayed categories the laws are homogeneous, so the
  roundtrip is unnecessary: `FunctorᶠᴰComprehension` below is built
  directly out of the displayed universal elements' `βᴰ`/`ηᴰ`, with no
  `∫C`, no `∫Prof`, no `∫ues`, and no hom-level `rectify`.

  WHAT DOES NOT GO AWAY.  `F-seqⱽ` is a chain of HOMOGENEOUS equations
  --- every step stays over the base heteromorphism `element ⋆ʳᶜ h`.
  `F-idⱽ` is not: the base functor's own `F-id` is
  `cong intro (⋆IdRʳᶜ element)`, and `element ⋆ʳᶜ id` is a different
  element of the profunctor from `element`.  So one step of `F-idⱽ` is
  genuinely heterogeneous over that path and needs the ford coherences
  plus `Prectify` --- exactly as `Categoryᶠᴰ` needs `idᴰ-coh`/`⋆ᴰ-coh`
  to build `∫ᶠ`.

  Making the ford `Eq`-valued does NOT change this, and the reason is
  worth recording because `Eq` fords are strictly stronger than Path
  ones: an `Eq` ford can be MATCHED, so `F-idⱽ i ei` may be specialised
  to `i := C.id`.  Even then the step stays heterogeneous, because
  `h ⋆ʳᶜ C.id` is `(P ⟪ C.id ⟫) .N-ob d h` --- stuck on the neutral
  functor `P` --- and is only PROPOSITIONALLY `h`.  (Checked: `refl`
  does not prove `h ⋆ʳᶜ Category.id C ≡ h` for a variable profunctor.)
  Fording removes the transports that come from the displayed CATEGORY;
  it does not remove the ones that come from the base profunctor's own
  equations.

-}
module Cubical.Categories.Displayed.Forded.FunctorComprehension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More hiding (rectify; _≡[_]_)

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.Functors.Strict.Base
open import Cubical.Categories.Displayed.Forded
open import Cubical.Categories.Displayed.Forded.Functor

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS ℓSᴰ ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' : Level

open StrictFunctor
open Functorⱽᶠ
open Functor

-- ------------------------------------------------------------------
-- A FORDED DISPLAYED PROFUNCTOR, in relator form: heteromorphisms
-- displayed over heteromorphisms, with both actions forded on their
-- target.
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (P : Profunctor C D ℓS)
  (Cᴰ : Categoryᶠᴰ C ℓCᴰ ℓCᴰ') (Dᴰ : Categoryᶠᴰ D ℓDᴰ ℓDᴰ')
  (ℓSᴰ : Level)
  where
  private
    module C = Category C
    module D = Category D
    module P = ProfunctorNotation P
    module Cᴰ = Categoryᶠᴰ Cᴰ
    module Dᴰ = Categoryᶠᴰ Dᴰ

  record Profunctorᶠᴰ
    : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
           (ℓ-max (ℓ-max ℓS (ℓ-max ℓCᴰ ℓCᴰ'))
                  (ℓ-max (ℓ-max ℓDᴰ ℓDᴰ') (ℓ-suc ℓSᴰ)))) where
    field
      Het[_][_,_] : {c : C.ob} {d : D.ob}
        → P.Het[ d , c ] → Cᴰ.ob[ c ] → Dᴰ.ob[ d ] → Type ℓSᴰ

      -- the D-side (presheaf) action
      ⋆ᶜʳᴰ : {c : C.ob} {d d' : D.ob} {cᴰ : Cᴰ.ob[ c ]}
        {dᴰ : Dᴰ.ob[ d ]} {d'ᴰ : Dᴰ.ob[ d' ]}
        (g : D [ d' , d ]) (h : P.Het[ d , c ]) (k : P.Het[ d' , c ])
        → g P.⋆ᶜʳ h Eq.≡ k
        → Dᴰ.Hom[ g ][ d'ᴰ , dᴰ ] → Het[ h ][ cᴰ , dᴰ ]
        → Het[ k ][ cᴰ , d'ᴰ ]

      -- the C-side (functor) action
      ⋆ʳᶜᴰ : {c c' : C.ob} {d : D.ob} {cᴰ : Cᴰ.ob[ c ]}
        {c'ᴰ : Cᴰ.ob[ c' ]} {dᴰ : Dᴰ.ob[ d ]}
        (h : P.Het[ d , c ]) (f : C [ c , c' ]) (k : P.Het[ d , c' ])
        → h P.⋆ʳᶜ f Eq.≡ k
        → Het[ h ][ cᴰ , dᴰ ] → Cᴰ.Hom[ f ][ cᴰ , c'ᴰ ]
        → Het[ k ][ c'ᴰ , dᴰ ]

      ⋆IdLᶜʳᴰ : {c : C.ob} {d : D.ob} {cᴰ : Cᴰ.ob[ c ]} {dᴰ : Dᴰ.ob[ d ]}
        (i : D [ d , d ]) (ei : D.id Eq.≡ i) (h : P.Het[ d , c ])
        (e : i P.⋆ᶜʳ h Eq.≡ h) (hᴰ : Het[ h ][ cᴰ , dᴰ ])
        → ⋆ᶜʳᴰ i h h e (Dᴰ.idᴰ i ei) hᴰ ≡ hᴰ

      ⋆IdRʳᶜᴰ : {c : C.ob} {d : D.ob} {cᴰ : Cᴰ.ob[ c ]} {dᴰ : Dᴰ.ob[ d ]}
        (h : P.Het[ d , c ]) (i : C [ c , c ]) (ei : C.id Eq.≡ i)
        (e : h P.⋆ʳᶜ i Eq.≡ h) (hᴰ : Het[ h ][ cᴰ , dᴰ ])
        → ⋆ʳᶜᴰ h i h e hᴰ (Cᴰ.idᴰ i ei) ≡ hᴰ

      ⋆Assocᶜᶜʳᴰ : {c : C.ob} {d d' d'' : D.ob} {cᴰ : Cᴰ.ob[ c ]}
        {dᴰ : Dᴰ.ob[ d ]} {d'ᴰ : Dᴰ.ob[ d' ]} {d''ᴰ : Dᴰ.ob[ d'' ]}
        (g : D [ d'' , d' ]) (g' : D [ d' , d ]) (h : P.Het[ d , c ])
        (gg' : D [ d'' , d ]) (egg' : g D.⋆ g' Eq.≡ gg')
        (g'h : P.Het[ d' , c ]) (eg'h : g' P.⋆ᶜʳ h Eq.≡ g'h)
        (k : P.Het[ d'' , c ])
        (e₁ : gg' P.⋆ᶜʳ h Eq.≡ k) (e₂ : g P.⋆ᶜʳ g'h Eq.≡ k)
        (gᴰ : Dᴰ.Hom[ g ][ d''ᴰ , d'ᴰ ]) (g'ᴰ : Dᴰ.Hom[ g' ][ d'ᴰ , dᴰ ])
        (hᴰ : Het[ h ][ cᴰ , dᴰ ])
        → ⋆ᶜʳᴰ gg' h k e₁ (Dᴰ.⋆ᴰ g g' gg' egg' gᴰ g'ᴰ) hᴰ
          ≡ ⋆ᶜʳᴰ g g'h k e₂ gᴰ (⋆ᶜʳᴰ g' h g'h eg'h g'ᴰ hᴰ)

      ⋆Assocᶜʳᶜᴰ : {c c' : C.ob} {d d' : D.ob}
        {cᴰ : Cᴰ.ob[ c ]} {c'ᴰ : Cᴰ.ob[ c' ]}
        {dᴰ : Dᴰ.ob[ d ]} {d'ᴰ : Dᴰ.ob[ d' ]}
        (g : D [ d' , d ]) (h : P.Het[ d , c ]) (f : C [ c , c' ])
        (gh : P.Het[ d' , c ]) (egh : g P.⋆ᶜʳ h Eq.≡ gh)
        (hf : P.Het[ d , c' ]) (ehf : h P.⋆ʳᶜ f Eq.≡ hf)
        (k : P.Het[ d' , c' ])
        (e₁ : gh P.⋆ʳᶜ f Eq.≡ k) (e₂ : g P.⋆ᶜʳ hf Eq.≡ k)
        (gᴰ : Dᴰ.Hom[ g ][ d'ᴰ , dᴰ ]) (hᴰ : Het[ h ][ cᴰ , dᴰ ])
        (fᴰ : Cᴰ.Hom[ f ][ cᴰ , c'ᴰ ])
        → ⋆ʳᶜᴰ gh f k e₁ (⋆ᶜʳᴰ g h gh egh gᴰ hᴰ) fᴰ
          ≡ ⋆ᶜʳᴰ g hf k e₂ gᴰ (⋆ʳᶜᴰ h f hf ehf hᴰ fᴰ)

      ⋆Assocʳᶜᶜᴰ : {c c' c'' : C.ob} {d : D.ob}
        {cᴰ : Cᴰ.ob[ c ]} {c'ᴰ : Cᴰ.ob[ c' ]} {c''ᴰ : Cᴰ.ob[ c'' ]}
        {dᴰ : Dᴰ.ob[ d ]}
        (h : P.Het[ d , c ]) (f : C [ c , c' ]) (f' : C [ c' , c'' ])
        (hf : P.Het[ d , c' ]) (ehf : h P.⋆ʳᶜ f Eq.≡ hf)
        (ff' : C [ c , c'' ]) (eff' : f C.⋆ f' Eq.≡ ff')
        (k : P.Het[ d , c'' ])
        (e₁ : hf P.⋆ʳᶜ f' Eq.≡ k) (e₂ : h P.⋆ʳᶜ ff' Eq.≡ k)
        (hᴰ : Het[ h ][ cᴰ , dᴰ ]) (fᴰ : Cᴰ.Hom[ f ][ cᴰ , c'ᴰ ])
        (f'ᴰ : Cᴰ.Hom[ f' ][ c'ᴰ , c''ᴰ ])
        → ⋆ʳᶜᴰ hf f' k e₁ (⋆ʳᶜᴰ h f hf ehf hᴰ fᴰ) f'ᴰ
          ≡ ⋆ʳᶜᴰ h ff' k e₂ hᴰ (Cᴰ.⋆ᴰ f f' ff' eff' fᴰ f'ᴰ)

      -- FORD COHERENCES, as in Categoryᶠᴰ
      ⋆ᶜʳᴰ-coh : {c : C.ob} {d d' : D.ob} {cᴰ : Cᴰ.ob[ c ]}
        {dᴰ : Dᴰ.ob[ d ]} {d'ᴰ : Dᴰ.ob[ d' ]}
        (g : D [ d' , d ]) (h : P.Het[ d , c ]) (k k' : P.Het[ d' , c ])
        (e : g P.⋆ᶜʳ h Eq.≡ k) (e' : g P.⋆ᶜʳ h Eq.≡ k') (pth : k ≡ k')
        (gᴰ : Dᴰ.Hom[ g ][ d'ᴰ , dᴰ ]) (hᴰ : Het[ h ][ cᴰ , dᴰ ])
        → PathP (λ j → Het[ pth j ][ cᴰ , d'ᴰ ])
            (⋆ᶜʳᴰ g h k e gᴰ hᴰ) (⋆ᶜʳᴰ g h k' e' gᴰ hᴰ)

      ⋆ʳᶜᴰ-coh : {c c' : C.ob} {d : D.ob} {cᴰ : Cᴰ.ob[ c ]}
        {c'ᴰ : Cᴰ.ob[ c' ]} {dᴰ : Dᴰ.ob[ d ]}
        (h : P.Het[ d , c ]) (f : C [ c , c' ]) (k k' : P.Het[ d , c' ])
        (e : h P.⋆ʳᶜ f Eq.≡ k) (e' : h P.⋆ʳᶜ f Eq.≡ k') (pth : k ≡ k')
        (hᴰ : Het[ h ][ cᴰ , dᴰ ]) (fᴰ : Cᴰ.Hom[ f ][ cᴰ , c'ᴰ ])
        → PathP (λ j → Het[ pth j ][ c'ᴰ , dᴰ ])
            (⋆ʳᶜᴰ h f k e hᴰ fᴰ) (⋆ʳᶜᴰ h f k' e' hᴰ fᴰ)

      isSetHetᴰ : {c : C.ob} {d : D.ob} {cᴰ : Cᴰ.ob[ c ]}
        {dᴰ : Dᴰ.ob[ d ]} {h : P.Het[ d , c ]} → isSet Het[ h ][ cᴰ , dᴰ ]

module ProfᶠᴰNotation {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {P : Profunctor C D ℓS}
  {Cᴰ : Categoryᶠᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᶠᴰ D ℓDᴰ ℓDᴰ'} {ℓSᴰ : Level}
  (Pᴰ : Profunctorᶠᴰ P Cᴰ Dᴰ ℓSᴰ) where
  open Profunctorᶠᴰ Pᴰ public

  private
    module P = ProfunctorNotation P
    module Cᴰ = Categoryᶠᴰ Cᴰ
    module Dᴰ = Categoryᶠᴰ Dᴰ

  -- reasoning about the fibres of Het[_][_,_] over the hSet of
  -- heteromorphisms.  This is the ONLY reindexing left.
  module HetR {c : Category.ob C} {d : Category.ob D}
    {cᴰ : Cᴰ.ob[ c ]} {dᴰ : Dᴰ.ob[ d ]} =
    hSetReasoning (P.Bif-ob d c) (λ h → Het[ h ][ cᴰ , dᴰ ])

-- ------------------------------------------------------------------
-- DISPLAYED UNIVERSAL ELEMENTS, forded.  βᴰ and ηᴰ are ORDINARY
-- equations, not PathPs, so nothing has to be routed through ∫.
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {P : Profunctor C D ℓS}
  {Cᴰ : Categoryᶠᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᶠᴰ D ℓDᴰ ℓDᴰ'} {ℓSᴰ : Level}
  (Pᴰ : Profunctorᶠᴰ P Cᴰ Dᴰ ℓSᴰ)
  where
  private
    module C = Category C
    module D = Category D
    module P = ProfunctorNotation P
    module Cᴰ = Categoryᶠᴰ Cᴰ
    module Dᴰ = Categoryᶠᴰ Dᴰ
  open ProfᶠᴰNotation Pᴰ

  record UniversalElementᶠᴰ {c : C.ob}
    (ue : UniversalElement D (P ⟅ c ⟆)) (cᴰ : Cᴰ.ob[ c ])
    : Type (ℓ-max (ℓ-max ℓD ℓD') (ℓ-max (ℓ-max ℓS ℓSᴰ)
                                        (ℓ-max ℓDᴰ ℓDᴰ'))) where
    private module ue = UniversalElementNotation ue
    field
      vertexᴰ : Dᴰ.ob[ ue.vertex ]
      elementᴰ : Het[ ue.element ][ cᴰ , vertexᴰ ]

      introᴰ : {d : D.ob} {dᴰ : Dᴰ.ob[ d ]}
        (h : P.Het[ d , c ]) (g : D [ d , ue.vertex ])
        → ue.intro h Eq.≡ g
        → Het[ h ][ cᴰ , dᴰ ] → Dᴰ.Hom[ g ][ dᴰ , vertexᴰ ]

      βᴰ : {d : D.ob} {dᴰ : Dᴰ.ob[ d ]}
        (h : P.Het[ d , c ]) (g : D [ d , ue.vertex ])
        (eg : ue.intro h Eq.≡ g) (e : g P.⋆ᶜʳ ue.element Eq.≡ h)
        (hᴰ : Het[ h ][ cᴰ , dᴰ ])
        → ⋆ᶜʳᴰ g ue.element h e (introᴰ h g eg hᴰ) elementᴰ ≡ hᴰ

      ηᴰ : {d : D.ob} {dᴰ : Dᴰ.ob[ d ]}
        (g : D [ d , ue.vertex ]) (h : P.Het[ d , c ])
        (e : g P.⋆ᶜʳ ue.element Eq.≡ h) (eg : ue.intro h Eq.≡ g)
        (gᴰ : Dᴰ.Hom[ g ][ dᴰ , vertexᴰ ])
        → introᴰ h g eg (⋆ᶜʳᴰ g ue.element h e gᴰ elementᴰ) ≡ gᴰ

  UniversalElementsᶠᴰ : (ues : UniversalElements P) → Type _
  UniversalElementsᶠᴰ ues =
    ∀ (c : C.ob) (cᴰ : Cᴰ.ob[ c ]) → UniversalElementᶠᴰ (ues c) cᴰ

-- ------------------------------------------------------------------
-- THE COMPREHENSION, built directly --- no ∫, no hom-level rectify.
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {P : Profunctor C D ℓS}
  {Cᴰ : Categoryᶠᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᶠᴰ D ℓDᴰ ℓDᴰ'} {ℓSᴰ : Level}
  (Pᴰ : Profunctorᶠᴰ P Cᴰ Dᴰ ℓSᴰ)
  (ues : UniversalElements P)
  (uesᴰ : UniversalElementsᶠᴰ Pᴰ ues)
  where
  private
    module C = Category C
    module D = Category D
    module P = ProfunctorNotation P
    module Cᴰ = Categoryᶠᴰ Cᴰ
    module Dᴰ = Categoryᶠᴰ Dᴰ
  open ProfᶠᴰNotation Pᴰ

  private
    module ue {c : C.ob} = UniversalElementNotation (ues c)

  Comprehensionᶠ : StrictFunctor C D
  Comprehensionᶠ = Fun→Strict (FunctorComprehension P ues)

  private
    module F = StrictFunctor Comprehensionᶠ
    module u {c : C.ob} {cᴰ : Cᴰ.ob[ c ]} =
      UniversalElementᶠᴰ (uesᴰ c cᴰ)

    E : (c : C.ob) → P.Het[ ue.vertex {c} , c ]
    E c = ue.element {c}


  FunctorᶠᴰComprehension : Functorᶠᴰ Comprehensionᶠ Cᴰ Dᴰ
  FunctorᶠᴰComprehension .F-obⱽ {c} cᴰ = u.vertexᴰ {c} {cᴰ}
  FunctorᶠᴰComprehension .F-homⱽ {x} {y} {f} {xᴰ} {yᴰ} fᴰ =
    u.introᴰ {y} {yᴰ} (E x P.⋆ʳᶜ f) (F.F-hom f) Eq.refl
      (⋆ʳᶜᴰ (E x) f (E x P.⋆ʳᶜ f) Eq.refl (u.elementᴰ {x} {xᴰ}) fᴰ)
  FunctorᶠᴰComprehension .F-idⱽ {x} {xᴰ} i ei iᴰ eiᴰ = sym $
    cong (u.introᴰ {x} {xᴰ} (E x P.⋆ʳᶜ i) (F.F-hom i) Eq.refl) inner
    ∙ u.ηᴰ {x} {xᴰ} (F.F-hom i) (E x P.⋆ʳᶜ i) (Eq.pathToEq ue.β) Eq.refl
        (Dᴰ.idᴰ (F.F-hom i) ι)
    where
    ι : D.id Eq.≡ F.F-hom i
    ι = F.F-id i ei

    Eᴰ = u.elementᴰ {x} {xᴰ}

    e₁ : E x P.⋆ʳᶜ i ≡ E x
    e₁ = cong (E x P.⋆ʳᶜ_) (Eq.eqToPath (Eq.sym ei)) ∙ P.⋆IdRʳᶜ (E x)

    e₂ : F.F-hom i P.⋆ᶜʳ E x ≡ E x
    e₂ = cong (P._⋆ᶜʳ E x) (Eq.eqToPath (Eq.sym ι)) ∙ P.⋆IdLᶜʳ (E x)

    inner : ⋆ʳᶜᴰ (E x) i (E x P.⋆ʳᶜ i) Eq.refl Eᴰ iᴰ
          ≡ ⋆ᶜʳᴰ (F.F-hom i) (E x) (E x P.⋆ʳᶜ i) (Eq.pathToEq ue.β)
              (Dᴰ.idᴰ (F.F-hom i) ι) Eᴰ
    inner = HetR.Prectify $ HetR.≡out $
        ΣPathP (e₁ ,
          ⋆ʳᶜᴰ-coh (E x) i (E x P.⋆ʳᶜ i) (E x) Eq.refl
            (Eq.pathToEq e₁) e₁ Eᴰ iᴰ)
      ∙ ΣPathP (refl ,
          cong (⋆ʳᶜᴰ (E x) i (E x) (Eq.pathToEq e₁) Eᴰ) (sym eiᴰ)
          ∙ ⋆IdRʳᶜᴰ (E x) i ei (Eq.pathToEq e₁) Eᴰ)
      ∙ ΣPathP (refl ,
          sym (⋆IdLᶜʳᴰ (F.F-hom i) ι (E x) (Eq.pathToEq e₂) Eᴰ))
      ∙ ΣPathP (sym e₁ ,
          ⋆ᶜʳᴰ-coh (F.F-hom i) (E x) (E x) (E x P.⋆ʳᶜ i)
            (Eq.pathToEq e₂) (Eq.pathToEq ue.β) (sym e₁)
            (Dᴰ.idᴰ (F.F-hom i) ι) Eᴰ)
  FunctorᶠᴰComprehension .F-seqⱽ {x} {y} {z} {xᴰ} {yᴰ} {zᴰ}
    f g h e fᴰ gᴰ hᴰ eᴰ = sym $
    cong (u.introᴰ {z} {zᴰ} (E x P.⋆ʳᶜ h) (F.F-hom h) Eq.refl) inner
    ∙ u.ηᴰ {z} {zᴰ} (F.F-hom h) (E x P.⋆ʳᶜ h) (Eq.pathToEq ue.β) Eq.refl
        (Dᴰ.⋆ᴰ (F.F-hom f) (F.F-hom g) (F.F-hom h) σ Ff Fg)
    where
    σ : F.F-hom f D.⋆ F.F-hom g Eq.≡ F.F-hom h
    σ = F.F-seq f g h e

    Ff = FunctorᶠᴰComprehension .F-homⱽ {x} {y} {f} {xᴰ} {yᴰ} fᴰ
    Fg = FunctorᶠᴰComprehension .F-homⱽ {y} {z} {g} {yᴰ} {zᴰ} gᴰ

    e₂ : F.F-hom f P.⋆ᶜʳ (E y P.⋆ʳᶜ g) ≡ E x P.⋆ʳᶜ h
    e₂ = sym (P.⋆Assocᶜʳᶜ (F.F-hom f) (E y) g)
       ∙ cong (P._⋆ʳᶜ g) ue.β
       ∙ P.⋆Assocʳᶜᶜ (E x) f g
       ∙ cong (E x P.⋆ʳᶜ_) (Eq.eqToPath e)

    e₁ : (E x P.⋆ʳᶜ f) P.⋆ʳᶜ g ≡ E x P.⋆ʳᶜ h
    e₁ = P.⋆Assocʳᶜᶜ (E x) f g ∙ cong (E x P.⋆ʳᶜ_) (Eq.eqToPath e)

    inner : ⋆ʳᶜᴰ (E x) h (E x P.⋆ʳᶜ h) Eq.refl (u.elementᴰ {x} {xᴰ}) hᴰ
          ≡ ⋆ᶜʳᴰ (F.F-hom h) (E z) (E x P.⋆ʳᶜ h) (Eq.pathToEq ue.β)
              (Dᴰ.⋆ᴰ (F.F-hom f) (F.F-hom g) (F.F-hom h) σ Ff Fg)
              (u.elementᴰ {z} {zᴰ})
    inner =
        cong (⋆ʳᶜᴰ (E x) h (E x P.⋆ʳᶜ h) Eq.refl (u.elementᴰ {x} {xᴰ}))
          (sym eᴰ)
      ∙ sym (⋆Assocʳᶜᶜᴰ (E x) f g (E x P.⋆ʳᶜ f) Eq.refl h e
              (E x P.⋆ʳᶜ h) (Eq.pathToEq e₁) Eq.refl
              (u.elementᴰ {x} {xᴰ}) fᴰ gᴰ)
      ∙ cong (λ w → ⋆ʳᶜᴰ (E x P.⋆ʳᶜ f) g (E x P.⋆ʳᶜ h)
                      (Eq.pathToEq e₁) w gᴰ)
          (sym (u.βᴰ {y} {yᴰ} (E x P.⋆ʳᶜ f) (F.F-hom f) Eq.refl
                 (Eq.pathToEq ue.β)
                 (⋆ʳᶜᴰ (E x) f (E x P.⋆ʳᶜ f) Eq.refl
                   (u.elementᴰ {x} {xᴰ}) fᴰ)))
      ∙ ⋆Assocᶜʳᶜᴰ (F.F-hom f) (E y) g (E x P.⋆ʳᶜ f)
          (Eq.pathToEq ue.β) (E y P.⋆ʳᶜ g) Eq.refl (E x P.⋆ʳᶜ h)
          (Eq.pathToEq e₁) (Eq.pathToEq e₂)
          Ff (u.elementᴰ {y} {yᴰ}) gᴰ
      ∙ cong (⋆ᶜʳᴰ (F.F-hom f) (E y P.⋆ʳᶜ g) (E x P.⋆ʳᶜ h)
               (Eq.pathToEq e₂) Ff)
          (sym (u.βᴰ {z} {zᴰ} (E y P.⋆ʳᶜ g) (F.F-hom g) Eq.refl
                 (Eq.pathToEq ue.β)
                 (⋆ʳᶜᴰ (E y) g (E y P.⋆ʳᶜ g) Eq.refl
                   (u.elementᴰ {y} {yᴰ}) gᴰ)))
      ∙ sym (⋆Assocᶜᶜʳᴰ (F.F-hom f) (F.F-hom g) (E z) (F.F-hom h) σ
              (E y P.⋆ʳᶜ g) (Eq.pathToEq ue.β) (E x P.⋆ʳᶜ h)
              (Eq.pathToEq ue.β) (Eq.pathToEq e₂)
              Ff Fg (u.elementᴰ {z} {zᴰ}))
