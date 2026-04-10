-- Displayed and vertical fixed points
--
-- These are "displayed diagrammatic concepts", maybe the properties
-- we prove here can be generalized?

-- TODO: split this into base and properties
module Cubical.Categories.Displayed.FixedPoint where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.More

import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.FixedPoint
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Instances.Reindex.Base
open import Cubical.Categories.Displayed.Instances.Reindex.Cartesian
open import Cubical.Categories.Displayed.Instances.Reindex.Fibration
open import Cubical.Categories.Displayed.Instances.Reindex.Properties

open Category
open Functor
open Functorᴰ
open NatTrans
open NatTransᴰ

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  fixed-pointᴰ : ∀ {𝟙 x}{f : C [ x , x ]}
    → fixed-point C 𝟙 f
    → (𝟙ᴰ : Cᴰ.ob[ 𝟙 ])
    → {xᴰ : Cᴰ.ob[ x ]}
    → Cᴰ.Hom[ f ][ xᴰ , xᴰ ] → Type _
  fixed-pointᴰ {𝟙} {x} {f} (fix⟨f⟩ , fix⟨f⟩f≡fix⟨f⟩) 𝟙ᴰ {xᴰ} fᴰ =
    Σ[ fixᴰ⟨fᴰ⟩ ∈ Cᴰ.Hom[ fix⟨f⟩ ][ 𝟙ᴰ , xᴰ ] ]
    ((fixᴰ⟨fᴰ⟩ Cᴰ.⋆ᴰ fᴰ) Cᴰ.≡[ fix⟨f⟩f≡fix⟨f⟩ ] fixᴰ⟨fᴰ⟩)

  fixed-pointⱽ : (y : C.ob) (𝟙ⱽ : Cᴰ.ob[ y ]) {xⱽ : Cᴰ.ob[ y ]} →
                  Cᴰ.v[ y ] [ xⱽ , xⱽ ] → Type ℓCᴰ'
  fixed-pointⱽ = λ (y : C .ob) → fixed-point Cᴰ.v[ y ]

  module _ (EqId⋆ : ∀ {x} → C.id {x} C.⋆ C.id Eq.≡ C.id) (y : C.ob) (𝟙ⱽ : Cᴰ.ob[ y ]) {xⱽ : Cᴰ.ob[ y ]}
    (fⱽ : Cᴰ.v[ y ] [ xⱽ , xⱽ ]) where
    fixed-pointⱽEq : Type _
    fixed-pointⱽEq = fixed-point (Cᴰ.Eqv[ EqId⋆ ] y) 𝟙ⱽ fⱽ

    fixed-pointⱽEq→ⱽ : fixed-pointⱽEq → fixed-pointⱽ y 𝟙ⱽ fⱽ
    fixed-pointⱽEq→ⱽ fix⟨fⱽ⟩ .fst = fix⟨fⱽ⟩ .fst
    fixed-pointⱽEq→ⱽ fix⟨fⱽ⟩ .snd = Cᴰ.rectifyOut
      (Cᴰ.reind-filler⁻ _ ∙ Cᴰ.reindEq-filler _ ∙ Cᴰ.≡in (fix⟨fⱽ⟩ .snd))

  -- TODO: this is probably a way better definition to use in practice bc of the lack of reind
  fixed-pointⱽ' : (y : C.ob) (𝟙ⱽ : Cᴰ.ob[ y ]) {xⱽ : Cᴰ.ob[ y ]} →
                  Cᴰ.v[ y ] [ xⱽ , xⱽ ] → Type ℓCᴰ'
  fixed-pointⱽ' y = fixed-pointᴰ (id-fixed-point C y)

  -- -- TODO: is this one even better?
  -- module _ (y : C.ob) (𝟙ⱽ : Cᴰ.ob[ y ]) {xⱽ : Cᴰ.ob[ y ]} (id~ : singl (C .id {x = y})) (fⱽ : Cᴰ.Hom[ id~ .fst ][ xⱽ , xⱽ ]) where
  --   fixed-pointⱽ'' : Type ℓCᴰ'
  --   fixed-pointⱽ'' = fixed-pointᴰ (id~-fixed-point C y id~) 𝟙ⱽ fⱽ

  --   fixed-pointⱽ''→ⱽ : fixed-pointⱽ y 𝟙 fⱽ
  --   fixed-pointⱽ''→ⱽ = ?


  module _ (y : C.ob) (𝟙ⱽ : Cᴰ.ob[ y ]) {xⱽ : Cᴰ.ob[ y ]} (fⱽ : Cᴰ.v[ y ] [ xⱽ , xⱽ ]) where
    fixed-pointⱽ'→ⱽ : fixed-pointⱽ' y 𝟙ⱽ fⱽ → fixed-pointⱽ y 𝟙ⱽ fⱽ
    fixed-pointⱽ'→ⱽ fpⱽ' .fst = fpⱽ' .fst
    fixed-pointⱽ'→ⱽ fpⱽ' .snd = Cᴰ.rectifyOut (Cᴰ.reind-filler⁻ _ ∙ (Cᴰ.≡in $ fpⱽ' .snd))

  -- Theorem: To construct a displayed fixed point it is
  -- sufficient to have a vertical fixed point for a cartesian
  -- lift of the fixed point in the base.
  module _ {𝟙 x}{f : C [ x , x ]}
      (fix⟨f⟩ : fixed-point C 𝟙 f)
      (𝟙ᴰ : Cᴰ.ob[ 𝟙 ])
      {xᴰ : Cᴰ.ob[ x ]}
      (fᴰ : Cᴰ.Hom[ f ][ xᴰ , xᴰ ])
      (fix⟨f⟩*xᴰ : CartesianLift Cᴰ (fix⟨f⟩ .fst) xᴰ) where
    private module fix⟨f⟩*xᴰ = CartesianLiftNotation Cᴰ fix⟨f⟩*xᴰ
    fixed-pointⱽ→ᴰ :
      fixed-pointⱽ 𝟙 𝟙ᴰ {xⱽ = fix⟨f⟩*xᴰ .fst}
        (fix⟨f⟩*xᴰ.introᴰ (Cᴰ.reind (C.⟨ C.⋆IdL _ ⟩⋆⟨ refl ⟩ ∙ fix⟨f⟩ .snd ∙ sym (C.⋆IdL _))
          (fix⟨f⟩*xᴰ.πⱽ Cᴰ.⋆ᴰ fᴰ)))
      → fixed-pointᴰ fix⟨f⟩ 𝟙ᴰ fᴰ
    fixed-pointⱽ→ᴰ fixⱽ⟨f⟩ .fst = Cᴰ.reind (C.⋆IdL _) $ fixⱽ⟨f⟩ .fst fix⟨f⟩*xᴰ.⋆πⱽ
    fixed-pointⱽ→ᴰ fixⱽ⟨f⟩ .snd = Cᴰ.rectifyOut
      (Cᴰ.⟨ Cᴰ.reind-filler⁻ _ ∙ refl ⟩⋆⟨⟩
      -- (fixⱽ⟨f⟩ ⋆πⱽ) ⋆ᴰ fᴰ
      ∙ (Cᴰ.⟨ fix⟨f⟩*xᴰ.⋆πⱽ≡⋆ᴰπⱽ _ ⟩⋆⟨⟩ ∙ Cᴰ.⋆Assoc _ _ _)
      -- fixⱽ⟨f⟩ ⋆ᴰ introᴰ _ ⋆πⱽ
      ∙ Cᴰ.⟨⟩⋆⟨ Cᴰ.reind-filler _ ∙ (sym $ fix⟨f⟩*xᴰ.βᴰ _) ⟩
      ∙ sym fix⟨f⟩*xᴰ.⋆πⱽ-natural
      ∙ fix⟨f⟩*xᴰ.⟨ Cᴰ.reind-filler _ ∙ (Cᴰ.≡in $ fixⱽ⟨f⟩ .snd) ⟩⋆πⱽ
      -- fixⱽ⟨f⟩ ⋆πⱽ
      ∙ Cᴰ.reind-filler _)

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ') (F : Functor C D)
  where
  private
    module C = Category C
    module D = Category D
    module Dᴰ = Fibers Dᴰ
    module F*Dᴰ = Fibers (reindex Dᴰ F)
  module _ {x : C.ob} {𝟙ⱽ xⱽ : Dᴰ.ob[ F ⟅ x ⟆ ]}{fⱽ : Dᴰ.Hom[ F ⟪ C.id ⟫ ][ xⱽ , xⱽ ]} where
    reindexFixed-pointⱽ :
      fixed-pointⱽ Dᴰ (F ⟅ x ⟆) 𝟙ⱽ (Dᴰ.reind (F .F-id) fⱽ)
      → fixed-pointⱽ (reindex Dᴰ F) x 𝟙ⱽ fⱽ
    reindexFixed-pointⱽ fixⱽ⟨fⱽ⟩ .fst = Dᴰ.reind (sym $ F .F-id) $ fixⱽ⟨fⱽ⟩ .fst
    reindexFixed-pointⱽ fixⱽ⟨fⱽ⟩ .snd =
      F*Dᴰ.rectifyOut
      (F*Dᴰ.reind-filler⁻ _
      ∙ change-base {C = Dᴰ.Hom[_][ 𝟙ⱽ , xⱽ ]} (F .F-hom) D.isSetHom (C.⋆IdL _)
        (Dᴰ.reind-revealed-filler⁻ _
        ∙ Dᴰ.⟨ Dᴰ.reind-filler⁻ _ ⟩⋆⟨ Dᴰ.reind-filler _ ⟩
        ∙ Dᴰ.reind-filler _
        ∙ (Dᴰ.≡in $ fixⱽ⟨fⱽ⟩ .snd)
        ∙ Dᴰ.reind-filler _))

  -- Because fixed points are diagrammatic we also have a direct
  -- reindexFixed-pointᴰ theorem
  module _ {𝟙 x : C.ob}{𝟙ᴰ : Dᴰ.ob[ F ⟅ 𝟙 ⟆ ]} {xᴰ : Dᴰ.ob[ F ⟅ x ⟆ ]}
    {f : C [ x , x ]}
    (fix⟨f⟩ : fixed-point C 𝟙 f)
    (fᴰ : Dᴰ.Hom[ F ⟪ f ⟫ ][ xᴰ , xᴰ ])
    where
    reindexFixed-pointᴰ :
      fixed-pointᴰ Dᴰ (F-hom-fixed-point F fix⟨f⟩) 𝟙ᴰ fᴰ
      → fixed-pointᴰ (reindex Dᴰ F) fix⟨f⟩ 𝟙ᴰ fᴰ
    reindexFixed-pointᴰ fixᴰ⟨fᴰ⟩ .fst = fixᴰ⟨fᴰ⟩ .fst
    reindexFixed-pointᴰ fixᴰ⟨fᴰ⟩ .snd = Dᴰ.rectifyOut
      (Dᴰ.reind-revealed-filler⁻ _ ∙ Dᴰ.≡in (fixᴰ⟨fᴰ⟩ .snd))

-- Guarded fixed point version of the theorem
--
-- Maybe possible to generalize to where ▷ⱽ is displayed over ▷ in the
-- base (with the current being the trivial case where ▷ = Id)
record GuardedLogic (C : Category ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level) : Type (ℓ-suc (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ'))) where
  field
    Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'
    ▷ⱽ : Functorⱽ Cᴰ Cᴰ
    next : NatTransᴰ (idTrans Id) Idᴰ ▷ⱽ
    isFibCᴰ : isFibration Cᴰ
    termⱽ : Terminalsⱽ Cᴰ
  module C = Category C
  module Cᴰ = Fibers Cᴰ

  field
    gfpⱽ :
    -- ⋆ⱽ here is killing me
      ∀ {A : C.ob} {Aᴰ : Cᴰ.ob[ A ]} (f : Cᴰ.v[ A ] [ ▷ⱽ .F-obᴰ Aᴰ , Aᴰ ])
        → fixed-pointⱽ Cᴰ A (termⱽ A .fst) (next .N-obᴰ Aᴰ Cᴰ.⋆ⱽ f)

  module _
    𝟙 A Aᴰ
    (δ : C [ A , A ])
    (M : C [ A , A ])
    (θᴰ : Cᴰ [ δ ][ ▷ⱽ .F-obᴰ Aᴰ , Aᴰ ])
    (Mᴰ : Cᴰ [ M ][ Aᴰ , Aᴰ ])
    (gfix⟨M⟩ : fixed-point C 𝟙 (δ C.⋆ M))
    where
    private
      module isFibCᴰ = FibrationNotation Cᴰ isFibCᴰ
    gfixⱽ→ᴰ : fixed-pointᴰ Cᴰ gfix⟨M⟩ (termⱽ 𝟙 .fst)
      ((next .N-obᴰ Aᴰ Cᴰ.⋆ⱽᴰ θᴰ) Cᴰ.⋆ᴰ Mᴰ)
    gfixⱽ→ᴰ = fixed-pointⱽ→ᴰ Cᴰ gfix⟨M⟩ (termⱽ 𝟙 .fst)
      ((next .N-obᴰ Aᴰ Cᴰ.⋆ⱽᴰ θᴰ) Cᴰ.⋆ᴰ Mᴰ)
      (isFibCᴰ Aᴰ 𝟙 (gfix⟨M⟩ .fst))
      (subst (fixed-pointⱽ Cᴰ 𝟙 (termⱽ 𝟙 .fst))
        (Cᴰ.rectifyOut
          (Cᴰ.reind-filler⁻ _
          ∙ sym (isFibCᴰ.introᴰ≡' (sym (C.⋆IdL C.id))
            (Cᴰ.reind-filler⁻ _
            -- πⱽ ⋆ᴰ (next ⋆ⱽᴰ θᴰ) ⋆ᴰ Mᴰ
            ∙ Cᴰ.⟨⟩⋆⟨ Cᴰ.⟨ Cᴰ.reind-filler⁻ _ ⟩⋆⟨⟩ ∙ Cᴰ.⋆Assoc _ _ _ ⟩ ∙ sym (Cᴰ.⋆Assoc _ _ _)
            ∙ Cᴰ.⟨ ∫NT next .N-hom _ ⟩⋆⟨⟩ -- naturality of next
            ∙ Cᴰ.⋆Assoc _ _ _
            -- next ⋆ᴰ ▷ⱽ πⱽ ⋆ᴰ θᴰ ⋆ᴰ Mᴰ
            ∙ Cᴰ.⟨⟩⋆⟨ Cᴰ.reind-filler _ ∙ sym (Cᴰ.⋆IdL _) ∙ sym (isFibCᴰ.βᴰ _) ⟩ ∙ sym isFibCᴰ.⋆πⱽ-natural
            -- (next ⋆ᴰ introⱽ _) ⋆πⱽ
            ))))
        (gfpⱽ ((isFibCᴰ.introⱽ (Cᴰ.reind (C.⟨ C.⋆IdL _ ⟩⋆⟨ refl ⟩ ∙ gfix⟨M⟩ .snd) (▷ⱽ .F-homᴰ isFibCᴰ.πⱽ Cᴰ.⋆ᴰ (θᴰ Cᴰ.⋆ᴰ Mᴰ)))))))

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'} (F : Functor C D) (Dᴰ : GuardedLogic D ℓDᴰ ℓDᴰ') where
  private
    module Dᴰ = GuardedLogic Dᴰ
    module F*Dᴰ = Fibers (reindex Dᴰ.Cᴰ F)
  open GuardedLogic
  reindexGuardedLogic : GuardedLogic C ℓDᴰ ℓDᴰ'
  reindexGuardedLogic .Cᴰ = reindex Dᴰ.Cᴰ F
  reindexGuardedLogic .▷ⱽ =
    introFⱽ (Dᴰ.▷ⱽ ∘Fⱽᴰ π Dᴰ.Cᴰ F)
  -- TODO: generalize?
  reindexGuardedLogic .next .N-obᴰ xᴰ = Dᴰ.Cᴰ.reind (sym (F .F-id)) $ Dᴰ.next .N-obᴰ xᴰ
  reindexGuardedLogic .next .N-homᴰ fᴰ =
    Dᴰ.Cᴰ.rectifyOut (Dᴰ.Cᴰ.reind-revealed-filler⁻ _ ∙ Dᴰ.Cᴰ.⟨⟩⋆⟨ Dᴰ.Cᴰ.reind-filler⁻ _ ⟩
      ∙ ∫NT Dᴰ.next .N-hom _ ∙ Dᴰ.Cᴰ.⟨ Dᴰ.Cᴰ.reind-filler _ ⟩⋆⟨⟩
      ∙ Dᴰ.Cᴰ.reind-revealed-filler _)
  reindexGuardedLogic .isFibCᴰ =
    -- TODO: Why is this so slow
    isFibrationReindex {ℓC = ℓC}{ℓC' = ℓC'}{ℓD = ℓD}{ℓD' = ℓD'}{C = C}{D = D} Dᴰ.Cᴰ F Dᴰ.isFibCᴰ
  reindexGuardedLogic .termⱽ = TerminalsⱽReindex F Dᴰ.termⱽ
  reindexGuardedLogic .gfpⱽ {A} {Aᴰ} f = reindexFixed-pointⱽ Dᴰ.Cᴰ F
    (subst
      (fixed-pointⱽ Dᴰ.Cᴰ (F ⟅ A ⟆)
       (TerminalsⱽReindex F Dᴰ.termⱽ A .fst))
      (Dᴰ.Cᴰ.rectifyOut (Dᴰ.Cᴰ.reind-filler⁻ _
        ∙ Dᴰ.Cᴰ.⟨⟩⋆⟨ Dᴰ.Cᴰ.reind-filler⁻ _ ⟩
        ∙ Dᴰ.Cᴰ.⟨ Dᴰ.Cᴰ.reind-filler _ ⟩⋆⟨⟩
        ∙ Dᴰ.Cᴰ.reind-revealed-filler _
        ∙ change-base⁻ {C = Dᴰ.Cᴰ.Hom[_][ Aᴰ , Aᴰ ]} (F .F-hom) (F*Dᴰ.reind-filler _)
        ∙ Dᴰ.Cᴰ.reind-filler _))
      (Dᴰ.gfpⱽ (Dᴰ.Cᴰ.reind (F .F-id) f)))
