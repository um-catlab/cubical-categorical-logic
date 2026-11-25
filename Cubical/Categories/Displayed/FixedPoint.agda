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
open import Cubical.Categories.Displayed.ChosenReind
open Cubical.Categories.Displayed.ChosenReind public using (TransportReindInst)
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Instances.Reindex.Base
open import Cubical.Categories.Displayed.Instances.Reindex.ChosenReind
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
    module _ ⦃ cr : ChosenReind Cᴰ ⦄ where
      private
        module CR = ChosenReindNotation Cᴰ
      fixed-pointⱽ→ᴰ :
        fixed-pointⱽ 𝟙 𝟙ᴰ {xⱽ = fix⟨f⟩*xᴰ .fst}
          (fix⟨f⟩*xᴰ.introᴰ (CR.reind⟨ C.⟨ C.⋆IdL _ ⟩⋆⟨ refl ⟩
              ∙ fix⟨f⟩ .snd ∙ sym (C.⋆IdL _) ⟩
            (fix⟨f⟩*xᴰ.πⱽ Cᴰ.⋆ᴰ fᴰ)))
        → fixed-pointᴰ fix⟨f⟩ 𝟙ᴰ fᴰ
      fixed-pointⱽ→ᴰ fixⱽ⟨f⟩ .fst =
        CR.reind⟨ C.⋆IdL _ ⟩ $ fixⱽ⟨f⟩ .fst fix⟨f⟩*xᴰ.⋆πⱽ
      fixed-pointⱽ→ᴰ fixⱽ⟨f⟩ .snd = Cᴰ.rectifyOut
        (Cᴰ.⟨ CR.reind-∫≡ _ _ ⟩⋆⟨⟩
        ∙ (Cᴰ.⟨ fix⟨f⟩*xᴰ.⋆πⱽ≡⋆ᴰπⱽ _ ⟩⋆⟨⟩ ∙ Cᴰ.⋆Assoc _ _ _)
        ∙ Cᴰ.⟨⟩⋆⟨ sym (CR.reind-∫≡ _ _) ∙ (sym $ fix⟨f⟩*xᴰ.βᴰ _) ⟩
        ∙ sym fix⟨f⟩*xᴰ.⋆πⱽ-natural
        ∙ fix⟨f⟩*xᴰ.⟨ Cᴰ.reind-filler _ ∙ (Cᴰ.≡in $ fixⱽ⟨f⟩ .snd) ⟩⋆πⱽ
        ∙ sym (CR.reind-∫≡ _ _))

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
    module _ ⦃ cr : ChosenReind Cᴰ ⦄ where
      private
        module CR = ChosenReindNotation Cᴰ
        fixᴹ = gfpⱽ (isFibCᴰ.introⱽ
          (CR.reind⟨ C.⟨ C.⋆IdL _ ⟩⋆⟨ refl ⟩ ∙ gfix⟨M⟩ .snd ⟩
          (▷ⱽ .F-homᴰ isFibCᴰ.πⱽ Cᴰ.⋆ᴰ (θᴰ Cᴰ.⋆ᴰ Mᴰ))))
      gfixⱽ→ᴰ : fixed-pointᴰ Cᴰ gfix⟨M⟩ (termⱽ 𝟙 .fst)
        ((next .N-obᴰ Aᴰ CR.⋆ⱽᴰ θᴰ) Cᴰ.⋆ᴰ Mᴰ)
      gfixⱽ→ᴰ = fixed-pointⱽ→ᴰ Cᴰ gfix⟨M⟩ (termⱽ 𝟙 .fst)
        ((next .N-obᴰ Aᴰ CR.⋆ⱽᴰ θᴰ) Cᴰ.⋆ᴰ Mᴰ)
        (isFibCᴰ Aᴰ 𝟙 (gfix⟨M⟩ .fst))
        ( fixᴹ .fst
        , cong (fixᴹ .fst Cᴰ.⋆ⱽ_)
            (Cᴰ.rectifyOut
              (isFibCᴰ.introᴰ≡' (sym (C.⋆IdL C.id))
                (CR.reind-∫≡ _ _
                ∙ Cᴰ.⟨⟩⋆⟨ Cᴰ.⟨ CR.reind-∫≡ _ _ ⟩⋆⟨⟩ ∙ Cᴰ.⋆Assoc _ _ _ ⟩
                ∙ sym (Cᴰ.⋆Assoc _ _ _)
                ∙ Cᴰ.⟨ ∫NT next .N-hom _ ⟩⋆⟨⟩
                ∙ Cᴰ.⋆Assoc _ _ _
                ∙ Cᴰ.⟨⟩⋆⟨ sym (CR.reind-∫≡ _ _) ∙ sym (Cᴰ.⋆IdL _)
                    ∙ sym (isFibCᴰ.βᴰ _) ⟩
                ∙ sym isFibCᴰ.⋆πⱽ-natural)
              ∙ sym (Cᴰ.reind-filler⁻ _)))
          ∙ fixᴹ .snd)

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

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ') (F : Functor C D) ⦃ cr : ChosenReind Dᴰ ⦄
  where
  private
    module C = Category C
    module CR = ChosenReindNotation Dᴰ
    module R = Fibers (reindexChosenReind Dᴰ F)

  toReindexChosenReind∫ : ∀ {x y} {f g : C [ x , y ]} {a b}
    {fᴰ : CR.Hom[ F ⟪ f ⟫ ][ a , b ]} {gᴰ : CR.Hom[ F ⟪ g ⟫ ][ a , b ]}
    → (_ , fᴰ) ≡ (_ , gᴰ) → fᴰ CR.∫≡ gᴰ
  toReindexChosenReind∫ = cong (λ u → F ⟪ u .fst ⟫ , u .snd)

  reindexFixed-pointⱽChosenReind : ∀ {x} {𝟙ⱽ xⱽ : CR.ob[ F ⟅ x ⟆ ]}
    {fⱽ : CR.Hom[ F ⟪ C.id ⟫ ][ xⱽ , xⱽ ]}
    → fixed-pointⱽ Dᴰ (F ⟅ x ⟆) 𝟙ⱽ (CR.reind⟨ F .F-id ⟩ fⱽ)
    → fixed-pointⱽ (reindexChosenReind Dᴰ F) x 𝟙ⱽ fⱽ
  reindexFixed-pointⱽChosenReind fix .fst = CR.reind⟨ sym (F .F-id) ⟩ (fix .fst)
  reindexFixed-pointⱽChosenReind {fⱽ = fⱽ} fix .snd = CR.rectifyOut
    (toReindexChosenReind∫ (R.reind-filler⁻ _)
    ∙ CR.reind-∫≡ _ _
    ∙ CR.⟨ CR.reind-∫≡ _ _ ⟩⋆⟨ sym (CR.reind-∫≡ _ fⱽ) ⟩
    ∙ sym (CR.F.reind-filler⁻ _)
    ∙ cong (_ ,_) (fix .snd)
    ∙ sym (CR.reind-∫≡ _ _))

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F : Functor C D)
  (L : GuardedLogic D ℓDᴰ ℓDᴰ') ⦃ cr : ChosenReind (GuardedLogic.Cᴰ L) ⦄
  where
  private
    module L = GuardedLogic L
    module CR = ChosenReindNotation L.Cᴰ
    module R = Fibers (reindexChosenReind L.Cᴰ F)

    ▷∫ : ∀ {x y} {a b} → Σ (D [ x , y ]) (λ h → CR.Hom[ h ][ a , b ])
      → Σ (D [ x , y ]) (λ h → CR.Hom[ h ][ L.▷ⱽ .F-obᴰ a , L.▷ⱽ .F-obᴰ b ])
    ▷∫ u = u .fst , L.▷ⱽ .F-homᴰ (u .snd)

  open GuardedLogic
  open NatTransᴰ

  reindexGuardedLogicChosenReind : GuardedLogic C ℓDᴰ ℓDᴰ'
  reindexGuardedLogicChosenReind .Cᴰ = reindexChosenReind L.Cᴰ F
  reindexGuardedLogicChosenReind .▷ⱽ .F-obᴰ = L.▷ⱽ .F-obᴰ
  reindexGuardedLogicChosenReind .▷ⱽ .F-homᴰ = L.▷ⱽ .F-homᴰ
  reindexGuardedLogicChosenReind .▷ⱽ .F-idᴰ = CR.rectifyOut
    (cong ▷∫ (CR.reind-∫≡ _ _) ∙ L.Cᴰ.≡in (L.▷ⱽ .F-idᴰ)
    ∙ sym (CR.reind-∫≡ _ _))
  reindexGuardedLogicChosenReind .▷ⱽ .F-seqᴰ fᴰ gᴰ = CR.rectifyOut
    (cong ▷∫ (CR.reind-∫≡ _ _) ∙ L.Cᴰ.≡in (L.▷ⱽ .F-seqᴰ fᴰ gᴰ)
    ∙ sym (CR.reind-∫≡ _ _))
  reindexGuardedLogicChosenReind .next .N-obᴰ xᴰ =
    CR.reind⟨ sym (F .F-id) ⟩ (L.next .N-obᴰ xᴰ)
  reindexGuardedLogicChosenReind .next .N-homᴰ {f = f} fᴰ =
    CR.rectifyOut {e' = cong (F ⟪_⟫) (idTrans (Id {C = C}) .N-hom f)}
      (CR.reind-∫≡ _ _ ∙ CR.⟨ refl ⟩⋆⟨ CR.reind-∫≡ _ _ ⟩
      ∙ L.Cᴰ.≡in (L.next .N-homᴰ fᴰ)
      ∙ sym (CR.reind-∫≡ _ _ ∙ CR.⟨ CR.reind-∫≡ _ _ ⟩⋆⟨ refl ⟩))
  reindexGuardedLogicChosenReind .isFibCᴰ = isFibrationReindexChosenReind L.Cᴰ F
    L.isFibCᴰ
  reindexGuardedLogicChosenReind .termⱽ = TerminalsⱽReindexChosenReind L.Cᴰ F
    L.termⱽ
  reindexGuardedLogicChosenReind .gfpⱽ {A} {Aᴰ} f =
    reindexFixed-pointⱽChosenReind L.Cᴰ F
    ( fp .fst
    , cong (fp .fst L.Cᴰ.⋆ⱽ_)
        (CR.rectifyOut
          (CR.reind-∫≡ _ _
          ∙ toReindexChosenReind∫ L.Cᴰ F (R.reind-filler⁻ _)
          ∙ CR.reind-∫≡ _ _
          ∙ CR.⟨ CR.reind-∫≡ _ _ ⟩⋆⟨ sym (CR.reind-∫≡ _ f) ⟩
          ∙ sym (CR.F.reind-filler⁻ _)))
      ∙ fp .snd)
    where
    fp = L.gfpⱽ (CR.reind⟨ F .F-id ⟩ f)
