{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Fibration where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Presheaf
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Limits.Terminal

open import Cubical.Tactics.CategorySolver.Reflection

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    C/Cᴰ = (C /C Cᴰ)
    module C/Cᴰ = Categoryᴰ C/Cᴰ
    Δ = Δ/C C Cᴰ
  -- The "high tech" formulation
  CartesianLift : ∀ {c : C .ob} → C/Cᴰ.ob[ c ] → Type _
  CartesianLift = LocalRightAdjointAtᴰ Δ

  isFibration : Type _
  isFibration = LocalRightAdjointᴰ Δ

  private
    module R = HomᴰReasoning Cᴰ
    module Cᴰ = Categoryᴰ Cᴰ
  -- The "explicit" formulation
  -- TODO: better names
  record CartesianOver {c : C .ob}{c' : C .ob}
                       (cᴰ' : Cᴰ.ob[ c' ])(f : C [ c , c' ])
         : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ')) where
    field
      f*cᴰ' : Cᴰ.ob[ c ]
      π     : Cᴰ.Hom[ f ][ f*cᴰ' , cᴰ' ]
      isCartesian : ∀ {c'' : C .ob}(cᴰ'' : Cᴰ.ob[ c'' ])(g : C [ c'' , c ])
                    (gfᴰ : Cᴰ.Hom[ g ⋆⟨ C ⟩ f ][ cᴰ'' , cᴰ' ])
                  → ∃![ gᴰ ∈ Cᴰ.Hom[ g ][ cᴰ'' , f*cᴰ' ] ] (gᴰ Cᴰ.⋆ᴰ π ≡ gfᴰ)

  module _ {c c' : C .ob}(c'ᴰ : Cᴰ.ob[ c' ])(f : C [ c , c' ]) where
    -- type of witnesses that fᴰ : Cᴰ.Hom[ f ][ f*c'ᴰ , c'ᴰ ] is cartesian, for convenience
    isCartesianOver : ∀{f*c'ᴰ : Cᴰ.ob[ c ]} → (fᴰ : Cᴰ.Hom[ f ][ f*c'ᴰ , c'ᴰ ]) → Type _
    isCartesianOver {f*c'ᴰ = f*c'ᴰ} fᴰ =
      ∀ {c'' : C .ob}(c''ᴰ : Cᴰ.ob[ c'' ])(g : C [ c'' , c ])
      (gfᴰ : Cᴰ.Hom[ g ⋆⟨ C ⟩ f ][ c''ᴰ , c'ᴰ ]) →
      ∃![ gᴰ ∈ Cᴰ.Hom[ g ][ c''ᴰ , f*c'ᴰ ] ] (gᴰ Cᴰ.⋆ᴰ fᴰ ≡ gfᴰ)

    open CartesianOver

    isCartesianOver→CartesianOver : {f*c'ᴰ : Cᴰ.ob[ c ]}{fᴰ : Cᴰ.Hom[ f ][ f*c'ᴰ , c'ᴰ ]} →
      isCartesianOver fᴰ → CartesianOver c'ᴰ f
    isCartesianOver→CartesianOver {f*c'ᴰ = f*c'ᴰ} _ .f*cᴰ' = f*c'ᴰ
    isCartesianOver→CartesianOver {fᴰ = fᴰ} _ .π = fᴰ
    isCartesianOver→CartesianOver !gᴰ .isCartesian = !gᴰ

  AllCartesianOvers : Type _
  AllCartesianOvers =
    ∀ {c : C .ob}{c' : C .ob}
    (cᴰ' : Cᴰ.ob[ c' ])(f : C [ c , c' ])
    → CartesianOver cᴰ' f

  open UniversalElementᴰ
  open isEquiv
  module _ {c : C .ob} {c' : C .ob}
           {f : C [ c , c' ]}{cᴰ' : Cᴰ.ob[ c' ]}
           (cartOver : CartesianOver cᴰ' f)
           where
    open CartesianOver cartOver
    -- | ALERT: this definition does have to introduce a reind, may
    -- | likely complicate goals
    CartesianOver→CartesianLift : CartesianLift (c' , (cᴰ' , f))
    CartesianOver→CartesianLift .vertexᴰ = f*cᴰ'
    CartesianOver→CartesianLift .elementᴰ = f , (π , refl)
    CartesianOver→CartesianLift .universalᴰ {c''} {cᴰ''} {g}
      .equiv-proof (gf , gfᴰ , gf≡g⋆f') =
      uniqueExists
        ⟨gfᴰ⟩
        (ΣPathP ((sym gf≡g⋆f) , (ΣPathPProp (λ _ → C .isSetHom _ _)
          (symP (R.≡→≡[] (sym β))))))
        (λ _ → C/Cᴰ.isSetHomᴰ _ _)
        λ gᴰ gᴰ-lifts →
        cong fst (isCL .snd (gᴰ
                   , sym (fromPathP (symP (cong (λ p → p .snd .fst) gᴰ-lifts)))
          ∙ R.reind-rectify))
      where
        gf≡g⋆f = sym (C .⋆IdL gf) ∙ sym gf≡g⋆f' ∙ cong (comp' C f) (C .⋆IdR g)
        isCL = isCartesian cᴰ'' g (R.reind gf≡g⋆f gfᴰ)
        ⟨gfᴰ⟩ : Cᴰ.Hom[ g ][ cᴰ'' , f*cᴰ' ]
        ⟨gfᴰ⟩ = isCL .fst .fst
        β : ⟨gfᴰ⟩ Cᴰ.⋆ᴰ π ≡ R.reind gf≡g⋆f gfᴰ
        β = isCL .fst .snd

  module _ {c : C .ob} {c' : C .ob}
           {cᴰ' : Cᴰ.ob[ c' ]}{f : C [ c , c' ]}
           (cartLift : CartesianLift (c' , (cᴰ' , f)))
           where
    open CartesianOver
    module cL = UniversalElementᴰ cartLift
    private
      f' : C [ c , c' ]
      f' = cL.elementᴰ .fst

      f'≡f : f' ≡ f
      f'≡f = sym (C .⋆IdL _) ∙ sym (cL.elementᴰ .snd .snd) ∙ C .⋆IdL _

      f'*cᴰ' : Cᴰ.ob[ c ]
      f'*cᴰ' = cL.vertexᴰ

      π' : Cᴰ.Hom[ f' ][ f'*cᴰ' , cᴰ' ]
      π' = cL.elementᴰ .snd .fst

      the-π : Cᴰ.Hom[ f ][ f'*cᴰ' , cᴰ' ]
      the-π = R.reind f'≡f π'

    CartesianLift→CartesianOver : CartesianOver cᴰ' f
    CartesianLift→CartesianOver .f*cᴰ' = cL.vertexᴰ
    CartesianLift→CartesianOver .π     = the-π
    CartesianLift→CartesianOver .isCartesian {c''} cᴰ'' g gfᴰ =
      uniqueExists
        ⟨gfᴰ⟩
        (R.≡[]-rectify (R.≡[]∙ _ _
          (R.≡[]⋆ refl (sym f'≡f) refl (symP (R.reind-filler f'≡f π')))
          (λ i → the-CL .fst .snd i .snd .fst)))
        (λ _ → Cᴰ.isSetHomᴰ _ _)
        λ gᴰ gᴰ⋆π≡gfᴰ → cong fst (the-CL .snd (gᴰ ,
          ΣPathP (g⋆f'≡g⋆f , (ΣPathPProp (λ _ → C .isSetHom _ _)
          (R.≡[]-rectify (R.≡[]⋆ refl f'≡f refl (R.reind-filler f'≡f π'))
          ▷ gᴰ⋆π≡gfᴰ)))))
      where
        the-CL = cL.universalᴰ .equiv-proof (g ⋆⟨ C ⟩ f , gfᴰ , solveCat! C)
        ⟨gfᴰ⟩ : Cᴰ.Hom[ g ][ cᴰ'' , cL.vertexᴰ ]
        ⟨gfᴰ⟩ = the-CL .fst .fst

        g⋆f'≡g⋆f : g ⋆⟨ C ⟩ f' ≡ g ⋆⟨ C ⟩ f
        g⋆f'≡g⋆f = cong fst (the-CL .fst .snd)

        gᴰ⋆π'≡gᴰ⋆π : ∀ (gᴰ : Cᴰ.Hom[ g ][ cᴰ'' , f'*cᴰ' ])
                   → gᴰ Cᴰ.⋆ᴰ π' Cᴰ.≡[ cong (seq' C g) f'≡f ] (gᴰ Cᴰ.⋆ᴰ the-π)
        gᴰ⋆π'≡gᴰ⋆π gᴰ =
          R.≡[]-rectify (R.≡[]⋆ refl f'≡f refl (R.reind-filler f'≡f π'))

-- package together a fibration and its cleavage
ClovenFibration : (C : Category ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level) → Type _
ClovenFibration C ℓCᴰ ℓCᴰ' = Σ[ Cᴰ ∈ Categoryᴰ C ℓCᴰ ℓCᴰ' ] isFibration Cᴰ

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  (p : ClovenFibration C ℓCᴰ ℓCᴰ')(q : ClovenFibration D ℓDᴰ ℓDᴰ') where
  module _ {F : Functor C D} (Fᴰ : Functorᴰ F (p .fst) (q .fst)) where
    open Category
    open Functorᴰ
    private
      module Cᴰ = Categoryᴰ (p .fst)

    -- whether a 1-cell preserves cartesian morphisms
    isFibered : Type _
    isFibered =
      ∀ {c c' : C .ob} (c'ᴰ : Cᴰ.ob[ c' ]) (f : C [ c , c' ]) →
      (f*c'ᴰ : Cᴰ.ob[ c ])(fᴰ : Cᴰ.Hom[ f ][ f*c'ᴰ , c'ᴰ ]) →
        isCartesianOver (p .fst) c'ᴰ f fᴰ →
        isCartesianOver (q .fst) (Fᴰ .F-obᴰ c'ᴰ) (F ⟪ f ⟫) (Fᴰ .F-homᴰ fᴰ)

  record FiberedFunctor
      : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
      (ℓ-max (ℓ-max ℓCᴰ ℓCᴰ') (ℓ-max ℓDᴰ ℓDᴰ'))) where
    field
      base : Functor C D
      over : Functorᴰ base (p .fst) (q .fst)
      preserves-cartesian : isFibered over

--module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
--  isFibration→AllCartesianOvers : isFibration Cᴰ → AllCartesianOvers Cᴰ
--  isFibration→AllCartesianOvers isfib cᴰ' f =
--    CartesianLift→CartesianOver Cᴰ (isfib (_ , cᴰ' , f))

module _ {C : Category ℓC ℓC'} where
  open CartesianOver
  open FiberedFunctor

  isFibC/C : isFibration (Unitᴰ C)
  isFibC/C _ = CartesianOver→CartesianLift (Unitᴰ C) ue
    where
    ue : CartesianOver (Unitᴰ C) _ _
    ue .f*cᴰ' = tt
    ue .π = tt
    ue .isCartesian _ _ _ =
      uniqueExists _ (isPropUnit _ _) (λ _ → isSetUnit _ _)
      λ _ _ → isPropUnit _ _

  -- terminal fibration over C, ie the identity fibration
  TerminalFib : ClovenFibration C _ _
  TerminalFib = (Unitᴰ C , isFibC/C)

  module _ (p : ClovenFibration C ℓCᴰ ℓCᴰ') where
    open Functorᴰ

    !ₚ : FiberedFunctor p TerminalFib
    !ₚ .base = Id
    !ₚ .over .F-obᴰ _ = tt
    !ₚ .over .F-homᴰ _ = tt
    !ₚ .over .F-idᴰ = refl
    !ₚ .over .F-seqᴰ _ _ = refl
    !ₚ .preserves-cartesian _ _ _ _ _ _ _ _ =
        uniqueExists _ (isPropUnit _ _)
        (λ _ → isSetUnit _ _) λ _ _ → isPropUnit _ _

-- This makes sense for any displayed category, but is traditionally used for fibrations
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where

  AllVerticalTerminals : Type _
  AllVerticalTerminals = (c : C .ob) → VerticalTerminal Cᴰ c

  module _ (term : Terminal' C) where

    open VerticalTerminalNotation Cᴰ
    open UniversalElementᴰ
    open UniversalElement
    module Cᴰ = Categoryᴰ Cᴰ

    -- if the base has [structure], and Cᴰ has fibered [structure], then Cᴰ has displayed [structure]
    Vertical→LiftedTerm : VerticalTerminal Cᴰ (term .vertex) → LiftedTerminal Cᴰ term
    Vertical→LiftedTerm a1ᴰ .vertexᴰ = a1ᴰ .vertexᴰ
    Vertical→LiftedTerm a1ᴰ .elementᴰ = tt
    Vertical→LiftedTerm a1ᴰ .universalᴰ  {xᴰ = xᴰ} {f = f} .equiv-proof _ =
      uniqueExists (!tᴰ (term .vertex) a1ᴰ f xᴰ) refl
      (λ _ p q →
        LiftedTerminalSpec Cᴰ .Functorᴰ.F-obᴰ xᴰ
        (TerminalPresheaf {C = C} .Functor.F-hom f (term .element)) .snd tt tt p q)
        λ fᴰ' _ → {!!} --!tᴰ-unique (term .vertex) 𝟙ᴰ f xᴰ .snd fᴰ'

--module _ {B : Category ℓB ℓB'}{C : Category ℓC ℓC'}
--  (F : Functor B C)
--  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
--  (fibterm : hasFibTerminal' Cᴰ) where
--  open import Cubical.Categories.Displayed.Properties
--  open UniversalElementᴰ
--  fib-stable-under-reind : hasFibTerminal' (reindex Cᴰ F)
--  -- TODO: why do I have to eta expand this?
--  fib-stable-under-reind b .vertexᴰ = fibterm (F ⟅ b ⟆) .vertexᴰ
--  fib-stable-under-reind b .elementᴰ = fibterm (F ⟅ b ⟆) .elementᴰ
--  fib-stable-under-reind b .universalᴰ = fibterm (F ⟅ b ⟆) .universalᴰ
--
--  module _ (term' : Terminal' B) where
--    baz : Terminalᴰ (reindex Cᴰ F) term'
--    baz = FibTerm→Termᴰ (reindex Cᴰ F) term' fib-stable-under-reind
--module _ {C : Category ℓC ℓC'} where
--  open CartesianOver
--
--  1/C = Unitᴰ C
--
--  isFib1/C : isFibration 1/C
--  isFib1/C _ = CartesianOver→CartesianLift 1/C ue
--    where
--    ue : CartesianOver 1/C tt _
--    ue .f*cᴰ' = tt
--    ue .π = tt
--    ue .isCartesian _ _ _ =
--      uniqueExists _ (isPropUnit _ _) (λ _ _ _ → isSetUnit _ _ _ _)
--      λ _ _ → isPropUnit _ _
--
--  -- terminal fibration over C, ie the identity fibration
--  TerminalFib : Fibration C _ _
--  TerminalFib = (1/C , isFib1/C)
--
--  module _ (p : Fibration C ℓCᴰ ℓCᴰ') where
--    open Functorᴰ
--
--    !/C : FiberedFunctor p TerminalFib
--    !/C .base = Id
--    !/C .over .F-obᴰ _ = tt
--    !/C .over .F-homᴰ _ = tt
--    !/C .over .F-idᴰ = refl
--    !/C .over .F-seqᴰ _ _ = refl
--    !/C .preserves-cartesian _ _ _ _ _ _ _ _ =
--        uniqueExists tt (isPropUnit tt tt)
--        (λ _ p q → isSetUnit tt tt p q) λ _ _ → isPropUnit tt tt
--
---- This makes sense for any displayed category, but is traditionally used for fibrations
--module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
--
--  -- fibered terminal objects, in terms of UniversalElementᴰ
--  hasFibTerminal' : Type _
--  hasFibTerminal' = (c : C .ob) → FibTerminalᴰ Cᴰ c
--
--  module _ (term : Terminal' C) where
--
--    open FibTerminalᴰNotation Cᴰ
--    open UniversalElementᴰ
--    open UniversalElement
--    module Cᴰ = Categoryᴰ Cᴰ
--
--    -- if the base has [structure], and Cᴰ has fibered [structure], then Cᴰ has displayed [structure]
--    FibTerm→Termᴰ : hasFibTerminal' → Terminalᴰ Cᴰ term
--    FibTerm→Termᴰ fibterm .vertexᴰ = 1ᴰ (term .vertex) (fibterm (term .vertex))
--    FibTerm→Termᴰ fibterm .elementᴰ = tt
--    FibTerm→Termᴰ fibterm .universalᴰ  {xᴰ = xᴰ} {f = f} .equiv-proof _ =
--      uniqueExists (!tᴰ (term .vertex) 𝟙ᴰ f xᴰ) refl
--      (λ _ p q →
--        TerminalᴰSpec Cᴰ .Functorᴰ.F-obᴰ xᴰ
--        (TerminalPresheaf {C = C} .Functor.F-hom f (term .element)) .snd tt tt p q)
--        λ fᴰ' _ → {!!} --!tᴰ-unique (term .vertex) 𝟙ᴰ f xᴰ .snd fᴰ'
--      where
--      𝟙ᴰ : FibTerminalᴰ Cᴰ (term .vertex)
--      𝟙ᴰ = (fibterm (term .vertex))
--
--module _ {B : Category ℓB ℓB'}{C : Category ℓC ℓC'}
--  (F : Functor B C)
--  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
--  (fibterm : hasFibTerminal' Cᴰ) where
--  open import Cubical.Categories.Displayed.Properties
--  open UniversalElementᴰ
--  fib-stable-under-reind : hasFibTerminal' (reindex Cᴰ F)
--  -- TODO: why do I have to eta expand this?
--  fib-stable-under-reind b .vertexᴰ = fibterm (F ⟅ b ⟆) .vertexᴰ
--  fib-stable-under-reind b .elementᴰ = fibterm (F ⟅ b ⟆) .elementᴰ
--  fib-stable-under-reind b .universalᴰ = fibterm (F ⟅ b ⟆) .universalᴰ
--
--  module _ (term' : Terminal' B) where
--    baz : Terminalᴰ (reindex Cᴰ F) term'
--    baz = FibTerm→Termᴰ (reindex Cᴰ F) term' fib-stable-under-reind
