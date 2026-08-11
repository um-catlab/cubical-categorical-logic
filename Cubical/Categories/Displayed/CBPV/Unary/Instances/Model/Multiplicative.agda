{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.Model.Multiplicative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.More
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Bool
import Cubical.Data.Equality as Eq

open import Cubical.Algebra.Theory.Base
  hiding (ℓ; ℓᴰ; ℓᴰᴰ; ℓ'; ℓᴰ'; ℓᴰᴰ'; ℓ''; ℓᴰ''; ℓO; ℓA; ℓE)

open import Cubical.Categories.Category
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.TotalCategory hiding (elim)
open import Cubical.Categories.Instances.WalkingArrow
  renaming (l to 𝒱; r to 𝒞)
import Cubical.Categories.Instances.WalkingArrow as WA
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Algebra.Model
open import Cubical.Categories.Displayed.Instances.Algebra.DisplayedModel
open import Cubical.Categories.Displayed.Instances.Opposite
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base as EqPsh
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Model.Base

private
  variable
    ℓX ℓO ℓA ℓE ℓEA : Level

module _ (T : Theory ℓO ℓA ℓE ℓEA) where
  open Theory T

  private
    L = ModelLevel T
    C = ModelCBPV T .fst
    Cᴰ = ModelCBPVᴰ T

    MODELOb→Model : Category.ob (MODEL T L) → Model L
    MODELOb→Model B .fst = ⟨ B .fst ⟩ , B .snd .fst
    MODELOb→Model B .snd .fst = B .snd .snd
    MODELOb→Model B .snd .snd = B .fst .snd

    MODELᴰOb→Modelᴰ : ∀ {B : Category.ob (MODEL T L)}
      → Categoryᴰ.ob[_] (MODELᴰ T L L) B
      → Modelᴰ (MODELOb→Model B) L
    MODELᴰOb→Modelᴰ Bᴰ .fst .fst b = ⟨ Bᴰ .fst b ⟩
    MODELᴰOb→Modelᴰ Bᴰ .fst .snd = Bᴰ .snd .fst
    MODELᴰOb→Modelᴰ Bᴰ .snd .fst = Bᴰ .snd .snd
    MODELᴰOb→Modelᴰ Bᴰ .snd .snd b = Bᴰ .fst b .snd

    CBPVIdR : EqPsh.EqIdR (∫C C)
    CBPVIdR {x = 𝒱 , A} {y = 𝒱 , B} f = Eq.refl
    CBPVIdR {x = 𝒱 , A} {y = 𝒞 , B} f =
      Eq.pathToEq (Category.⋆IdR (∫C C) f)
    CBPVIdR {x = 𝒞 , A} {y = 𝒱 , B} ()
    CBPVIdR {x = 𝒞 , A} {y = 𝒞 , B} f = Eq.refl

    CBPVAssoc : EqPsh.ReprEqAssoc (∫C C)
    CBPVAssoc (𝒱 , A)
      {c = 𝒱 , W} {c' = 𝒱 , X} {c'' = 𝒱 , Y}
      _ _ _ _ Eq.refl = Eq.refl
    CBPVAssoc (𝒞 , B)
      {c = 𝒱 , W} {c' = 𝒱 , X} {c'' = 𝒱 , Y}
      _ _ _ _ Eq.refl = Eq.refl
    CBPVAssoc x f g p f⋆g e = Eq.pathToEq
      (sym (D.⋆Assoc f g p) ∙ cong (λ fg → fg D.⋆ p) (Eq.eqToPath e))
      where module D = Category (∫C C)

  FreeMODELη : (Free : LeftAdjoint (MODELForget T)) (A : hSet L)
    → ∫C (C ^opᴰ)
        [ (WA.r , Free A .UniversalElement.vertex) , (WA.l , A) ]
  FreeMODELη Free A = _ , Free A .UniversalElement.element

  -- A chosen free-model adjunction together with the displayed universal
  -- property of its unit.  The vertex of the lift is the chosen free
  -- displayed model; no particular syntax for either free object is exposed.
  FreeMODELConstruction : Type _
  FreeMODELConstruction =
    Σ[ Free ∈ LeftAdjoint (MODELForget T) ]
      ((A : hSet L) (Aᴰ : ⟨ A ⟩ → hSet L) →
        CartesianLift ((ModelCBPVᴰWithFree T Free) ^opᴰᴰ)
          (FreeMODELη Free A) Aᴰ)

  -- A possibly lower-universe presentation of a free model.  This separate
  -- formulation lets canonicity return native carriers such as the usual
  -- state, writer, or reader representation rather than a lifted generator.
  FreeMODELPresentation : Type ℓX → Type _
  FreeMODELPresentation X =
    Σ[ FreeX ∈ Category.ob (MODEL T L) ]
    Σ[ ηX ∈ (X → ⟨ FreeX .fst ⟩) ]
      ((B : Category.ob (MODEL T L)) →
        isEquiv (λ (ϕ : MODEL T L [ FreeX , B ]) →
          ϕ .fst ∘ ηX))

  FreeMODELPresentationFromAdjunction :
    (Free : LeftAdjoint (MODELForget T)) (X : hSet L)
    → FreeMODELPresentation ⟨ X ⟩
  FreeMODELPresentationFromAdjunction Free X .fst =
    Free X .UniversalElement.vertex
  FreeMODELPresentationFromAdjunction Free X .snd .fst =
    Free X .UniversalElement.element
  FreeMODELPresentationFromAdjunction Free X .snd .snd =
    Free X .UniversalElement.universal

  BoolFreeMODELConstruction : Type _
  BoolFreeMODELConstruction = FreeMODELPresentation Bool

  ModelCBPV-Uⱽ : hasUⱽ Cᴰ
  ModelCBPV-Uⱽ {A = A} {B = B} f Bᴰ =
    EqCartesianLift→CartesianLift CBPVAssoc Cᴰ Bᴰ (𝒱 , A) (_ , f)
      (EqPsh.UEⱽ→Reprⱽ _ CBPVIdR ue)
    where
    ue : EqPsh.CartesianLiftUE Cᴰ CBPVAssoc CBPVIdR (_ , f) Bᴰ
    ue .EqPsh.UEⱽ.v x = Bᴰ .fst (f x)
    ue .EqPsh.UEⱽ.e _ xᴰ = xᴰ
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , Z) , Zᴰ , g) .fst h = h
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , Z) , Zᴰ , ()) .fst
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , Z) , Zᴰ , g) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , Z) , Zᴰ , ()) .snd .fst
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , Z) , Zᴰ , g) .snd .snd _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , Z) , Zᴰ , ()) .snd .snd

  private
    FreeMODELᴰ : (A : hSet L) (Aᴰ : ⟨ A ⟩ → hSet L)
      → Categoryᴰ.ob[_] (MODELᴰ T L L) (FreeMODEL T A)
    FreeMODELᴰ A Aᴰ .fst t =
      |FreeModelᴰ| ⟨ A ⟩ (λ x → ⟨ Aᴰ x ⟩) t ,
      isSetFreeModelᴰ ⟨ A ⟩ (λ x → ⟨ Aᴰ x ⟩) t
    FreeMODELᴰ A Aᴰ .snd .fst =
      FreeModelᴰ ⟨ A ⟩ (λ x → ⟨ Aᴰ x ⟩) .fst .snd
    FreeMODELᴰ A Aᴰ .snd .snd =
      FreeModelᴰ ⟨ A ⟩ (λ x → ⟨ Aᴰ x ⟩) .snd .fst

    η-base : (A : hSet L) → (∫C C) [ (𝒱 , A) , (𝒞 , FreeMODEL T A) ]
    η-base A = _ , var

    η-lift : (A : hSet L) (Aᴰ : ⟨ A ⟩ → hSet L)
      → CartesianLift (Cᴰ ^opᴰᴰ) (η-base A) Aᴰ
    η-lift A Aᴰ = UniversalElementⱽ'.REPRⱽ ue
      where
      module Cᴰᶠ = Fibers (Cᴰ ^opᴰᴰ)
      module Dᴰ = Fibers (MODELᴰ T L L)

      ue : UniversalElementⱽ' (Cᴰ ^opᴰᴰ)
        (𝒞 , FreeMODEL T A)
        (CartesianLiftPshSpec
          ((∫C (C ^opᴰ)) [-, (𝒱 , A) ])
          (Cᴰ ^opᴰᴰ)
          ((Cᴰ ^opᴰᴰ) [-][-, Aᴰ ])
          (η-base A))
      ue .UniversalElementⱽ'.vertexⱽ = FreeMODELᴰ A Aᴰ
      ue .UniversalElementⱽ'.elementⱽ x xᴰ = |FreeModelᴰ|.var xᴰ
      ue .UniversalElementⱽ'.universalⱽ
        ((𝒱 , Z) , Zᴰ , ()) .fst
      ue .UniversalElementⱽ'.universalⱽ
        ((𝒞 , Z) , Zᴰ , ϕ) .fst ıᴰ =
          recFMᴰ ⟨ A ⟩ (λ x → ⟨ Aᴰ x ⟩) (ϕ .snd)
            (MODELᴰOb→Modelᴰ Zᴰ) ıᴰ
      ue .UniversalElementⱽ'.universalⱽ
        ((𝒱 , Z) , Zᴰ , ()) .snd .fst
      ue .UniversalElementⱽ'.universalⱽ
        ((𝒞 , Z) , Zᴰ , ϕ) .snd .fst ıᴰ =
          Cᴰᶠ.rectifyOut {e' = refl} $
            Cᴰᶠ.reind-filler⁻ _
            ∙ Cᴰᶠ.≡in {pth = refl} (funExt λ x → funExt λ xᴰ →
              hSetReasoning.rectifyOut (Z .fst)
                (λ z → ⟨ Zᴰ .fst z ⟩) refl)
      ue .UniversalElementⱽ'.universalⱽ
        ((𝒱 , Z) , Zᴰ , ()) .snd .snd
      ue .UniversalElementⱽ'.universalⱽ
        ((𝒞 , Z) , Zᴰ , ϕ) .snd .snd ϕᴰ =
          cong (ue .UniversalElementⱽ'.universalⱽ
            ((𝒞 , Z) , Zᴰ , ϕ) .fst)
            (Cᴰᶠ.rectifyOut {e' = refl} (Cᴰᶠ.reind-filler⁻ _))
          ∙ (Dᴰ.rectify $ Dᴰ.≡out $
              Dᴰ.≡in {pth = refl}
                (MODELᴰHomo≡ T _ _
                  (sym (recFMᴰ-η ⟨ A ⟩ (λ x → ⟨ Aᴰ x ⟩)
                    (ϕ .snd) (MODELᴰOb→Modelᴰ Zᴰ)
                    (_ , ϕᴰ .snd)))))

    module _ {B B' : Category.ob (MODEL T L)}
      (ϕ : Homo (MODELOb→Model B .fst) (MODELOb→Model B' .fst))
      (Bᴰ : Categoryᴰ.ob[_] (MODELᴰ T L L) B) where

      private
        BModelᴰ = MODELᴰOb→Modelᴰ Bᴰ

      PushAlgebraᴰ : Algebraᴰ (MODELOb→Model B' .fst) L
      PushAlgebraᴰ .fst b' =
        Σ[ b ∈ ⟨ B .fst ⟩ ] (ϕ .fst b ≡ b') × ⟨ Bᴰ .fst b ⟩
      PushAlgebraᴰ .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
        B .snd .fst op (λ v → γᴰ v .fst) ,
        (sym (ϕ .snd op (λ v → γᴰ v .fst) _ refl)
          ∙ cong (B' .snd .fst op) (funExt λ v → γᴰ v .snd .fst)
          ∙ op∘γ≡op⟨γ⟩) ,
        Bᴰ .snd .fst op (λ v → γᴰ v .fst)
          (λ v → γᴰ v .snd .snd) _ refl

      private
        PushTotal : Algebra L
        PushTotal = ∫Algebra PushAlgebraᴰ

        SourceTotal : Model L
        SourceTotal = ∫Model BModelᴰ

        forgetPush : PushTotal .fst → SourceTotal .fst .fst
        forgetPush z = z .snd .fst , z .snd .snd .snd

        forgetPushHomo : Homo PushTotal (SourceTotal .fst)
        forgetPushHomo .fst = forgetPush
        forgetPushHomo .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ i .fst =
          op∘γ≡op⟨γ⟩ i .snd .fst
        forgetPushHomo .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ i .snd =
          op∘γ≡op⟨γ⟩ i .snd .snd .snd

        sourceEquation : ∀ e
          (ρ : EqArity e → ⟨ B' .fst ⟩)
          (ρᴰ : (v : EqArity e) → PushAlgebraᴰ .fst (ρ v))
          → Path (SourceTotal .fst .fst)
              ( forgetPush
                ( interp (MODELOb→Model B' .fst) ρ (lhs e)
                , interpᴰ PushAlgebraᴰ ρ ρᴰ (lhs e)))
              ( forgetPush
                ( interp (MODELOb→Model B' .fst) ρ (rhs e)
                , interpᴰ PushAlgebraᴰ ρ ρᴰ (rhs e)))
        sourceEquation e ρ ρᴰ =
          cong forgetPush
            (sym (interp∫ {Aᴰ = PushAlgebraᴰ}
              (λ v → ρ v , ρᴰ v) (lhs e)))
          ∙ sym (interpHomo forgetPushHomo
              (λ v → ρ v , ρᴰ v) (lhs e))
          ∙ SourceTotal .snd .fst e
              (λ v → ρᴰ v .fst , ρᴰ v .snd .snd)
          ∙ interpHomo forgetPushHomo
              (λ v → ρ v , ρᴰ v) (rhs e)
          ∙ cong forgetPush
            (interp∫ {Aᴰ = PushAlgebraᴰ}
              (λ v → ρ v , ρᴰ v) (rhs e))

      PushMODELInternalᴰ : Categoryᴰ.ob[_] (MODELᴰ T L L) B'
      PushMODELInternalᴰ .fst b' .fst = PushAlgebraᴰ .fst b'
      PushMODELInternalᴰ .fst b' .snd =
        isSetΣ (B .fst .snd) λ b →
          isSet× (isProp→isSet (B' .fst .snd _ _)) (Bᴰ .fst b .snd)
      PushMODELInternalᴰ .snd .fst = PushAlgebraᴰ .snd
      PushMODELInternalᴰ .snd .snd e ρ ρᴰ i .fst =
        sourceEquation e ρ ρᴰ i .fst
      PushMODELInternalᴰ .snd .snd e ρ ρᴰ i .snd .fst =
        isProp→PathP
          (λ j → B' .fst .snd
            (ϕ .fst (sourceEquation e ρ ρᴰ j .fst))
            (B' .snd .snd e ρ j))
          (interpᴰ PushAlgebraᴰ ρ ρᴰ (lhs e) .snd .fst)
          (interpᴰ PushAlgebraᴰ ρ ρᴰ (rhs e) .snd .fst) i
      PushMODELInternalᴰ .snd .snd e ρ ρᴰ i .snd .snd =
        sourceEquation e ρ ρᴰ i .snd

      push-inᴰ : Categoryᴰ.Hom[_][_,_] (MODELᴰ T L L) ϕ Bᴰ PushMODELInternalᴰ
      push-inᴰ .fst b bᴰ = b , refl , bᴰ
      push-inᴰ .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩
        op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ =
          ΣPathP
            ( op∘γ≡op⟨γ⟩
            , ΣPathP
                ( isProp→PathP
                    (λ i → B' .fst .snd
                      (ϕ .fst (op∘γ≡op⟨γ⟩ i))
                      (ϕ .fst op⟨γ⟩)) _ _
                , hSetReasoning.rectifyOut (B .fst)
                    (λ b → ⟨ Bᴰ .fst b ⟩)
                    {e' = op∘γ≡op⟨γ⟩}
                    (hSetReasoning.≡in (B .fst)
                      (λ b → ⟨ Bᴰ .fst b ⟩)
                      (λ i → Bᴰ .snd .fst op γ γᴰ
                        (op∘γ≡op⟨γ⟩ i)
                        (λ j → op∘γ≡op⟨γ⟩ (i ∧ j)))
                    ∙ hSetReasoning.≡in (B .fst)
                        (λ b → ⟨ Bᴰ .fst b ⟩)
                        op∘γᴰ≡op⟨γᴰ⟩)))

      module _ {Z : Category.ob (MODEL T L)}
        (ψ : Homo (MODELOb→Model B' .fst) (MODELOb→Model Z .fst))
        (Zᴰ : Categoryᴰ.ob[_] (MODELᴰ T L L) Z)
        (γᴰ : Categoryᴰ.Hom[_][_,_] (MODELᴰ T L L)
          (ϕ ⋆H ψ) Bᴰ Zᴰ) where

        private
          module ZᴰR = hSetReasoning (Z .fst) (λ z → ⟨ Zᴰ .fst z ⟩)

        recPush-fᴰ : ∀ b' → ⟨ PushMODELInternalᴰ .fst b' ⟩
          → ⟨ Zᴰ .fst (ψ .fst b') ⟩
        recPush-fᴰ b' (b , p , bᴰ) =
          ZᴰR.reind (cong (ψ .fst) p) (γᴰ .fst b bᴰ)

        private
          op-filler : ∀ op δ δᴰ z (p : Z .snd .fst op δ ≡ z)
            → (Z .snd .fst op δ , Zᴰ .snd .fst op δ δᴰ _ refl)
              ≡ (z , Zᴰ .snd .fst op δ δᴰ z p)
          op-filler op δ δᴰ z p i .fst = p i
          op-filler op δ δᴰ z p i .snd =
            Zᴰ .snd .fst op δ δᴰ (p i) (λ j → p (i ∧ j))

          child-path : ∀ {b'} (x : ⟨ PushMODELInternalᴰ .fst b' ⟩) →
            Path (Σ ⟨ Z .fst ⟩ (λ z → ⟨ Zᴰ .fst z ⟩))
              (ψ .fst (ϕ .fst (x .fst)) ,
                γᴰ .fst (x .fst) (x .snd .snd))
              (ψ .fst b' , recPush-fᴰ b' x)
          child-path (b , p , bᴰ) = ΣPathP
            ( cong (ψ .fst) p
            , ZᴰR.rectifyOut (ZᴰR.reind-filler (cong (ψ .fst) p)))

        recPushᴰ : Categoryᴰ.Hom[_][_,_] (MODELᴰ T L L)
          ψ PushMODELInternalᴰ Zᴰ
        recPushᴰ .fst = recPush-fᴰ
        recPushᴰ .snd op δ δᴰ op⟨δ⟩ op∘δ≡op⟨δ⟩
          op⟨δᴰ⟩ op∘δᴰ≡op⟨δᴰ⟩ =
            ZᴰR.rectifyOut $
              sym (op-filler op (ψ .fst ∘ δ)
                (λ v → recPush-fᴰ (δ v) (δᴰ v)) _
                (ψ .snd op δ op⟨δ⟩ op∘δ≡op⟨δ⟩))
              ∙ sym (cong (∫Algebra (_ , Zᴰ .snd .fst) .snd op)
                  (funExt (λ v → child-path (δᴰ v))))
              ∙ op-filler op
                  (ψ .fst ∘ ϕ .fst ∘ (λ v → δᴰ v .fst))
                  (λ v → γᴰ .fst (δᴰ v .fst) (δᴰ v .snd .snd))
                  _ ((ϕ ⋆H ψ) .snd op
                    (λ v → δᴰ v .fst) _ refl)
              ∙ ZᴰR.≡in
                  (γᴰ .snd op
                    (λ v → δᴰ v .fst)
                    (λ v → δᴰ v .snd .snd) _ refl _ refl)
              ∙ ZᴰR.reind-filler
                  (cong (ψ .fst)
                    (PushMODELInternalᴰ .snd .fst op δ δᴰ op⟨δ⟩
                      op∘δ≡op⟨δ⟩ .snd .fst))
              ∙ ZᴰR.≡in
                  (cong (recPush-fᴰ op⟨δ⟩)
                    op∘δᴰ≡op⟨δᴰ⟩)

      push-path : ∀ b bᴰ {b'} (p : ϕ .fst b ≡ b') →
        Path (Σ ⟨ B' .fst ⟩ (λ b' → ⟨ PushMODELInternalᴰ .fst b' ⟩))
          (ϕ .fst b , b , refl , bᴰ)
          (b' , b , p , bᴰ)
      push-path b bᴰ p = ΣPathP
        ( p
        , ΣPathP
            ( refl
            , ΣPathP
                ( isProp→PathP
                    (λ i → B' .fst .snd (ϕ .fst b) (p i)) _ _
                , refl)))

      canonical-homᴰ : ∀ {Z : Category.ob (MODEL T L)}
        (ψ : Homo (MODELOb→Model B' .fst) (MODELOb→Model Z .fst))
        (Zᴰ : Categoryᴰ.ob[_] (MODELᴰ T L L) Z)
        (χᴰ : Categoryᴰ.Hom[_][_,_] (MODELᴰ T L L) ψ PushMODELInternalᴰ Zᴰ)
        → Categoryᴰ.Hom[_][_,_] (MODELᴰ T L L) (ϕ ⋆H ψ) Bᴰ Zᴰ
      canonical-homᴰ {Z = Z} ψ Zᴰ χᴰ =
        _⋆Hᴰ_
          {A = MODELOb→Model B .fst}
          {B = MODELOb→Model B' .fst}
          {C = MODELOb→Model Z .fst}
          {Aᴰ = MODELᴰOb→Modelᴰ Bᴰ .fst}
          {Bᴰ = MODELᴰOb→Modelᴰ PushMODELInternalᴰ .fst}
          {Cᴰ = MODELᴰOb→Modelᴰ Zᴰ .fst}
          {ϕ = ϕ} {ψ = ψ} (_ , push-inᴰ .snd) (_ , χᴰ .snd)

      recPush-η-fᴰ : ∀ {Z : Category.ob (MODEL T L)}
        (ψ : Homo (MODELOb→Model B' .fst) (MODELOb→Model Z .fst))
        (Zᴰ : Categoryᴰ.ob[_] (MODELᴰ T L L) Z)
        (χᴰ : Categoryᴰ.Hom[_][_,_] (MODELᴰ T L L) ψ PushMODELInternalᴰ Zᴰ)
        b' (x : ⟨ PushMODELInternalᴰ .fst b' ⟩)
        → recPush-fᴰ ψ Zᴰ (canonical-homᴰ ψ Zᴰ χᴰ) b' x
          ≡ χᴰ .fst b' x
      recPush-η-fᴰ {Z = Z} ψ Zᴰ χᴰ b' (b , p , bᴰ) =
        ZᴰR.rectifyOut $
          ZᴰR.reind-filler⁻ (cong (ψ .fst) p)
          ∙ cong totalχ (push-path b bᴰ p)
        where
        module ZᴰR = hSetReasoning (Z .fst) (λ z → ⟨ Zᴰ .fst z ⟩)
        totalχ : (Σ ⟨ B' .fst ⟩ (λ z → ⟨ PushMODELInternalᴰ .fst z ⟩))
          → Σ ⟨ Z .fst ⟩ (λ z → ⟨ Zᴰ .fst z ⟩)
        totalχ q = ψ .fst (q .fst) , χᴰ .fst (q .fst) (q .snd)

      push-base : ∫C (C ^opᴰ)
        [ (𝒞 , B') , (𝒞 , B) ]
      push-base = _ , ϕ

      push-lift : CartesianLift (Cᴰ ^opᴰᴰ) push-base Bᴰ
      push-lift = UniversalElementⱽ'.REPRⱽ ue
        where
        module Cᴰᶠ = Fibers (Cᴰ ^opᴰᴰ)
        module Dᴰ = Fibers (MODELᴰ T L L)

        Homo≡ : ∀ {X Z : Category.ob (MODEL T L)}
          (f g : Homo (MODELOb→Model X .fst) (MODELOb→Model Z .fst))
          → f .fst ≡ g .fst → f ≡ g
        Homo≡ {Z = Z} f g p i .fst = p i
        Homo≡ {Z = Z} f g p i .snd =
          isProp→PathP
            {B = λ i → isHomoSimpl _ _ (p i)}
            (λ _ → isPropΠ4 λ _ _ _ _ → Z .fst .snd _ _)
            (f .snd) (g .snd) i

        CBPVHomo≡ : ∀ {X Z : Category.ob (MODEL T L)}
          (f g : ∫C (C ^opᴰ) [ (𝒞 , Z) , (𝒞 , X) ])
          → f .snd .fst ≡ g .snd .fst → f ≡ g
        CBPVHomo≡ f g p i .fst = f .fst
        CBPVHomo≡ {X = X} {Z = Z} f g p i .snd =
          Homo≡ {X = X} {Z = Z} (f .snd) (g .snd) p i

        MODELᴰHomoP≡ : ∀ {X Z : Category.ob (MODEL T L)}
          {Xᴰ : Categoryᴰ.ob[_] (MODELᴰ T L L) X}
          {Zᴰ : Categoryᴰ.ob[_] (MODELᴰ T L L) Z}
          {f g : Homo (MODELOb→Model X .fst) (MODELOb→Model Z .fst)}
          (p : f ≡ g)
          (fᴰ : Categoryᴰ.Hom[_][_,_] (MODELᴰ T L L) f Xᴰ Zᴰ)
          (gᴰ : Categoryᴰ.Hom[_][_,_] (MODELᴰ T L L) g Xᴰ Zᴰ)
          → PathP
              (λ i → ∀ x → ⟨ Xᴰ .fst x ⟩ → ⟨ Zᴰ .fst (p i .fst x) ⟩)
              (fᴰ .fst) (gᴰ .fst)
          → PathP
              (λ i → Categoryᴰ.Hom[_][_,_] (MODELᴰ T L L) (p i) Xᴰ Zᴰ)
              fᴰ gᴰ
        MODELᴰHomoP≡ p fᴰ gᴰ q i .fst = q i
        MODELᴰHomoP≡ {Zᴰ = Zᴰ} p fᴰ gᴰ q i .snd =
          isProp→PathP
            {B = λ i → isHomoᴰSimpl (p i)
              (_ , _) (_ , Zᴰ .snd .fst) (q i)}
            (λ _ → isPropΠ6 λ _ _ _ _ _ _ →
              isPropΠ λ _ → Zᴰ .fst _ .snd _ _)
            (fᴰ .snd) (gᴰ .snd) i

        ue : UniversalElementⱽ' (Cᴰ ^opᴰᴰ)
          (𝒞 , B')
          (CartesianLiftPshSpec
            ((∫C (C ^opᴰ)) [-, (𝒞 , B) ])
            (Cᴰ ^opᴰᴰ)
            ((Cᴰ ^opᴰᴰ) [-][-, Bᴰ ])
            push-base)
        ue .UniversalElementⱽ'.vertexⱽ = PushMODELInternalᴰ
        ue .UniversalElementⱽ'.elementⱽ .fst = push-inᴰ .fst
        ue .UniversalElementⱽ'.elementⱽ .snd =
          subst
            (λ hϕ → isHomoᴰSimpl (ϕ .fst , hϕ)
              (_ , Bᴰ .snd .fst) (_ , PushMODELInternalᴰ .snd .fst)
              (push-inᴰ .fst))
            (isProp→PathP
              (λ _ → isPropΠ4 λ _ _ _ _ → B' .fst .snd _ _)
              (ϕ .snd) _)
            (push-inᴰ .snd)
        ue .UniversalElementⱽ'.universalⱽ
          ((𝒞 , Z) , Zᴰ , ψ) .fst γᴰ =
            recPushᴰ (ψ .snd) Zᴰ γᴰ
        ue .UniversalElementⱽ'.universalⱽ
          ((𝒞 , Z) , Zᴰ , ψ) .snd .fst γᴰ =
            Cᴰᶠ.rectifyOut {e' = refl} $
              Cᴰᶠ.reind-filler⁻ _
              ∙ Cᴰᶠ.≡in
                  {pth = CBPVHomo≡ _ _ refl}
                  (MODELᴰHomoP≡ {X = B} {Z = Z}
                    (Homo≡ {X = B} {Z = Z} _ _ refl) _ _
                    (funExt λ b → funExt λ bᴰ →
                      hSetReasoning.rectifyOut (Z .fst)
                        (λ z → ⟨ Zᴰ .fst z ⟩)
                        (hSetReasoning.reind-filler⁻ (Z .fst)
                          (λ z → ⟨ Zᴰ .fst z ⟩) refl)))
        ue .UniversalElementⱽ'.universalⱽ
          ((𝒞 , Z) , Zᴰ , ψ) .snd .snd χᴰ =
            cong (ue .UniversalElementⱽ'.universalⱽ
              ((𝒞 , Z) , Zᴰ , ψ) .fst)
              (Cᴰᶠ.rectifyOut {e' = refl} $
                Cᴰᶠ.reind-filler⁻ _
                ∙ Cᴰᶠ.≡in
                    {pth = CBPVHomo≡ _ _ refl}
                    (MODELᴰHomoP≡ {X = B} {Z = Z}
                      (Homo≡ {X = B} {Z = Z} _ _ refl) _ _ refl))
            ∙ (Dᴰ.rectify {a = B'} {b = Z}
                {aᴰ = PushMODELInternalᴰ} {bᴰ = Zᴰ} $
                Dᴰ.≡out $ Dᴰ.≡in {a = B'} {b = Z}
                  {aᴰ = PushMODELInternalᴰ} {bᴰ = Zᴰ}
                  {p = recPushᴰ (ψ .snd) Zᴰ
                    (canonical-homᴰ (ψ .snd) Zᴰ χᴰ)}
                  {q = χᴰ}
                  (MODELᴰHomo≡ T _ _
                    (funExt λ b' → funExt λ x →
                      recPush-η-fᴰ (ψ .snd) Zᴰ χᴰ b' x)))

  PushMODELᴰ : ∀ {B B' : Category.ob (MODEL T L)}
    (ϕ : MODEL T L [ B , B' ])
    (Bᴰ : Categoryᴰ.ob[_] (MODELᴰ T L L) B)
    → Categoryᴰ.ob[_] (MODELᴰ T L L) B'
  PushMODELᴰ = PushMODELInternalᴰ

  CanonicalFreeMODELConstruction : FreeMODELConstruction
  CanonicalFreeMODELConstruction .fst = MODELFree T
  CanonicalFreeMODELConstruction .snd = η-lift

  CanonicalBoolFreeMODELConstruction : BoolFreeMODELConstruction
  CanonicalBoolFreeMODELConstruction .fst .fst =
    FreeModel Bool .fst .fst , FreeModel Bool .snd .snd
  CanonicalBoolFreeMODELConstruction .fst .snd .fst =
    FreeModel Bool .fst .snd
  CanonicalBoolFreeMODELConstruction .fst .snd .snd =
    FreeModel Bool .snd .fst
  CanonicalBoolFreeMODELConstruction .snd .fst = var
  CanonicalBoolFreeMODELConstruction .snd .snd B = isIsoToIsEquiv
    ( recFM Bool (MODELOb→Model B)
    , (λ _ → refl)
    , (λ ϕ → Σ≡Prop
        (λ _ → isPropΠ4 λ _ _ _ _ → B .fst .snd _ _)
        (sym (recFM-uniq Bool (MODELOb→Model B) ϕ)))
    )

  ModelCBPV-FⱽWithFree : (Free : FreeMODELConstruction) → hasFⱽ Cᴰ
  ModelCBPV-FⱽWithFree Free {A = A} {B = B} f Aᴰ =
    transportCartesianLift (Cᴰ ^opᴰᴰ) factor≡f composite
    where
    module Cᵒᵖ = Category (∫C (C ^opᴰ))

    recf : MODEL T L [ Free .fst A .UniversalElement.vertex , B ]
    recf = isEquivToIsIso _
      (Free .fst A .UniversalElement.universal B) .fst f

    free-lift : CartesianLift (Cᴰ ^opᴰᴰ)
      (FreeMODELη (Free .fst) A) Aᴰ
    free-lift = Free .snd A Aᴰ

    composite : CartesianLift (Cᴰ ^opᴰᴰ)
      ((_ , recf) Cᵒᵖ.⋆ (FreeMODELη (Free .fst) A)) Aᴰ
    composite = composeCartesianLifts (Cᴰ ^opᴰᴰ)
      free-lift (push-lift recf (free-lift .fst))

    factor≡f :
      ((_ , recf) Cᵒᵖ.⋆ (FreeMODELη (Free .fst) A)) ≡ (_ , f)
    factor≡f = ΣPathP
      ( refl
      , isEquivToIsIso _
          (Free .fst A .UniversalElement.universal B) .snd .fst f)

  ModelCBPV-Fⱽ : hasFⱽ Cᴰ
  ModelCBPV-Fⱽ = ModelCBPV-FⱽWithFree CanonicalFreeMODELConstruction

  ModelCBPVⱽWithFree : (Free : FreeMODELConstruction) →
    MultCBPVCatⱽ (ModelCBPVWithFree T (Free .fst) .fst)
      (ℓ-suc L) L
  ModelCBPVⱽWithFree Free .fst = Cᴰ
  ModelCBPVⱽWithFree Free .snd .fst = ModelCBPV-Uⱽ
  ModelCBPVⱽWithFree Free .snd .snd = ModelCBPV-FⱽWithFree Free

  ModelCBPVⱽ : MultCBPVCatⱽ (ModelCBPV T .fst)
    (ℓ-suc L) L
  ModelCBPVⱽ = ModelCBPVⱽWithFree CanonicalFreeMODELConstruction
