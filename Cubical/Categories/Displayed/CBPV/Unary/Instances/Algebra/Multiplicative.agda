{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.Algebra.Multiplicative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.More
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Algebra.Signature.Base

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.TotalCategory hiding (elim)
open import Cubical.Categories.Instances.WalkingArrow
  renaming (l to 𝒱; r to 𝒞)
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Algebra.Algebra
open import Cubical.Categories.Displayed.Instances.Algebra.DisplayedAlgebra
open import Cubical.Categories.Displayed.Instances.Opposite
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base as EqPsh
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Algebra.Base

private
  variable
    ℓO ℓA : Level

module _ (Sig : Signature ℓO ℓA) (isSetOp : isSet (Signature.Op Sig)) where
  open Signature Sig

  private
    L = AlgebraLevel Sig
    C = AlgebraCBPV Sig isSetOp .fst
    Cᴰ = AlgebraCBPVᴰ Sig isSetOp

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

  AlgebraCBPV-Uⱽ : hasUⱽ Cᴰ
  AlgebraCBPV-Uⱽ {A = A} {B = B} f Bᴰ =
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
    FreeALGᴰ : (A : hSet L) (Aᴰ : ⟨ A ⟩ → hSet L)
      → Categoryᴰ.ob[_] (ALGᴰ Sig L L) (FreeALG Sig isSetOp A)
    FreeALGᴰ A Aᴰ .fst t =
      |FreeAlgebraᴰ| (λ x → ⟨ Aᴰ x ⟩) t ,
      isSetFreeAlgebraᴰ (λ x → ⟨ Aᴰ x ⟩)
        isSetOp (A .snd) (λ x → Aᴰ x .snd) t
    FreeALGᴰ A Aᴰ .snd = FreeAlgebraᴰ (λ x → ⟨ Aᴰ x ⟩) .snd

    η-base : (A : hSet L) → (∫C C) [ (𝒱 , A) , (𝒞 , FreeALG Sig isSetOp A) ]
    η-base A = _ , var

    η-lift : (A : hSet L) (Aᴰ : ⟨ A ⟩ → hSet L)
      → CartesianLift (Cᴰ ^opᴰᴰ) (η-base A) Aᴰ
    η-lift A Aᴰ = UniversalElementⱽ'.REPRⱽ ue
      where
      module Cᴰᶠ = Fibers (Cᴰ ^opᴰᴰ)
      module Dᴰ = Fibers (ALGᴰ Sig L L)

      ue : UniversalElementⱽ' (Cᴰ ^opᴰᴰ)
        (𝒞 , FreeALG Sig isSetOp A)
        (CartesianLiftPshSpec
          ((∫C (C ^opᴰ)) [-, (𝒱 , A) ])
          (Cᴰ ^opᴰᴰ)
          ((Cᴰ ^opᴰᴰ) [-][-, Aᴰ ])
          (η-base A))
      ue .UniversalElementⱽ'.vertexⱽ = FreeALGᴰ A Aᴰ
      ue .UniversalElementⱽ'.elementⱽ x xᴰ = |FreeAlgebraᴰ|.var xᴰ
      ue .UniversalElementⱽ'.universalⱽ
        ((𝒱 , Z) , Zᴰ , ()) .fst
      ue .UniversalElementⱽ'.universalⱽ
        ((𝒞 , Z) , Zᴰ , ϕ) .fst ıᴰ =
          recFAᴰ (λ x → ⟨ Aᴰ x ⟩) (ϕ .snd) (_ , Zᴰ .snd) ıᴰ
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
                (ALGᴰHomo≡ Sig _ _
                  (sym (recFAᴰ-η (λ x → ⟨ Aᴰ x ⟩)
                    (ϕ .snd) (_ , Zᴰ .snd) (_ , ϕᴰ .snd)))))

    module _ {B B' : Category.ob (ALG Sig L)}
      (ϕ : Homo (_ , B .snd) (_ , B' .snd))
      (Bᴰ : Categoryᴰ.ob[_] (ALGᴰ Sig L L) B) where

      PushALGᴰ : Categoryᴰ.ob[_] (ALGᴰ Sig L L) B'
      PushALGᴰ .fst b' .fst =
        Σ[ b ∈ ⟨ B .fst ⟩ ] (ϕ .fst b ≡ b') × ⟨ Bᴰ .fst b ⟩
      PushALGᴰ .fst b' .snd =
        isSetΣ (B .fst .snd) λ b →
          isSet× (isProp→isSet (B' .fst .snd _ _)) (Bᴰ .fst b .snd)
      PushALGᴰ .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
        B .snd op (λ v → γᴰ v .fst) ,
        (sym (ϕ .snd op (λ v → γᴰ v .fst) _ refl)
          ∙ cong (B' .snd op) (funExt λ v → γᴰ v .snd .fst)
          ∙ op∘γ≡op⟨γ⟩) ,
        Bᴰ .snd op (λ v → γᴰ v .fst)
          (λ v → γᴰ v .snd .snd) _ refl

      push-inᴰ : Categoryᴰ.Hom[_][_,_] (ALGᴰ Sig L L) ϕ Bᴰ PushALGᴰ
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
                      (λ i → Bᴰ .snd op γ γᴰ
                        (op∘γ≡op⟨γ⟩ i)
                        (λ j → op∘γ≡op⟨γ⟩ (i ∧ j)))
                    ∙ hSetReasoning.≡in (B .fst)
                        (λ b → ⟨ Bᴰ .fst b ⟩)
                        op∘γᴰ≡op⟨γᴰ⟩)))

      module _ {Z : Category.ob (ALG Sig L)}
        (ψ : Homo (_ , B' .snd) (_ , Z .snd))
        (Zᴰ : Categoryᴰ.ob[_] (ALGᴰ Sig L L) Z)
        (γᴰ : Categoryᴰ.Hom[_][_,_] (ALGᴰ Sig L L)
          (ϕ ⋆H ψ) Bᴰ Zᴰ) where

        private
          module ZᴰR = hSetReasoning (Z .fst) (λ z → ⟨ Zᴰ .fst z ⟩)

        recPush-fᴰ : ∀ b' → ⟨ PushALGᴰ .fst b' ⟩
          → ⟨ Zᴰ .fst (ψ .fst b') ⟩
        recPush-fᴰ b' (b , p , bᴰ) =
          ZᴰR.reind (cong (ψ .fst) p) (γᴰ .fst b bᴰ)

        private
          op-filler : ∀ op δ δᴰ z (p : Z .snd op δ ≡ z)
            → (Z .snd op δ , Zᴰ .snd op δ δᴰ _ refl)
              ≡ (z , Zᴰ .snd op δ δᴰ z p)
          op-filler op δ δᴰ z p i .fst = p i
          op-filler op δ δᴰ z p i .snd =
            Zᴰ .snd op δ δᴰ (p i) (λ j → p (i ∧ j))

          child-path : ∀ {b'} (x : ⟨ PushALGᴰ .fst b' ⟩) →
            Path (Σ ⟨ Z .fst ⟩ (λ z → ⟨ Zᴰ .fst z ⟩))
              (ψ .fst (ϕ .fst (x .fst)) ,
                γᴰ .fst (x .fst) (x .snd .snd))
              (ψ .fst b' , recPush-fᴰ b' x)
          child-path (b , p , bᴰ) = ΣPathP
            ( cong (ψ .fst) p
            , ZᴰR.rectifyOut (ZᴰR.reind-filler (cong (ψ .fst) p)))

        recPushᴰ : Categoryᴰ.Hom[_][_,_] (ALGᴰ Sig L L)
          ψ PushALGᴰ Zᴰ
        recPushᴰ .fst = recPush-fᴰ
        recPushᴰ .snd op δ δᴰ op⟨δ⟩ op∘δ≡op⟨δ⟩
          op⟨δᴰ⟩ op∘δᴰ≡op⟨δᴰ⟩ =
            ZᴰR.rectifyOut $
              sym (op-filler op (ψ .fst ∘ δ)
                (λ v → recPush-fᴰ (δ v) (δᴰ v)) _
                (ψ .snd op δ op⟨δ⟩ op∘δ≡op⟨δ⟩))
              ∙ sym (cong (∫Algebra (_ , Zᴰ .snd) .snd op)
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
                    (PushALGᴰ .snd op δ δᴰ op⟨δ⟩
                      op∘δ≡op⟨δ⟩ .snd .fst))
              ∙ ZᴰR.≡in
                  (cong (recPush-fᴰ op⟨δ⟩)
                    op∘δᴰ≡op⟨δᴰ⟩)

      push-path : ∀ b bᴰ {b'} (p : ϕ .fst b ≡ b') →
        Path (Σ ⟨ B' .fst ⟩ (λ b' → ⟨ PushALGᴰ .fst b' ⟩))
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

      canonical-homᴰ : ∀ {Z : Category.ob (ALG Sig L)}
        (ψ : Homo (_ , B' .snd) (_ , Z .snd))
        (Zᴰ : Categoryᴰ.ob[_] (ALGᴰ Sig L L) Z)
        (χᴰ : Categoryᴰ.Hom[_][_,_] (ALGᴰ Sig L L) ψ PushALGᴰ Zᴰ)
        → Categoryᴰ.Hom[_][_,_] (ALGᴰ Sig L L) (ϕ ⋆H ψ) Bᴰ Zᴰ
      canonical-homᴰ {Z = Z} ψ Zᴰ χᴰ =
        _⋆Hᴰ_ {A = (_ , B .snd)} {B = (_ , B' .snd)} {C = (_ , Z .snd)}
          {Aᴰ = (_ , Bᴰ .snd)} {Bᴰ = (_ , PushALGᴰ .snd)}
          {Cᴰ = (_ , Zᴰ .snd)} {ϕ = ϕ} {ψ = ψ} push-inᴰ χᴰ

      recPush-η-fᴰ : ∀ {Z : Category.ob (ALG Sig L)}
        (ψ : Homo (_ , B' .snd) (_ , Z .snd))
        (Zᴰ : Categoryᴰ.ob[_] (ALGᴰ Sig L L) Z)
        (χᴰ : Categoryᴰ.Hom[_][_,_] (ALGᴰ Sig L L) ψ PushALGᴰ Zᴰ)
        b' (x : ⟨ PushALGᴰ .fst b' ⟩)
        → recPush-fᴰ ψ Zᴰ (canonical-homᴰ ψ Zᴰ χᴰ) b' x
          ≡ χᴰ .fst b' x
      recPush-η-fᴰ {Z = Z} ψ Zᴰ χᴰ b' (b , p , bᴰ) =
        ZᴰR.rectifyOut $
          ZᴰR.reind-filler⁻ (cong (ψ .fst) p)
          ∙ cong totalχ (push-path b bᴰ p)
        where
        module ZᴰR = hSetReasoning (Z .fst) (λ z → ⟨ Zᴰ .fst z ⟩)
        totalχ : (Σ ⟨ B' .fst ⟩ (λ z → ⟨ PushALGᴰ .fst z ⟩))
          → Σ ⟨ Z .fst ⟩ (λ z → ⟨ Zᴰ .fst z ⟩)
        totalχ q = ψ .fst (q .fst) , χᴰ .fst (q .fst) (q .snd)

      push-base : ∫C (C ^opᴰ)
        [ (𝒞 , B') , (𝒞 , B) ]
      push-base = _ , ϕ

      push-lift : CartesianLift (Cᴰ ^opᴰᴰ) push-base Bᴰ
      push-lift = UniversalElementⱽ'.REPRⱽ ue
        where
        module Cᴰᶠ = Fibers (Cᴰ ^opᴰᴰ)
        module Dᴰ = Fibers (ALGᴰ Sig L L)

        Homo≡ : ∀ {X Z : Category.ob (ALG Sig L)}
          (f g : Homo (_ , X .snd) (_ , Z .snd))
          → f .fst ≡ g .fst → f ≡ g
        Homo≡ {Z = Z} f g p i .fst = p i
        Homo≡ {Z = Z} f g p i .snd =
          isProp→PathP
            {B = λ i → isHomoSimpl _ _ (p i)}
            (λ _ → isPropΠ4 λ _ _ _ _ → Z .fst .snd _ _)
            (f .snd) (g .snd) i

        CBPVHomo≡ : ∀ {X Z : Category.ob (ALG Sig L)}
          (f g : ∫C (C ^opᴰ) [ (𝒞 , Z) , (𝒞 , X) ])
          → f .snd .fst ≡ g .snd .fst → f ≡ g
        CBPVHomo≡ f g p i .fst = f .fst
        CBPVHomo≡ f g p i .snd = Homo≡ (f .snd) (g .snd) p i

        ALGᴰHomoP≡ : ∀ {X Z : Category.ob (ALG Sig L)}
          {Xᴰ : Categoryᴰ.ob[_] (ALGᴰ Sig L L) X}
          {Zᴰ : Categoryᴰ.ob[_] (ALGᴰ Sig L L) Z}
          {f g : Homo (_ , X .snd) (_ , Z .snd)}
          (p : f ≡ g)
          (fᴰ : Categoryᴰ.Hom[_][_,_] (ALGᴰ Sig L L) f Xᴰ Zᴰ)
          (gᴰ : Categoryᴰ.Hom[_][_,_] (ALGᴰ Sig L L) g Xᴰ Zᴰ)
          → PathP
              (λ i → ∀ x → ⟨ Xᴰ .fst x ⟩ → ⟨ Zᴰ .fst (p i .fst x) ⟩)
              (fᴰ .fst) (gᴰ .fst)
          → PathP
              (λ i → Categoryᴰ.Hom[_][_,_] (ALGᴰ Sig L L) (p i) Xᴰ Zᴰ)
              fᴰ gᴰ
        ALGᴰHomoP≡ p fᴰ gᴰ q i .fst = q i
        ALGᴰHomoP≡ {Zᴰ = Zᴰ} p fᴰ gᴰ q i .snd =
          isProp→PathP
            {B = λ i → isHomoᴰSimpl (p i)
              (_ , _) (_ , Zᴰ .snd) (q i)}
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
        ue .UniversalElementⱽ'.vertexⱽ = PushALGᴰ
        ue .UniversalElementⱽ'.elementⱽ .fst = push-inᴰ .fst
        ue .UniversalElementⱽ'.elementⱽ .snd =
          subst
            (λ hϕ → isHomoᴰSimpl (ϕ .fst , hϕ)
              (_ , Bᴰ .snd) (_ , PushALGᴰ .snd) (push-inᴰ .fst))
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
                  (ALGᴰHomoP≡ (Homo≡ _ _ refl) _ _
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
                    (ALGᴰHomoP≡ (Homo≡ _ _ refl) _ _ refl))
            ∙ (Dᴰ.rectify {a = B'} {b = Z}
                {aᴰ = PushALGᴰ} {bᴰ = Zᴰ} $
                Dᴰ.≡out $ Dᴰ.≡in {a = B'} {b = Z}
                  {aᴰ = PushALGᴰ} {bᴰ = Zᴰ}
                  {p = recPushᴰ (ψ .snd) Zᴰ
                    (canonical-homᴰ (ψ .snd) Zᴰ χᴰ)}
                  {q = χᴰ}
                  (ALGᴰHomo≡ Sig _ _
                    (funExt λ b' → funExt λ x →
                      recPush-η-fᴰ (ψ .snd) Zᴰ χᴰ b' x)))

  AlgebraCBPV-Fⱽ : hasFⱽ Cᴰ
  AlgebraCBPV-Fⱽ {A = A} {B = B} f Aᴰ =
    transportCartesianLift (Cᴰ ^opᴰᴰ) factor≡f composite
    where
    module Cᵒᵖ = Category (∫C (C ^opᴰ))

    recf : Homo (_ , FreeALG Sig isSetOp A .snd) (_ , B .snd)
    recf = recFA (_ , B .snd) f

    composite : CartesianLift (Cᴰ ^opᴰᴰ)
      ((_ , recf) Cᵒᵖ.⋆ (η-base A)) Aᴰ
    composite = composeCartesianLifts (Cᴰ ^opᴰᴰ)
      (η-lift A Aᴰ) (push-lift recf (FreeALGᴰ A Aᴰ))

    factor≡f : ((_ , recf) Cᵒᵖ.⋆ (η-base A)) ≡ (_ , f)
    factor≡f = ΣPathP (refl , refl)

  AlgebraCBPVⱽ : MultCBPVCatⱽ (AlgebraCBPV Sig isSetOp .fst)
    (ℓ-suc L) L
  AlgebraCBPVⱽ .fst = Cᴰ
  AlgebraCBPVⱽ .snd .fst = AlgebraCBPV-Uⱽ
  AlgebraCBPVⱽ .snd .snd = AlgebraCBPV-Fⱽ
