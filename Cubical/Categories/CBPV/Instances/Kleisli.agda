{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.CBPV.Instances.Kleisli where
  open import Cubical.Foundations.Prelude
  open import Cubical.Categories.Functor
  open import Cubical.Categories.Category
  open import Cubical.Categories.NaturalTransformation
  open import Cubical.Categories.Instances.Sets
  open import Cubical.Categories.Presheaf.Morphism.Alt
  open import Cubical.Foundations.HLevels
  open import Cubical.Foundations.Structure
  open import Cubical.Data.Unit
  open import Cubical.Data.Sigma
  open import Cubical.Categories.Monoidal.Base
  open import Cubical.Categories.Monoidal.Enriched
  open import Cubical.Categories.Monad.ExtensionSystem
  open import Cubical.Categories.CBPV.Instances.Free
  open import Cubical.Categories.Enriched.More
  open import Cubical.Categories.Enriched.Presheaf
  open import Cubical.Categories.CBPV.Base

  open Functor
  open CBPVModel
  open Category
  open EnrichedFunctor
  open EnrichedCategory
  open MonoidalCategory hiding (η)
  open NatTrans
  open PshHom

  module Model {ℓ : Level}(M : ExtensionSystem (SET ℓ)) where
    private
      set = SET ℓ

    open model set {ℓ}
    open ExtensionSystemFor (M .snd)

    private
      T : ob set → ob set
      T = M .fst
      K = Kleisli set M
      E = enrich K

      𝓟[_,_] : ob 𝓟 → ob 𝓟 → Type (ℓ-suc ℓ)
      𝓟[_,_] = 𝓟 .Hom[_,_]

      E[_,_] : ob E → ob E → ob 𝓟
      E[_,_] = E .Hom[_,_]

      self[_,_] : ob self → ob self → ob 𝓟Mon
      self[_,_] = self .Hom[_,_]

    cmp : ob set → Functor (set ^op) (SET (ℓ-suc ℓ))
    cmp B .F-ob Γ = Lift (K [ Γ , B ]) , isOfHLevelLift 2 (K .isSetHom {Γ}{B})
    cmp B .F-hom γ (lift f) = lift λ z → f (γ z) -- precomposition
    cmp B .F-id = funExt λ _ → refl
    cmp B .F-seq _ _ = funExt λ _ → refl

    inner : (B B' : ob E)(Γ : ob set)(k : ⟨ Γ ⟩ → K [ B , B' ]) →
     ⟨ self[ cmp B , cmp B' ] .F-ob Γ ⟩
    -- Given B,B',Γ,k : Γ → B → MB, Δ, γ : Δ → Γ, m : Δ → B, d : Δ
    -- construct _ : Δ → M B'
    -- m d >>= k (γ d)
    inner B B' Γ k .N-ob Δ (γ , m) = lift λ d → bind (k (γ d)) (m .lower d)
    inner B B' Γ k .N-hom Δ Θ γ (δ , lift m) = refl

    stk : (B B' : ob E) → 𝓟[ E[ B , B' ] , self[ cmp B , cmp B' ] ]
    stk B B' .N-ob Γ k = inner _ _ _ (k .lower)
    stk B B' .N-hom {Γ}{Δ} γ =
      funExt λ _ → makePshHomPath (funExt λ _ → funExt λ _ → refl)

    tmb : EnrichedFunctor 𝓟Mon E self
    tmb .F₀  = cmp
    tmb .F₁ {B}{B'} = stk B B'
    tmb .Fid {B} =
      makeNatTransPath (funExt λ Γ → funExt λ _ →
        makePshHomPath (funExt λ Δ → funExt λ {(γ , m) →
          cong lift (funExt λ d → funExt⁻ bind-r _)}) )
    tmb .Fseq {X}{Y}{Z} =
      makeNatTransPath (funExt λ Γ → funExt λ k,k' →
        makePshHomPath (funExt λ Δ → funExt λ {(γ , m) →
        cong lift (funExt λ d → funExt⁻ bind-comp _)}))

    kleisli : CBPVModel
    kleisli .𝓒 = set
    kleisli .𝓔 = E
    kleisli .vTy = ob set
    kleisli .vTm A = set [-, A ]
    kleisli .cTm = tmb
    kleisli .emp = (Unit*  {ℓ}, isSetUnit*) ,
                    λ X → (λ _ → tt*) ,
                    λ f → funExt λ _ → refl
    kleisli ._×c_ =  λ A B → ⟨ A ⟩ × ⟨ B ⟩ , isSetΣ (A .snd) λ _ → B .snd
    kleisli .up×c = λ Γ A →
      record {
        trans =
          natTrans
            (λ X f → (λ x → fst (f x)) , (λ x → snd (f x)))
            λ _ → refl ;
        nIso = λ X →
          isiso
            (λ {(f , g) x → (f x) , (g x)})
            (funExt (λ _ → refl))
            (funExt (λ _ → refl)) }
