{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.2Functor.CodomainFibration where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor as Func
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Limits.Pullback.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More

open import Cubical.Categories.2Category.Base
open import Cubical.Categories.2Functor.Base
open import Cubical.Categories.2Functor.Fibration

private
  variable
    ℓC ℓC' ℓC'' ℓD ℓD' ℓD'' ℓE ℓE' : Level

open 2Category
open LaxFunctor
open PseudoFunctor
open isPseudo
open Functorᴰ
open Functor
open NatTrans
open isIso2Cell

module _ {ℓC ℓC'} (C : Category ℓC ℓC') (pb : Pullbacks C) where
  private
    module C = Category C

  CodomainFibration-lax : LaxFunctor (Cat→2CatEq (C ^op)) (CAT {ℓC = _} {ℓC' = _})
  CodomainFibration-lax .F₀ c = ∫C (Slice C c)
  CodomainFibration-lax .F₁ = ChangeBase C pb
  CodomainFibration-lax .F₂ Eq.refl = idTrans _
  CodomainFibration-lax .F-id = ChangeBaseId C pb
  CodomainFibration-lax .F-seq f g = ChangeBaseComp C pb f g
  CodomainFibration-lax .F-id₂ = refl
  CodomainFibration-lax .F-seqⱽ {y = y} Eq.refl Eq.refl =
    makeNatTransPath (funExt λ _ → sym $ ∫C (Slice C y) .Category.⋆IdL _)
  CodomainFibration-lax .F-seqᴴ {z = z} {f = f} {g = g} Eq.refl Eq.refl =
    makeNatTransPath (funExt λ _ →
        Slice.⋆IdR _
      ∙ sym (Slice.⋆IdL _)
      ∙ Slice.⟨ sym (ChangeBase C pb g .F-id) ⟩⋆⟨ refl ⟩
      ∙ Slice.⟨ sym (Slice.⋆IdR _) ⟩⋆⟨ refl ⟩)
      where module Slice = Category (∫C (Slice C z))
  CodomainFibration-lax .F-unitality-l {x = x} {y = y} f =
    -- Gross proof that I outsourced to Claude
    makeNatTransPathP _ _ (λ i (a , α) → hPath (a , α) i , condPath (a , α) i)
    where
    module _ ((a , α) : ∫C (Slice C x) .Category.ob) where
      module pbfα = PullbackNotation (pb f α)
      module pbfid = PullbackNotation (pb (f C.⋆ C.id) α)
      module pbId = PullbackNotation (pb (C.id {x}) α)
      module pbgₗ = PullbackNotation (pb f pbId.pbπ₁)
      -- Y = ChangeBase f applied to (F-id at (a,α))
      Y : C.Hom[ pbfα.vert , pbgₗ.vert ]
      Y = ChangeBase C pb f .F-hom (ChangeBaseId C pb .N-ob (a , α)) .fst
      -- Z = F-seq id f at (a,α)
      Z : C.Hom[ pbgₗ.vert , pbfid.vert ]
      Z = ChangeBaseComp C pb (C.id {x}) f .N-ob (a , α) .fst
      -- LHS.N-ob(a,α).fst computes to (Y ⋆ id) ⋆ Z
      lhs-π₁ : ((Y C.⋆ C.id) C.⋆ Z) C.⋆ pbfid.pbπ₁ ≡ pbfα.pbπ₁
      lhs-π₁ =
          C.⋆Assoc _ _ _
        ∙ C.⟨ refl ⟩⋆⟨ pbfid.pbβ₁ ⟩
        ∙ C.⟨ C.⋆IdR _ ⟩⋆⟨ refl ⟩
        ∙ pbgₗ.pbβ₁
      lhs-π₂ : ((Y C.⋆ C.id) C.⋆ Z) C.⋆ pbfid.pbπ₂ ≡ pbfα.pbπ₂
      lhs-π₂ =
          C.⋆Assoc _ _ _
        ∙ C.⟨ refl ⟩⋆⟨ pbfid.pbβ₂ ⟩
        ∙ C.⟨ C.⋆IdR _ ⟩⋆⟨ refl ⟩
        ∙ sym (C.⋆Assoc _ _ _)
        ∙ C.⟨ pbgₗ.pbβ₂ ⟩⋆⟨ refl ⟩
        ∙ C.⋆Assoc _ _ _
        ∙ C.⟨ refl ⟩⋆⟨ pbId.pbβ₂ ⟩
        ∙ C.⋆IdR _
      -- interpolating family
      eq : (i : I) → pbfα.pbπ₁ C.⋆ C.⋆IdR f i ≡ pbfα.pbπ₂ C.⋆ α
      eq i = (λ j → pbfα.pbπ₁ C.⋆ C.⋆IdR f (i ∨ j)) ∙ pbfα.pbCommutes
      θ-path : PathP (λ i → C.Hom[ pbfα.vert , PullbackNotation.vert (pb (C.⋆IdR f i) α) ])
                     (pbfid.pbIntro pbfα.pbπ₁ pbfα.pbπ₂ (eq i0))
                     (pbfα.pbIntro pbfα.pbπ₁ pbfα.pbπ₂ (eq i1))
      θ-path i = PullbackNotation.pbIntro (pb (C.⋆IdR f i) α) pbfα.pbπ₁ pbfα.pbπ₂ (eq i)
      hPath : PathP (λ i → C.Hom[ pbfα.vert , PullbackNotation.vert (pb (C.⋆IdR f i) α) ])
                    ((Y C.⋆ C.id) C.⋆ Z) C.id
      hPath = sym (pbfid.pbIntro≡ (sym lhs-π₁) (sym lhs-π₂)) ◁ θ-path ▷
              pbfα.pbIntro≡ (sym (C.⋆IdL _)) (sym (C.⋆IdL _))
      condPath : PathP (λ i → hPath i C.⋆ PullbackNotation.pbπ₁ (pb (C.⋆IdR f i) α) ≡ pbfα.pbπ₁)
                 _ _
      condPath = isProp→PathP (λ _ → C.isSetHom _ _) _ _
  CodomainFibration-lax .F-unitality-r {x = x} {y = y} f =
    -- Claude
    makeNatTransPathP _ _ (λ i (a , α) → hPath (a , α) i , condPath (a , α) i)
    where
    module _ ((a , α) : ∫C (Slice C x) .Category.ob) where
      module pbfα = PullbackNotation (pb f α)
      module pbidf = PullbackNotation (pb (C.id C.⋆ f) α)
      module pbIdᵧ = PullbackNotation (pb (C.id {y}) pbfα.pbπ₁)
      -- W = F-id at (pbfα.vert, pbfα.pbπ₁) (in ∫C (Slice C y))
      W : C.Hom[ pbfα.vert , pbIdᵧ.vert ]
      W = ChangeBaseId C pb .N-ob (pbfα.vert , pbfα.pbπ₁) .fst
      -- V = F-seq f id at (a,α)
      V : C.Hom[ pbIdᵧ.vert , pbidf.vert ]
      V = ChangeBaseComp C pb f (C.id {y}) .N-ob (a , α) .fst
      -- LHS.N-ob(a,α).fst computes to (C.id ⋆ W) ⋆ V
      lhs-π₁ : ((C.id C.⋆ W) C.⋆ V) C.⋆ pbidf.pbπ₁ ≡ pbfα.pbπ₁
      lhs-π₁ =
          C.⋆Assoc _ _ _
        ∙ C.⟨ refl ⟩⋆⟨ pbidf.pbβ₁ ⟩
        ∙ C.⟨ C.⋆IdL _ ⟩⋆⟨ refl ⟩
        ∙ pbIdᵧ.pbβ₁
      lhs-π₂ : ((C.id C.⋆ W) C.⋆ V) C.⋆ pbidf.pbπ₂ ≡ pbfα.pbπ₂
      lhs-π₂ =
          C.⋆Assoc _ _ _
        ∙ C.⟨ refl ⟩⋆⟨ pbidf.pbβ₂ ⟩
        ∙ C.⟨ C.⋆IdL _ ⟩⋆⟨ refl ⟩
        ∙ sym (C.⋆Assoc _ _ _)
        ∙ C.⟨ pbIdᵧ.pbβ₂ ⟩⋆⟨ refl ⟩
        ∙ C.⋆IdL _
      eq : (i : I) → pbfα.pbπ₁ C.⋆ C.⋆IdL f i ≡ pbfα.pbπ₂ C.⋆ α
      eq i = (λ j → pbfα.pbπ₁ C.⋆ C.⋆IdL f (i ∨ j)) ∙ pbfα.pbCommutes
      θ-path : PathP (λ i → C.Hom[ pbfα.vert , PullbackNotation.vert (pb (C.⋆IdL f i) α) ])
                     (pbidf.pbIntro pbfα.pbπ₁ pbfα.pbπ₂ (eq i0))
                     (pbfα.pbIntro pbfα.pbπ₁ pbfα.pbπ₂ (eq i1))
      θ-path i = PullbackNotation.pbIntro (pb (C.⋆IdL f i) α) pbfα.pbπ₁ pbfα.pbπ₂ (eq i)
      hPath : PathP (λ i → C.Hom[ pbfα.vert , PullbackNotation.vert (pb (C.⋆IdL f i) α) ])
                    ((C.id C.⋆ W) C.⋆ V) C.id
      hPath = sym (pbidf.pbIntro≡ (sym lhs-π₁) (sym lhs-π₂)) ◁ θ-path ▷
              pbfα.pbIntro≡ (sym (C.⋆IdL _)) (sym (C.⋆IdL _))
      condPath : PathP (λ i → hPath i C.⋆ PullbackNotation.pbπ₁ (pb (C.⋆IdL f i) α) ≡ pbfα.pbπ₁)
                 _ _
      condPath = isProp→PathP (λ _ → C.isSetHom _ _) _ _
  CodomainFibration-lax .F-associativity {w = w} f g h =
    -- Claude
    makeNatTransPathP _ _ (λ i (a , α) → hPath (a , α) i , condPath (a , α) i)
    where
    module _ ((a , α) : ∫C (Slice C w) .Category.ob) where
      module pbf    = PullbackNotation (pb f α)
      module pbg    = PullbackNotation (pb g pbf.pbπ₁)
      module pbh    = PullbackNotation (pb h pbg.pbπ₁)
      module pbgf   = PullbackNotation (pb (g C.⋆ f) α)
      module pbhg   = PullbackNotation (pb (h C.⋆ g) pbf.pbπ₁)
      module pbH_gf = PullbackNotation (pb h pbgf.pbπ₁)
      module pbLHS  = PullbackNotation (pb (h C.⋆ (g C.⋆ f)) α)
      module pbRHS  = PullbackNotation (pb ((h C.⋆ g) C.⋆ f) α)

      commonπ₂ : C.Hom[ pbh.vert , a ]
      commonπ₂ = (pbh.pbπ₂ C.⋆ pbg.pbπ₂) C.⋆ pbf.pbπ₂

      finalProof : pbh.pbπ₁ C.⋆ ((h C.⋆ g) C.⋆ f) ≡ commonπ₂ C.⋆ α
      finalProof =
          sym (C.⋆Assoc _ _ _)
        ∙ C.⟨ sym (C.⋆Assoc _ _ _) ⟩⋆⟨ refl ⟩
        ∙ C.⟨ C.⟨ pbh.pbCommutes ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩
        ∙ C.⟨ C.⋆Assoc _ _ _ ⟩⋆⟨ refl ⟩
        ∙ C.⟨ C.⟨ refl ⟩⋆⟨ pbg.pbCommutes ⟩ ⟩⋆⟨ refl ⟩
        ∙ C.⟨ sym (C.⋆Assoc _ _ _) ⟩⋆⟨ refl ⟩
        ∙ C.⋆Assoc _ _ _
        ∙ C.⟨ refl ⟩⋆⟨ pbf.pbCommutes ⟩
        ∙ sym (C.⋆Assoc _ _ _)

      eq : (i : I) → pbh.pbπ₁ C.⋆ sym (C.⋆Assoc h g f) i ≡ commonπ₂ C.⋆ α
      eq i = (λ j → pbh.pbπ₁ C.⋆ sym (C.⋆Assoc h g f) (i ∨ j)) ∙ finalProof

      θ-path : PathP (λ i → C.Hom[ pbh.vert ,
                                   PullbackNotation.vert (pb (sym (C.⋆Assoc h g f) i) α) ])
                     (pbLHS.pbIntro pbh.pbπ₁ commonπ₂ (eq i0))
                     (pbRHS.pbIntro pbh.pbπ₁ commonπ₂ (eq i1))
      θ-path i = PullbackNotation.pbIntro
                   (pb (sym (C.⋆Assoc h g f) i) α) pbh.pbπ₁ commonπ₂ (eq i)

      LHSv : C.Hom[ pbh.vert , pbLHS.vert ]
      LHSv =
        ((ChangeBase C pb h .F-hom (ChangeBaseComp C pb f g .N-ob (a , α)) .fst)
         C.⋆ C.id)
        C.⋆ (ChangeBaseComp C pb (g C.⋆ f) h .N-ob (a , α) .fst)

      lhs-π₁ : LHSv C.⋆ pbLHS.pbπ₁ ≡ pbh.pbπ₁
      lhs-π₁ =
          C.⋆Assoc _ _ _
        ∙ C.⟨ refl ⟩⋆⟨ pbLHS.pbβ₁ ⟩
        ∙ C.⟨ C.⋆IdR _ ⟩⋆⟨ refl ⟩
        ∙ pbH_gf.pbβ₁

      lhs-π₂ : LHSv C.⋆ pbLHS.pbπ₂ ≡ commonπ₂
      lhs-π₂ =
          C.⋆Assoc _ _ _
        ∙ C.⟨ refl ⟩⋆⟨ pbLHS.pbβ₂ ⟩
        ∙ C.⟨ C.⋆IdR _ ⟩⋆⟨ refl ⟩
        ∙ sym (C.⋆Assoc _ _ _)
        ∙ C.⟨ pbH_gf.pbβ₂ ⟩⋆⟨ refl ⟩
        ∙ C.⋆Assoc _ _ _
        ∙ C.⟨ refl ⟩⋆⟨ pbgf.pbβ₂ ⟩
        ∙ sym (C.⋆Assoc _ _ _)

      RHSv : C.Hom[ pbh.vert , pbRHS.vert ]
      RHSv =
        (((ChangeBase C pb h ∘F ChangeBase C pb g)
              .F-hom (∫C (Slice C x) .Category.id) .fst)
          C.⋆ (ChangeBaseComp C pb g h .N-ob (pbf.vert , pbf.pbπ₁) .fst))
        C.⋆ (ChangeBaseComp C pb f (h C.⋆ g) .N-ob (a , α) .fst)
        where x = _

      rhs-π₁ : RHSv C.⋆ pbRHS.pbπ₁ ≡ pbh.pbπ₁
      rhs-π₁ =
          C.⋆Assoc _ _ _
        ∙ C.⟨ refl ⟩⋆⟨ pbRHS.pbβ₁ ⟩
        ∙ C.⋆Assoc _ _ _
        ∙ C.⟨ refl ⟩⋆⟨ pbhg.pbβ₁ ⟩
        ∙ pbh.pbβ₁

      rhs-π₂ : RHSv C.⋆ pbRHS.pbπ₂ ≡ commonπ₂
      rhs-π₂ =
          C.⋆Assoc _ _ _
        ∙ C.⟨ refl ⟩⋆⟨ pbRHS.pbβ₂ ⟩
        ∙ sym (C.⋆Assoc _ _ _)
        ∙ C.⟨ C.⋆Assoc _ _ _ ⟩⋆⟨ refl ⟩
        ∙ C.⟨ C.⟨ refl ⟩⋆⟨ pbhg.pbβ₂ ⟩ ⟩⋆⟨ refl ⟩
        ∙ C.⟨ sym (C.⋆Assoc _ _ _) ⟩⋆⟨ refl ⟩
        ∙ C.⟨ C.⟨ pbh.pbβ₂ ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩
        ∙ C.⟨ C.⋆Assoc _ _ _ ⟩⋆⟨ refl ⟩
        ∙ C.⟨ C.⟨ refl ⟩⋆⟨ pbg.pbβ₂ ⟩ ⟩⋆⟨ refl ⟩
        ∙ C.⟨ C.⟨ refl ⟩⋆⟨ C.⋆IdR _ ⟩ ⟩⋆⟨ refl ⟩

      hPath : PathP (λ i → C.Hom[ pbh.vert ,
                                  PullbackNotation.vert (pb (sym (C.⋆Assoc h g f) i) α) ])
                    LHSv RHSv
      hPath = sym (pbLHS.pbIntro≡ (sym lhs-π₁) (sym lhs-π₂)) ◁ θ-path ▷
              pbRHS.pbIntro≡ (sym rhs-π₁) (sym rhs-π₂)

      condPath : PathP (λ i → hPath i C.⋆ PullbackNotation.pbπ₁
                               (pb (sym (C.⋆Assoc h g f) i) α) ≡ pbh.pbπ₁)
                 _ _
      condPath = isProp→PathP (λ _ → C.isSetHom _ _) _ _

  private
    CodomainFibration-pseudo-F-id-iso : ∀ {x : C.ob}
      → isIso2Cell (CAT {ℓC = _} {ℓC' = _})
          {x = CodomainFibration-lax .F₀ x} {y = CodomainFibration-lax .F₀ x}
          (CodomainFibration-lax .F-id {x})
    CodomainFibration-pseudo-F-id-iso {x = x} .inv .N-ob (a , α) =
      pbId.pbπ₂ , sym pbId.pbCommutes ∙ C.⋆IdR _
      where module pbId = PullbackNotation (pb (C.id {x}) α)
    CodomainFibration-pseudo-F-id-iso {x = x} .inv .N-hom
      {x = a , α} {y = b , β} (h , h≡) =
      ΣPathP (pbIdβ.pbβ₂ , isProp→PathP (λ _ → C.isSetHom _ _) _ _)
      where
        module pbIdα = PullbackNotation (pb (C.id {x}) α)
        module pbIdβ = PullbackNotation (pb (C.id {x}) β)
    CodomainFibration-pseudo-F-id-iso {x = x} .sec =
      makeNatTransPath (funExt λ (a , α) →
        ΣPathP ( pbId.pbβ₂ , isProp→PathP (λ _ → C.isSetHom _ _) _ _))
      where module pbId {a} {α : C [ a , x ]} = PullbackNotation (pb (C.id {x}) α)
    CodomainFibration-pseudo-F-id-iso {x = x} .ret =
      makeNatTransPath (funExt λ (a , α) →
        ΣPathP ( pbId.pbExtensionality
                   ( C.⋆Assoc _ _ _
                   ∙ C.⟨ refl ⟩⋆⟨ pbId.pbβ₁ ⟩
                   ∙ sym pbId.pbCommutes
                   ∙ C.⋆IdR _
                   ∙ sym (C.⋆IdL _))
                   ( C.⋆Assoc _ _ _
                   ∙ C.⟨ refl ⟩⋆⟨ pbId.pbβ₂ ⟩
                   ∙ C.⋆IdR _
                   ∙ sym (C.⋆IdL _))
               , isProp→PathP (λ _ → C.isSetHom _ _) _ _))
      where module pbId {a} {α : C [ a , x ]} = PullbackNotation (pb (C.id {x}) α)

    CodomainFibration-pseudo-F-seq-iso : ∀ {x y z : C.ob}
      (f : C [ y , x ]) (g : C [ z , y ])
      → isIso2Cell (CAT {ℓC = _} {ℓC' = _})
          {x = CodomainFibration-lax .F₀ x} {y = CodomainFibration-lax .F₀ z}
          (CodomainFibration-lax .F-seq f g)
    CodomainFibration-pseudo-F-seq-iso f g .inv .N-ob (a , α) =
        pbg.pbIntro pbgf.pbπ₁
          (pbf.pbIntro (pbgf.pbπ₁ C.⋆ g) pbgf.pbπ₂
            (C.⋆Assoc _ _ _ ∙ pbgf.pbCommutes))
          (sym pbf.pbβ₁)
      , pbg.pbβ₁
      where module pbf = PullbackNotation (pb f α)
            module pbg = PullbackNotation (pb g pbf.pbπ₁)
            module pbgf = PullbackNotation (pb (g C.⋆ f) α)
    CodomainFibration-pseudo-F-seq-iso f g .inv .N-hom
      {x = a , α} {y = b , β} (h , h≡) =
      -- Claude
      ΣPathP ( pbg_β.pbExtensionality
        (  C.⋆Assoc _ _ _
         ∙ C.⟨ refl ⟩⋆⟨ pbg_β.pbβ₁ ⟩
         ∙ pbgf_β.pbβ₁
         ∙ sym pbg_α.pbβ₁
         ∙ C.⟨ refl ⟩⋆⟨ sym pbg_β.pbβ₁ ⟩
         ∙ sym (C.⋆Assoc _ _ _))
        (  C.⋆Assoc _ _ _
         ∙ C.⟨ refl ⟩⋆⟨ pbg_β.pbβ₂ ⟩
         ∙ pbf_β.pbExtensionality
             (  C.⋆Assoc _ _ _
              ∙ C.⟨ refl ⟩⋆⟨ pbf_β.pbβ₁ ⟩
              ∙ sym (C.⋆Assoc _ _ _)
              ∙ C.⟨ pbgf_β.pbβ₁ ⟩⋆⟨ refl ⟩
              ∙ sym pbf_α.pbβ₁
              ∙ C.⟨ refl ⟩⋆⟨ sym pbf_β.pbβ₁ ⟩
              ∙ sym (C.⋆Assoc _ _ _))
             (  C.⋆Assoc _ _ _
              ∙ C.⟨ refl ⟩⋆⟨ pbf_β.pbβ₂ ⟩
              ∙ pbgf_β.pbβ₂
              ∙ C.⟨ sym pbf_α.pbβ₂ ⟩⋆⟨ refl ⟩
              ∙ C.⋆Assoc _ _ _
              ∙ C.⟨ refl ⟩⋆⟨ sym pbf_β.pbβ₂ ⟩
              ∙ sym (C.⋆Assoc _ _ _))
         ∙ C.⟨ sym pbg_α.pbβ₂ ⟩⋆⟨ refl ⟩
         ∙ C.⋆Assoc _ _ _
         ∙ C.⟨ refl ⟩⋆⟨ sym pbg_β.pbβ₂ ⟩
         ∙ sym (C.⋆Assoc _ _ _))
      , isProp→PathP (λ _ → C.isSetHom _ _) _ _)
      where
        module pbf_α = PullbackNotation (pb f α)
        module pbf_β = PullbackNotation (pb f β)
        module pbg_α = PullbackNotation (pb g pbf_α.pbπ₁)
        module pbg_β = PullbackNotation (pb g pbf_β.pbπ₁)
        module pbgf_α = PullbackNotation (pb (g C.⋆ f) α)
        module pbgf_β = PullbackNotation (pb (g C.⋆ f) β)
    CodomainFibration-pseudo-F-seq-iso f g .sec =
      -- Claude
      makeNatTransPath (funExt λ (a , α) →
        let module pbf  = PullbackNotation (pb f α)
            module pbg  = PullbackNotation (pb g pbf.pbπ₁)
            module pbgf = PullbackNotation (pb (g C.⋆ f) α)
        in ΣPathP
          ( pbg.pbExtensionality
              ( C.⋆Assoc _ _ _
              ∙ C.⟨ refl ⟩⋆⟨ pbg.pbβ₁ ⟩
              ∙ pbgf.pbβ₁
              ∙ sym (C.⋆IdL _))
              ( C.⋆Assoc _ _ _
              ∙ C.⟨ refl ⟩⋆⟨ pbg.pbβ₂ ⟩
              ∙ pbf.pbExtensionality
                  ( C.⋆Assoc _ _ _
                  ∙ C.⟨ refl ⟩⋆⟨ pbf.pbβ₁ ⟩
                  ∙ sym (C.⋆Assoc _ _ _)
                  ∙ C.⟨ pbgf.pbβ₁ ⟩⋆⟨ refl ⟩
                  ∙ pbg.pbCommutes)
                  ( C.⋆Assoc _ _ _
                  ∙ C.⟨ refl ⟩⋆⟨ pbf.pbβ₂ ⟩
                  ∙ pbgf.pbβ₂)
              ∙ sym (C.⋆IdL _))
          , isProp→PathP (λ _ → C.isSetHom _ _) _ _))
    CodomainFibration-pseudo-F-seq-iso f g .ret =
      makeNatTransPath (funExt λ (a , α) →
        let module pbf  = PullbackNotation (pb f α)
            module pbg  = PullbackNotation (pb g pbf.pbπ₁)
            module pbgf = PullbackNotation (pb (g C.⋆ f) α)
        in ΣPathP
          ( pbgf.pbExtensionality
              ( C.⋆Assoc _ _ _
              ∙ C.⟨ refl ⟩⋆⟨ pbgf.pbβ₁ ⟩
              ∙ pbg.pbβ₁
              ∙ sym (C.⋆IdL _))
              ( C.⋆Assoc _ _ _
              ∙ C.⟨ refl ⟩⋆⟨ pbgf.pbβ₂ ⟩
              ∙ sym (C.⋆Assoc _ _ _)
              ∙ C.⟨ pbg.pbβ₂ ⟩⋆⟨ refl ⟩
              ∙ pbf.pbβ₂
              ∙ sym (C.⋆IdL _))
          , isProp→PathP (λ _ → C.isSetHom _ _) _ _))

  CodomainFibration-pseudo : isPseudo CodomainFibration-lax
  CodomainFibration-pseudo .F-id-iso {x} = CodomainFibration-pseudo-F-id-iso {x}
  CodomainFibration-pseudo .F-seq-iso f g = CodomainFibration-pseudo-F-seq-iso f g

  -- Splitting lax and pseudo into separate top-level definitions is needed to
  -- convince Agda that this definition is terminating (cf. SetsFibration).
  CodomainFibration : FibrationEq C _ _
  CodomainFibration .lax = CodomainFibration-lax
  CodomainFibration .pseudo = CodomainFibration-pseudo
