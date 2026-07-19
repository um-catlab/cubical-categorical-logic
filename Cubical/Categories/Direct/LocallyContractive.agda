{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Direct.LocallyContractive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor using (Functor ; _∘F_)
import Cubical.Categories.Presheaf.Family.Base as FamBase
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Constructions.BinProduct using (_×Psh_)
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.StrictHom.CartesianClosed
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.StrictDownset
open import Cubical.Categories.Displayed.Instances.Algebras.Recursive

open Functor
open PshHomStrict

private
  variable
    ℓ ℓ' ℓD : Level

module _ {C : Category ℓ ℓ'} {Wo : WFOrder ℓD ℓ'}
         (dir : DirectStr {C = C} Wo) where
  open Category C using (ob ; id ; _⋆_ ; ⋆IdL)
  open DirectNotation dir using (_≺_)

  private
    ℓ▷ : Level
    ℓ▷ = ℓ-max ℓ ℓ'

    infixr 5 _⇒_
    _⇒_ : Presheaf C ℓ▷ → Presheaf C ℓ▷ → Presheaf C ℓ▷
    X ⇒ Y = X ⇒PshLargeStrict Y

  ▷HomActionPsh : (Presheaf C ℓ▷ → Presheaf C ℓ▷) → Type _
  ▷HomActionPsh F₀ =
    {X Y : Presheaf C ℓ▷} → PshHomStrict (▷ dir .F-ob (X ⇒ Y)) (F₀ X ⇒ F₀ Y)

  private
    nm : {X Y : Presheaf C ℓ▷} (h : PshHomStrict X Y) (y : ob)
       → ⟨ (X ⇒ Y) .F-ob y ⟩
    nm h y .N-ob d (f , ξ) = h .N-ob d ξ
    nm h y .N-hom d' d g (f' , ξ') (f , ξ) e =
      h .N-hom d' d g ξ' ξ (cong snd e)

  -- the transpose of h as a global element of ▷ (X ⇒ Y)
  ▷transpose : {X Y : Presheaf C ℓ▷} (h : PshHomStrict X Y)
        → PshHomStrict UnitPsh (▷ dir .F-ob (X ⇒ Y))
  ▷transpose h .N-ob x _ =
    pshhom (λ y _ → nm h y) (λ y' y g p' p e → makePshHomStrictPath refl)
  ▷transpose h .N-hom x' x f _ _ _ = makePshHomStrictPath refl

  -- F's hom-action factors through next, via Fδ
  isContractiveHomAction :
    (F : Functor (PRESHEAF C ℓ▷) (PRESHEAF C ℓ▷))
    → ▷HomActionPsh (F .F-ob) → Type _
  isContractiveHomAction F Fδ =
    {X Y : Presheaf C ℓ▷} (h : PshHomStrict X Y)
    → F .F-hom h ≡ eltPshHomStrict (▷transpose h ⋆PshHomStrict Fδ {X} {Y})

  LocallyContractive : Type _
  LocallyContractive =
    Σ[ F ∈ Functor (PRESHEAF C ℓ▷) (PRESHEAF C ℓ▷) ]
    Σ[ Fδ ∈ ▷HomActionPsh (F .F-ob) ]
      isContractiveHomAction F Fδ

  Fam : Category _ _
  Fam = FamBase.Fam {ℓ = ℓ'} C

  module HyloPsh (F : LocallyContractive)
                 (X B : Presheaf C ℓ▷)
                 (c : PshHomStrict X (F .fst .F-ob X))
                 (a : PshHomStrict (F .fst .F-ob B) B)
                 where
    private
      F₀ = F .fst .F-ob
      Fδ = F .snd .fst
      Fhom≡ = F .snd .snd

    hyloBody : PshHomStrict ((▷ dir .F-ob (X ⇒ B)) ×Psh X) B
    hyloBody =
      (Fδ {X} {B} ×PshHomStrict c)
        ⋆PshHomStrict appPshHomStrict (F₀ X) (F₀ B)
        ⋆PshHomStrict a

    hyloStep : PshHomStrict (▷ dir .F-ob (X ⇒ B)) (X ⇒ B)
    hyloStep = λPshHomStrict X B hyloBody

    hyloTranspose : PshHomStrict UnitPsh (X ⇒ B)
    hyloTranspose = löb dir (X ⇒ B) hyloStep

    private
      hyloMap : PshHomStrict X B
      hyloMap =
        ×PshIntroStrict (UnitPsh-introStrict ⋆PshHomStrict hyloTranspose)
          idPshHomStrict
          ⋆PshHomStrict appPshHomStrict X B

    hyloTranspose-fix :
      hyloTranspose
      ≡ (hyloTranspose ⋆PshHomStrict next dir (X ⇒ B)) ⋆PshHomStrict hyloStep
    hyloTranspose-fix = löb-fix dir (X ⇒ B) hyloStep

    hyloTranspose-uniq :
      (s : PshHomStrict UnitPsh (X ⇒ B))
      → s ≡ (s ⋆PshHomStrict next dir (X ⇒ B)) ⋆PshHomStrict hyloStep
      → s ≡ hyloTranspose
    hyloTranspose-uniq = löb-uniq dir (X ⇒ B) hyloStep

    hylo : Hylo (F .fst) (X , c) (B , a)
    hylo .fst = hyloMap
    hylo .snd = makePshHomStrictPath (funExt λ x → funExt λ p →
      cong (λ s → s .N-ob x tt .N-ob x (id , p)) hyloTranspose-fix
      ∙ cong (λ z → a .N-ob x (Fδ .N-ob x z .N-ob x (id , c .N-ob x p)))
          (funExt⁻ (▷ dir .F-ob (X ⇒ B) .F-id)
             (next dir (X ⇒ B) .N-ob x (hyloTranspose .N-ob x tt))
           ∙ nextT≡▷transpose x)
      ∙ cong (λ φ → a .N-ob x (φ .N-ob x (c .N-ob x p)))
          (sym (Fhom≡ hyloMap)))
      where
      nextT≡▷transpose : ∀ x →
        next dir (X ⇒ B) .N-ob x (hyloTranspose .N-ob x tt)
          ≡ ▷transpose hyloMap .N-ob x tt
      nextT≡▷transpose x = makePshHomStrictPath (funExt λ y → funExt λ (g , q) →
        makePshHomStrictPath (funExt λ d → funExt λ (f , ξ) →
          sym (cong (λ m → hyloTranspose .N-ob x tt .N-ob d (m , ξ))
                 (⋆IdL (f ⋆ g)))
          ∙ cong (λ α → α .N-ob d (id , ξ))
              (hyloTranspose .N-hom d x (f ⋆ g) tt tt refl)))

  _⇒Fam_ : Category.ob Fam → Category.ob Fam → Category.ob Fam
  (A ⇒Fam B) x = (⟨ A x ⟩ → ⟨ B x ⟩) , isSet→ (B x .snd)

  ▷HomActionFam : Functor Fam Fam → Type _
  ▷HomActionFam H =
    {A B : Category.ob Fam}
    → Fam [ ▷Fam dir {ℓF = ℓ-zero} (A ⇒Fam B)
          , (H .F-ob A ⇒Fam H .F-ob B) ]

  -- apply a later function-family at a strict bound
  ▷app : {A B : Category.ob Fam} {x y : ob}
       → ⟨ ▷Fam dir {ℓF = ℓ-zero} (A ⇒Fam B) x ⟩
       → C [ y , x ] → y ≺ x → ⟨ A y ⟩ → ⟨ B y ⟩
  ▷app β g q = β .N-ob _ (g , q) _ id

  -- ▷ preserves the pointwise product laxly
  ▷× : {P Q : Presheaf C ℓ▷}
     → PshHomStrict (▷ dir .F-ob P ×Psh ▷ dir .F-ob Q)
                    (▷ dir .F-ob (P ×Psh Q))
  ▷× .N-ob x (α , β) = ×PshIntroStrict α β
  ▷× .N-hom x x' f (α' , β') (α , β) e =
    makePshHomStrictPath refl
    ∙ (λ i → ×PshIntroStrict (cong fst e i) (cong snd e i))

  -- H's hom-action factors through nextFam, via Hδ
  isContractiveHomActionFam :
    (H : Functor Fam Fam) → ▷HomActionFam H → Type _
  isContractiveHomActionFam H Hδ =
    {A B : Category.ob Fam} (h : Fam [ A , B ]) (x : ob)
    → H .F-hom h x
      ≡ Hδ {A} {B} x (nextFam dir {ℓF = ℓ-zero} (A ⇒Fam B) h x)

  LocallyContractiveFam : Type _
  LocallyContractiveFam =
    Σ[ H ∈ Functor Fam Fam ]
    Σ[ Hδ ∈ ▷HomActionFam H ]
      isContractiveHomActionFam H Hδ

  module HyloFam (H : LocallyContractiveFam)
                 (X B : Category.ob Fam)
                 (c : Fam [ X , H .fst .F-ob X ])
                 (a : Fam [ H .fst .F-ob B , B ])
                 where
    private
      Hδ = H .snd .fst
      Hhom≡ = H .snd .snd

      hyloStep : ∀ x → ⟨ ▷Fam dir {ℓF = ℓ-zero} (X ⇒Fam B) x ⟩
               → ⟨ (X ⇒Fam B) x ⟩
      hyloStep x β ξ = a x (Hδ {X} {B} x β (c x ξ))

    private
      hyloMap : Fam [ X , B ]
      hyloMap = löbFam dir {ℓF = ℓ-zero} (X ⇒Fam B) hyloStep

    hylo : Hylo (H .fst) (X , c) (B , a)
    hylo .fst = hyloMap
    hylo .snd = funExt λ x →
      löbFam-unfold dir {ℓF = ℓ-zero} (X ⇒Fam B) hyloStep x
      ∙ cong (λ k → λ ξ → a x (k (c x ξ)))
          (sym (Hhom≡ {X} {B} hyloMap x))

    hylo-unfold : ∀ x ξ
      → hylo .fst x ξ ≡ a x (H .fst .F-hom {X} {B} (hylo .fst) x (c x ξ))
    hylo-unfold x ξ = funExt⁻ (funExt⁻ (hylo .snd) x) ξ

    hylo-uniq : (h : Hylo (H .fst) (X , c) (B , a)) → h ≡ hylo
    hylo-uniq (h , he) = ΣPathP (mapEq , path2)
      where
        mapEq : h ≡ hyloMap
        mapEq =
          löbFam-uniq-unfold dir {ℓF = ℓ-zero} (X ⇒Fam B) hyloStep h
            λ x → funExt⁻ he x
                  ∙ (λ i ξ → a x (Hhom≡ {X} {B} h x i (c x ξ)))

        path2 : PathP
          (λ i → mapEq i
                 ≡ (λ x ξ → a x (H .fst .F-hom (mapEq i) x (c x ξ))))
          he (hylo .snd)
        path2 = isProp→PathP
          (λ i → isSetΠ (λ x → isSet→ (B x .snd))
                   (mapEq i)
                   (λ x ξ → a x (H .fst .F-hom (mapEq i) x (c x ξ))))
          he (hylo .snd)

    hylo-uniq-unfold : (h : Fam [ X , B ])
      → (∀ x ξ → h x ξ ≡ a x (H .fst .F-hom {X} {B} h x (c x ξ)))
      → ∀ x ξ → h x ξ ≡ hylo .fst x ξ
    hylo-uniq-unfold h he x ξ =
      funExt⁻
        (funExt⁻ (cong fst (hylo-uniq (h , funExt λ y → funExt (he y)))) x) ξ

  -- local contractivity makes the hylomorphism profunctor trivial;
  -- recursiveness and corecursiveness are its curried readings, and
  -- finality/initiality at a fixed point follow from FixpointRecursion
  module Recursiveness (H : LocallyContractiveFam) where
    hyloTrivial : HYLOTrivial (H .fst)
    hyloTrivial (X , c) (B , a) = HF.hylo , λ h → sym (HF.hylo-uniq h)
      where module HF = HyloFam H X B c a

    recursive : ∀ Xc → isRecursiveCoalgebra (H .fst) Xc
    recursive = HYLOTrivial→recursive (H .fst) hyloTrivial

    corecursive : ∀ Ba → isCorecursiveAlgebra (H .fst) Ba
    corecursive = HYLOTrivial→corecursive (H .fst) hyloTrivial
