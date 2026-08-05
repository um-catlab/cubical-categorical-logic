{-

  Displayed and vertical models of a sketch: the sketch analogue of the
  displayed layer `Algᴰ`/`Homoᴰ` of `Cubical.Algebra.Theory`.

  `Cubical.Algebra.Sketch.Displayed` presents models of a sketch `S` in
  `E` as a `Categoryᴰ` over the carriers:

    Carrier = FAM 𝔼 (ind .ob)     (𝔼 = YonedaStrictify E)
    MODELᴰ  : Categoryᴰ Carrier _ _
    MODEL∫  = ∫C MODELᴰ

  This file displays that presentation once more.  Where `Theory.Algᴰ`
  takes a displayed carrier `Xᴰ : X → Type`, the sketch version must be
  told what "displayed" means in `E`, so the whole development is
  parameterised by a displayed category `Eᴰ` over `𝔼 S E`.  (Given
  `Dᴰ : Categoryᴰ E _ _` one obtains such an `Eᴰ` by reindexing along
  `fromStrict : Functor 𝔼 E`.)

  Contents:

    FAMᴰ         displayed families, `Categoryᴰ (FAM E I)`
    Carrierᴰ     `FAMᴰ Eᴰ (ind .ob)`, the displayed base
    ModelStrᴰ    a displayed action with FORDED displayed
                 functoriality, mirroring `Theory.Homoᴰ.op-homᴰ`
    toSectionᴰ   unfording: a displayed model structure is a `Section`
                 of `Eᴰ` along `toFunctorS B`
    isModelᴰ     the displayed model condition
    isNatFamᴰ    forded displayed naturality, the displayed homs
    MODELᴰᴰ      `Categoryᴰ (MODEL∫ S E) _ _`
    MODEL∫∫      `∫C MODELᴰᴰ`, the category of displayed models
    ∫Model       the total model, in `∫C Eᴰ`
    MODELⱽ       the fibre over a fixed base model (via the library's
                 generic `Fibers.v[_]`, not rebuilt here)
    isNatFamⱽ    `isNatFamᴰ` over the identity, as `Theory.Homoⱽ` is
                 `Theory.Homoᴰ` over `idHomo`

  DOES IT COME FOR FREE?

  The *structure* layer does: `isFunctorialActᴰ` and `isNatFamᴰ` are
  the mechanical forded lifts of their base counterparts, and the
  naturality component of every displayed law holds by
  `isPropIsNatFamᴰ`, so `NatFamᴰ≡` reduces each law to its carrier
  component.

  The *carrier* layer does not.  `MODELᴰ`'s three laws are `refl`
  because `𝔼`'s are; `MODELᴰᴰ`'s three laws are `Eᴰ`'s displayed laws
  and can only be `refl` when `Eᴰ` is itself strict.  Replacing
  `⋆IdLᴰ` below by `refl` fails with exactly one unsolved equation,

    Categoryᴰ.idᴰ MODELᴰᴰ .fst i Eᴰ.⋆ᴰ αᴰ i  =  αᴰ i

  i.e. `Eᴰ.⋆IdLᴰ`, and nothing else: the base path
  `⋆IdL (MODEL∫ S E) (α , ϕ)` is already `refl`.  So the fording
  bought at the first level is preserved exactly, and the residue is
  the ambient displayed category's own unit/associativity laws.  For
  the intended instances (`Eᴰ` a displayed category of families of
  sets, or any `StructureOver`) those are `refl` and everything is.

  NOT DONE.  There is no analogue of `Theory.reindexAlgᴰ` here.  That
  construction reindexes a displayed carrier `Yᴰ` along `f : X → Y` as
  `Yᴰ ∘ f`, which is free for families of types but for a general
  `Categoryᴰ` requires a *cartesian lift* of each `α i` at `Yᴰ i`.  A
  reindexing operation therefore has to assume `Eᴰ` is a fibration; it
  does not come for free from the displayed encoding.

-}
module Cubical.Algebra.Sketch.Vertical where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.TotalCategory

open import Cubical.Algebra.Sketch.Base
open import Cubical.Algebra.Sketch.Displayed

private
  variable
    ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' : Level
    ℓE ℓE' ℓEᴰ ℓEᴰ' ℓI : Level

open Category
open Functor

-- Families displayed over families: one displayed object of `Eᴰ` for
-- each element of `I`.  All three displayed laws are `Eᴰ`'s laws
-- componentwise, hence `refl` whenever `Eᴰ`'s are.
module _ {E : Category ℓE ℓE'} (Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ')
         (I : Type ℓI) where
  private module Eᴰ = Categoryᴰ Eᴰ

  FAMᴰ : Categoryᴰ (FAM E I) (ℓ-max ℓI ℓEᴰ) (ℓ-max ℓI ℓEᴰ')
  FAMᴰ .Categoryᴰ.ob[_] X = (i : I) → Eᴰ.ob[ X i ]
  FAMᴰ .Categoryᴰ.Hom[_][_,_] α Xᴰ Yᴰ =
    (i : I) → Eᴰ [ α i ][ Xᴰ i , Yᴰ i ]
  FAMᴰ .Categoryᴰ.idᴰ i = Eᴰ.idᴰ
  FAMᴰ .Categoryᴰ._⋆ᴰ_ fᴰ gᴰ i = fᴰ i Eᴰ.⋆ᴰ gᴰ i
  FAMᴰ .Categoryᴰ.⋆IdLᴰ fᴰ i j = Eᴰ.⋆IdLᴰ (fᴰ j) i
  FAMᴰ .Categoryᴰ.⋆IdRᴰ fᴰ i j = Eᴰ.⋆IdRᴰ (fᴰ j) i
  FAMᴰ .Categoryᴰ.⋆Assocᴰ fᴰ gᴰ hᴰ i j =
    Eᴰ.⋆Assocᴰ (fᴰ j) (gᴰ j) (hᴰ j) i
  FAMᴰ .Categoryᴰ.isSetHomᴰ = isSetΠ (λ _ → Eᴰ.isSetHomᴰ)

module _ (S : Sketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ')
         (E : Category ℓE ℓE')
         (Eᴰ : Categoryᴰ (𝔼 S E) ℓEᴰ ℓEᴰ') where
  open Sketch S
  private
    module Eᴰ = Categoryᴰ Eᴰ
    module R = HomᴰReasoning Eᴰ

  -- the displayed base: `Carrierᴰ.ob[ X ]` is `(i : ind .ob) → Eᴰ.ob[ X i ]`
  Carrierᴰ : Categoryᴰ (Carrier S E) _ _
  Carrierᴰ = FAMᴰ Eᴰ (ind .ob)

  ----------------------------------------------------------------
  -- displayed objects: the displayed model structure
  ----------------------------------------------------------------

  ActOnᴰ : {X : ind .ob → E .ob} (B : ModelStr S E X)
           (Xᴰ : (i : ind .ob) → Eᴰ.ob[ X i ]) → Type _
  ActOnᴰ B Xᴰ =
    {x y : ind .ob} (f : ind [ x , y ]) → Eᴰ [ B .fst f ][ Xᴰ x , Xᴰ y ]

  -- Displayed functoriality, forded over the *base* functoriality
  -- exactly as `Theory.Homoᴰ.op-homᴰ` is forded over
  -- `Theory.Homo.op-hom`: the base equation `e` is a parameter, and the
  -- displayed clause is a `PathP` over the base clause applied to `e`.
  isFunctorialActᴰ : {X : ind .ob → E .ob} (B : ModelStr S E X)
    {Xᴰ : (i : ind .ob) → Eᴰ.ob[ X i ]} → ActOnᴰ B Xᴰ → Type _
  isFunctorialActᴰ B actᴰ =
    ({x : ind .ob} (f : ind [ x , x ]) (e : ind .id ≡ f)
      → actᴰ f Eᴰ.≡[ B .snd .fst f e ] Eᴰ.idᴰ)
    × ({x y z : ind .ob} (f : ind [ x , y ]) (g : ind [ y , z ])
       (h : ind [ x , z ]) (e : f ⋆⟨ ind ⟩ g ≡ h)
      → actᴰ h Eᴰ.≡[ B .snd .snd f g h e ] (actᴰ f Eᴰ.⋆ᴰ actᴰ g))

  isPropIsFunctorialActᴰ : {X : ind .ob → E .ob} (B : ModelStr S E X)
    {Xᴰ : (i : ind .ob) → Eᴰ.ob[ X i ]} (actᴰ : ActOnᴰ B Xᴰ)
    → isProp (isFunctorialActᴰ B actᴰ)
  isPropIsFunctorialActᴰ B {Xᴰ} actᴰ =
    isProp×
      (isPropImplicitΠ (λ x → isPropΠ2 (λ _ _ →
        isOfHLevelPathP' 1 (Eᴰ.isSetHomᴰ {xᴰ = Xᴰ x} {yᴰ = Xᴰ x}) _ _)))
      (isPropImplicitΠ3 (λ x _ z → isPropΠ4 (λ _ _ _ _ →
        isOfHLevelPathP' 1 (Eᴰ.isSetHomᴰ {xᴰ = Xᴰ x} {yᴰ = Xᴰ z}) _ _)))

  ModelStrᴰ : {X : ind .ob → E .ob} (B : ModelStr S E X)
              (Xᴰ : (i : ind .ob) → Eᴰ.ob[ X i ]) → Type _
  ModelStrᴰ B Xᴰ = Σ[ actᴰ ∈ ActOnᴰ B Xᴰ ] isFunctorialActᴰ B actᴰ

  -- unfording: a displayed model structure is a *section* of `Eᴰ`
  -- along the functor `toFunctorS B`, i.e. a displayed functor out of
  -- `ind` (the exact analogue of `Algᴰ.∫`, which unfords a displayed
  -- algebra into an algebra on the total space).
  toSectionᴰ : {X : ind .ob → E .ob} (B : ModelStr S E X)
    {Xᴰ : (i : ind .ob) → Eᴰ.ob[ X i ]} (Bᴰ : ModelStrᴰ B Xᴰ)
    → Section (toFunctorS S E B) Eᴰ
  toSectionᴰ B {Xᴰ} Bᴰ .Section.F-obᴰ = Xᴰ
  toSectionᴰ B Bᴰ .Section.F-homᴰ = Bᴰ .fst
  toSectionᴰ B Bᴰ .Section.F-idᴰ = Bᴰ .snd .fst _ refl
  toSectionᴰ B Bᴰ .Section.F-seqᴰ f g = Bᴰ .snd .snd f g _ refl

  -- the total functor `ind → ∫C Eᴰ`
  ∫ModelStr : {X : ind .ob → E .ob} (B : ModelStr S E X)
    {Xᴰ : (i : ind .ob) → Eᴰ.ob[ X i ]} (Bᴰ : ModelStrᴰ B Xᴰ)
    → Functor ind (∫C Eᴰ)
  ∫ModelStr B Bᴰ = intro (toFunctorS S E B) (toSectionᴰ B Bᴰ)

  -- The displayed model condition.  The library has no `isLimConeᴰ`,
  -- so the condition is stated on the total category: a displayed
  -- model over a model `B` is a displayed structure whose *total*
  -- functor is itself a model of `S`, this time in `∫C Eᴰ`.  This is
  -- exactly the condition one wants for gluing/logical relations.
  isModelᴰ : {X : ind .ob → E .ob} (B : ModelStr S E X)
    {Xᴰ : (i : ind .ob) → Eᴰ.ob[ X i ]} (Bᴰ : ModelStrᴰ B Xᴰ) → Type _
  isModelᴰ B Bᴰ = isModel S (∫C Eᴰ) (∫ModelStr B Bᴰ)

  isPropIsModelᴰ : {X : ind .ob → E .ob} (B : ModelStr S E X)
    {Xᴰ : (i : ind .ob) → Eᴰ.ob[ X i ]} (Bᴰ : ModelStrᴰ B Xᴰ)
    → isProp (isModelᴰ B Bᴰ)
  isPropIsModelᴰ B Bᴰ = isPropIsModel S (∫C Eᴰ) (∫ModelStr B Bᴰ)

  -- displayed objects of `MODELᴰᴰ`, over a base object of `MODEL∫`
  ModelObᴰ : {X : ind .ob → E .ob} (B : ModelStr S E X)
    (Xᴰ : (i : ind .ob) → Eᴰ.ob[ X i ]) → Type _
  ModelObᴰ B Xᴰ = Σ[ Bᴰ ∈ ModelStrᴰ B Xᴰ ] isModelᴰ B Bᴰ

  ----------------------------------------------------------------
  -- displayed morphisms: forded displayed naturality
  ----------------------------------------------------------------

  module _ {X Y : ind .ob → E .ob}
           (α : Carrier S E [ X , Y ])
           (B : ModelStr S E X) (C : ModelStr S E Y)
           (ϕ : isNatFam S E α B C)
           (Xᴰ : (i : ind .ob) → Eᴰ.ob[ X i ])
           (Yᴰ : (i : ind .ob) → Eᴰ.ob[ Y i ])
           (Bᴰ : ModelStrᴰ B Xᴰ) (Cᴰ : ModelStrᴰ C Yᴰ)
           where
    private
      sq : {x y : ind .ob} (f : ind [ x , y ])
         → B .fst f ⋆⟨ 𝔼 S E ⟩ α y ≡ α x ⋆⟨ 𝔼 S E ⟩ C .fst f
      sq = natSquare S E {α = α} {B} {C} ϕ

    ActOnᴰHom : Type _
    ActOnᴰHom = (i : ind .ob) → Eᴰ [ α i ][ Xᴰ i , Yᴰ i ]

    -- The displayed naturality square, forded on the base exactly as
    -- `Theory.Homoᴰ.op-homᴰ` fords `Theory.Homo.op-hom`: the base
    -- witness `e` and its displayed lift `eᴰ` are parameters.
    isNatFamᴰ : ActOnᴰHom → Type _
    isNatFamᴰ αᴰ =
      {x y : ind .ob} (f : ind [ x , y ])
      (m : 𝔼 S E [ X x , Y y ]) (mᴰ : Eᴰ [ m ][ Xᴰ x , Yᴰ y ])
      (e : B .fst f ⋆⟨ 𝔼 S E ⟩ α y ≡ m)
      → (Bᴰ .fst f Eᴰ.⋆ᴰ αᴰ y) Eᴰ.≡[ e ] mᴰ
      → (αᴰ x Eᴰ.⋆ᴰ Cᴰ .fst f) Eᴰ.≡[ sym (sq f) ∙ e ] mᴰ

    isPropIsNatFamᴰ : (αᴰ : ActOnᴰHom) → isProp (isNatFamᴰ αᴰ)
    isPropIsNatFamᴰ αᴰ =
      isPropImplicitΠ2 (λ x y → isPropΠ4 (λ _ _ _ _ → isPropΠ (λ _ →
        isOfHLevelPathP' 1 (Eᴰ.isSetHomᴰ {xᴰ = Xᴰ x} {yᴰ = Yᴰ y}) _ _)))

    -- unfording: an honest displayed square over `natSquare`
    natSquareᴰ : (αᴰ : ActOnᴰHom) → isNatFamᴰ αᴰ
      → {x y : ind .ob} (f : ind [ x , y ])
      → (Bᴰ .fst f Eᴰ.⋆ᴰ αᴰ y) Eᴰ.≡[ sq f ] (αᴰ x Eᴰ.⋆ᴰ Cᴰ .fst f)
    natSquareᴰ αᴰ ϕᴰ f = R.rectify (symP (ϕᴰ f _ _ refl refl))

    -- the displayed hom-set of `MODELᴰᴰ`
    NatFamᴰ : Type _
    NatFamᴰ = Σ[ αᴰ ∈ ActOnᴰHom ] isNatFamᴰ αᴰ

    NatFamᴰ≡ : {u v : NatFamᴰ} → u .fst ≡ v .fst → u ≡ v
    NatFamᴰ≡ = ΣPathPProp isPropIsNatFamᴰ

    isSetNatFamᴰ : isSet NatFamᴰ
    isSetNatFamᴰ =
      isSetΣ (isSetΠ (λ _ → Eᴰ.isSetHomᴰ))
             (λ αᴰ → isProp→isSet (isPropIsNatFamᴰ αᴰ))

  private
    idNatFamᴰ : {X : ind .ob → E .ob} (B : ModelStr S E X)
      (ϕ : isNatFam S E (Carrier S E .id) B B)
      (Xᴰ : (i : ind .ob) → Eᴰ.ob[ X i ]) (Bᴰ : ModelStrᴰ B Xᴰ)
      → isNatFamᴰ (Carrier S E .id) B B ϕ Xᴰ Xᴰ Bᴰ Bᴰ (λ _ → Eᴰ.idᴰ)
    idNatFamᴰ B ϕ Xᴰ Bᴰ f m mᴰ e eᴰ =
      R.rectify (R.≡out (R.⋆IdL _ ∙ sym (R.⋆IdR _) ∙ R.≡in eᴰ))

    seqNatFamᴰ : {X Y Z : ind .ob → E .ob}
      (α : Carrier S E [ X , Y ]) (β : Carrier S E [ Y , Z ])
      (B : ModelStr S E X) (C : ModelStr S E Y) (D : ModelStr S E Z)
      (ϕ : isNatFam S E α B C) (ψ : isNatFam S E β C D)
      (χ : isNatFam S E (α ⋆⟨ Carrier S E ⟩ β) B D)
      (Xᴰ : (i : ind .ob) → Eᴰ.ob[ X i ])
      (Yᴰ : (i : ind .ob) → Eᴰ.ob[ Y i ])
      (Zᴰ : (i : ind .ob) → Eᴰ.ob[ Z i ])
      (Bᴰ : ModelStrᴰ B Xᴰ) (Cᴰ : ModelStrᴰ C Yᴰ) (Dᴰ : ModelStrᴰ D Zᴰ)
      (αᴰ : (i : ind .ob) → Eᴰ [ α i ][ Xᴰ i , Yᴰ i ])
      (βᴰ : (i : ind .ob) → Eᴰ [ β i ][ Yᴰ i , Zᴰ i ])
      → isNatFamᴰ α B C ϕ Xᴰ Yᴰ Bᴰ Cᴰ αᴰ
      → isNatFamᴰ β C D ψ Yᴰ Zᴰ Cᴰ Dᴰ βᴰ
      → isNatFamᴰ (α ⋆⟨ Carrier S E ⟩ β) B D χ Xᴰ Zᴰ Bᴰ Dᴰ
          (λ i → αᴰ i Eᴰ.⋆ᴰ βᴰ i)
    seqNatFamᴰ α β B C D ϕ ψ χ Xᴰ Yᴰ Zᴰ Bᴰ Cᴰ Dᴰ αᴰ βᴰ ϕᴰ ψᴰ f m mᴰ e eᴰ =
      R.rectify (R.≡out
        ( R.⋆Assoc _ _ _
        ∙ R.⟨ refl ⟩⋆⟨ R.≡in (ψᴰ f _ _ refl refl) ⟩
        ∙ sym (R.⋆Assoc _ _ _)
        ∙ R.⟨ R.≡in (ϕᴰ f _ _ refl refl) ⟩⋆⟨ refl ⟩
        ∙ R.⋆Assoc _ _ _
        ∙ R.≡in eᴰ))

  ----------------------------------------------------------------
  -- the displayed category of displayed models
  ----------------------------------------------------------------

  -- `MODELᴰᴰ` is displayed over `MODEL∫ = ∫C MODELᴰ`: over a model
  -- `(X , B , m)` it has the displayed carriers together with a
  -- displayed model structure, and over a homomorphism `(α , ϕ)` it has
  -- the displayed families together with the forded displayed
  -- naturality.
  MODELᴰᴰ : Categoryᴰ (MODEL∫ S E) _ _
  MODELᴰᴰ .Categoryᴰ.ob[_] (X , Bm) =
    Σ[ Xᴰ ∈ ((i : ind .ob) → Eᴰ.ob[ X i ]) ] ModelObᴰ (Bm .fst) Xᴰ
  MODELᴰᴰ .Categoryᴰ.Hom[_][_,_]
    {x = X , Bm} {y = Y , Cm} (α , ϕ) (Xᴰ , Bmᴰ) (Yᴰ , Cmᴰ) =
    NatFamᴰ α (Bm .fst) (Cm .fst) ϕ Xᴰ Yᴰ (Bmᴰ .fst) (Cmᴰ .fst)
  MODELᴰᴰ .Categoryᴰ.idᴰ {x = X , Bm} {p = Xᴰ , Bmᴰ} =
    (λ _ → Eᴰ.idᴰ)
    , idNatFamᴰ (Bm .fst)
        (MODELᴰ S E .Categoryᴰ.idᴰ {x = X} {p = Bm}) Xᴰ (Bmᴰ .fst)
  MODELᴰᴰ .Categoryᴰ._⋆ᴰ_
    {x = X , Bm} {y = Y , Cm} {z = Z , Dm} {f = α , ϕ} {g = β , ψ}
    {xᴰ = Xᴰ , Bmᴰ} {yᴰ = Yᴰ , Cmᴰ} {zᴰ = Zᴰ , Dmᴰ}
    (αᴰ , ϕᴰ) (βᴰ , ψᴰ) =
    (λ i → αᴰ i Eᴰ.⋆ᴰ βᴰ i)
    , seqNatFamᴰ α β (Bm .fst) (Cm .fst) (Dm .fst) ϕ ψ
        (MODELᴰ S E .Categoryᴰ._⋆ᴰ_
          {x = X} {y = Y} {z = Z} {f = α} {g = β}
          {xᴰ = Bm} {yᴰ = Cm} {zᴰ = Dm} ϕ ψ)
        Xᴰ Yᴰ Zᴰ (Bmᴰ .fst) (Cmᴰ .fst) (Dmᴰ .fst) αᴰ βᴰ ϕᴰ ψᴰ
  MODELᴰᴰ .Categoryᴰ.⋆IdLᴰ
    {x = X , Bm} {y = Y , Cm} {f = α , ϕ}
    {xᴰ = Xᴰ , Bmᴰ} {yᴰ = Yᴰ , Cmᴰ} (αᴰ , ϕᴰ) =
    NatFamᴰ≡ α (Bm .fst) (Cm .fst) ϕ Xᴰ Yᴰ (Bmᴰ .fst) (Cmᴰ .fst)
      (Carrierᴰ .Categoryᴰ.⋆IdLᴰ αᴰ)
  MODELᴰᴰ .Categoryᴰ.⋆IdRᴰ
    {x = X , Bm} {y = Y , Cm} {f = α , ϕ}
    {xᴰ = Xᴰ , Bmᴰ} {yᴰ = Yᴰ , Cmᴰ} (αᴰ , ϕᴰ) =
    NatFamᴰ≡ α (Bm .fst) (Cm .fst) ϕ Xᴰ Yᴰ (Bmᴰ .fst) (Cmᴰ .fst)
      (Carrierᴰ .Categoryᴰ.⋆IdRᴰ αᴰ)
  MODELᴰᴰ .Categoryᴰ.⋆Assocᴰ
    {x = X , Bm} {y = Y , Cm} {z = Z , Dm} {w = W , Gm}
    {f = α , ϕ} {g = β , ψ} {h = γ , χ}
    {xᴰ = Xᴰ , Bmᴰ} {yᴰ = Yᴰ , Cmᴰ} {zᴰ = Zᴰ , Dmᴰ} {wᴰ = Wᴰ , Gmᴰ}
    (αᴰ , ϕᴰ) (βᴰ , ψᴰ) (γᴰ , χᴰ) =
    NatFamᴰ≡ (α ⋆⟨ Carrier S E ⟩ (β ⋆⟨ Carrier S E ⟩ γ))
      (Bm .fst) (Gm .fst) αβγ Xᴰ Wᴰ (Bmᴰ .fst) (Gmᴰ .fst)
      (Carrierᴰ .Categoryᴰ.⋆Assocᴰ αᴰ βᴰ γᴰ)
    where
    βγ : isNatFam S E (β ⋆⟨ Carrier S E ⟩ γ) (Cm .fst) (Gm .fst)
    βγ = MODELᴰ S E .Categoryᴰ._⋆ᴰ_ {x = Y} {y = Z} {z = W}
           {f = β} {g = γ} {xᴰ = Cm} {yᴰ = Dm} {zᴰ = Gm} ψ χ

    αβγ : isNatFam S E (α ⋆⟨ Carrier S E ⟩ (β ⋆⟨ Carrier S E ⟩ γ))
            (Bm .fst) (Gm .fst)
    αβγ = MODELᴰ S E .Categoryᴰ._⋆ᴰ_ {x = X} {y = Y} {z = W}
            {f = α} {g = β ⋆⟨ Carrier S E ⟩ γ}
            {xᴰ = Bm} {yᴰ = Cm} {zᴰ = Gm} ϕ βγ
  MODELᴰᴰ .Categoryᴰ.isSetHomᴰ
    {x = X , Bm} {y = Y , Cm} {f = α , ϕ}
    {xᴰ = Xᴰ , Bmᴰ} {yᴰ = Yᴰ , Cmᴰ} =
    isSetNatFamᴰ α (Bm .fst) (Cm .fst) ϕ Xᴰ Yᴰ (Bmᴰ .fst) (Cmᴰ .fst)

  -- the total category: displayed models of `S` in `Eᴰ`
  MODEL∫∫ : Category _ _
  MODEL∫∫ = ∫C MODELᴰᴰ

  -- projection back to the base models
  ForgetToBase : Functor MODEL∫∫ (MODEL∫ S E)
  ForgetToBase = Fst

  -- the analogue of `Theory.Algᴰ.∫`: a displayed model has a total
  -- model, this time in `∫C Eᴰ`
  ∫Model : MODEL∫∫ .ob → Model S (∫C Eᴰ)
  ∫Model (M , Mᴰ) =
    ∫ModelStr (M .snd .fst) (Mᴰ .snd .fst) , Mᴰ .snd .snd

  ----------------------------------------------------------------
  -- vertical models
  ----------------------------------------------------------------

  -- The fibre of `MODELᴰᴰ` over a fixed base model `M`: displayed
  -- models over `M`, and displayed homomorphisms over the identity.
  -- We reuse the library's generic fibre construction rather than
  -- rebuilding it.
  MODELⱽ : (M : MODEL∫ S E .ob) → Category _ _
  MODELⱽ = Fibers.v[_] MODELᴰᴰ

  Modelⱽ : (M : MODEL∫ S E .ob) → Type _
  Modelⱽ M = MODELⱽ M .ob

  -- Vertical homomorphisms are `isNatFamᴰ` over the identity, exactly
  -- as `Theory.Homoⱽ fᴰ Bᴰ Bᴰ' = Theory.Homoᴰ fᴰ idHomo Bᴰ Bᴰ'`.
  isNatFamⱽ : {X : ind .ob → E .ob} (B : ModelStr S E X)
    (ϕ : isNatFam S E (Carrier S E .id) B B)
    (Xᴰ Yᴰ : (i : ind .ob) → Eᴰ.ob[ X i ])
    (Bᴰ : ModelStrᴰ B Xᴰ) (Cᴰ : ModelStrᴰ B Yᴰ)
    (αᴰ : (i : ind .ob) → Eᴰ [ Carrier S E .id {x = X} i ][ Xᴰ i , Yᴰ i ])
    → Type _
  isNatFamⱽ {X} B ϕ Xᴰ Yᴰ Bᴰ Cᴰ αᴰ =
    isNatFamᴰ (Carrier S E .id {x = X}) B B ϕ Xᴰ Yᴰ Bᴰ Cᴰ αᴰ
