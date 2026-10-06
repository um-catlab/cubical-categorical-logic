{-# OPTIONS --lossy-unification #-}
-- For any category C, the power category `Cᴬ = C^A = PowerCategory A C`
-- is naturally enriched over `Setᴬ = Set^A = PowerCategory A (SET _)` with
-- its cartesian monoidal structure.  Hom-object at (F, G) is the pointwise
-- family of hom-sets: `VE[F, G] a = Hom_C (F a, G a)`.
module Cubical.Categories.Enriched.Enrichment.Instances.Power where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Power
open import Cubical.Categories.Monoidal.Base hiding (MonoidalStr)
open import Cubical.Categories.Monoidal.Cartesian using (cartesianMonoidalStr)
open import Cubical.Categories.Limits.Terminal
  using (Terminal)
open import Cubical.Categories.Limits.BinProduct
  using (BinProducts; BinProduct; isBinProduct)
open import Cubical.Categories.Enriched.Enrichment.Base
  renaming (Enrichment to VE)
open import Cubical.Categories.Enriched.Enrichment.BaseChange.Base

open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.Family.Base
open import Cubical.Categories.Adjoint
  using (module UnitCounit; module NaturalBijection; adj→adj')

private variable ℓ ℓ' ℓA ℓC ℓC' : Level

module _ (A : Type ℓA) where

  -- Setᴬ as a monoidal category (cartesian).
  Setᴬ : (ℓ : Level) → Category (ℓ-max ℓA (ℓ-suc ℓ)) (ℓ-max ℓA ℓ)
  Setᴬ ℓ = PowerCategory A (SET ℓ)

  -- `Setᴬ-term` uses `(Lift Unit, isOfHLevelLift 2 isSetUnit)` so that it
  -- matches `PSH→Fam 𝟙` definitionally (`PSH→Fam 𝟙 .F-ob = LiftF ∘ UnitPsh`
  -- unfolds to the same hSet).  This lets us read off `Cofree-pres` from
  -- the hom-adjunction `adj→adj' CofreeFamAdj` without transport.
  Setᴬ-term : (ℓ : Level) → Terminal (Setᴬ ℓ)
  Setᴬ-term ℓ .fst = λ _ → Lift ℓ Unit , isOfHLevelLift 2 isSetUnit
  Setᴬ-term ℓ .snd Y = (λ _ _ → lift tt) , (λ ! → funExt λ _ → funExt λ _ → refl)

  -- TODO this should follow from abstract nonsense
  -- In _particular_ it should follow from Sets being cartesianmonoidal.
  Setᴬ-bp : (ℓ : Level) → BinProducts (Setᴬ ℓ)
  Setᴬ-bp ℓ F G .BinProduct.binProdOb a =
    F a .fst × G a .fst , isSet× (F a .snd) (G a .snd)
  Setᴬ-bp ℓ F G .BinProduct.binProdPr₁ a x = x .fst
  Setᴬ-bp ℓ F G .BinProduct.binProdPr₂ a x = x .snd
  Setᴬ-bp ℓ F G .BinProduct.univProp {z = Z} f g =
    ((λ a z → f a z , g a z) , refl , refl) ,
    λ (h , h⋆π₁≡f , h⋆π₂≡g) →
      Σ≡Prop (λ _ → isProp× (isSetΠ (λ a → isSet→ (F a .snd)) _ _)
                            (isSetΠ (λ a → isSet→ (G a .snd)) _ _))
        (funExt λ a → funExt λ z i →
          h⋆π₁≡f (~ i) a z , h⋆π₂≡g (~ i) a z)

  Setᴬ-Mon : (ℓ : Level) → MonoidalCategory (ℓ-max ℓA (ℓ-suc ℓ)) (ℓ-max ℓA ℓ)
  Setᴬ-Mon ℓ .MonoidalCategory.C = Setᴬ ℓ
  Setᴬ-Mon ℓ .MonoidalCategory.monstr =
    cartesianMonoidalStr (Setᴬ ℓ) (Setᴬ-bp ℓ) (Setᴬ-term ℓ)

  -- The Set^A-enrichment of C^A
  --   VE[F, G] a = Hom_C (F a, G a)
  --   id, seq inherited pointwise from C
  --   ⇄-agree : Hom_{Cᴬ}(F,G) = ∀ a, Hom_C(F a, G a) ↔ ∀ a, Unit → Hom_C(F a, G a)

  module _ (C : Category ℓC ℓC') (ℓ⁺ : Level) where
    private
      module C = Category C
      -- Level of hom-sets of Set^A into which we enrich.  The `ℓ⁺` is an
      -- extra Lift level so consumers can adjust the ambient Set^A level.
      ℓSetᴬ = ℓ-max ℓC' ℓ⁺

    Cᴬ-Enrichment : VE (PowerCategory A C) (Setᴬ-Mon ℓSetᴬ)
    Cᴬ-Enrichment .VE.VE[_,_] F G a =
      Lift ℓ⁺ C.Hom[ F a , G a ] , isOfHLevelLift 2 C.isSetHom
    Cᴬ-Enrichment .VE.id {F} a _ = lift C.id
    Cᴬ-Enrichment .VE.seq F G H a fg = lift (fg .fst .lower C.⋆ fg .snd .lower)
    Cᴬ-Enrichment .VE.⇄-agree {F}{G} .Iso.fun h a _ = lift (h a)
    Cᴬ-Enrichment .VE.⇄-agree .Iso.inv k a = k a _ .lower
    Cᴬ-Enrichment .VE.⇄-agree .Iso.sec k = funExt λ _ → funExt λ _ → refl
    Cᴬ-Enrichment .VE.⇄-agree .Iso.ret _ = refl
    Cᴬ-Enrichment .VE.⋆IdL F G =
      funExt λ a → funExt λ _ → cong lift (sym (C.⋆IdL _))
    Cᴬ-Enrichment .VE.⋆IdR F G =
      funExt λ a → funExt λ _ → cong lift (sym (C.⋆IdR _))
    Cᴬ-Enrichment .VE.⋆Assoc F G H K =
      funExt λ a → funExt λ _ → cong lift (C.⋆Assoc _ _ _)
    Cᴬ-Enrichment .VE.⌜id⌝ = refl
    Cᴬ-Enrichment .VE.⌜⋆⌝ f g = refl


  Setᴬ-self : (ℓ : Level) → VE (Setᴬ ℓ) (Setᴬ-Mon ℓ)
  Setᴬ-self ℓ .VE.VE[_,_] F G a = (F a .fst → G a .fst) , isSet→ (G a .snd)
  Setᴬ-self ℓ .VE.id a _ x = x
  Setᴬ-self ℓ .VE.seq F G H a fg x = fg .snd (fg .fst x)
  Setᴬ-self ℓ .VE.⇄-agree .Iso.fun h a _ = h a
  Setᴬ-self ℓ .VE.⇄-agree .Iso.inv k a = k a (lift tt)
  Setᴬ-self ℓ .VE.⇄-agree .Iso.sec k = funExt λ _ → funExt λ _ → refl
  Setᴬ-self ℓ .VE.⇄-agree .Iso.ret _ = refl
  Setᴬ-self ℓ .VE.⋆IdL F G = refl
  Setᴬ-self ℓ .VE.⋆IdR F G = refl
  Setᴬ-self ℓ .VE.⋆Assoc F G H K = refl
  Setᴬ-self ℓ .VE.⌜id⌝ = refl
  Setᴬ-self ℓ .VE.⌜⋆⌝ f g = refl

-- When A is (the object-type of) a Category, we can further change base
-- along `Cofree : Fam A → PSH A` to obtain the presheaf-enrichment of
-- Cᴬ, whose hom-object at (F, G) is the presheaf
--     `c ↦ ∀ y, A[y, c] → C.Hom(F y, G y)`.

open Category
open Functor
open PshHomStrict
open LaxMonoidalFunctor
open LaxMonoidalStr
open NatTrans

module _ (A : Category ℓ ℓ') (ℓS : Level) where
  private
    module A = Category A
    ell = ℓ-max ℓ (ℓ-max ℓ' ℓS)

  -- PshMon.𝓟Mon on A at level `ell` (the level on which Cofree lands).
  private
    Psh-Mon = PshMon.𝓟Mon A ell

  -- `Cofree : Fam A → PSH A`, packaged as a lax monoidal functor from
  -- the cartesian-monoidal Fam-Mon to the cartesian-monoidal Psh-Mon.
  -- TODO: this follows from U ⊣ Cofree being a monoidal adjunction.
  private
    open UnitCounit using (_⊣_)
    Adj : PSH→Fam A ⊣ Cofree A
    Adj = CofreeFamAdj {ℓ = ell} A

  Cofree-lax : LaxMonoidalFunctor (Setᴬ-Mon A.ob ell) Psh-Mon
  Cofree-lax .F = Cofree {ℓ = ell} A
  Cofree-lax .laxmonstr .ε = _⊣_.η Adj .N-ob (PshMon.𝟙 A ell)
  Cofree-lax .laxmonstr .μ .N-ob (P , Q) .N-ob x fpfq y h =
    fpfq .fst y h , fpfq .snd y h
  Cofree-lax .laxmonstr .μ .N-ob (P , Q) .N-hom _ _ _ _ _ e =
    funExt λ y → funExt λ h i → e i .fst y h , e i .snd y h
  Cofree-lax .laxmonstr .μ .N-hom (φ , ψ) =
    makePshHomStrictPath refl
  Cofree-lax .laxmonstr .αμ-law _ _ _ = makePshHomStrictPath refl
  Cofree-lax .laxmonstr .ηε-law _ = makePshHomStrictPath refl
  Cofree-lax .laxmonstr .ρε-law _ = makePshHomStrictPath refl

  -- Cofree preserves the underlying category.  Because:
  --   (a) `Fam-Mon.unit = PSH→Fam 𝟙` definitionally (by our `Setᴬ-term` choice);
  --   (b) `Cofree-lax.ε = Adj.η .N-ob 𝟙` definitionally (by construction);
  -- the map `ε̂ = ε ⋆ Cofree⟪_⟫` is *definitionally* the forward hom-adjunction
  -- `adj→adj' CofreeFamAdj .adjIso .fun` at `(c = 𝟙, d = X)`.  So the
  -- preservation witness is just that `adjIso`'s inverse data.`
  -- TODO: we're relying on ``Fam-Mon.unit = PSH→Fam 𝟙` definitionally.
  -- We should instead define the iso by precomposition with the congruence under the representable functor `Set^A(_ , X)` of `unit ≅ U 𝟙`,
  -- which should hold from U (i.e. PSH→Fam) being RA and preserving limits so in particular `𝟙`.
  -- i.e. the chain Fam(unit, X) ≅⟨ representable Set^A(_, X) preserves iso (unit ≅ U 𝟙) ⟩ Set^A(U 𝟙, X) ≅⟨ U ⊣ G ⟩ PSh(𝟙, G₀ X)
  private
    open NaturalBijection using (module _⊣_)
    Adj² = adj→adj' (PSH→Fam A) (Cofree {ℓ = ell} A) Adj

  Cofree-pres : LaxMonoidalFunctor.preservesUnderlyingCategories Cofree-lax
  Cofree-pres X = IsoToIsIso (_⊣_.adjIso Adj² {c = PshMon.𝟙 A ell} {d = X})

  Fam-Psh-Enrichment : VE (Setᴬ A.ob ell) Psh-Mon
  Fam-Psh-Enrichment = BaseChange Cofree-lax Cofree-pres (Setᴬ-self A.ob ell)

module _ (A : Category ℓ ℓ') (C : Category ℓC ℓC') where
  private
    module A = Category A
    module C = Category C
    ell = ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓC ℓC'))
    Psh-Mon = PshMon.𝓟Mon A ell

  -- The presheaf-enrichment of Cᴬ via BaseChange along Cofree.
  -- We use the Lift-parametric `Cᴬ-Enrichment` at level `ℓ-max ℓ ℓ'` so
  -- that its hom-set level matches Cofree's `ell`.
  Cᴬ-Psh-Enrichment : VE (PowerCategory A.ob C) Psh-Mon
  Cᴬ-Psh-Enrichment =
    BaseChange (Cofree-lax A (ℓ-max ℓC ℓC')) (Cofree-pres A (ℓ-max ℓC ℓC'))
      (Cᴬ-Enrichment A.ob C (ℓ-max ℓ (ℓ-max ℓ' ℓC)))
