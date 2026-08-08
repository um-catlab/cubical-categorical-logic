{-

  Normalization, packaged the way the rest of the program is packaged.

  The Kripke logical predicate of Multicategory.NbE is not an ad-hoc
  construction: it is an object of a displayed cartesian multicategory
  obtained by REINDEXING, exactly as canonicity's glue is.

    Predᴾᴰ            displayed over PSHₘ: a predicate on a presheaf,
                      closed under restriction — a displayed presheaf
    Tmᴾ               the multifunctor sending a type to its presheaf
                      of terms and a term to substitution into it
    Glueᴺ = reindexᴰ Tmᴾ Predᴾᴰ

  and the fundamental theorem is a Sectionᴰ of Glueᴺ whose fibre over a
  type is the logical predicate at that type.  The displayed homs of
  Glueᴺ are definitionally "sends related environments to related
  results", which is why the section is the elimProp already proved.

-}
module Multicategory.NbEGlue where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base

open import Multicategory.Cartesian
open import Multicategory.Multifunctor
open import Multicategory.Displayed
open import Multicategory.Reindex
open import Multicategory.Presheaf
open import Multicategory.PresheafPred
open import Multicategory.STLC
open import Multicategory.NbE

private
  ℓ1 : Level
  ℓ1 = ℓ-suc ℓ-zero

open Category
open Functor
open Rename
open PshMHom

-- the category of renamings for the fragment.  All three laws are
-- refl, because the typing condition is forded.
isSetRename : {Γ Δ : CtxA} → isSet (Rename Γ Δ)
isSetRename {Γ} {Δ} =
  isOfHLevelRetract 2
    (λ ρ → ρ .vars , ρ .typed)
    (λ p → record { vars = p .fst ; typed = p .snd })
    (λ _ → refl)
    (isSetΣ (isSet→ (str (Δ .fst)))
      (λ _ → isSetΠ (λ _ → isSetImplicitΠ (λ _ →
        isSet→ (isProp→isSet (isSetTyA _ _))))))

RENA : Category ℓ1 ℓ-zero
RENA .ob = CtxA
RENA .Hom[_,_] = Rename
RENA .id = idRen
RENA ._⋆_ = _⨟_
RENA .⋆IdL _ = refl
RENA .⋆IdR _ = refl
RENA .⋆Assoc _ _ _ = refl
RENA .isSetHom = isSetRename

-- terms of a type, as a presheaf on renamings.  Its functor laws are
-- wk-id and wk-⨟.
TmPsh : TyA → Presheaf (RENA ^op) ℓ1
TmPsh A .F-ob Γ = Term Γ A , truncA
TmPsh A .F-hom ρ t = wk ρ t
TmPsh A .F-id {Γ} = funExt (λ t → wk-id {Γ} t)
TmPsh A .F-seq ρ σ = funExt (λ t → wk-⨟ ρ σ t)

-- substitution is natural, which is the multifunctor's action
Tmᴾ : Multifunctor SynA (PSHₘ (RENA ^op) ℓ-zero ℓ1)
Tmᴾ .Multifunctor.F-ob = TmPsh
Tmᴾ .Multifunctor.F-hom t .N-ob Δ γ = t ⟨ γ ⟩A
Tmᴾ .Multifunctor.F-hom t .N-hom Δ Δ' ρ γ' γ e =
  ⟨⟩⟨⟩A t γ' (wkVar ρ) ∙ cong (t ⟨_⟩A) (funExt e)
Tmᴾ .Multifunctor.F-var i =
  makePshMHomPath (funExt (λ Δ → funExt (λ γ → ⟨⟩varA i γ)))
Tmᴾ .Multifunctor.F-⋆ t f =
  makePshMHomPath (funExt (λ Δ → funExt (λ δ → ⟨⟩⟨⟩A t f δ)))

-- THE GLUE, as a reindexing
Glueᴺ : CartesianMulticategoryᴰ SynA (ℓ-suc ℓ1) ℓ1
Glueᴺ = reindexᴰ Tmᴾ (Predᴾᴰ (RENA ^op) ℓ-zero ℓ1)

-- its displayed homs are exactly the motive the fundamental theorem
-- was proved for
_ : {I : Type} {Γ : CtxtA I} {A : TyA}
    {Γᴰ : (i : I) → PredOb (RENA ^op) ℓ-zero ℓ1 (TmPsh (Γ i))}
    {Aᴰ : PredOb (RENA ^op) ℓ-zero ℓ1 (TmPsh A)}
    (t : TmA I Γ A)
  → CartesianMulticategoryᴰ.MHomᴰ[_][_,_] Glueᴺ {I = I} {Γ = Γ} {A = A}
      t Γᴰ Aᴰ
    ≡ ((Δ : CtxA) (γ : (i : I) → Term Δ (Γ i))
       → ((i : I) → ⟨ Γᴰ i .fst Δ (γ i) ⟩)
       → ⟨ Aᴰ .fst Δ (t ⟨ γ ⟩A) ⟩)
_ = λ t → refl

-- the logical predicate, as a fibre object of the glue
Rᴰ : (A : TyA) → PredOb (RENA ^op) ℓ-zero ℓ1 (TmPsh A)
Rᴰ A .fst Γ t = R A Γ t , isPropR A Γ t
Rᴰ A .snd Δ Γ ρ t = monR A ρ t

open Sectionᴰ

-- THE FUNDAMENTAL THEOREM, as a section of the glue
FTLRᴺ : Sectionᴰ Glueᴺ
FTLRᴺ .S-ob = Rᴰ
FTLRᴺ .S-hom = fund
FTLRᴺ .S-var {Γ = Γ} i =
  isPropΠ3 (λ Δ γ _ → isPropR (Γ i) Δ _) _ _
FTLRᴺ .S-⋆ {A = A} t f =
  isPropΠ3 (λ Δ γ _ → isPropR A Δ _) _ _


-- ==================================================================
-- NORMALIZATION, IN THE GLUING FRAMEWORK.
--
-- Everything specific to the logical predicate is isolated into one
-- record: a NORMALIZATION STRUCTURE on a displayed object of the glue
-- is the pair reflect/reify, and nothing else about the predicate is
-- used.  Given one, ANY section of Glueᴺ normalizes — the section
-- supplies the interpretation of every term, reflect builds the
-- identity environment out of variables, and reify reads the result
-- back.  So normalization is not a second argument on top of the
-- fundamental theorem: it is what a section of this displayed
-- multicategory MEANS, once its fibres carry the two structure maps.
record NormStr (Pᴰ : (A : TyA) → PredOb (RENA ^op) ℓ-zero ℓ1 (TmPsh A))
  : Type ℓ1 where
  field
    reflectᴰ : (A : TyA) {Γ : CtxA} (n : NeA Γ A)
      → ⟨ Pᴰ A .fst Γ ⌜ n ⌝ne ⟩
    reifyᴰ : (A : TyA) {Γ : CtxA} (t : Term Γ A) → ⟨ Pᴰ A .fst Γ t ⟩
      → ∥ Σ[ n ∈ NfA Γ A ] ⌜ n ⌝nf ≡ t ∥₁

open NormStr

normalizeᴳ : (S : Sectionᴰ Glueᴺ) → NormStr (S .S-ob)
  → {Γ : CtxA} {A : TyA} (t : Term Γ A)
  → ∥ Σ[ n ∈ NfA Γ A ] ⌜ n ⌝nf ≡ t ∥₁
normalizeᴳ S ns {Γ} {A} t =
  ns .reifyᴰ A t
    (subst (λ s → ⟨ S .S-ob A .fst Γ s ⟩) (⟨⟩idA t)
      (S .S-hom t Γ varA (λ i → ns .reflectᴰ (Typing Γ i) (varNe i))))

-- the logical predicate of Multicategory.NbE is such a structure
Rᴺ : NormStr (FTLRᴺ .S-ob)
Rᴺ .reflectᴰ = reflect
Rᴺ .reifyᴰ = reify

-- and running the framework on it gives back `norm` ON THE NOSE, so
-- the packaging is not a re-proof: it is the same term, factored.
_ : {Γ : CtxA} {A : TyA} (t : Term Γ A)
  → normalizeᴳ FTLRᴺ Rᴺ {Γ} {A} t ≡ norm {Γ} {A} t
_ = λ t → refl
