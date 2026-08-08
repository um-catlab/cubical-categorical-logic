{-

  The cartesian multicategory of presheaves over a category C, with
  FORDED naturality, so that all three multicategory laws are refl.

  The naive I-ary presheaf morphism would state naturality as

    f ⋆ N c' γ' ≡ N c (λ i → f ⋆ γ' i)

  and then composing two of them has to TRANSPORT the inner action
  along the outer one's naturality: the laws would only hold up to a
  path, and ⋆Assoc would be a coherence.  Fording fixes that.  We
  quantify over an arbitrary γ together with a witness that it is the
  reindexing (Ford's trick), so naturality reads

    ((i : I) → f ⋆ γ' i ≡ γ i) → f ⋆ N c' γ' ≡ N c γ

  which is a FUNCTION from witnesses to witnesses.  Composing two
  multimorphisms composes these functions, so ⋆Var/⋆Id/⋆Assoc are
  exactly the unit and associativity laws of ∘ — refl, by η.  (This is
  the multi-ary form of PshHomStrict.)

  Note that naturality is a proposition either way, so the forded
  record is equivalent to the naive one; the ford buys definitional
  behaviour, not new content.

-}
module Multicategory.Presheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf.Base

open import Multicategory.Cartesian

private
  variable
    ℓc ℓc' ℓp ℓI : Level

module _ {C : Category ℓc ℓc'} {ℓp} where
  private
    module C = Category C

  module _ {I : Type ℓI} (Γ : I → Presheaf C ℓp) (A : Presheaf C ℓp) where
    private
      module A = PresheafNotation A
      -- the family Γ is indexed, so its notation is spelled out rather
      -- than opened: a parameterised module alias cannot carry the
      -- mixfix p[_] / _⋆_ through the index.
      Γp[_,_] : I → C.ob → Type ℓp
      Γp[ i , c ] = PresheafNotation.p[_] (Γ i) c

      _⋆[_]_ : ∀ {c c'} → C [ c , c' ] → (i : I) → Γp[ i , c' ] → Γp[ i , c ]
      f ⋆[ i ] p = PresheafNotation._⋆_ (Γ i) f p

    -- an I-ary "section" of Γ at a stage
    Sect : C.ob → Type (ℓ-max ℓI ℓp)
    Sect c = (i : I) → Γp[ i , c ]

    PshMHomN-obTy : Type (ℓ-max ℓc (ℓ-max ℓI ℓp))
    PshMHomN-obTy = (c : C.ob) → Sect c → A.p[ c ]

    -- THE FORD: γ is arbitrary, and the reindexing hypothesis is
    -- passed positionwise, so this field is a function type.
    PshMHomN-homTy : PshMHomN-obTy → Type (ℓ-max ℓc (ℓ-max ℓc' (ℓ-max ℓI ℓp)))
    PshMHomN-homTy N-ob =
      (c c' : C.ob) (f : C [ c , c' ]) (γ' : Sect c') (γ : Sect c)
      → ((i : I) → f ⋆[ i ] γ' i ≡ γ i)
      → f A.⋆ N-ob c' γ' ≡ N-ob c γ

    record PshMHom : Type (ℓ-max ℓc (ℓ-max ℓc' (ℓ-max ℓI ℓp))) where
      constructor pshmhom
      field
        N-ob : PshMHomN-obTy
        N-hom : PshMHomN-homTy N-ob

    open PshMHom

    PshMHomΣ : Type (ℓ-max ℓc (ℓ-max ℓc' (ℓ-max ℓI ℓp)))
    PshMHomΣ = Σ PshMHomN-obTy PshMHomN-homTy

    PshMHomΣIso : Iso PshMHom PshMHomΣ
    PshMHomΣIso = iso
      (λ M → M .N-ob , M .N-hom)
      (λ M → pshmhom (M .fst) (M .snd))
      (λ _ → refl)
      (λ _ → refl)

    isPropN-hom : (N-ob : PshMHomN-obTy) → isProp (PshMHomN-homTy N-ob)
    isPropN-hom N-ob = isPropΠ6 λ _ _ _ _ _ _ → A.isSetPsh _ _

    isSetPshMHom : isSet PshMHom
    isSetPshMHom = isOfHLevelRetractFromIso 2 PshMHomΣIso
      (isSetΣ (isSetΠ λ _ → isSetΠ λ _ → A.isSetPsh)
        λ _ → isProp→isSet (isPropN-hom _))

open PshMHom

-- The fields are written qualified so the names stay free for later
-- modules, as in SETₘ.
PSHₘ : ∀ {ℓc ℓc'} (C : Category ℓc ℓc') (ℓI ℓp : Level)
  → CartesianMulticategory ℓI
      (ℓ-max (ℓ-max ℓc ℓc') (ℓ-suc ℓp))
      (ℓ-max (ℓ-max ℓc ℓc') (ℓ-max ℓI ℓp))
PSHₘ C ℓI ℓp .CartesianMulticategory.ob = Presheaf C ℓp
PSHₘ C ℓI ℓp .CartesianMulticategory.MHom⟨_⟩[_,_] I Γ A = PshMHom Γ A
PSHₘ C ℓI ℓp .CartesianMulticategory.var i .N-ob c γ = γ i
PSHₘ C ℓI ℓp .CartesianMulticategory.var i .N-hom c c' f γ' γ e = e i
PSHₘ C ℓI ℓp .CartesianMulticategory._⋆_ M g .N-ob c δ =
  M .N-ob c λ i → g i .N-ob c δ
-- naturality of the composite IS the composite of the naturality
-- functions: feed M's the witnesses produced by the g i's.
PSHₘ C ℓI ℓp .CartesianMulticategory._⋆_ M g .N-hom c c' f δ' δ e =
  M .N-hom c c' f
    (λ i → g i .N-ob c' δ') (λ i → g i .N-ob c δ)
    (λ i → g i .N-hom c c' f δ' δ e)
-- THE LAWS.  All three are the laws of function composition.
PSHₘ C ℓI ℓp .CartesianMulticategory.⋆Var i g = refl
PSHₘ C ℓI ℓp .CartesianMulticategory.⋆Id M = refl
PSHₘ C ℓI ℓp .CartesianMulticategory.⋆Assoc M g h = refl
PSHₘ C ℓI ℓp .CartesianMulticategory.isSetMHom = isSetPshMHom _ _
