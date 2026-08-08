{-

  DISPLAYED presheaves, as displayed multifunctors into displayed SET.

  The design principle, from first principles:

    a presheaf is a SET-valued (multi)functor, so a DISPLAYED presheaf
    is a DISPLAYED multifunctor into DISPLAYED SET

  and the displayed multifunctor's own functoriality IS the restriction
  action that Multicategory.PresheafPred's Famᴾᴰ leaves out.

  Concretely.  Evₘ c : PSHₘ C → SETₘ, evaluation at a stage, is a
  STRICT multifunctor (both laws refl, see below): that is the sense in
  which a presheaf is a SET-valued multifunctor — it is the C-indexed
  family of the Evₘ c together with restriction.  Displayed SET is
  Setᴰ = Famᴰ SETₘ, from Multicategory.Family.  So:

    obᴰ over P    = a stage-indexed family of Setᴰ-objects over
                    Evₘ c .F-ob P, plus restriction
    MHomᴰ over M  = a stage-indexed family of Setᴰ-homs over
                    Evₘ c .F-hom M, plus FORDED naturality

  Both components are literally Setᴰ's, and varᴰ / _⋆ᴰ_ are literally
  Setᴰ.varᴰ / Setᴰ._⋆ᴰ_ stagewise.  The second component is forded
  exactly as in Multicategory.Presheaf: an arbitrary γ with a witness
  that it is the reindexing, so that displayed naturality is a FUNCTION
  from witnesses to witnesses and composing displayed multimorphisms
  composes those functions.  Hence all three displayed laws are refl,
  with DATA-valued fibres.

  Evᴰ c : Multifunctorᴰ (Evₘ c) PSHᴰₘ Setᴰ then says, in the sense of
  Multicategory.MultifunctorD, that a displayed presheaf IS a displayed
  multifunctor into displayed SET.

  Fgtᴰ compares with Famᴾᴰ: forgetting displayed naturality is a
  displayed multifunctor over the IDENTITY of PSHₘ.  It has no section:
  Famᴾᴰ's displayed homs are bare families, this file's are morphisms.

  WHY THE FORD IS NOT OPTIONAL (measured, not asserted).  With the
  NAIVE displayed naturality — the reindexed section spelled out
  instead of quantified with a witness — _⋆ᴰ_ is not even DEFINABLE
  without a transport.  Composing Mᴰ with the gᴰ i needs Mᴰ's
  naturality at the section (λ i → g i .N-ob c (f ⋆ δ')), while the
  naive field supplies it only at (λ i → f ⋆ (g i .N-ob c' δ')); the
  two are related by g i's own naturality, which is a PATH.  Agda
  reports exactly that mismatch.  Fording moves that path into the
  hypothesis, where it is threaded rather than transported along.

  ONE COST, paid in levels, not in coherence: the displayed hom type
  mentions C's morphisms, so PSHᴰₘ's hom level is
  ℓc ⊔ ℓc' ⊔ ℓI ⊔ ℓp where Famᴾᴰ's was ℓc ⊔ ℓI ⊔ ℓp.

-}
module Multicategory.PresheafD where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf.Base

open import Multicategory.Cartesian
open import Multicategory.Displayed
open import Multicategory.Multifunctor
open import Multicategory.MultifunctorD
open import Multicategory.Family
open import Multicategory.Presheaf
open import Multicategory.PresheafPred

private
  variable
    ℓc ℓc' ℓI ℓp : Level

open PshMHom
open Multifunctor

-- ==================================================================
-- Evaluation at a stage is a STRICT multifunctor into SET.  This is
-- the precise sense of "presheaves are multifunctors into SET": both
-- laws are refl, so nothing downstairs will have to be reindexed.

module _ {ℓc ℓc' : Level} (C : Category ℓc ℓc') (ℓI ℓp : Level) where
  private
    module C = Category C

  Evₘ : C.ob → Multifunctor (PSHₘ C ℓI ℓp) (SETₘ {ℓI} {ℓp})
  Evₘ c .F-ob P =
    PresheafNotation.p[_] P c , PresheafNotation.isSetPsh P
  Evₘ c .F-hom M γ = M .N-ob c γ
  Evₘ c .F-var i = refl
  Evₘ c .F-⋆ M g = refl

  -- displayed SET, from Multicategory.Family
  private
    module SD = CartesianMulticategoryᴰ (Setᴰ {ℓI} {ℓp})

  -- ================================================================
  -- OBJECTS.  A displayed presheaf over P is a stagewise Setᴰ-object
  -- over Evₘ c .F-ob P, together with restriction.
  PshDOb : Presheaf C ℓp → Type (ℓ-max ℓc (ℓ-max ℓc' (ℓ-suc ℓp)))
  PshDOb P =
    Σ[ S ∈ ((c : C.ob) → SD.obᴰ (Evₘ c .F-ob P)) ]
      ((c c' : C.ob) (f : C [ c , c' ])
        (p : PresheafNotation.p[_] P c')
       → ⟨ S c' p ⟩ → ⟨ S c (PresheafNotation._⋆_ P f p) ⟩)

  -- on objects this agrees with Famᴾᴰ on the nose
  _ : (P : Presheaf C ℓp) → PshDOb P ≡ FamOb C ℓI ℓp P
  _ = λ P → refl

  -- ================================================================
  -- MULTIMORPHISMS.  Stagewise a displayed hom of Setᴰ, plus FORDED
  -- displayed naturality.
  module _ {I : Type ℓI} {Γ : I → Presheaf C ℓp} {A : Presheaf C ℓp}
    (M : PshMHom Γ A) (Γᴰ : (i : I) → PshDOb (Γ i)) (Aᴰ : PshDOb A)
    where
    private
      module A = PresheafNotation A
      Γₛ : C.ob → I → hSet ℓp
      Γₛ c i = Evₘ c .F-ob (Γ i)
      Aₛ : C.ob → hSet ℓp
      Aₛ c = Evₘ c .F-ob A
      _⋆[_]_ : ∀ {c c'} → C [ c , c' ] → (i : I)
        → ⟨ Γₛ c' i ⟩ → ⟨ Γₛ c i ⟩
      f ⋆[ i ] p = PresheafNotation._⋆_ (Γ i) f p

    PshMHomᴰN-obTy : Type (ℓ-max ℓc (ℓ-max ℓI ℓp))
    PshMHomᴰN-obTy = (c : C.ob)
      → SD.MHomᴰ[_][_,_] {I = I} {Γ = Γₛ c} {A = Aₛ c}
          (Evₘ c .F-hom M) (λ i → Γᴰ i .fst c) (Aᴰ .fst c)

    -- THE FORD, displayed.  γ' and γ are arbitrary, e witnesses that
    -- γ is the reindexing of γ', γ'ᴰ and γᴰ are arbitrary, and the
    -- last hypothesis witnesses that γᴰ is the restriction of γ'ᴰ
    -- OVER e.  A function from witnesses to witnesses, again.
    PshMHomᴰN-homTy : PshMHomᴰN-obTy
      → Type (ℓ-max ℓc (ℓ-max ℓc' (ℓ-max ℓI ℓp)))
    PshMHomᴰN-homTy Nᴰ =
      (c c' : C.ob) (f : C [ c , c' ])
      (γ' : Sect Γ A c') (γ : Sect Γ A c)
      (e : (i : I) → f ⋆[ i ] γ' i ≡ γ i)
      (γ'ᴰ : (i : I) → ⟨ Γᴰ i .fst c' (γ' i) ⟩)
      (γᴰ : (i : I) → ⟨ Γᴰ i .fst c (γ i) ⟩)
      → ((i : I) → PathP (λ k → ⟨ Γᴰ i .fst c (e i k) ⟩)
            (Γᴰ i .snd c c' f (γ' i) (γ'ᴰ i)) (γᴰ i))
      → PathP (λ k → ⟨ Aᴰ .fst c (M .N-hom c c' f γ' γ e k) ⟩)
          (Aᴰ .snd c c' f (M .N-ob c' γ') (Nᴰ c' γ' γ'ᴰ))
          (Nᴰ c γ γᴰ)

    record PshMHomᴰ
      : Type (ℓ-max ℓc (ℓ-max ℓc' (ℓ-max ℓI ℓp))) where
      constructor pshmhomᴰ
      field
        N-obᴰ : PshMHomᴰN-obTy
        N-homᴰ : PshMHomᴰN-homTy N-obᴰ

    open PshMHomᴰ

    PshMHomᴰΣ : Type (ℓ-max ℓc (ℓ-max ℓc' (ℓ-max ℓI ℓp)))
    PshMHomᴰΣ = Σ PshMHomᴰN-obTy PshMHomᴰN-homTy

    PshMHomᴰΣIso : Iso PshMHomᴰ PshMHomᴰΣ
    PshMHomᴰΣIso = iso
      (λ Mᴰ → Mᴰ .N-obᴰ , Mᴰ .N-homᴰ)
      (λ Mᴰ → pshmhomᴰ (Mᴰ .fst) (Mᴰ .snd))
      (λ _ → refl)
      (λ _ → refl)

    isPropN-homᴰ : (Nᴰ : PshMHomᴰN-obTy) → isProp (PshMHomᴰN-homTy Nᴰ)
    isPropN-homᴰ Nᴰ =
      isPropΠ λ c → isPropΠ λ c' → isPropΠ λ f → isPropΠ λ γ' →
      isPropΠ λ γ → isPropΠ λ e → isPropΠ λ γ'ᴰ → isPropΠ λ γᴰ →
      isPropΠ λ _ →
        isOfHLevelPathP' 1 (str (Aᴰ .fst c (M .N-ob c γ))) _ _

    isSetPshMHomᴰ : isSet PshMHomᴰ
    isSetPshMHomᴰ = isOfHLevelRetractFromIso 2 PshMHomᴰΣIso
      (isSetΣ
        (isSetΠ λ c → isSetΠ λ γ → isSetΠ λ γᴰ →
          str (Aᴰ .fst c (M .N-ob c γ)))
        λ Nᴰ → isProp→isSet (isPropN-homᴰ Nᴰ))

    -- The UNFORDED displayed naturality, recovered by instantiating
    -- the ford at the actual reindexing: restricting the value equals
    -- the value at the restricted argument, over the base's own
    -- naturality.  THIS is what Famᴾᴰ's displayed homs do not carry.
    N-homᴰ-naive : (Mᴰ : PshMHomᴰ)
      (c c' : C.ob) (f : C [ c , c' ]) (γ' : Sect Γ A c')
      (γ'ᴰ : (i : I) → ⟨ Γᴰ i .fst c' (γ' i) ⟩)
      → PathP (λ k → ⟨ Aᴰ .fst c
              (M .N-hom c c' f γ' (λ i → f ⋆[ i ] γ' i)
                (λ i → refl) k) ⟩)
          (Aᴰ .snd c c' f (M .N-ob c' γ') (Mᴰ .N-obᴰ c' γ' γ'ᴰ))
          (Mᴰ .N-obᴰ c (λ i → f ⋆[ i ] γ' i)
            (λ i → Γᴰ i .snd c c' f (γ' i) (γ'ᴰ i)))
    N-homᴰ-naive Mᴰ c c' f γ' γ'ᴰ =
      Mᴰ .N-homᴰ c c' f γ' (λ i → f ⋆[ i ] γ' i) (λ i → refl)
        γ'ᴰ (λ i → Γᴰ i .snd c c' f (γ' i) (γ'ᴰ i)) (λ i → refl)

open PshMHomᴰ

-- ==================================================================
-- THE DISPLAYED CARTESIAN MULTICATEGORY OF DISPLAYED PRESHEAVES.
--
-- varᴰ and _⋆ᴰ_ are Setᴰ's, stagewise; the naturality components are
-- pure witness-passing.  All three laws are refl.

module _ {ℓc ℓc' : Level} (C : Category ℓc ℓc') (ℓI ℓp : Level) where
  private
    module C = Category C
    module SD = CartesianMulticategoryᴰ (Setᴰ {ℓI} {ℓp})

    -- the stagewise context, as a SETₘ-context
    Ctxₛ : {I : Type ℓI} → (I → Presheaf C ℓp) → C.ob → I → hSet ℓp
    Ctxₛ Γ c i = Evₘ C ℓI ℓp c .F-ob (Γ i)

  open CartesianMulticategoryᴰ

  PSHᴰₘ : CartesianMulticategoryᴰ (PSHₘ C ℓI ℓp)
    (ℓ-max ℓc (ℓ-max ℓc' (ℓ-suc ℓp)))
    (ℓ-max ℓc (ℓ-max ℓc' (ℓ-max ℓI ℓp)))
  PSHᴰₘ .obᴰ = PshDOb C ℓI ℓp
  PSHᴰₘ .MHomᴰ[_][_,_] = PshMHomᴰ C ℓI ℓp
  PSHᴰₘ .varᴰ {I = I} {Γ = Γ} {Γᴰ = Γᴰ} i .N-obᴰ c =
    SD.varᴰ {I = I} {Γ = Ctxₛ Γ c} {Γᴰ = λ j → Γᴰ j .fst c} i
  PSHᴰₘ .varᴰ i .N-homᴰ c c' f γ' γ e γ'ᴰ γᴰ eᴰ = eᴰ i
  PSHᴰₘ ._⋆ᴰ_ {I = I} {J = J} {Γ = Γ} {Δ = Δ} {A = A}
    {Γᴰ = Γᴰ} {Δᴰ = Δᴰ} {Aᴰ = Aᴰ} {f = M} {g = g} Mᴰ gᴰ .N-obᴰ c =
    SD._⋆ᴰ_ {I = I} {J = J} {Γ = Ctxₛ Γ c} {Δ = Ctxₛ Δ c}
      {A = Evₘ C ℓI ℓp c .F-ob A}
      {Γᴰ = λ i → Γᴰ i .fst c} {Δᴰ = λ j → Δᴰ j .fst c}
      {Aᴰ = Aᴰ .fst c}
      {f = Evₘ C ℓI ℓp c .F-hom M}
      {g = λ i → Evₘ C ℓI ℓp c .F-hom (g i)}
      (Mᴰ .N-obᴰ c) (λ i → gᴰ i .N-obᴰ c)
  -- displayed naturality of the composite IS the composite of the
  -- displayed naturality functions
  PSHᴰₘ ._⋆ᴰ_ {g = g} Mᴰ gᴰ .N-homᴰ c c' f δ' δ e δ'ᴰ δᴰ eᴰ =
    Mᴰ .N-homᴰ c c' f
      (λ i → g i .N-ob c' δ') (λ i → g i .N-ob c δ)
      (λ i → g i .N-hom c c' f δ' δ e)
      (λ i → gᴰ i .N-obᴰ c' δ' δ'ᴰ) (λ i → gᴰ i .N-obᴰ c δ δᴰ)
      (λ i → gᴰ i .N-homᴰ c c' f δ' δ e δ'ᴰ δᴰ eᴰ)
  -- THE LAWS
  PSHᴰₘ .⋆Varᴰ i gᴰ = refl
  PSHᴰₘ .⋆Idᴰ Mᴰ = refl
  PSHᴰₘ .⋆Assocᴰ Mᴰ gᴰ hᴰ = refl
  PSHᴰₘ .isSetMHomᴰ = isSetPshMHomᴰ C ℓI ℓp _ _ _

-- ==================================================================
-- DISPLAYED PRESHEAVES *ARE* DISPLAYED MULTIFUNCTORS INTO DISPLAYED
-- SET.  Evaluation at a stage is a displayed multifunctor over the
-- strict multifunctor Evₘ c, into Setᴰ = Famᴰ SETₘ.  Its two forded
-- laws are cong of a STRICT map, so nothing is transported: the
-- displayed presheaf's restriction action is this multifunctor's
-- functoriality, not a side condition.

module _ {ℓc ℓc' : Level} (C : Category ℓc ℓc') (ℓI ℓp : Level) where
  private
    module C = Category C

  open Multifunctorᴰ

  Evᴰ : (c : C.ob)
    → Multifunctorᴰ (Evₘ C ℓI ℓp c) (PSHᴰₘ C ℓI ℓp) (Setᴰ {ℓI} {ℓp})
  Evᴰ c .F-obᴰ Pᴰ = Pᴰ .fst c
  Evᴰ c .F-homᴰ Mᴰ = Mᴰ .N-obᴰ c
  Evᴰ c .F-varᴰ i e =
    cong (λ z → Evₘ C ℓI ℓp c .F-hom (z .fst) , z .snd .N-obᴰ c) e
  Evᴰ c .F-⋆ᴰ fᴰ gᴰ e =
    cong (λ z → Evₘ C ℓI ℓp c .F-hom (z .fst) , z .snd .N-obᴰ c) e

-- ==================================================================
-- COMPARISON WITH Famᴾᴰ.  On OBJECTS the two agree definitionally
-- (checked above).  On MULTIMORPHISMS, Famᴾᴰ's are exactly the N-obᴰ
-- component: forgetting displayed naturality is a displayed
-- multifunctor over the IDENTITY of PSHₘ.  There is no section — a
-- bare family carries no witness that it commutes with restriction,
-- and that is the defect this file removes.

module _ {ℓc ℓc' : Level} (C : Category ℓc ℓc') (ℓI ℓp : Level) where
  open Multifunctorᴰ

  Fgtᴰ : Multifunctorᴰ (Idᴹ (PSHₘ C ℓI ℓp)) (PSHᴰₘ C ℓI ℓp)
           (Famᴾᴰ C ℓI ℓp)
  Fgtᴰ .F-obᴰ Pᴰ = Pᴰ
  Fgtᴰ .F-homᴰ Mᴰ = Mᴰ .N-obᴰ
  Fgtᴰ .F-varᴰ i e = cong (λ z → z .fst , z .snd .N-obᴰ) e
  Fgtᴰ .F-⋆ᴰ fᴰ gᴰ e = cong (λ z → z .fst , z .snd .N-obᴰ) e

-- ==================================================================
-- MEASUREMENT.  The three displayed laws, stated at VARIABLE data.
-- Each is a plain _≡_ rather than a _≡[_]_ because PSHₘ's own laws
-- are refl; each holds by refl.

module Measurements {ℓc ℓc' : Level} {C : Category ℓc ℓc'}
  {ℓI ℓp : Level} where
  private
    module P = CartesianMulticategory (PSHₘ C ℓI ℓp)
    module Pᴰ = CartesianMulticategoryᴰ (PSHᴰₘ C ℓI ℓp)

  ⋆Varᴰ-refl : {I J : Type ℓI} {Γ : P.Ctx I} {Δ : P.Ctx J}
    {Γᴰ : (i : I) → Pᴰ.obᴰ (Γ i)} {Δᴰ : (j : J) → Pᴰ.obᴰ (Δ j)}
    {g : (i : I) → P.MHom⟨ J ⟩[ Δ , Γ i ]}
    (i : I) (gᴰ : (i : I) → Pᴰ.MHomᴰ[ g i ][ Δᴰ , Γᴰ i ])
    → Pᴰ.varᴰ i Pᴰ.⋆ᴰ gᴰ ≡ gᴰ i
  ⋆Varᴰ-refl i gᴰ = refl

  ⋆Idᴰ-refl : {I : Type ℓI} {Γ : P.Ctx I} {A : P.ob}
    {Γᴰ : (i : I) → Pᴰ.obᴰ (Γ i)} {Aᴰ : Pᴰ.obᴰ A}
    {M : P.MHom⟨ I ⟩[ Γ , A ]}
    (Mᴰ : Pᴰ.MHomᴰ[ M ][ Γᴰ , Aᴰ ])
    → Mᴰ Pᴰ.⋆ᴰ Pᴰ.varᴰ ≡ Mᴰ
  ⋆Idᴰ-refl Mᴰ = refl

  ⋆Assocᴰ-refl : {I J K : Type ℓI}
    {Γ : P.Ctx I} {Δ : P.Ctx J} {Θ : P.Ctx K} {A : P.ob}
    {Γᴰ : (i : I) → Pᴰ.obᴰ (Γ i)} {Δᴰ : (j : J) → Pᴰ.obᴰ (Δ j)}
    {Θᴰ : (k : K) → Pᴰ.obᴰ (Θ k)} {Aᴰ : Pᴰ.obᴰ A}
    {M : P.MHom⟨ I ⟩[ Γ , A ]} {g : (i : I) → P.MHom⟨ J ⟩[ Δ , Γ i ]}
    {h : (j : J) → P.MHom⟨ K ⟩[ Θ , Δ j ]}
    (Mᴰ : Pᴰ.MHomᴰ[ M ][ Γᴰ , Aᴰ ])
    (gᴰ : (i : I) → Pᴰ.MHomᴰ[ g i ][ Δᴰ , Γᴰ i ])
    (hᴰ : (j : J) → Pᴰ.MHomᴰ[ h j ][ Θᴰ , Δᴰ j ])
    → (Mᴰ Pᴰ.⋆ᴰ gᴰ) Pᴰ.⋆ᴰ hᴰ ≡ (Mᴰ Pᴰ.⋆ᴰ λ i → gᴰ i Pᴰ.⋆ᴰ hᴰ)
  ⋆Assocᴰ-refl Mᴰ gᴰ hᴰ = refl
