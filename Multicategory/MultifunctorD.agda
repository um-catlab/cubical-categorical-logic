{-

  DISPLAYED multifunctors of cartesian multicategories.

  A Multifunctorᴰ over F : M → N maps Mᴰ (displayed over M) into Nᴰ
  (displayed over N), lying over F.  The interesting question is how to
  state its two laws.

  The naive statement is a dependent path over the base law,

    F-homᴰ (varᴰ i) ≡[ F.F-var i ] varᴰ i

  and it does NOT compose: to compose Gᴰ after Fᴰ one has to conjugate
  the inner PathP along the outer base path, which is a compPathP, and
  the base index of the result is cong G (cong F p ∙ F-var) ∙ G-var —
  so unitality and associativity of ∘ᴹᴰ fail definitionally, for the
  same reason ⋆Assoc would have been a coherence in Multicategory.
  Presheaf.

  So we FORD, in the same forward-oriented style: the source of the
  equation is an ARBITRARY displayed hom uᴰ over an arbitrary u,
  together with a witness that it is varᴰ (resp. fᴰ ⋆ᴰ gᴰ), and the law
  is a FUNCTION from witnesses to witnesses.  Composing two displayed
  multifunctors composes these functions.

  The witnesses are paths in the TOTAL SPACE ∫MHom, not PathPs over a
  named base path.  That is what removes the base-path bookkeeping: a
  total-space path carries its own base path in its fst.  It is no
  weaker, because base hom-types are sets, so any two base paths with
  the same endpoints agree — F-varᴰ→PathP below recovers the naive law
  from the forded one, and forded-var/forded-⋆ build the forded law
  from the naive one.

  With this shape Idᴹᴰ is the identity function on witnesses and ∘ᴹᴰ is
  function composition, so ∘ᴹᴰ is definitionally unital and
  associative — see the statements at the bottom of the file.

-}
module Multicategory.MultifunctorD where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.More
open import Cubical.Data.Sigma

open import Multicategory.Cartesian
open import Multicategory.Displayed
open import Multicategory.Multifunctor

private
  variable
    ℓI ℓM ℓM' ℓN ℓN' ℓP ℓP' : Level
    ℓMᴰ ℓMᴰ' ℓNᴰ ℓNᴰ' ℓPᴰ ℓPᴰ' : Level

-- The total space of the displayed homs over a fixed arity and
-- context.  A path in here is a base path together with a displayed
-- path over it; this is Reindex.agda's ∫≡, specialised.
module _ {M : CartesianMulticategory ℓI ℓM ℓM'}
  (Mᴰ : CartesianMulticategoryᴰ M ℓMᴰ ℓMᴰ') where
  private
    module M = CartesianMulticategory M
    module Mᴰ = CartesianMulticategoryᴰ Mᴰ

  ∫MHom : {I : Type ℓI} {Γ : M.Ctx I} {A : M.ob}
    → ((i : I) → Mᴰ.obᴰ (Γ i)) → Mᴰ.obᴰ A → Type (ℓ-max ℓM' ℓMᴰ')
  ∫MHom {I = I} {Γ = Γ} {A = A} Γᴰ Aᴰ =
    Σ[ h ∈ M.MHom⟨ I ⟩[ Γ , A ] ] Mᴰ.MHomᴰ[ h ][ Γᴰ , Aᴰ ]

record Multifunctorᴰ
    {M : CartesianMulticategory ℓI ℓM ℓM'}
    {N : CartesianMulticategory ℓI ℓN ℓN'}
    (F : Multifunctor M N)
    (Mᴰ : CartesianMulticategoryᴰ M ℓMᴰ ℓMᴰ')
    (Nᴰ : CartesianMulticategoryᴰ N ℓNᴰ ℓNᴰ')
    : Type (ℓ-suc (ℓ-max ℓI
        (ℓ-max (ℓ-max (ℓ-max ℓM ℓM') (ℓ-max ℓMᴰ ℓMᴰ'))
               (ℓ-max (ℓ-max ℓN ℓN') (ℓ-max ℓNᴰ ℓNᴰ'))))) where
  private
    module M = CartesianMulticategory M
    module N = CartesianMulticategory N
    module F = Multifunctor F
    module Mᴰ = CartesianMulticategoryᴰ Mᴰ
    module Nᴰ = CartesianMulticategoryᴰ Nᴰ
  field
    F-obᴰ : {A : M.ob} → Mᴰ.obᴰ A → Nᴰ.obᴰ (F.F-ob A)

    F-homᴰ : {I : Type ℓI} {Γ : M.Ctx I} {A : M.ob}
      {Γᴰ : (i : I) → Mᴰ.obᴰ (Γ i)} {Aᴰ : Mᴰ.obᴰ A}
      {f : M.MHom⟨ I ⟩[ Γ , A ]}
      → Mᴰ.MHomᴰ[ f ][ Γᴰ , Aᴰ ]
      → Nᴰ.MHomᴰ[ F.F-hom f ][ (λ j → F-obᴰ (Γᴰ j)) , F-obᴰ Aᴰ ]

    -- THE FORD.  uᴰ is arbitrary; the hypothesis that it is varᴰ is a
    -- total-space path, and the law turns it into one downstairs.
    F-varᴰ : {I : Type ℓI} {Γ : M.Ctx I}
      {Γᴰ : (i : I) → Mᴰ.obᴰ (Γ i)} (i : I)
      {u : M.MHom⟨ I ⟩[ Γ , Γ i ]} {uᴰ : Mᴰ.MHomᴰ[ u ][ Γᴰ , Γᴰ i ]}
      → Path (∫MHom Mᴰ Γᴰ (Γᴰ i)) (u , uᴰ) (M.var i , Mᴰ.varᴰ i)
      → Path (∫MHom Nᴰ (λ j → F-obᴰ (Γᴰ j)) (F-obᴰ (Γᴰ i)))
             (F.F-hom u , F-homᴰ uᴰ) (N.var i , Nᴰ.varᴰ i)

    F-⋆ᴰ : {I J : Type ℓI} {Γ : M.Ctx I} {Δ : M.Ctx J} {A : M.ob}
      {Γᴰ : (i : I) → Mᴰ.obᴰ (Γ i)} {Δᴰ : (j : J) → Mᴰ.obᴰ (Δ j)}
      {Aᴰ : Mᴰ.obᴰ A}
      {f : M.MHom⟨ I ⟩[ Γ , A ]} {g : (i : I) → M.MHom⟨ J ⟩[ Δ , Γ i ]}
      (fᴰ : Mᴰ.MHomᴰ[ f ][ Γᴰ , Aᴰ ])
      (gᴰ : (i : I) → Mᴰ.MHomᴰ[ g i ][ Δᴰ , Γᴰ i ])
      {u : M.MHom⟨ J ⟩[ Δ , A ]} {uᴰ : Mᴰ.MHomᴰ[ u ][ Δᴰ , Aᴰ ]}
      → Path (∫MHom Mᴰ Δᴰ Aᴰ) (u , uᴰ) (f M.⋆ g , fᴰ Mᴰ.⋆ᴰ gᴰ)
      → Path (∫MHom Nᴰ (λ j → F-obᴰ (Δᴰ j)) (F-obᴰ Aᴰ))
             (F.F-hom u , F-homᴰ uᴰ)
             ( F.F-hom f N.⋆ (λ i → F.F-hom (g i))
             , F-homᴰ fᴰ Nᴰ.⋆ᴰ (λ i → F-homᴰ (gᴰ i)))

open Multifunctorᴰ

-- The identity displayed multifunctor: the identity function on
-- witnesses.
Idᴹᴰ : {M : CartesianMulticategory ℓI ℓM ℓM'}
  (Mᴰ : CartesianMulticategoryᴰ M ℓMᴰ ℓMᴰ')
  → Multifunctorᴰ (Idᴹ M) Mᴰ Mᴰ
Idᴹᴰ Mᴰ .F-obᴰ Aᴰ = Aᴰ
Idᴹᴰ Mᴰ .F-homᴰ fᴰ = fᴰ
Idᴹᴰ Mᴰ .F-varᴰ i e = e
Idᴹᴰ Mᴰ .F-⋆ᴰ fᴰ gᴰ e = e

-- Composition: the witness produced by Fᴰ is fed straight to Gᴰ.  No
-- cong, no _∙_, no compPathP.
module _
  {M : CartesianMulticategory ℓI ℓM ℓM'}
  {N : CartesianMulticategory ℓI ℓN ℓN'}
  {P : CartesianMulticategory ℓI ℓP ℓP'}
  {F : Multifunctor M N} {G : Multifunctor N P}
  {Mᴰ : CartesianMulticategoryᴰ M ℓMᴰ ℓMᴰ'}
  {Nᴰ : CartesianMulticategoryᴰ N ℓNᴰ ℓNᴰ'}
  {Pᴰ : CartesianMulticategoryᴰ P ℓPᴰ ℓPᴰ'}
  where
  _∘ᴹᴰ_ : Multifunctorᴰ G Nᴰ Pᴰ → Multifunctorᴰ F Mᴰ Nᴰ
    → Multifunctorᴰ (G ∘ᴹ F) Mᴰ Pᴰ
  (Gᴰ ∘ᴹᴰ Fᴰ) .F-obᴰ Aᴰ = Gᴰ .F-obᴰ (Fᴰ .F-obᴰ Aᴰ)
  (Gᴰ ∘ᴹᴰ Fᴰ) .F-homᴰ fᴰ = Gᴰ .F-homᴰ (Fᴰ .F-homᴰ fᴰ)
  (Gᴰ ∘ᴹᴰ Fᴰ) .F-varᴰ i e = Gᴰ .F-varᴰ i (Fᴰ .F-varᴰ i e)
  (Gᴰ ∘ᴹᴰ Fᴰ) .F-⋆ᴰ fᴰ gᴰ e =
    Gᴰ .F-⋆ᴰ (Fᴰ .F-homᴰ fᴰ) (λ i → Fᴰ .F-homᴰ (gᴰ i))
      (Fᴰ .F-⋆ᴰ fᴰ gᴰ e)

-- ==================================================================
-- The ford is equivalent to the naive law, in both directions.

module _
  {M : CartesianMulticategory ℓI ℓM ℓM'}
  {N : CartesianMulticategory ℓI ℓN ℓN'}
  {F : Multifunctor M N}
  {Mᴰ : CartesianMulticategoryᴰ M ℓMᴰ ℓMᴰ'}
  {Nᴰ : CartesianMulticategoryᴰ N ℓNᴰ ℓNᴰ'}
  (Fᴰ : Multifunctorᴰ F Mᴰ Nᴰ)
  where
  private
    module M = CartesianMulticategory M
    module N = CartesianMulticategory N
    module F = Multifunctor F
    module Mᴰ = CartesianMulticategoryᴰ Mᴰ
    module Nᴰ = CartesianMulticategoryᴰ Nᴰ

    module R {I : Type ℓI} {Γ : N.Ctx I} {A : N.ob}
      {Γᴰ : (i : I) → Nᴰ.obᴰ (Γ i)} {Aᴰ : Nᴰ.obᴰ A} =
      hSetReasoning (N.MHom⟨ I ⟩[ Γ , A ] , N.isSetMHom)
        (λ h → Nᴰ.MHomᴰ[ h ][ Γᴰ , Aᴰ ])

  -- the naive displayed law, recovered: base hom-types are sets, so
  -- the base path carried by the total-space path is F.F-var i.
  F-varᴰ→PathP : {I : Type ℓI} {Γ : M.Ctx I}
    {Γᴰ : (i : I) → Mᴰ.obᴰ (Γ i)} (i : I)
    → Fᴰ .F-homᴰ (Mᴰ.varᴰ {Γᴰ = Γᴰ} i) Nᴰ.≡[ F.F-var i ] Nᴰ.varᴰ i
  F-varᴰ→PathP i = R.Prectify (R.≡out (Fᴰ .F-varᴰ i refl))

  F-⋆ᴰ→PathP : {I J : Type ℓI} {Γ : M.Ctx I} {Δ : M.Ctx J} {A : M.ob}
    {Γᴰ : (i : I) → Mᴰ.obᴰ (Γ i)} {Δᴰ : (j : J) → Mᴰ.obᴰ (Δ j)}
    {Aᴰ : Mᴰ.obᴰ A}
    {f : M.MHom⟨ I ⟩[ Γ , A ]} {g : (i : I) → M.MHom⟨ J ⟩[ Δ , Γ i ]}
    (fᴰ : Mᴰ.MHomᴰ[ f ][ Γᴰ , Aᴰ ])
    (gᴰ : (i : I) → Mᴰ.MHomᴰ[ g i ][ Δᴰ , Γᴰ i ])
    → Fᴰ .F-homᴰ (fᴰ Mᴰ.⋆ᴰ gᴰ)
      Nᴰ.≡[ F.F-⋆ f g ] (Fᴰ .F-homᴰ fᴰ Nᴰ.⋆ᴰ (λ i → Fᴰ .F-homᴰ (gᴰ i)))
  F-⋆ᴰ→PathP fᴰ gᴰ = R.Prectify (R.≡out (Fᴰ .F-⋆ᴰ fᴰ gᴰ refl))

-- and conversely: the forded law is BUILT from the naive one, by
-- transporting the hypothesis along it.  (Here the _∙_ appears once,
-- in the builder — never again in any composite.)
module _
  {M : CartesianMulticategory ℓI ℓM ℓM'}
  {N : CartesianMulticategory ℓI ℓN ℓN'}
  {F : Multifunctor M N}
  {Mᴰ : CartesianMulticategoryᴰ M ℓMᴰ ℓMᴰ'}
  {Nᴰ : CartesianMulticategoryᴰ N ℓNᴰ ℓNᴰ'}
  where
  private
    module M = CartesianMulticategory M
    module N = CartesianMulticategory N
    module F = Multifunctor F
    module Mᴰ = CartesianMulticategoryᴰ Mᴰ
    module Nᴰ = CartesianMulticategoryᴰ Nᴰ

  module _
    (F-obᴰ : {A : M.ob} → Mᴰ.obᴰ A → Nᴰ.obᴰ (F.F-ob A))
    (F-homᴰ : {I : Type ℓI} {Γ : M.Ctx I} {A : M.ob}
      {Γᴰ : (i : I) → Mᴰ.obᴰ (Γ i)} {Aᴰ : Mᴰ.obᴰ A}
      {f : M.MHom⟨ I ⟩[ Γ , A ]}
      → Mᴰ.MHomᴰ[ f ][ Γᴰ , Aᴰ ]
      → Nᴰ.MHomᴰ[ F.F-hom f ][ (λ j → F-obᴰ (Γᴰ j)) , F-obᴰ Aᴰ ])
    where
    private
      ∫F : {I : Type ℓI} {Γ : M.Ctx I} {A : M.ob}
        {Γᴰ : (i : I) → Mᴰ.obᴰ (Γ i)} {Aᴰ : Mᴰ.obᴰ A}
        → ∫MHom Mᴰ Γᴰ Aᴰ
        → ∫MHom Nᴰ (λ j → F-obᴰ (Γᴰ j)) (F-obᴰ Aᴰ)
      ∫F z = F.F-hom (z .fst) , F-homᴰ (z .snd)

    fordVar : {I : Type ℓI} {Γ : M.Ctx I}
      {Γᴰ : (i : I) → Mᴰ.obᴰ (Γ i)} (i : I)
      → F-homᴰ (Mᴰ.varᴰ {Γᴰ = Γᴰ} i) Nᴰ.≡[ F.F-var i ] Nᴰ.varᴰ i
      → {u : M.MHom⟨ I ⟩[ Γ , Γ i ]}
        {uᴰ : Mᴰ.MHomᴰ[ u ][ Γᴰ , Γᴰ i ]}
      → Path (∫MHom Mᴰ Γᴰ (Γᴰ i)) (u , uᴰ) (M.var i , Mᴰ.varᴰ i)
      → Path (∫MHom Nᴰ (λ j → F-obᴰ (Γᴰ j)) (F-obᴰ (Γᴰ i)))
             (F.F-hom u , F-homᴰ uᴰ) (N.var i , Nᴰ.varᴰ i)
    fordVar i law e = cong ∫F e ∙ ΣPathP (F.F-var i , law)

    ford⋆ : {I J : Type ℓI} {Γ : M.Ctx I} {Δ : M.Ctx J} {A : M.ob}
      {Γᴰ : (i : I) → Mᴰ.obᴰ (Γ i)} {Δᴰ : (j : J) → Mᴰ.obᴰ (Δ j)}
      {Aᴰ : Mᴰ.obᴰ A}
      {f : M.MHom⟨ I ⟩[ Γ , A ]} {g : (i : I) → M.MHom⟨ J ⟩[ Δ , Γ i ]}
      (fᴰ : Mᴰ.MHomᴰ[ f ][ Γᴰ , Aᴰ ])
      (gᴰ : (i : I) → Mᴰ.MHomᴰ[ g i ][ Δᴰ , Γᴰ i ])
      → F-homᴰ (fᴰ Mᴰ.⋆ᴰ gᴰ)
        Nᴰ.≡[ F.F-⋆ f g ] (F-homᴰ fᴰ Nᴰ.⋆ᴰ (λ i → F-homᴰ (gᴰ i)))
      → {u : M.MHom⟨ J ⟩[ Δ , A ]} {uᴰ : Mᴰ.MHomᴰ[ u ][ Δᴰ , Aᴰ ]}
      → Path (∫MHom Mᴰ Δᴰ Aᴰ) (u , uᴰ) (f M.⋆ g , fᴰ Mᴰ.⋆ᴰ gᴰ)
      → Path (∫MHom Nᴰ (λ j → F-obᴰ (Δᴰ j)) (F-obᴰ Aᴰ))
             (F.F-hom u , F-homᴰ uᴰ)
             ( F.F-hom f N.⋆ (λ i → F.F-hom (g i))
             , F-homᴰ fᴰ Nᴰ.⋆ᴰ (λ i → F-homᴰ (gᴰ i)))
    ford⋆ {f = f} {g = g} fᴰ gᴰ law e =
      cong ∫F e ∙ ΣPathP (F.F-⋆ f g , law)

-- ==================================================================
-- MEASUREMENT: ∘ᴹᴰ is definitionally unital and associative, for
-- VARIABLE displayed multifunctors.
--
-- One caveat, and it is a caveat about the BASE, not about
-- Multifunctorᴰ: the record is indexed by the whole base multifunctor,
-- and the base Multifunctor is NOT forded, so Idᴹ N ∘ᴹ F is not
-- definitionally F — its F-var is cong (F-var) ∙ refl.  So the two
-- sides of a unit law do not even have the same TYPE on the nose.
--
-- Every field type, however, mentions the base only through F-ob and
-- F-hom, and those DO compose strictly.  So we may retype the
-- composite at F by copatterns — no transport is involved, each
-- clause is accepted by conversion alone — and then compare.  The
-- comparison is refl.

module _
  {M : CartesianMulticategory ℓI ℓM ℓM'}
  {N : CartesianMulticategory ℓI ℓN ℓN'}
  {F : Multifunctor M N}
  {Mᴰ : CartesianMulticategoryᴰ M ℓMᴰ ℓMᴰ'}
  {Nᴰ : CartesianMulticategoryᴰ N ℓNᴰ ℓNᴰ'}
  (Fᴰ : Multifunctorᴰ F Mᴰ Nᴰ)
  where
  -- (Idᴹᴰ ∘ᴹᴰ Fᴰ), retyped at F.  Each clause typechecks by
  -- conversion.
  IdL∘ : Multifunctorᴰ F Mᴰ Nᴰ
  IdL∘ .F-obᴰ = (Idᴹᴰ Nᴰ ∘ᴹᴰ Fᴰ) .F-obᴰ
  IdL∘ .F-homᴰ = (Idᴹᴰ Nᴰ ∘ᴹᴰ Fᴰ) .F-homᴰ
  IdL∘ .F-varᴰ = (Idᴹᴰ Nᴰ ∘ᴹᴰ Fᴰ) .F-varᴰ
  IdL∘ .F-⋆ᴰ = (Idᴹᴰ Nᴰ ∘ᴹᴰ Fᴰ) .F-⋆ᴰ

  ∘ᴹᴰIdL : IdL∘ ≡ Fᴰ
  ∘ᴹᴰIdL = refl

  IdR∘ : Multifunctorᴰ F Mᴰ Nᴰ
  IdR∘ .F-obᴰ = (Fᴰ ∘ᴹᴰ Idᴹᴰ Mᴰ) .F-obᴰ
  IdR∘ .F-homᴰ = (Fᴰ ∘ᴹᴰ Idᴹᴰ Mᴰ) .F-homᴰ
  IdR∘ .F-varᴰ = (Fᴰ ∘ᴹᴰ Idᴹᴰ Mᴰ) .F-varᴰ
  IdR∘ .F-⋆ᴰ = (Fᴰ ∘ᴹᴰ Idᴹᴰ Mᴰ) .F-⋆ᴰ

  ∘ᴹᴰIdR : IdR∘ ≡ Fᴰ
  ∘ᴹᴰIdR = refl

module _
  {M : CartesianMulticategory ℓI ℓM ℓM'}
  {N : CartesianMulticategory ℓI ℓN ℓN'}
  {P : CartesianMulticategory ℓI ℓP ℓP'}
  {Q : CartesianMulticategory ℓI ℓM ℓM'}
  {F : Multifunctor M N} {G : Multifunctor N P} {H : Multifunctor P Q}
  {Mᴰ : CartesianMulticategoryᴰ M ℓMᴰ ℓMᴰ'}
  {Nᴰ : CartesianMulticategoryᴰ N ℓNᴰ ℓNᴰ'}
  {Pᴰ : CartesianMulticategoryᴰ P ℓPᴰ ℓPᴰ'}
  {Qᴰ : CartesianMulticategoryᴰ Q ℓMᴰ ℓMᴰ'}
  (Fᴰ : Multifunctorᴰ F Mᴰ Nᴰ) (Gᴰ : Multifunctorᴰ G Nᴰ Pᴰ)
  (Hᴰ : Multifunctorᴰ H Pᴰ Qᴰ)
  where
  -- same caveat, same cure: (H ∘ᴹ G) ∘ᴹ F and H ∘ᴹ (G ∘ᴹ F) differ
  -- definitionally in their LAWS (_∙_ is not strictly associative and
  -- cong does not strictly distribute over it), which is a defect of
  -- the unforded base, not of Multifunctorᴰ.  Retyping by copatterns
  -- costs nothing: every clause is accepted by conversion.
  AssocL : Multifunctorᴰ (H ∘ᴹ (G ∘ᴹ F)) Mᴰ Qᴰ
  AssocL .F-obᴰ = ((Hᴰ ∘ᴹᴰ Gᴰ) ∘ᴹᴰ Fᴰ) .F-obᴰ
  AssocL .F-homᴰ = ((Hᴰ ∘ᴹᴰ Gᴰ) ∘ᴹᴰ Fᴰ) .F-homᴰ
  AssocL .F-varᴰ = ((Hᴰ ∘ᴹᴰ Gᴰ) ∘ᴹᴰ Fᴰ) .F-varᴰ
  AssocL .F-⋆ᴰ = ((Hᴰ ∘ᴹᴰ Gᴰ) ∘ᴹᴰ Fᴰ) .F-⋆ᴰ

  ∘ᴹᴰAssoc : AssocL ≡ Hᴰ ∘ᴹᴰ (Gᴰ ∘ᴹᴰ Fᴰ)
  ∘ᴹᴰAssoc = refl
