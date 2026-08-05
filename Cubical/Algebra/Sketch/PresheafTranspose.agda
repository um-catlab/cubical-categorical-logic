{-

  The transpose, and the functorial form of "a model of a sketch in
  presheaves is a presheaf of models".

  `Cubical.Algebra.Sketch.Presheaf` proves the *pointwise*
  characterisation

    isModel S (PRESHEAF C ℓ) M ≃ (∀ c → isModel S (SET ℓ) (evPsh c ∘F M)),

  and leaves open the transpose that upgrades it to the slogan.  This
  file supplies the transpose

    Functor D (PRESHEAF C ℓ) ≅ Functor (C ^op) (FUNCTOR D (SET ℓ))

  (`transposeIso`) and assembles the two into

    Model S (PRESHEAF C ℓ) ≃ Functor (C ^op) (MODEL S (SET ℓ))

  (`modelInPresheaves≃presheafOfModelsF`).

  The transpose is built directly rather than through `curryF`: there
  is no product category, no `_×C_` symmetry and no transport along
  `PshHom≅PshHomStrict`, because every component is already available
  on the nose.  Going right, the restriction maps of the presheaves
  `M ⟅ x ⟆` assemble into a natural transformation whose naturality is
  *literally* the forded `PshHomStrict.N-hom` of `M ⟪ f ⟫`; going
  left, the forded naturality of `M ⟪ f ⟫` is *literally* the
  naturality of `N ⟪ g ⟫`.  The two directions exchange the roles of
  the two naturality squares and nothing else.

  Both round trips would be `refl` if `Functor` had eta; since it is
  declared `no-eta-equality` they are `Functor≡` applied to families
  of `refl`s.  The resulting paths are constant on `F-ob` and `F-hom`,
  so the `PathP`s over them still hold by `refl` in the `N-ob`
  component, and the naturality components follow because naturality
  is a proposition (`makeNatTransPathP`, and `makePshHomStrictPathP`,
  which is defined here).

  Everything is then upgraded from bijections to isomorphisms of
  categories, in the unambiguous "fully faithful and bijective on
  objects" form:

    * `transposeFunctor`, `isFullyFaithfulTransposeFunctor`,
      `isEquivF-obTransposeFunctor` for the transpose itself;
    * `modelTransposeFunctor`, `isFullyFaithfulModelTransposeFunctor`,
      `isEquivF-obModelTransposeFunctor` for models.

  For the model-level statement the hypotheses of `Presheaf.agda` are
  carried unchanged (`limSET`, `colimSET`), since the direction
  "model in presheaves ⟹ pointwise model" needs `SET ℓ` to have
  (co)limits of the sketch's shapes.  Landing in `MODEL` costs nothing
  extra: `isModel` is a proposition and `MODEL` is a *full*
  subcategory, so its morphisms are the morphisms of `FUNCTOR ind E`
  verbatim and `transposeNat` applies to them unchanged.

-}
module Cubical.Algebra.Sketch.PresheafTranspose where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.FullSubcategory
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.StrictHom.Pointwise
open import Cubical.Categories.Presheaf.StrictHom.PointwiseColim
open import Cubical.Categories.Limits.Limits

open import Cubical.Algebra.Sketch.Base
open import Cubical.Algebra.Sketch.Presheaf
open import Cubical.Algebra.Sketch.Instances.Magma

private
  variable
    ℓB ℓB' ℓD ℓD' ℓC ℓC' ℓE ℓE' ℓP ℓ : Level
    ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' : Level

open Category
open Functor
open NatTrans
open PshHomStrict

module _ {D : Category ℓD ℓD'} {C : Category ℓC ℓC'} {ℓ : Level} where

  module _ (M : Functor D (PRESHEAF C ℓ)) where

    transposeNT : {c c' : C .ob} (g : (C ^op) [ c , c' ])
                → NatTrans (evPsh c ∘F M) (evPsh c' ∘F M)
    transposeNT g .N-ob x = (M ⟅ x ⟆) .F-hom g
    transposeNT {c} {c'} g .N-hom {x} {y} f =
      funExt λ p → (M ⟪ f ⟫) .N-hom c' c g p _ refl

    transposeF : Functor (C ^op) (FUNCTOR D (SET ℓ))
    transposeF .F-ob c = evPsh c ∘F M
    transposeF .F-hom = transposeNT
    transposeF .F-id = makeNatTransPath (funExt λ x → (M ⟅ x ⟆) .F-id)
    transposeF .F-seq g h =
      makeNatTransPath (funExt λ x → (M ⟅ x ⟆) .F-seq g h)

  module _ (N : Functor (C ^op) (FUNCTOR D (SET ℓ))) where

    untransposePsh : (x : D .ob) → Presheaf C ℓ
    untransposePsh x .F-ob c = (N ⟅ c ⟆) ⟅ x ⟆
    untransposePsh x .F-hom g = (N ⟪ g ⟫) .N-ob x
    untransposePsh x .F-id = cong (λ α → α .N-ob x) (N .F-id)
    untransposePsh x .F-seq g h = cong (λ α → α .N-ob x) (N .F-seq g h)

    untransposeHom : {x y : D .ob} (f : D [ x , y ])
                   → PshHomStrict (untransposePsh x) (untransposePsh y)
    untransposeHom f .N-ob c = (N ⟅ c ⟆) ⟪ f ⟫
    untransposeHom f .N-hom c c' g p' p eq =
      funExt⁻ ((N ⟪ g ⟫) .N-hom f) p' ∙ cong ((N ⟅ c ⟆) ⟪ f ⟫) eq

    untransposeF : Functor D (PRESHEAF C ℓ)
    untransposeF .F-ob = untransposePsh
    untransposeF .F-hom = untransposeHom
    untransposeF .F-id =
      makePshHomStrictPath (funExt λ c → (N ⟅ c ⟆) .F-id)
    untransposeF .F-seq f f' =
      makePshHomStrictPath (funExt λ c → (N ⟅ c ⟆) .F-seq f f')

  -- The `PshHomStrict` analogue of `makeNatTransPathP`: naturality is
  -- proposition-valued, so a `PathP` of strict presheaf morphisms over
  -- paths of their (co)domains is determined by its `N-ob` component.
  module _ {P P' : Presheaf C ℓ} {Q Q' : Presheaf C ℓ}
           {α : PshHomStrict P Q} {β : PshHomStrict P' Q'} where
    makePshHomStrictPathP : (p : P ≡ P') (q : Q ≡ Q')
      → PathP (λ i → PshHomStrictN-obTy (p i) (q i)) (α .N-ob) (β .N-ob)
      → PathP (λ i → PshHomStrict (p i) (q i)) α β
    makePshHomStrictPathP p q h i .N-ob = h i
    makePshHomStrictPathP p q h i .N-hom =
      isProp→PathP (λ j → isPropN-hom (p j) (q j) (h j))
        (α .N-hom) (β .N-hom) i

  untransposeF∘transposeF : (M : Functor D (PRESHEAF C ℓ))
                          → untransposeF (transposeF M) ≡ M
  untransposeF∘transposeF M = Functor≡ obPath homPath
    where
      obPath : ∀ x → untransposePsh (transposeF M) x ≡ M ⟅ x ⟆
      obPath x = Functor≡ (λ c → refl) (λ g → refl)

      homPath : {x y : D .ob} (f : D [ x , y ])
        → PathP (λ i → PshHomStrict (obPath x i) (obPath y i))
                (untransposeHom (transposeF M) f) (M ⟪ f ⟫)
      homPath {x} {y} f = makePshHomStrictPathP (obPath x) (obPath y) refl

  transposeF∘untransposeF : (N : Functor (C ^op) (FUNCTOR D (SET ℓ)))
                          → transposeF (untransposeF N) ≡ N
  transposeF∘untransposeF N = Functor≡ obPath homPath
    where
      obPath : ∀ c → evPsh c ∘F untransposeF N ≡ N ⟅ c ⟆
      obPath c = Functor≡ (λ x → refl) (λ f → refl)

      homPath : {c c' : C .ob} (g : (C ^op) [ c , c' ])
        → PathP (λ i → NatTrans (obPath c i) (obPath c' i))
                (transposeNT (untransposeF N) g) (N ⟪ g ⟫)
      homPath {c} {c'} g = makeNatTransPathP (obPath c) (obPath c') refl

  -- The transpose: a functor into presheaves is a presheaf of functors.
  transposeIso : Iso (Functor D (PRESHEAF C ℓ))
                     (Functor (C ^op) (FUNCTOR D (SET ℓ)))
  transposeIso .Iso.fun = transposeF
  transposeIso .Iso.inv = untransposeF
  transposeIso .Iso.sec = transposeF∘untransposeF
  transposeIso .Iso.ret = untransposeF∘transposeF

  transposeEquiv : Functor D (PRESHEAF C ℓ)
                 ≃ Functor (C ^op) (FUNCTOR D (SET ℓ))
  transposeEquiv = isoToEquiv transposeIso

  -- The transpose is not merely a bijection on objects: it is an
  -- isomorphism of functor *categories*.  A natural transformation
  -- `M ⇒ M'` (components strict presheaf morphisms) is the same data
  -- as a natural transformation `transposeF M ⇒ transposeF M'`, since
  -- both amount to a family of functions indexed by `D .ob × C .ob`
  -- natural in each variable separately; the two naturality squares
  -- just swap roles.
  module _ {M M' : Functor D (PRESHEAF C ℓ)} where

    transposeNat : NatTrans M M'
                 → NatTrans (transposeF M) (transposeF M')
    transposeNat θ .N-ob c .N-ob x = (θ .N-ob x) .N-ob c
    transposeNat θ .N-ob c .N-hom f = cong (λ α → α .N-ob c) (θ .N-hom f)
    transposeNat θ .N-hom {c} {c'} g =
      makeNatTransPath (funExt λ x → funExt λ p →
        sym ((θ .N-ob x) .N-hom c' c g p _ refl))

    untransposeNat : NatTrans (transposeF M) (transposeF M')
                   → NatTrans M M'
    untransposeNat Θ .N-ob x .N-ob c = (Θ .N-ob c) .N-ob x
    untransposeNat Θ .N-ob x .N-hom c c' g p' p eq =
      sym (funExt⁻ (cong (λ α → α .N-ob x) (Θ .N-hom g)) p')
      ∙ cong ((Θ .N-ob c) .N-ob x) eq
    untransposeNat Θ .N-hom f =
      makePshHomStrictPath (funExt λ c → (Θ .N-ob c) .N-hom f)

    transposeNatIso : Iso (NatTrans M M')
                          (NatTrans (transposeF M) (transposeF M'))
    transposeNatIso .Iso.fun = transposeNat
    transposeNatIso .Iso.inv = untransposeNat
    transposeNatIso .Iso.sec Θ =
      makeNatTransPath (funExt λ c → makeNatTransPath refl)
    transposeNatIso .Iso.ret θ =
      makeNatTransPath (funExt λ x → makePshHomStrictPath refl)

  transposeFunctor : Functor (FUNCTOR D (PRESHEAF C ℓ))
                             (FUNCTOR (C ^op) (FUNCTOR D (SET ℓ)))
  transposeFunctor .F-ob = transposeF
  transposeFunctor .F-hom = transposeNat
  transposeFunctor .F-id =
    makeNatTransPath (funExt λ c → makeNatTransPath refl)
  transposeFunctor .F-seq θ θ' =
    makeNatTransPath (funExt λ c → makeNatTransPath refl)

  isFullyFaithfulTransposeFunctor : isFullyFaithful transposeFunctor
  isFullyFaithfulTransposeFunctor M M' = isoToIsEquiv transposeNatIso

  -- ... and bijective on objects, since `transposeFunctor .F-ob` is
  -- literally `transposeF`.  Fully faithful + bijective on objects is
  -- an isomorphism of categories.
  isEquivF-obTransposeFunctor : isEquiv (transposeFunctor .F-ob)
  isEquivF-obTransposeFunctor = transposeEquiv .snd

-- A functor into a full subcategory is exactly a functor into the
-- ambient category that lands in the subcategory: the objects of
-- `FullSubcategory E P` are pairs, but its homs, identities and
-- composites are literally those of `E`, so only the object part
-- changes and nothing has to be transported.
module _ {B : Category ℓB ℓB'} {E : Category ℓE ℓE'}
         (P : E .ob → Type ℓP) where

  fullSubFunctor→ : Functor B (FullSubcategory E P) → Functor B E
  fullSubFunctor→ G .F-ob b = (G ⟅ b ⟆) .fst
  fullSubFunctor→ G .F-hom = G .F-hom
  fullSubFunctor→ G .F-id = G .F-id
  fullSubFunctor→ G .F-seq = G .F-seq

  fullSubFunctor← : (F : Functor B E) → (∀ b → P (F ⟅ b ⟆))
                  → Functor B (FullSubcategory E P)
  fullSubFunctor← F p .F-ob b = F ⟅ b ⟆ , p b
  fullSubFunctor← F p .F-hom = F .F-hom
  fullSubFunctor← F p .F-id = F .F-id
  fullSubFunctor← F p .F-seq = F .F-seq

  fullSubFunctorIso :
    Iso (Functor B (FullSubcategory E P))
        (Σ[ F ∈ Functor B E ] (∀ b → P (F ⟅ b ⟆)))
  fullSubFunctorIso .Iso.fun G =
    fullSubFunctor→ G , λ b → (G ⟅ b ⟆) .snd
  fullSubFunctorIso .Iso.inv (F , p) = fullSubFunctor← F p
  fullSubFunctorIso .Iso.sec (F , p) =
    ΣPathP (Functor≡ (λ _ → refl) (λ _ → refl) , refl)
  fullSubFunctorIso .Iso.ret G = Functor≡ (λ _ → refl) (λ _ → refl)

  fullSubFunctor→← : (F : Functor B E) (p : ∀ b → P (F ⟅ b ⟆))
                   → fullSubFunctor→ (fullSubFunctor← F p) ≡ F
  fullSubFunctor→← F p = Functor≡ (λ _ → refl) (λ _ → refl)

-- The slogan, in its functorial form: a model of `S` in presheaves on
-- `C` *is* a presheaf of models of `S` in sets.  Combining
--
--   * `isModel-pointwise`, which says that being a model in presheaves
--     is the property of being pointwise a model in sets, and
--   * `transposeIso`, which says that the underlying functor
--     `ind → PRESHEAF C ℓ` is the same data as a functor
--     `C ^op → FUNCTOR ind (SET ℓ)`,
--
-- and using that `MODEL` is a *full* subcategory, so that landing in
-- it is a property of the underlying functor and nothing more.
module _ (S : Sketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ')
         {C : Category ℓC ℓC'} {ℓ : Level}
         (limSET : ∀ (i : Sketch.LIdx S)
                     (D : Functor (Sketch.LShape S i) (SET ℓ)) → LimCone D)
         (colimSET : ∀ (i : Sketch.CIdx S)
                       (D : Functor ((Sketch.CShape S i) ^op) (SET ℓ))
                     → ColimCocone D) where
  open Sketch S

  private
    isModelᶜ : Functor (C ^op) (FUNCTOR ind (SET ℓ)) → Type _
    isModelᶜ N = ∀ (c : C .ob) → isModel S (SET ℓ) (N ⟅ c ⟆)

    step₁ : Model S (PRESHEAF C ℓ)
          ≃ (Σ[ M ∈ Functor ind (PRESHEAF C ℓ) ]
               (∀ (c : C .ob) → isModel S (SET ℓ) (evPsh c ∘F M)))
    step₁ = Σ-cong-equiv-snd λ M → isModel-pointwise S M limSET colimSET

    step₂ : (Σ[ M ∈ Functor ind (PRESHEAF C ℓ) ]
               (∀ (c : C .ob) → isModel S (SET ℓ) (evPsh c ∘F M)))
          ≃ (Σ[ N ∈ Functor (C ^op) (FUNCTOR ind (SET ℓ)) ] isModelᶜ N)
    step₂ = Σ-cong-equiv-fst {B = isModelᶜ} transposeEquiv

    step₃ : (Σ[ N ∈ Functor (C ^op) (FUNCTOR ind (SET ℓ)) ] isModelᶜ N)
          ≃ Functor (C ^op) (MODEL S (SET ℓ))
    step₃ = invEquiv (isoToEquiv (fullSubFunctorIso (isModel S (SET ℓ))))

  modelInPresheaves≃presheafOfModelsF :
    Model S (PRESHEAF C ℓ) ≃ Functor (C ^op) (MODEL S (SET ℓ))
  modelInPresheaves≃presheafOfModelsF = step₁ ∙ₑ step₂ ∙ₑ step₃

  -- The same statement, phrased so that the slogan is visible: the
  -- objects of the category of models of `S` in presheaves on `C` are
  -- exactly the presheaves on `C` valued in models of `S` in sets.
  -- (`Model S E` is by definition `MODEL S E .ob`.)
  modelInPresheaves≃presheafOfModelsOb :
    MODEL S (PRESHEAF C ℓ) .ob ≃ Functor (C ^op) (MODEL S (SET ℓ))
  modelInPresheaves≃presheafOfModelsOb = modelInPresheaves≃presheafOfModelsF

  -- The same equivalence again, but with its two maps spelled out
  -- rather than assembled from the chain above, so that they reduce.
  -- This is what lets the object part below be the object part of an
  -- actual functor.
  private
    P' : Functor ind (SET ℓ) → Type _
    P' = isModel S (SET ℓ)

    undF : Functor (C ^op) (MODEL S (SET ℓ))
         → Functor (C ^op) (FUNCTOR ind (SET ℓ))
    undF G = fullSubFunctor→ P' G

    obPathG : (G : Functor (C ^op) (MODEL S (SET ℓ))) (c : C .ob)
            → evPsh c ∘F untransposeF (undF G) ≡ (G ⟅ c ⟆) .fst
    obPathG G c = Functor≡ (λ x → refl) (λ f → refl)

  modelTransposeObIso :
    Iso (Model S (PRESHEAF C ℓ)) (Functor (C ^op) (MODEL S (SET ℓ)))
  modelTransposeObIso .Iso.fun (M , pf) =
    fullSubFunctor← P' (transposeF M)
      (isModel-toPointwise S M limSET colimSET pf)
  modelTransposeObIso .Iso.inv G =
      untransposeF (undF G)
    , isModel-fromPointwise S (untransposeF (undF G))
        (λ c → subst P' (sym (obPathG G c)) ((G ⟅ c ⟆) .snd))
  modelTransposeObIso .Iso.sec G =
    Functor≡ (λ c → Σ≡Prop (isPropIsModel S (SET ℓ)) (obPathG G c))
             (λ {c} {c'} g →
                makeNatTransPathP (obPathG G c) (obPathG G c') refl)
  modelTransposeObIso .Iso.ret (M , pf) =
    Σ≡Prop (isPropIsModel S (PRESHEAF C ℓ))
      (cong untransposeF (fullSubFunctor→← P' (transposeF M) _)
       ∙ untransposeF∘transposeF M)

  -- ... and this bijection on objects is the object part of an
  -- isomorphism of *categories*.  `MODEL` is full on both sides, so a
  -- morphism of models is just a natural transformation of the
  -- underlying functors and `transposeNat` applies verbatim.
  modelTransposeFunctor :
    Functor (MODEL S (PRESHEAF C ℓ)) (FUNCTOR (C ^op) (MODEL S (SET ℓ)))
  modelTransposeFunctor .F-ob = modelTransposeObIso .Iso.fun
  modelTransposeFunctor .F-hom θ .N-ob = transposeNat θ .N-ob
  modelTransposeFunctor .F-hom θ .N-hom = transposeNat θ .N-hom
  modelTransposeFunctor .F-id =
    makeNatTransPath (funExt λ c → makeNatTransPath refl)
  modelTransposeFunctor .F-seq θ θ' =
    makeNatTransPath (funExt λ c → makeNatTransPath refl)

  isFullyFaithfulModelTransposeFunctor :
    isFullyFaithful modelTransposeFunctor
  isFullyFaithfulModelTransposeFunctor x y = isoToIsEquiv theIso
    where
      theIso : Iso (MODEL S (PRESHEAF C ℓ) [ x , y ])
                   (FUNCTOR (C ^op) (MODEL S (SET ℓ))
                     [ modelTransposeFunctor ⟅ x ⟆
                     , modelTransposeFunctor ⟅ y ⟆ ])
      theIso .Iso.fun = modelTransposeFunctor .F-hom {x} {y}
      theIso .Iso.inv Θ =
        untransposeNat {M = x .fst} {M' = y .fst}
          (natTrans (Θ .N-ob) (Θ .N-hom))
      theIso .Iso.sec Θ =
        makeNatTransPath (funExt λ c → makeNatTransPath refl)
      theIso .Iso.ret θ =
        makeNatTransPath (funExt λ v → makePshHomStrictPath refl)

  isEquivF-obModelTransposeFunctor :
    isEquiv (modelTransposeFunctor .F-ob)
  isEquivF-obModelTransposeFunctor = isoToIsEquiv modelTransposeObIso

-- The magma sketch again: both hypotheses are discharged outright, so
-- a magma in presheaves on `C` is exactly a presheaf of magmas.
module _ {C : Category ℓC ℓC'} where
  magmaInPresheaves≃presheafOfMagmasF :
      Model MagmaSketch (PRESHEAF C ℓ-zero)
    ≃ Functor (C ^op) (MODEL MagmaSketch (SET ℓ-zero))
  magmaInPresheaves≃presheafOfMagmasF =
    modelInPresheaves≃presheafOfModelsF MagmaSketch
      (λ _ D → completeSET Two D) (λ ())
