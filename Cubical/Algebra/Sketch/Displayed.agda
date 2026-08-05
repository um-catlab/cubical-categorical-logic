{-

  Models of a sketch as a category DISPLAYED over the category of
  carriers, in the style of `Cubical.Algebra.Theory.Category`.

  There, `MODᴰ` is displayed over `SET`: the base is the *carrier*, the
  displayed objects are the *operations*, and the displayed morphisms
  are the (prop-valued, forded) homomorphism condition, so that all
  three displayed laws are `refl`.

  The sketch analogue is:

    base           the object assignment, one object of `E` for each
                   object of the index category
    displayed ob   the action on index morphisms, its functoriality,
                   and the model condition on the designated
                   (co)cones
    displayed hom  naturality of a family with respect to the actions

  WHY THE BASE IS `FAM (YonedaStrictify E)` AND NOT `FAM E`.

  For the displayed laws to be `refl`, the naturality condition must be
  *forded* so that `idᴰ` is the identity function on proofs and `_⋆ᴰ_`
  is composition of proofs -- exactly as `Homo.op-hom` is forded in
  `Cubical.Algebra.Theory` and `PshHomStrict.N-hom` in
  `Cubical.Categories.Presheaf.StrictHom.Base`.  Stacking two
  naturality squares, however, uses the *unit and associativity laws of
  the ambient category*.  With `E` arbitrary those laws are honest
  paths, so `idᴰ` must insert `E .⋆IdL`/`E .⋆IdR` and `_⋆ᴰ_` must
  insert `E .⋆Assoc`, and then `⋆IdLᴰ` cannot be `refl`.  (This is not
  hypothetical: the naive version fails with
  `[MetaCannotDependOn] ... since it contains the variable i`, because
  the PathP is over `Carrier .⋆IdL`, which is not `refl`.)

  `Cubical.Algebra.Theory.Category` does not hit this because its base
  is `SET`, whose `⋆IdL`/`⋆IdR`/`⋆Assoc` *are* `refl`.

  The repository's own answer to this is `YonedaStrictify`
  (`Cubical.Categories.Instances.Strictification`): the full image of
  the strict Yoneda embedding `YOStrict : Functor E (PRESHEAF E ℓE')`.
  It has the same objects as `E`, is fully faithfully isomorphic to `E`
  on homs, and its `⋆IdL`, `⋆IdR`, `⋆Assoc` are literally `refl`
  (inherited from the strict presheaf category, whose morphisms are
  `PshHomStrict`s -- functions on generalized elements with a forded
  naturality clause).  Taking the base to be `FAM (YonedaStrictify E)`
  therefore keeps the intended shape (`Carrier .ob` is *definitionally*
  `ind .ob → E .ob`) while making all three displayed laws `refl`.  The
  only concession is that `Carrier [ X , Y ]` is
  `(x : ind .ob) → 𝔼 [ X x , Y x ]` rather than
  `(x : ind .ob) → E [ X x , Y x ]`; the two are fully faithfully
  isomorphic, and `fromStrict` translates back.

  Contents:

    FAM            the family category over any `E`
    MODELᴰ         models displayed over `Carrier = FAM 𝔼 (ind .ob)`,
                   with `⋆IdLᴰ`, `⋆IdRᴰ`, `⋆Assocᴰ` all `refl`
    MODEL∫         `∫C MODELᴰ`, with projection `ForgetToCarrier = Fst`
    ModelObIso     `Iso (MODEL∫ .ob) (Model S E)`: the displayed
                   notion of model agrees with `Base.agda`'s
    ∫→MODEL        `Functor MODEL∫ (MODEL S E)`

-}
module Cubical.Algebra.Sketch.Displayed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.FullImage
open import Cubical.Categories.Instances.Strictification
open import Cubical.Categories.Presheaf.StrictHom.Base
  using (PshHomStrict ; YOStrict ; isFullyFaithfulYOStrict
        ; makePshHomStrictPath)
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Instances.TotalCategory

open import Cubical.Algebra.Sketch.Base

private
  variable
    ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' ℓE ℓE' ℓI : Level

open Category
open Functor
open PshHomStrict

-- The category of families: one object of `E` for each element of `I`,
-- and a family of morphisms between them.  Laws are `E`'s laws
-- componentwise, hence `refl` whenever `E`'s are.
module _ (E : Category ℓE ℓE') (I : Type ℓI) where
  FAM : Category (ℓ-max ℓI ℓE) (ℓ-max ℓI ℓE')
  FAM .ob = I → E .ob
  FAM .Hom[_,_] X Y = (i : I) → E [ X i , Y i ]
  FAM .id i = E .id
  FAM ._⋆_ f g i = f i ⋆⟨ E ⟩ g i
  FAM .⋆IdL f = funExt (λ i → E .⋆IdL (f i))
  FAM .⋆IdR f = funExt (λ i → E .⋆IdR (f i))
  FAM .⋆Assoc f g h = funExt (λ i → E .⋆Assoc (f i) (g i) (h i))
  FAM .isSetHom = isSetΠ (λ i → E .isSetHom)

module _ (S : Sketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ')
         (E : Category ℓE ℓE') where
  open Sketch S

  -- `𝔼` has the same objects as `E` and strictly composing morphisms
  𝔼 : Category ℓE (ℓ-max ℓE ℓE')
  𝔼 = YonedaStrictify E

  toStrict : Functor E 𝔼
  toStrict = toYonedaStrictify E

  fromStrict : Functor 𝔼 E
  fromStrict = fromYonedaStrictify E

  -- the base: `Carrier .ob = ind .ob → E .ob`
  Carrier : Category (ℓ-max ℓS ℓE) (ℓ-max ℓS (ℓ-max ℓE ℓE'))
  Carrier = FAM 𝔼 (ind .ob)

  ----------------------------------------------------------------
  -- displayed objects: the model structure over a carrier
  ----------------------------------------------------------------

  ActOn : (X : ind .ob → E .ob) → Type _
  ActOn X = {x y : ind .ob} → ind [ x , y ] → 𝔼 [ X x , X y ]

  -- Functoriality, forded exactly like `Homo.op-hom` /
  -- `StrictFunctor.F-id`: the composite is a variable together with a
  -- proof that it is the composite.
  isFunctorialAct : {X : ind .ob → E .ob} → ActOn X → Type _
  isFunctorialAct {X} act =
    ({x : ind .ob} (f : ind [ x , x ]) → ind .id ≡ f → act f ≡ 𝔼 .id)
    × ({x y z : ind .ob} (f : ind [ x , y ]) (g : ind [ y , z ])
       (h : ind [ x , z ]) → f ⋆⟨ ind ⟩ g ≡ h
       → act h ≡ act f ⋆⟨ 𝔼 ⟩ act g)

  isPropIsFunctorialAct : {X : ind .ob → E .ob} (act : ActOn X)
                        → isProp (isFunctorialAct act)
  isPropIsFunctorialAct act =
    isProp× (isPropImplicitΠ (λ _ → isPropΠ2 (λ _ _ → 𝔼 .isSetHom _ _)))
            (isPropImplicitΠ3
              (λ _ _ _ → isPropΠ4 (λ _ _ _ _ → 𝔼 .isSetHom _ _)))

  ModelStr : (X : ind .ob → E .ob) → Type _
  ModelStr X = Σ[ act ∈ ActOn X ] isFunctorialAct act

  -- unfording: a model structure is a functor into `𝔼`
  toFunctorS : {X : ind .ob → E .ob} → ModelStr X → Functor ind 𝔼
  toFunctorS {X} B .F-ob = X
  toFunctorS B .F-hom = B .fst
  toFunctorS B .F-id = B .snd .fst _ refl
  toFunctorS B .F-seq f g = B .snd .snd f g _ refl

  -- ... hence a functor into `E`, with the same object part
  toFunctorE : {X : ind .ob → E .ob} → ModelStr X → Functor ind E
  toFunctorE B = fromStrict ∘F toFunctorS B

  -- displayed objects
  ModelOb : (X : ind .ob → E .ob) → Type _
  ModelOb X = Σ[ B ∈ ModelStr X ] isModel S E (toFunctorE B)

  ----------------------------------------------------------------
  -- displayed morphisms: forded naturality
  ----------------------------------------------------------------

  -- `α x .N-ob c` is the action of `α x` on generalized elements
  -- `E [ c , X x ]`.  The clause below is the naturality square for
  -- `α` at `f`, forded on the `B`-image of the element.
  isNatFam : {X Y : ind .ob → E .ob} (α : Carrier [ X , Y ])
             (B : ModelStr X) (C : ModelStr Y) → Type _
  isNatFam {X} {Y} α B C =
    {x y : ind .ob} (f : ind [ x , y ]) (c : E .ob)
    (h : E [ c , X x ]) (p : E [ c , X y ])
    → B .fst f .N-ob c h ≡ p
    → C .fst f .N-ob c (α x .N-ob c h) ≡ α y .N-ob c p

  isPropIsNatFam : {X Y : ind .ob → E .ob} (α : Carrier [ X , Y ])
                   (B : ModelStr X) (C : ModelStr Y)
                 → isProp (isNatFam α B C)
  isPropIsNatFam α B C =
    isPropImplicitΠ2
      (λ _ _ → isPropΠ4 (λ _ _ _ _ → isPropΠ (λ _ → E .isSetHom _ _)))

  private
    idNatFam : {X : ind .ob → E .ob} (B : ModelStr X)
             → isNatFam (Carrier .id) B B
    idNatFam B f c h p e = e

    seqNatFam : {X Y Z : ind .ob → E .ob}
                {α : Carrier [ X , Y ]} {β : Carrier [ Y , Z ]}
                {B : ModelStr X} {C : ModelStr Y} {D : ModelStr Z}
              → isNatFam α B C → isNatFam β C D
              → isNatFam (α ⋆⟨ Carrier ⟩ β) B D
    seqNatFam {α = α} ϕ ψ {x} {y} f c h p e =
      ψ f c (α x .N-ob c h) (α y .N-ob c p) (ϕ f c h p e)

  MODELᴰ : Categoryᴰ Carrier _ _
  MODELᴰ .Categoryᴰ.ob[_] = ModelOb
  MODELᴰ .Categoryᴰ.Hom[_][_,_] α B C = isNatFam α (B .fst) (C .fst)
  -- objects are not recoverable from the (defined) hom types, so the
  -- implicits are pinned by hand
  MODELᴰ .Categoryᴰ.idᴰ {x = X} {p = B} = idNatFam {X = X} (B .fst)
  MODELᴰ .Categoryᴰ._⋆ᴰ_ {x = X} {y = Y} {z = Z} {f = α} {g = β}
    {xᴰ = B} {yᴰ = C} {zᴰ = D} =
    seqNatFam {X = X} {Y = Y} {Z = Z} {α = α} {β = β}
      {B = B .fst} {C = C .fst} {D = D .fst}
  MODELᴰ .Categoryᴰ.⋆IdLᴰ _ = refl
  MODELᴰ .Categoryᴰ.⋆IdRᴰ _ = refl
  MODELᴰ .Categoryᴰ.⋆Assocᴰ _ _ _ = refl
  MODELᴰ .Categoryᴰ.isSetHomᴰ {x = X} {y = Y} {f = α} {xᴰ = B} {yᴰ = C} =
    isProp→isSet (isPropIsNatFam {X = X} {Y = Y} α (B .fst) (C .fst))

  MODEL∫ : Category _ _
  MODEL∫ = ∫C MODELᴰ

  -- the projection to the carriers
  ForgetToCarrier : Functor MODEL∫ Carrier
  ForgetToCarrier = Fst

  ----------------------------------------------------------------
  -- comparison with `Cubical.Algebra.Sketch.Base`
  ----------------------------------------------------------------

  fromFunctorS : (M : Functor ind 𝔼) → ModelStr (M .F-ob)
  fromFunctorS M .fst = M .F-hom
  fromFunctorS M .snd .fst f e = cong (M .F-hom) (sym e) ∙ M .F-id
  fromFunctorS M .snd .snd f g h e =
    cong (M .F-hom) (sym e) ∙ M .F-seq f g

  toFromFunctorS : (M : Functor ind 𝔼) → toFunctorS (fromFunctorS M) ≡ M
  toFromFunctorS M = Functor≡ (λ _ → refl) (λ _ → refl)

  -- a model in the sense of `Base.agda` gives a model structure on its
  -- object part
  mkModelStr : (M : Functor ind E) → ModelStr (M .F-ob)
  mkModelStr M = fromFunctorS (toStrict ∘F M)

  toFunctorE-mkModelStr : (M : Functor ind E) → toFunctorE (mkModelStr M) ≡ M
  toFunctorE-mkModelStr M =
    cong (fromStrict ∘F_) (toFromFunctorS (toStrict ∘F M))
    ∙ F-assoc {F = M} {G = toStrict} {H = fromStrict}
    ∙ cong (_∘F M) (fromYonedaStrictify∘toYonedaStrictify≡Id E)
    ∙ F-rUnit

  -- ... and conversely.  The two notions of model agree.
  ModelObIso : Iso (MODEL∫ .ob) (Model S E)
  ModelObIso .Iso.fun (X , B , m) = toFunctorE B , m
  ModelObIso .Iso.inv (M , m) =
    M .F-ob , mkModelStr M
            , subst (isModel S E) (sym (toFunctorE-mkModelStr M)) m
  ModelObIso .Iso.sec (M , m) =
    Σ≡Prop (isPropIsModel S E) (toFunctorE-mkModelStr M)
  ModelObIso .Iso.ret (X , B , m) =
    ΣPathP (refl , Σ≡Prop (λ B' → isPropIsModel S E (toFunctorE B')) strPath)
    where
    actPath : Path (ActOn X) (mkModelStr (toFunctorE B) .fst) (B .fst)
    actPath i {x} {y} f =
      secIsEq (isFullyFaithfulYOStrict {C = E} (X x) (X y)) (B .fst f) i

    strPath : mkModelStr (toFunctorE B) ≡ B
    strPath = Σ≡Prop (isPropIsFunctorialAct {X = X})
                     {u = mkModelStr (toFunctorE B)} {v = B} actPath

  -- unfording the naturality clause: an honest commuting square in `𝔼`
  natSquare : {X Y : ind .ob → E .ob} {α : Carrier [ X , Y ]}
              {B : ModelStr X} {C : ModelStr Y}
            → isNatFam α B C
            → {x y : ind .ob} (f : ind [ x , y ])
            → B .fst f ⋆⟨ 𝔼 ⟩ α y ≡ α x ⋆⟨ 𝔼 ⟩ C .fst f
  natSquare ϕ f =
    makePshHomStrictPath
      (funExt (λ c → funExt (λ h → sym (ϕ f c h _ refl))))

  -- the comparison is functorial: `MODEL∫ → MODEL`
  ∫→MODEL : Functor MODEL∫ (MODEL S E)
  ∫→MODEL .F-ob (X , B , m) = toFunctorE B , m
  ∫→MODEL .F-hom (α , _) .NatTrans.N-ob x = fromStrict .F-hom (α x)
  ∫→MODEL .F-hom {x = X , B , _} {y = Y , C , _} (α , ϕ) .NatTrans.N-hom
    {x} {y} f =
    sym (fromStrict .F-seq (B .fst f) (α y))
    ∙ cong (fromStrict .F-hom) (natSquare {α = α} {B} {C} ϕ f)
    ∙ fromStrict .F-seq (α x) (C .fst f)
  ∫→MODEL .F-id = makeNatTransPath (funExt (λ _ → fromStrict .F-id))
  ∫→MODEL .F-seq (α , _) (β , _) =
    makeNatTransPath (funExt (λ x → fromStrict .F-seq (α x) (β x)))
