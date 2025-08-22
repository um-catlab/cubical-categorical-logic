module Gluing.Category where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Quiver.Base as Quiver
open import Cubical.Data.List as List hiding ([_])
open import Cubical.Data.Nat as Nat
open import Cubical.Data.Bool as Bool
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit as Unit
open import Cubical.Data.W.Indexed
open import Cubical.Relation.Nullary hiding (⟪_⟫)

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Free.Category.Quiver as Free
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓS ℓR : Level

open Category
open Section
open QuiverOver
module Normalization (Q : Quiver ℓC ℓC') where
  FQ = FreeCat Q
  module FQ = Category FQ

  -- We define normal forms inductively
  -- we can also think of this as a "property" that the given morphism
  -- has a normal form, but there's no reason to bother truncating it.
  data NormalForm {o1} : ∀ {o2} → FQ [ o1 , o2 ] → Type (ℓ-max ℓC ℓC') where
    cons : ∀ gen
         → ∀ {e} → NormalForm e
         → NormalForm ((η Q <$g> gen) ∘⟨ FQ ⟩ e)
    nil  : NormalForm FQ.id

  forget : ∀ {o1 o2} {e} → NormalForm {o1}{o2} e → List (Q .snd .mor)
  forget (cons gen fA) = gen ∷ forget fA
  forget nil = []

  data NormalForm' (o1 : Q .fst) : ∀ (o2 : Q .fst) → Type (ℓ-max ℓC ℓC') where
    nil : NormalForm' o1 o1
    cons : ∀ gen
         → NormalForm' o1 (Q .snd .dom gen)
         → NormalForm' o1 (Q .snd .cod gen)
    -- WHO CARES
    isSetNF' : ∀ {o2} → isSet (NormalForm' o1 o2)

  readBack : ∀ {o1 o2} → NormalForm' o1 o2 → FQ [ o1 , o2 ]
  readBack nil = FQ.id
  readBack (cons gen e) = readBack e ⋆⟨ FQ ⟩ (↑ gen)
  readBack (isSetNF' x y p q i j) =
    FQ .isSetHom (readBack x) (readBack y) (cong readBack p) (cong readBack q)
      i j

  hasNormalForm' : ∀ {o1 o2} → (e : FQ [ o1 , o2 ])
    → Σ[ nf ∈ _ ] readBack nf ≡ e
  hasNormalForm' = λ e → let nf' , isnf = normalize .F-homᴰ e FQ.id (nil , refl)
    in nf' , isnf ∙ FQ .⋆IdL e
    where
    hasNF : ∀ {o1 o2} → FQ [ o1 , o2 ] → Type _
    hasNF = λ e → Σ[ nf ∈ _ ] readBack nf ≡ e
    normalize : ∀ {o1} → Section (FQ [ o1 ,-]) (SETᴰ _ _)
    normalize {o1} = elimLocal Q _ _ (record
      { _$gᴰ_   = λ o2 e → hasNF e
        , isSetΣ isSetNF' (λ _ → isProp→isSet (FQ .isSetHom _ _))
      ; _<$g>ᴰ_ = λ g e (nf , r-nf≡e) → (cons g nf) , (cong (comp' FQ _) r-nf≡e)
      })

  -- hasUniqNormalForm' : ∀ {o1 o2} → isEquiv (readBack {o1}{o2})
  -- hasUniqNormalForm' = isoToIsEquiv (iso _ (λ e → hasNormalForm' e .fst)
  --   (λ e → hasNormalForm' e .snd)
  --   {!!}) where
  --   r : ∀ {o1 o2} → (nf : NormalForm' o1 o2)
  --     → hasNormalForm' (readBack nf) .fst ≡ nf
  --   -- This should be easy, but transport hell
  --   r nil = {!!}
  --   r (cons gen nf) = {!!}
  --   r (isSetNF' nf nf₁ x y i i₁) = {!!}

  module _ (isSetOb : isSet (Q .fst))
           (isSetMor : isSet (Q .snd .mor)) where

    -- | Hot take? We shouldn't bother with this, we should just
    -- | truncate NF to be a Set

    -- | I think someone made a macro for this in the 1lab recently?
    isSetNormalForm : ∀ {o1 o2 e} → isSet (NormalForm {o1} {o2} e)
    isSetNormalForm {o1}{o2}{e} = isSetRetract {B = IW S P inX (o2 , e)}
      encode
      decode
      retracts
      (isOfHLevelSuc-IW 1 isSetS _)
      where
        -- The Index
        X = Σ[ o ∈ Q .fst ] FQ [ o1 , o ]
        -- The data in the constructors besides subtrees
        S : X → Type _
        S x =
          -- nil
          ((o1 , FQ.id) ≡ x)
          ⊎ -- cons
          (Σ[ gen ∈ Q .snd .mor ] Σ[ e' ∈ FQ [ o1 , Q .snd .dom gen ] ]
            (Q .snd .cod gen , ((η Q <$g> gen) ∘⟨ FQ ⟩ e')) ≡ x)
        -- The type of subtrees of a constructor
        P : (x : X) → S x → Type _
        P _ = Sum.rec (λ _ → ⊥) (λ _ → Unit)
        -- The index of the subtrees
        inX : ∀ x (s : S x) → P x s → X
        inX x = Sum.elim
          (λ _ → Empty.elim)
          λ (gen , (e' , _)) tt →
            (Q .snd .dom gen , e')

        W : (o : Q .fst) (e : FQ [ o1 , o ]) → Type _
        W = λ o e → IW S P inX (o , e)

        encode : ∀ {o2}{e} → NormalForm e → W o2 e
        encode nil = node (inl refl) Empty.elim
        encode (cons gen {e'} l) = node (inr (gen , (e' , refl))) λ _ → encode l

        decode : ∀ {o2}{e} → W o2 e → NormalForm e
        decode (node (inl p) subtree) =
          subst (λ (o , e) → NormalForm e) p NormalForm.nil
        decode (node (inr (gen , (e' , q))) subtree) =
          subst (λ (o , e) → NormalForm e) q
            (cons gen {e = e'} (decode (subtree tt)))

        retracts : ∀ {o2}{e} → (nf : NormalForm {o2 = o2} e)
                 → decode (encode nf) ≡ nf
        retracts nil = transportRefl nil
        retracts (cons gen nf) =
          transportRefl (cons gen (decode (encode nf)))
          ∙ cong (cons gen) (retracts nf)

        isSetS : ∀ x → isSet (S x)
        isSetS x =
          isSet⊎
            (isOfHLevelPath 2 (isSetΣ isSetOb λ _ → FQ.isSetHom) _ _)
            (isSetΣ isSetMor
              (λ _ → isSetΣ
                FQ.isSetHom
                (λ _ → isOfHLevelPath 2
                  (isSetΣ isSetOb (λ _ → FQ.isSetHom)) _ _)))

    -- The main theorem/construction
    normalize : ∀ {o1}{o2} → (e : FQ [ o1 , o2 ]) → NormalForm e
    normalize {o1} = λ e → subst NormalForm (FQ.⋆IdL e) (S.F-homᴰ e FQ.id nil)
      where
      o1-pts : Functor FQ (SET _)
      o1-pts = FQ [ o1 ,-]

      S : Section o1-pts (SETᴰ _ _)
      -- TODO: should be able to use elim' directly once the definition of
      -- compFunctorᴰGlobalSection in Section.Base is fixed
      S = Free.elimLocal Q _ _ (record
        { _$gᴰ_ = λ o e → (NormalForm e) , isSetNormalForm
        ; _<$g>ᴰ_ = λ m e l → cons m l })
      module S = Section S

    -- uniqNF : ∀ {o1 o2} → (e : FQ [ o1 , o2 ]) → isContr (NormalForm e)
    -- uniqNF = λ e → (normalize e) , lem where
    --   lem : ∀ {o1 o2} {e : FQ [ o1 , o2 ]} nf
    --       → normalize e ≡ nf
    --   -- This should be easy, but transport hell
    --   lem nil = {!!}
    --   lem (cons gen nf) = {!!}

-- Consider the free category generated from a graph.

-- This is a very simple sort of language where we have base types and
-- unary function symbols.

module Example1 where
  data OB : Type ℓ-zero where
    a b c : OB

  discreteOB : Discrete OB
  discreteOB = sectionDiscrete {A = ℕ}
    (λ { zero → a ; 1 → b ; (suc (suc _)) → c })
    (λ { a → 0 ; b → 1 ; c → 2 })
    (λ { a → refl ; b → refl ; c → refl })
    discreteℕ

  isSetOB : isSet OB
  isSetOB = Discrete→isSet discreteOB

  data MOR : Type ℓ-zero where
    f g h : MOR

  discreteMOR : Discrete MOR
  discreteMOR = sectionDiscrete {A = ℕ}
    (λ { zero → f ; 1 → g ; (suc (suc _)) → h })
    (λ { f → 0 ; g → 1 ; h → 2 })
    (λ { f → refl ; g → refl ; h → refl })
    discreteℕ

  isSetMOR : isSet MOR
  isSetMOR = Discrete→isSet discreteMOR

  DOM COD : MOR → OB
  DOM f = a
  DOM g = b
  DOM h = a

  COD f = b
  COD g = a
  COD h = a

  QUIVER : Quiver ℓ-zero ℓ-zero
  QUIVER .fst = OB
  QUIVER .snd .mor = MOR
  QUIVER .snd .dom = DOM
  QUIVER .snd .cod = COD

  private
    open Normalization QUIVER
    norm = normalize isSetOB isSetMOR
    _ : forget (norm {c} FQ.id)
        ≡ []
    _ = refl

    -- The following two should be refl without length, but length is
    -- enough.
    _ : length (forget (norm (FQ.id ∘⟨ FQ ⟩ ↑ h)))
        ≡ length (h ∷ [])
    _ = refl

    _ : length (forget (norm
               ((↑ h ∘⟨ FQ ⟩ (↑ g ∘⟨ FQ ⟩ FQ.id)) ∘⟨ FQ ⟩ ↑ f)))
        ≡ length (h ∷ g ∷ f ∷ [])
    _ = refl

    non-triviality : ¬ (FQ.id ≡ ↑ h)
    non-triviality p = 0≠1 (cong (λ e → length (forget (norm e))) p)
      where
        0≠1 : ¬ (0 ≡ 1)
        0≠1 = znots

module Example2 where
  data OB : Type ℓ-zero where
    ⊤ b : OB

  discreteOB : Discrete OB
  discreteOB = sectionDiscrete {A = ℕ}
    (λ { zero → ⊤ ; (suc _) → b })
    (λ { ⊤ → 0 ; b → 1 })
    (λ { ⊤ → refl ; b → refl })
    discreteℕ

  isSetOB : isSet OB
  isSetOB = Discrete→isSet discreteOB

  data MOR : Type ℓ-zero where
    t f : MOR

  discreteMOR : Discrete MOR
  discreteMOR = sectionDiscrete {A = ℕ}
    (λ { zero → f ; (suc _) → t  })
    (λ { f → 0 ; t → 1  })
    (λ { f → refl ; t → refl })
    discreteℕ

  isSetMOR : isSet MOR
  isSetMOR = Discrete→isSet discreteMOR

  DOM COD : MOR → OB
  DOM t = ⊤
  DOM f = ⊤

  COD t = b
  COD f = b

  QUIVER : Quiver ℓ-zero ℓ-zero
  QUIVER .fst = OB
  QUIVER .snd .mor = MOR
  QUIVER .snd .dom = DOM
  QUIVER .snd .cod = COD

  private
    FQ = FreeCat QUIVER
    [t] [f] : FQ [ ⊤ , b ]
    [t] = ↑ t
    [f] = ↑ f

    set-semantics : Functor FQ (SET ℓ-zero)
    set-semantics = Free.rec QUIVER (record { _$g_ = ıo ; _<$g>_ = ım })
      where
      ıo : OB → hSet ℓ-zero
      ıo ⊤ = Unit , isSetUnit
      ıo b = Bool , isSetBool

      ım : ∀ m → ⟨ ıo (DOM m) ⟩ → ⟨ ıo (COD m) ⟩
      ım t x = true
      ım f x = false

    normalize : FQ [ ⊤ , b ] → Bool
    normalize e = (set-semantics ⟪ e ⟫) _

    non-triviality : ¬ ([t] ≡ [f])
    non-triviality p = true≢false (cong normalize p)

    motive = λ (e : FQ [ ⊤ , b ]) →  (e ≡ [t]) ⊎ (e ≡ [f])

    canonicalize : ∀ (e : FQ [ ⊤ , b ]) → (e ≡ [t]) ⊎ (e ≡ [f])
    canonicalize = λ e →
      subst motive (FQ .⋆IdL _) (Canonicalize .F-homᴰ e (FQ .id) refl)
      where
      ⊤-pts : Functor FQ (SET _)
      ⊤-pts = FQ [ ⊤ ,-]

      ıo : ∀ o → FQ [ ⊤ , o ] → hSet ℓ-zero
      ıo ⊤ e = (e ≡ FQ .id) , (isProp→isSet (FQ .isSetHom _ _))
      ıo b e = motive e
        , isSet⊎ (isProp→isSet (FQ .isSetHom _ _))
                 ((isProp→isSet (FQ .isSetHom _ _)))

      ıe : ∀ (m : MOR) (e : Exp QUIVER ⊤ (DOM m)) →
        ⟨ ıo (DOM m) e ⟩ → ⟨ ıo (COD m) (e ⋆⟨ FQ ⟩ (↑ m)) ⟩
      ıe t e e≡id = inl (cong (comp' FQ [t]) e≡id ∙ FQ .⋆IdL _)
      ıe f e e≡id = inr (cong (comp' FQ [f]) e≡id ∙ FQ .⋆IdL _)

      Canonicalize : Section ⊤-pts (SETᴰ _ _)
      Canonicalize = Free.elimLocal QUIVER _ _ (record
        { _$gᴰ_ = ıo
        ; _<$g>ᴰ_ = ıe })
