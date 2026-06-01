module Gluing.Category.Forded where

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
import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq
open import Cubical.Relation.Nullary hiding (⟪_⟫)

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Free.Category.Forded as Free
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
  -- data NormalForm {o1 o2} (e : FQ [ o1 , o2 ]) : Type (ℓ-max ℓC ℓC') where

  -- `o2` and `e` are *indices*, not parameters: the recursive field `nfe'`
  -- in `cons` lives at a different morphism, and Mikan's termination checker
  -- only tracks structural descent across a changing index (not a changing
  -- parameter). Cf. the same index-vs-parameter shape in `Cubical.Data.W.Indexed`.
  data NormalForm {o1} : ∀ {o2} → FQ [ o1 , o2 ] → Type (ℓ-max ℓC' ℓC) where
    cons : ∀ {o2} {e : FQ [ o1 , o2 ]} gen e'
         → (o2≡cod : o2 Eq.≡ Q .snd .cod gen)
         → (e≡e'⋆gen : Eq.HEq (Eq.ap (FQ [ o1 ,_]) o2≡cod) e (e' ⋆ₑ ⇑ Q gen))
         → (nfe' : NormalForm e')
         → NormalForm e
    nil : ∀ {o2} {e : FQ [ o1 , o2 ]}
      → (o1≡o2 : o1 Eq.≡ o2)
      → Eq.HEq (Eq.ap (FQ [ o1 ,_]) o1≡o2) (FQ.id {o1}) e
      → NormalForm e

  forget : ∀ {o1 o2} {e} → NormalForm {o1}{o2} e → List (Q .snd .mor)
  forget (cons gen e' o2≡cod e≡e'⋆gen nfe') = gen ∷ forget nfe'
  forget (nil o1≡o2 x) = []

  module _ (isSetOb : isSet (Q .fst))
           (isSetMor : isSet (Q .snd .mor)) where
    isSetNormalForm : ∀ {o1 o2 e} → isSet (NormalForm {o1} {o2} e)
    isSetNormalForm {o1} {o2} {e} = isSetRetract {B = IW {X = X} S P inX (o2 , e)}
      encode
      decode
      retracts
      ((isOfHLevelSuc-IW 1 isSetS _))
      where
        -- The Index
        X = Σ[ o ∈ Q .fst ] FQ [ o1 , o ]
        -- The data in the constructors besides subtrees
        S : X → Type _
        S x =
          -- nil
          ((o1 , FQ.id) Eq.≡ x) ⊎
          -- cons
          (Σ[ gen ∈ Q .snd .mor ]
           Σ[ e' ∈ FQ [ o1 , Q .snd .dom gen ] ]
           ((Q .snd .cod gen , (e' ⋆ₑ ⇑ Q gen))) Eq.≡ x)
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
        encode (cons gen e' Eq.refl Eq.refl nfe') = node (inr (gen , e' , Eq.refl)) λ { tt → encode nfe' }
        encode (nil Eq.refl Eq.refl) = node (inl Eq.refl) Empty.elim

        decode : ∀ {o2}{e} → W o2 e → NormalForm e
        decode (node (inl Eq.refl) subtree) = nil Eq.refl Eq.refl
        decode (node (inr (gen , e' , Eq.refl)) subtree) =
          cons gen e' Eq.refl Eq.refl (decode (subtree tt))
        retracts : ∀ {o2}{e} → (nf : NormalForm {o2 = o2} e)
                 → decode (encode nf) ≡ nf

        retracts (nil Eq.refl Eq.refl) = refl
        retracts (cons gen e' Eq.refl Eq.refl nfe') =
          cong (cons gen e' Eq.refl Eq.refl) (retracts nfe')

        isSetX : isSet X
        isSetX = isSetΣ isSetOb (λ _ → FQ.isSetHom)
        isSetS : ∀ x → isSet (S x)
        isSetS x =
          isSet⊎
            (isProp→isSet (Eq.isSet→isSetEq isSetX))
            (isSetΣ isSetMor
              (λ _ → isSetΣ
                FQ.isSetHom
                (λ _ → isProp→isSet (Eq.isSet→isSetEq isSetX))))

    -- The main theorem/construction
    normalize : ∀ {o1}{o2} → (e : FQ [ o1 , o2 ]) → NormalForm e
    normalize {o1} = λ e → subst NormalForm (FQ.⋆IdL e) (S.F-homᴰ e FQ.id (nil Eq.refl Eq.refl))
      where
      o1-pts : Functor FQ (SET _)
      o1-pts = FQ [ o1 ,-]

      S : Section o1-pts (SETᴰ _ _)
      S = Free.elimLocal Q _ _ (record
        { _$gᴰ_ = λ o e → (NormalForm e) , isSetNormalForm
        ; _<$g>ᴰ_ = λ m e l → cons m e Eq.refl Eq.refl l })
      module S = Section S

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
    _ : length (forget (norm (FQ.id ∘⟨ FQ ⟩ ⇑ QUIVER h)))
        ≡ 1
    _ = refl

    _ : (forget (norm (FQ.id ∘⟨ FQ ⟩ ⇑ QUIVER h)))
        ≡ (h ∷ [])
    _ = refl

    _ : (forget (norm
               ((⇑ QUIVER h ∘⟨ FQ ⟩ (⇑ QUIVER g ∘⟨ FQ ⟩ FQ.id)) ∘⟨ FQ ⟩ ⇑ QUIVER f)))
        ≡ (h ∷ g ∷ f ∷ [])
    _ = refl

    non-triviality : ¬ (FQ.id ≡ ⇑ QUIVER h)
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
    [t] = ⇑ QUIVER t
    [f] = ⇑ QUIVER f

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
        ⟨ ıo (DOM m) e ⟩ → ⟨ ıo (COD m) (e ⋆⟨ FQ ⟩ (⇑ QUIVER m)) ⟩
      ıe t e e≡id = inl (cong (comp' FQ [t]) e≡id ∙ FQ .⋆IdL _)
      ıe f e e≡id = inr (cong (comp' FQ [f]) e≡id ∙ FQ .⋆IdL _)

      Canonicalize : Section ⊤-pts (SETᴰ _ _)
      Canonicalize = Free.elimLocal QUIVER _ _ (record
        { _$gᴰ_ = ıo
        ; _<$g>ᴰ_ = ıe })
