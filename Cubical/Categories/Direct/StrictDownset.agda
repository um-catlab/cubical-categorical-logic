-- The strict-downset sieve ↡c of a direct category.
module Cubical.Categories.Direct.StrictDownset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit

open import Cubical.Induction.WellFounded

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Morphism
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Subobject.Base
open import Cubical.Categories.Presheaf.Sieve
open import Cubical.Categories.Direct.Base
import Cubical.Categories.Presheaf.Family.Base as FamBase
import Cubical.Categories.Adjoint as Adjoint
import Cubical.Categories.NaturalTransformation as NT

private
  variable
    ℓ ℓ' ℓD : Level

module _ {C : Category ℓ ℓ'} {Wo : WFOrder ℓD ℓ'} (dir : DirectStr {C = C} Wo) where
  open Category C
  open Functor
  open PshHomStrict
  open DirectNotation dir

  -- the strict-downset sub-presheaf of よc
  ↡Psh : (c : ob) → Presheaf C ℓ'
  ↡Psh c .F-ob y =
    (Σ[ f ∈ C [ y , c ] ] (y ≺ c))
    , isSetΣ isSetHom (λ _ → isProp→isSet (isProp≺ y c))
  ↡Psh c .F-hom g (f , p) = (g ⋆ f) , ≺-precomp g p
  ↡Psh c .F-id     = funExt λ (f , p) → Σ≡Prop (λ _ → isProp≺ _ _) (⋆IdL f)
  ↡Psh c .F-seq g h = funExt λ (f , p) → Σ≡Prop (λ _ → isProp≺ _ _) (⋆Assoc h g f)

  ↡incl : (c : ob) → PshHomStrict (↡Psh c) (yo c)
  ↡incl c .N-ob y (f , p) = f
  ↡incl c .N-hom y' y g (f' , p') (f , p) e = cong fst e

  ↡monic : (c : ob) → isMonic (PRESHEAF C ℓ') (↡incl c)
  ↡monic c {a = g} {a' = g'} eq =
    makePshHomStrictPath (funExt λ y → funExt λ t →
      Σ≡Prop (λ _ → isProp≺ _ _) (λ i → (eq i) .N-ob y t))

  -- the strict downset, as a sieve on c
  ↡ : (c : ob) → Sieve C c
  ↡ c = ↡Psh c , ↡incl c , ↡monic c

  ↡F : Functor C (PRESHEAF C ℓ')
  ↡F .F-ob = ↡Psh
  ↡F .F-hom a .N-ob y (f , p) = (f ⋆ a) , ≺-postcomp p a
  ↡F .F-hom a .N-hom y' y g (f' , p') (f , p) e =
    Σ≡Prop (λ _ → isProp≺ _ _) (sym (⋆Assoc g f' a) ∙ cong (_⋆ a) (cong fst e))
  ↡F .F-id =
    makePshHomStrictPath (funExt λ y → funExt λ (f , p) →
      Σ≡Prop (λ _ → isProp≺ _ _) (⋆IdR f))
  ↡F .F-seq a b =
    makePshHomStrictPath (funExt λ y → funExt λ (f , p) →
      Σ≡Prop (λ _ → isProp≺ _ _) (sym (⋆Assoc f a b)))

  private module Wo = WFOrder Wo

  -- ↡c contains exactly the strict maps into c
  ↡∋→≺ : ∀ {c y} (f : C [ y , c ]) → (↡ c) ∋ f → y ≺ c
  ↡∋→≺ f ((_ , p) , _) = p

  ≺→↡∋ : ∀ {c y} (f : C [ y , c ]) → y ≺ c → (↡ c) ∋ f
  ≺→↡∋ f p = (f , p) , refl

  -- ↡c omits the identity so its a proper sieve
  ↡-proper : ∀ {c} → isProperSieve (↡ c)
  ↡-proper {c} idIn = Wo.¬<refl (↡∋→≺ id idIn)

  -- A direct structure is reflecting when equal-degree maps are split epis.
  -- In such a category non-identities
  -- strictly raise degree, so ↡ is the maximal proper sieve
  Reflecting : Type (ℓ-max (ℓ-max ℓ ℓ') ℓD)
  Reflecting = ∀ {x y} (f : C [ x , y ])
    → deg x ≡ deg y → Σ[ s ∈ C [ y , x ] ] (s ⋆ f ≡ id)

  -- every proper sieve refines into ↡c
  ↡-maximal : Reflecting → ∀ {c} (S : Sieve C c) → isProperSieve S → S ⊆ ↡ c
  ↡-maximal refl-dir S proper f Sf with non-dec f
  ... | inl y≺c = ≺→↡∋ f y≺c
  ... | inr y≡c = ⊥.rec (proper idIn)
    where
      sec : Σ[ s ∈ C [ _ , _ ] ] (s ⋆ f ≡ id)
      sec = refl-dir f y≡c
      idIn : S ∋ id
      idIn = subst (S ∋_) (sec .snd) (sieve-precomp S (sec .fst) Sf)

  module _ {ℓP} (P : Presheaf C ℓP) where
    Later : Presheaf C (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓ') ℓP)
    Later .F-ob x = PshHomStrict (↡Psh x) P , isSetPshHomStrict _ _
    Later .F-hom a α = ↡F .F-hom a ⋆PshHomStrict α
    Later .F-id     = funExt λ α → cong (_⋆PshHomStrict α) (↡F .F-id)
    Later .F-seq a b = funExt λ α → cong (_⋆PshHomStrict α) (↡F .F-seq b a)

    next : PshHomStrict P Later
    next .N-ob x p = pshhom (λ y (g , q) → P .F-hom g p)
      (λ c c' h (g' , q') (g , q) e →
        sym (funExt⁻ (P .F-seq g' h) p) ∙ cong (λ k → P .F-hom k p) (cong fst e))
    next .N-hom c c' f p' p e =
      makePshHomStrictPath (funExt λ y → funExt λ (g , q) →
        funExt⁻ (P .F-seq f g) p' ∙ cong (P .F-hom g) e)

    module _ (fhom : PshHomStrict Later P) where
      private
        f₀ : ∀ c → PshHomStrict (↡Psh c) P → ⟨ P .F-ob c ⟩
        f₀ = fhom .N-ob

      down : ∀ c → Acc _≺_ c → PshHomStrict (↡Psh c) P
      downIrr : ∀ c (A A' : Acc _≺_ c) → down c A ≡ down c A'
      downNat : ∀ {y' y} (A' : Acc _≺_ y') (A : Acc _≺_ y) (h : C [ y' , y ])
              → ↡F .F-hom h ⋆PshHomStrict down y A ≡ down y' A'

      down c (acc r) .N-ob y (g , q) = f₀ y (down y (r y q))
      down c (acc r) .N-hom y' y h (g' , q') (g , q) e =
        fhom .N-hom y' y h (down y (r y q')) _ refl
        ∙ cong (f₀ y') (downNat (r y' q) (r y q') h)
      downIrr c (acc r) (acc r') =
        makePshHomStrictPath (funExt λ y → funExt λ (g , q) →
          cong (f₀ y) (downIrr y (r y q) (r' y q)))
      downNat (acc rA') (acc rA) h =
        makePshHomStrictPath (funExt λ z → funExt λ (m , s) →
          cong (f₀ z) (downIrr z (rA z (≺-postcomp s h)) (rA' z s)))

      löb : PshHomStrict UnitPsh P
      löb .N-ob c _ = f₀ c (down c (wf≺ c))
      löb .N-hom c c' h _ _ _ =
        fhom .N-hom c c' h (down c' (wf≺ c')) _ refl
        ∙ cong (f₀ c) (downNat (wf≺ c) (wf≺ c') h)

  module _ {ℓF} (A : ob → hSet (ℓ-max ℓF (ℓ-max ℓ ℓ'))) where
    private
      U = FamBase.Psh→Fam {ℓ = ℓF} C
      G = FamBase.Cofree {ℓ = ℓF} C
      module Adj = Adjoint.UnitCounit._⊣_ (FamBase.CofreeFamAdj {ℓ = ℓF} C)
      ηP = NT.NatTrans.N-ob Adj.η
      εA = NT.NatTrans.N-ob Adj.ε

    ▷Fam : ob → hSet _
    ▷Fam = U .F-ob (Later (G .F-ob A))

    module _ (φ : ∀ x → ⟨ ▷Fam x ⟩ → ⟨ A x ⟩) where
      φ↑ : PshHomStrict (Later (G .F-ob A)) (G .F-ob A)
      φ↑ = ηP (Later (G .F-ob A)) ⋆PshHomStrict G .F-hom φ

      löbFam : ∀ x → ⟨ A x ⟩
      löbFam x = εA A x (löb (G .F-ob A) φ↑ .N-ob x _)

    -- strong recursion for an arbitrary direct category: to define `f x` it
    -- suffices, for each NON-IDENTITY map `g : y → x` out of a strictly-lower
    -- object, to use the recursive value `f y`.  In a *non-thin* direct
    -- category the recursive data is indexed by the map `g`, not just by `y`.
    löbStr : (∀ x → (∀ y → C [ y , x ] → y ≺ x → ⟨ A y ⟩) → ⟨ A x ⟩)
           → ∀ x → ⟨ A x ⟩
    löbStr step = löbFam (λ x α → step x (λ y g q → α .N-ob y (g , q) y id))
