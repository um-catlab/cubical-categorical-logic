-- The strict-downset sieve ↡c of a direct category.
module Cubical.Categories.Direct.StrictDownset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
import Cubical.Data.Sum as Sum
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
import Cubical.Data.Equality as Eq

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
  ↡-maximal refl-dir {c} S proper f Sf =
    Sum.elim {C = λ _ → (↡ c) ∋ f}
      (λ y≺c → ≺→↡∋ f y≺c)
      (λ y≡c → let sec = refl-dir f (Eq.eqToPath y≡c)
               in ⊥.rec (proper (subst (S ∋_) (sec .snd)
                                        (sieve-precomp S (sec .fst) Sf))))
      (non-dec f)

  module _ {ℓP} (P : Presheaf C ℓP) where
    ▷Psh : Presheaf C (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓ') ℓP)
    ▷Psh .F-ob x = PshHomStrict (↡Psh x) P , isSetPshHomStrict _ _
    ▷Psh .F-hom a α = ↡F .F-hom a ⋆PshHomStrict α
    ▷Psh .F-id     = funExt λ α → cong (_⋆PshHomStrict α) (↡F .F-id)
    ▷Psh .F-seq a b = funExt λ α → cong (_⋆PshHomStrict α) (↡F .F-seq b a)

    next : PshHomStrict P ▷Psh
    next .N-ob x p = pshhom (λ y (g , q) → P .F-hom g p)
      (λ c c' h (g' , q') (g , q) e →
        sym (funExt⁻ (P .F-seq g' h) p) ∙ cong (λ k → P .F-hom k p) (cong fst e))
    next .N-hom c c' f p' p e =
      makePshHomStrictPath (funExt λ y → funExt λ (g , q) →
        funExt⁻ (P .F-seq f g) p' ∙ cong (P .F-hom g) e)

    module _ (fhom : PshHomStrict ▷Psh P) where
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

      downValue : ∀ c (Ac : Acc _≺_ c) {y} (g : C [ y , c ]) (q : y ≺ c)
                → down c Ac .N-ob y (g , q) ≡ f₀ y (down y (wf≺ y))
      downValue c (acc r) {y} g q = cong (f₀ y) (downIrr y (r y q) (wf≺ y))

      -- the guarded fixed-point equation:  löb = (löb ⋆ next) ⋆ f
      löb-fix : löb ≡ (löb ⋆PshHomStrict next) ⋆PshHomStrict fhom
      löb-fix = makePshHomStrictPath (funExt λ c → funExt λ _ →
        cong (f₀ c) (makePshHomStrictPath (funExt λ y → funExt λ (g , q) →
          downValue c (wf≺ c) g q ∙ sym (löb .N-hom y c g _ _ refl))))

      -- and it is the unique fixed point
      löb-uniq : (s : PshHomStrict UnitPsh P)
               → s ≡ (s ⋆PshHomStrict next) ⋆PshHomStrict fhom
               → s ≡ löb
      löb-uniq s s-fix =
        makePshHomStrictPath (funExt λ c → funExt λ _ → WFI.induction wf≺ step c)
        where
          step : ∀ c → (∀ y → y ≺ c → s .N-ob y tt ≡ löb .N-ob y tt)
               → s .N-ob c tt ≡ löb .N-ob c tt
          step c IH =
            funExt⁻ (funExt⁻ (cong N-ob s-fix) c) tt
            ∙ cong (f₀ c) (makePshHomStrictPath (funExt λ y → funExt λ (g , q) →
                s .N-hom y c g _ _ refl ∙ IH y q ∙ sym (downValue c (wf≺ c) g q)))

  module _ {ℓF} (A : ob → hSet (ℓ-max ℓF (ℓ-max ℓ ℓ'))) where
    private
      U = FamBase.PSH→Fam {ℓ = ℓF} C
      G = FamBase.Cofree {ℓ = ℓF} C
      module Adj = Adjoint.UnitCounit._⊣_ (FamBase.CofreeFamAdj {ℓ = ℓF} C)
      ηP = NT.NatTrans.N-ob Adj.η
      εA = NT.NatTrans.N-ob Adj.ε

    ▷Fam : ob → hSet _
    ▷Fam = U .F-ob (▷Psh (G .F-ob A))

    toFam : PshHomStrict UnitPsh (G .F-ob A) → (∀ x → ⟨ A x ⟩)
    toFam s x = εA A x (s .N-ob x _)

    fromFam : (∀ x → ⟨ A x ⟩) → PshHomStrict UnitPsh (G .F-ob A)
    fromFam t = pshhom (λ c _ y h → t y) (λ c c' f p' p e → refl)

    toFam-fromFam : (t : ∀ x → ⟨ A x ⟩) → toFam (fromFam t) ≡ t
    toFam-fromFam t = refl

    fromFam-toFam : (s : PshHomStrict UnitPsh (G .F-ob A)) → fromFam (toFam s) ≡ s
    fromFam-toFam s = makePshHomStrictPath (funExt λ c → funExt λ _ →
      funExt λ y → funExt λ h →
        sym (funExt⁻ (funExt⁻ (s .N-hom y c h _ _ refl) y) id)
        ∙ cong (s .N-ob c _ y) (⋆IdL h))

    nextFam : (∀ x → ⟨ A x ⟩) → ∀ x → ⟨ ▷Fam x ⟩
    nextFam t x =
      (fromFam t ⋆PshHomStrict next (G .F-ob A)) .N-ob x tt

    -- apply a later element at a strict bound
    ▷FamApp : {x y : ob} → ⟨ ▷Fam x ⟩ → C [ y , x ] → y ≺ x → ⟨ A y ⟩
    ▷FamApp β g q = β .N-ob _ (g , q) _ id

    module _ (φ : ∀ x → ⟨ ▷Fam x ⟩ → ⟨ A x ⟩) where
      φ↑ : PshHomStrict (▷Psh (G .F-ob A)) (G .F-ob A)
      φ↑ = ηP (▷Psh (G .F-ob A)) ⋆PshHomStrict G .F-hom φ

      löbFam : ∀ x → ⟨ A x ⟩
      löbFam = toFam (löb (G .F-ob A) φ↑)

      stepFam : (∀ x → ⟨ A x ⟩) → (∀ x → ⟨ A x ⟩)
      stepFam t =
        toFam ((fromFam t ⋆PshHomStrict next (G .F-ob A)) ⋆PshHomStrict φ↑)

      löbFam-fix : löbFam ≡ stepFam löbFam
      löbFam-fix =
        cong toFam (löb-fix (G .F-ob A) φ↑)
        ∙ sym (cong (λ s →
                 toFam ((s ⋆PshHomStrict next (G .F-ob A)) ⋆PshHomStrict φ↑))
                 (fromFam-toFam (löb (G .F-ob A) φ↑)))

      löbFam-uniq : (t : ∀ x → ⟨ A x ⟩) → t ≡ stepFam t → t ≡ löbFam
      löbFam-uniq t t-fix =
        sym (toFam-fromFam t)
        ∙ cong toFam
            (löb-uniq (G .F-ob A) φ↑ (fromFam t)
              (cong fromFam t-fix
               ∙ fromFam-toFam
                   ((fromFam t ⋆PshHomStrict next (G .F-ob A)) ⋆PshHomStrict φ↑)))

      löbFam-unfold : ∀ x → löbFam x ≡ φ x (nextFam löbFam x)
      löbFam-unfold x =
        funExt⁻ löbFam-fix x
        ∙ cong (φ x)
            (funExt⁻ (▷Psh (G .F-ob A) .F-id) (nextFam löbFam x))

      löbFam-uniq-unfold : (t : ∀ x → ⟨ A x ⟩)
        → (∀ x → t x ≡ φ x (nextFam t x)) → t ≡ löbFam
      löbFam-uniq-unfold t teq = löbFam-uniq t (funExt λ x →
        teq x
        ∙ cong (φ x)
            (sym (funExt⁻ (▷Psh (G .F-ob A) .F-id) (nextFam t x))))

  private
    ℓ▷ : Level
    ℓ▷ = ℓ-max ℓ ℓ'

  ▷ : Functor (PRESHEAF C ℓ▷) (PRESHEAF C ℓ▷)
  ▷ .F-ob P = ▷Psh P
  ▷ .F-hom φ .N-ob x β = β ⋆PshHomStrict φ
  ▷ .F-hom φ .N-hom c c' f β' β e = cong (_⋆PshHomStrict φ) e
  ▷ .F-id      = makePshHomStrictPath refl
  ▷ .F-seq φ ψ = makePshHomStrictPath refl

  nextNT : NT.NatTrans Id ▷
  nextNT = NT.natTrans (λ P → next P)
    (λ {P} {Q} φ →
      makePshHomStrictPath (funExt λ x → funExt λ p →
        makePshHomStrictPath (funExt λ y → funExt λ (g , q) →
          φ .N-hom y x g p (P .F-hom g p) refl)))
