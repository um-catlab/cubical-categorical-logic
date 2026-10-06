-- The strict-downset sieve ↡c of a direct category.
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Direct.Base
module Cubical.Categories.Direct.StrictDownset {ℓ ℓ' ℓD : Level} {C : Category ℓ ℓ'} {Wo : WFOrder ℓD ℓ'} (dir : DirectStr C Wo) where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit

open import Cubical.Induction.WellFounded

open import Cubical.Categories.Functor
open import Cubical.Categories.Morphism
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.StrictHom.CartesianClosed
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Subobject.Base
open import Cubical.Categories.Presheaf.Sieve

import Cubical.Categories.Presheaf.Family.Base as FamBase
import Cubical.Categories.NaturalTransformation as NT
import Cubical.Data.Equality as Eq

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

  private
    E = ▷Psh ⇒PshLargeStrict P
    module E = PresheafNotation E

    val : ∀ {c} → E.p[ c ] → ∀ y → C [ y , c ] → Acc _≺_ y → ⟨ P .F-ob y ⟩
    below : ∀ {c} → E.p[ c ] → ∀ y → C [ y , c ] → Acc _≺_ y
          → ⟨ ▷Psh .F-ob y ⟩
    valNat : ∀ {c} (e : E.p[ c ]) {y y'} (k : C [ y' , y ]) (g : C [ y , c ])
             (A : Acc _≺_ y) (A' : Acc _≺_ y')
           → P .F-hom k (val e y g A) ≡ val e y' (k ⋆ g) A'

    valIrr : ∀ {c} (e : E.p[ c ]) y (g : C [ y , c ]) (A A' : Acc _≺_ y)
           → val e y g A ≡ val e y g A'

    val e y g (acc r) = e .N-ob y (g , below e y g (acc r))

    below e y g (acc r) .N-ob z (h , q) = val e z (h ⋆ g) (r z q)
    below e y g (acc r) .N-hom z' z k (h , q) (h' , q') eq =
      valNat e k (h ⋆ g) (r z q) (r z' q')
      ∙ cong (λ m → val e z' m (r z' q'))
          (sym (⋆Assoc k h g) ∙ cong (_⋆ g) (cong fst eq))

    valNat e {y} {y'} k g (acc r) (acc r') =
      e .N-hom y' y k (g , below e y g (acc r))
        (k ⋆ g , below e y' (k ⋆ g) (acc r'))
        (ΣPathP (refl , makePshHomStrictPath (funExt λ z → funExt λ (h , q) →
          cong (λ m → val e z m (r z (≺-postcomp q k))) (⋆Assoc h k g)
          ∙ valIrr e z (h ⋆ (k ⋆ g)) (r z (≺-postcomp q k)) (r' z q))))

    valIrr e y g (acc r) (acc r') =
      cong (λ b → e .N-ob y (g , b))
        (makePshHomStrictPath (funExt λ z → funExt λ (h , q) →
          valIrr e z (h ⋆ g) (r z q) (r' z q)))

    valPath : ∀ {c} (e : E.p[ c ]) {y} {g g' : C [ y , c ]} → g ≡ g'
            → (A A' : Acc _≺_ y) → val e y g A ≡ val e y g' A'
    valPath e {y} {g' = g'} p A A' = cong (λ m → val e y m A) p ∙ valIrr e y g' A A'

    valUnfold : ∀ {c} (e : E.p[ c ]) y (g : C [ y , c ]) (A : Acc _≺_ y)
              → val e y g A ≡ e .N-ob y (g , below e y g A)
    valUnfold e y g (acc r) = refl

    valRestr : ∀ {c c'} (k : C [ c , c' ]) (e : E.p[ c' ]) y (g : C [ y , c ])
             (A A' : Acc _≺_ y)
           → val (k E.⋆ e) y g A ≡ val e y (g ⋆ k) A'
    valRestr k e y g (acc r) (acc r') =
      cong (λ b → e .N-ob y (g ⋆ k , b))
        (makePshHomStrictPath (funExt λ z → funExt λ (h , q) →
          valRestr k e z (h ⋆ g) (r z q) (r' z q)
          ∙ valPath e (⋆Assoc h g k) (r' z q) (r' z q)))

    belowVal : ∀ {c} (e : E.p[ c ]) {y} (g : C [ y , c ]) (A : Acc _≺_ y)
               {z} (h : C [ z , y ]) (q : z ≺ y) (A' : Acc _≺_ z)
             → below e y g A .N-ob z (h , q) ≡ val e z (h ⋆ g) A'
    belowVal e g (acc r) h q A' = valPath e refl (r _ q) A'

  löb : PshHomStrict (▷Psh ⇒PshLargeStrict P) P
  löb .N-ob c e = val e c id (wf≺ c)
  löb .N-hom c c' k e' e eq =
    valNat e' k id (wf≺ c') (wf≺ c)
    ∙ valPath e' (⋆IdR k ∙ sym (⋆IdL k)) (wf≺ c) (wf≺ c)
    ∙ sym (valRestr k e' c id (wf≺ c) (wf≺ c))
    ∙ cong (λ e'' → val e'' c id (wf≺ c)) eq

  löb-fix : löb ≡ ×PshIntroStrict idPshHomStrict (löb ⋆PshHomStrict next)
                    ⋆PshHomStrict appPshHomStrict ▷Psh P
  löb-fix = makePshHomStrictPath (funExt λ c → funExt λ e →
    valUnfold e c id (wf≺ c)
    ∙ cong (λ b → e .N-ob c (id , b))
      (makePshHomStrictPath (funExt λ z → funExt λ (h , q) →
        belowVal e id (wf≺ c) h q (wf≺ z)
        ∙ sym (valNat e h id (wf≺ c) (wf≺ z)))))

  löb-uniq : ∀ {ℓΓ} {Γ : Presheaf C ℓΓ}
    (f : PshHomStrict Γ (▷Psh ⇒PshLargeStrict P)) (s : PshHomStrict Γ P)
    → s ≡ ×PshIntroStrict f (s ⋆PshHomStrict next)
            ⋆PshHomStrict appPshHomStrict ▷Psh P
    → s ≡ f ⋆PshHomStrict löb
  löb-uniq {Γ = Γ} f s s-fix =
    makePshHomStrictPath (funExt λ c → funExt λ γ → WFI.induction wf≺ step c γ)
    where
      step : ∀ c → (∀ y → y ≺ c → ∀ γ → s .N-ob y γ ≡ löb .N-ob y (f .N-ob y γ))
           → ∀ γ → s .N-ob c γ ≡ löb .N-ob c (f .N-ob c γ)
      step c IH γ =
        funExt⁻ (funExt⁻ (cong N-ob s-fix) c) γ
        ∙ cong (λ b → f .N-ob c γ .N-ob c (id , b))
            (makePshHomStrictPath (funExt λ z → funExt λ (h , q) →
              s .N-hom z c h γ _ refl
              ∙ IH z q (Γ .F-hom h γ)
              ∙ cong (λ e → val e z id (wf≺ z)) (sym (f .N-hom z c h γ _ refl))
              ∙ valRestr h (f .N-ob c γ) z id (wf≺ z) (wf≺ z)
              ∙ valPath (f .N-ob c γ) (⋆IdL h ∙ sym (⋆IdR h)) (wf≺ z) (wf≺ z)
              ∙ sym (belowVal (f .N-ob c γ) id (wf≺ c) h q (wf≺ z))))
        ∙ sym (valUnfold (f .N-ob c γ) c id (wf≺ c))

module _ {ℓF} (A : ob → hSet (ℓ-max ℓF (ℓ-max ℓ ℓ'))) where
  private
    U = FamBase.PSH→Fam {ℓ = ℓF} C
    G = FamBase.Cofree {ℓ = ℓF} C
    □ = FamBase.□ {ℓ = ℓF} C
    Fam = FamBase.Fam {ℓ = ℓF} C
    GA = G .F-ob A

  ▷Fam : ob → hSet _
  ▷Fam = U .F-ob (▷Psh GA)

  nextFam : Fam [ □ ⟅ A ⟆ , ▷Fam ]
  nextFam = U .F-hom (next GA)

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
