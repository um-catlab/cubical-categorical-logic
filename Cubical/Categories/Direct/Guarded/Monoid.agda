{-# OPTIONS --lossy-unification #-}
open import Cubical.Categories.Direct.Instances.Monoid using (GradedMonoid)

module Cubical.Categories.Direct.Guarded.Monoid (GM : GradedMonoid) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr ; isSet⊎ ; isProp⊎)
open import Cubical.Foundations.HLevels using (Π-contractDomIso)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Nat.Order.Recursive using (_<_ ; _≤_ ; isProp≤ ; <→≢ ; ≤-trans ; k≤k+n ; n≤k+n)
import Cubical.Data.Empty as ⊥
open import Cubical.Algebra.Monoid.Base

open import Cubical.Categories.Category
open import Cubical.Categories.Direct.Instances.Monoid using (Suffix ; suffixDirect)
open import Cubical.Categories.Enriched.Enrichment.Instances.Power using (Setᴬ)
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.StrictHom.Base
open PshHomStrict
open Functor
open import Cubical.Categories.Direct.StrictDownset (suffixDirect GM) using (↡Psh)
open import Cubical.Categories.Direct.Guarded.Family (suffixDirect GM)
  using (▷FamF ; FamStrength ; strength→LC)
open import Cubical.Categories.Direct.Guarded.Presheaf (suffixDirect GM) using (pshGuarded)
open import Cubical.Categories.Enriched.Enrichment.LocallyContractive using (isLocallyContractive)
open import Cubical.Categories.Enriched.Enrichment.Instances.Family.Limits (Suffix GM) ℓ-zero
  using (famEnrichment)

private
  M = GM .fst
  deg = GM .snd .fst
  open MonoidStr (M .snd)
  open IsMonoidHom (GM .snd .snd)
  module S = Category (Suffix GM)

Ob : Type
Ob = Category.ob (Suffix GM)

Fam : Category _ _
Fam = Setᴬ Ob ℓ-zero

private
  module Fam = Category Fam

⌈_⌉ : ⟨ M ⟩ → Fam.ob
⌈ m ⌉ (_ , w) = (w ≡ m) , isProp→isSet (is-set w m)

N : Fam.ob
N (_ , u) = (0 < deg u) , isProp→isSet (isProp≤ {1} {deg u})

_⊗_ : Fam.ob → Fam.ob → Fam.ob
(A ⊗ B) (_ , w) = (Σ[ u ∈ ⟨ M ⟩ ] Σ[ v ∈ ⟨ M ⟩ ] (u · v ≡ w) × ⟨ A (tt , u) ⟩ × ⟨ B (tt , v) ⟩)
  , isSetΣ is-set λ u → isSetΣ is-set λ v →
      isSet× (isProp→isSet (is-set _ _)) (isSet× (A _ .snd) (B _ .snd))

_⊸_ : Fam.ob → Fam.ob → Fam.ob
(A ⊸ C) (_ , v) = (∀ u → ⟨ A (tt , u) ⟩ → ⟨ C (tt , u · v) ⟩)
  , isSetΠ2 λ u _ → C _ .snd

D : Fam.ob → Fam.ob → Fam.ob
D A X (_ , v) = (Σ[ u ∈ ⟨ M ⟩ ] ⟨ A (tt , u) ⟩ × ⟨ X (tt , u · v) ⟩)
  , isSetΣ is-set λ u → isSet× (A _ .snd) (X _ .snd)

√ : Fam.ob → Fam.ob → Fam.ob
√ A C (_ , w) = (∀ u v → u · v ≡ w → ⟨ A (tt , u) ⟩ → ⟨ C (tt , v) ⟩)
  , isSetΠ2 λ u v → isSetΠ2 λ _ _ → C _ .snd

▷ ◁ : Fam.ob → Fam.ob
▷ = √ N
◁ = D N

module _ {A C : Fam.ob} where
  ⊗⊣⊸ : ∀ X → Iso (Fam [ A ⊗ X , C ]) (Fam [ X , A ⊸ C ])
  ⊗⊣⊸ X .Iso.fun f (_ , v) x u a = f (tt , u · v) (u , v , refl , a , x)
  ⊗⊣⊸ X .Iso.inv g (_ , w) (u , v , p , a , x) = subst (λ z → ⟨ C (tt , z) ⟩) p (g (tt , v) x u a)
  ⊗⊣⊸ X .Iso.sec g = funExt λ (_ , v) → funExt λ x → funExt λ u → funExt λ a →
    transportRefl (g (tt , v) x u a)
  ⊗⊣⊸ X .Iso.ret f = funExt λ (_ , w) → funExt λ (u , v , p , a , x) →
    J (λ w' p' → subst (λ z → ⟨ C (tt , z) ⟩) p' (f (tt , u · v) (u , v , refl , a , x))
                 ≡ f (tt , w') (u , v , p' , a , x))
      (transportRefl _) p

  D⊣√ : ∀ X → Iso (Fam [ D A X , C ]) (Fam [ X , √ A C ])
  D⊣√ X .Iso.fun f (_ , w) x u v p a = f (tt , v) (u , a , subst (λ z → ⟨ X (tt , z) ⟩) (sym p) x)
  D⊣√ X .Iso.inv g (_ , v) (u , a , x) = g (tt , u · v) x u v refl a
  D⊣√ X .Iso.sec g = funExt λ (_ , w) → funExt λ x → funExt λ u → funExt λ v → funExt λ p →
    funExt λ a →
      J (λ w' p' → (x' : ⟨ X (tt , w') ⟩)
           → g (tt , u · v) (subst (λ z → ⟨ X (tt , z) ⟩) (sym p') x') u v refl a
             ≡ g (tt , w') x' u v p' a)
        (λ x' → cong (λ y → g (tt , u · v) y u v refl a) (transportRefl x')) p x
  D⊣√ X .Iso.ret f = funExt λ (_ , v) → funExt λ (u , a , x) →
    cong (λ y → f (tt , v) (u , a , y)) (transportRefl x)

module _ (m : ⟨ M ⟩) where
  D⌈⌉ : ∀ X v → Iso ⟨ D ⌈ m ⌉ X (tt , v) ⟩ ⟨ X (tt , m · v) ⟩
  D⌈⌉ X v .Iso.fun (u , p , x) = subst (λ z → ⟨ X (tt , z · v) ⟩) p x
  D⌈⌉ X v .Iso.inv x = m , refl , x
  D⌈⌉ X v .Iso.sec x = transportRefl x
  D⌈⌉ X v .Iso.ret (u , p , x) = ΣPathP (sym p , ΣPathP ((λ i j → p (~ i ∨ j)) ,
    symP (transport-filler (cong (λ z → ⟨ X (tt , z · v) ⟩) p) x)))

  ⌈⌉⊸ : ∀ C v → Iso ⟨ (⌈ m ⌉ ⊸ C) (tt , v) ⟩ ⟨ C (tt , m · v) ⟩
  ⌈⌉⊸ C v .Iso.fun g = g m refl
  ⌈⌉⊸ C v .Iso.inv c u p = subst (λ z → ⟨ C (tt , z · v) ⟩) (sym p) c
  ⌈⌉⊸ C v .Iso.sec c = transportRefl c
  ⌈⌉⊸ C v .Iso.ret g = funExt λ u → funExt λ p →
    J (λ u' p' → subst (λ z → ⟨ C (tt , z · v) ⟩) p' (g m refl) ≡ g u' (sym p'))
      (transportRefl _) (sym p)

  D⌈⌉≅⌈⌉⊸ : ∀ X v → Iso ⟨ D ⌈ m ⌉ X (tt , v) ⟩ ⟨ (⌈ m ⌉ ⊸ X) (tt , v) ⟩
  D⌈⌉≅⌈⌉⊸ X v = compIso (D⌈⌉ X v) (invIso (⌈⌉⊸ X v))

Pos : Type
Pos = Σ[ m ∈ ⟨ M ⟩ ] (0 < deg m)

▷≅⨀√ : ∀ C w → Iso ⟨ ▷ C (tt , w) ⟩ (∀ ((m , _) : Pos) → ⟨ √ ⌈ m ⌉ C (tt , w) ⟩)
▷≅⨀√ C w .Iso.fun f (m , n) u v p q = f u v p (subst (λ z → 0 < deg z) (sym q) n)
▷≅⨀√ C w .Iso.inv g u v p n = g (u , n) u v p refl
▷≅⨀√ C w .Iso.sec g = funExt λ (m , n) → funExt λ u → funExt λ v → funExt λ p → funExt λ q →
  J (λ m' q' → (n' : 0 < deg m')
       → g (u , subst (λ z → 0 < deg z) (sym q') n') u v p refl ≡ g (m' , n') u v p q')
    (λ n' → cong (λ k → g (u , k) u v p refl) (transportRefl n')) q n
▷≅⨀√ C w .Iso.ret f = funExt λ u → funExt λ v → funExt λ p → funExt λ n →
  cong (f u v p) (transportRefl n)

pos→< : ∀ a b c → a + b ≡ c → 0 < a → b < c
pos→< zero    b c e ()
pos→< (suc a) b c e _ = subst (suc b ≤_) e (n≤k+n {k = a} b)

<→pos : ∀ a b c → a + b ≡ c → b < c → 0 < a
<→pos zero    b c e q = ⊥.rec (<→≢ {b} {c} q e)
<→pos (suc a) b c e q = tt

pos· : ∀ h k → 0 < deg h → 0 < deg (h · k)
pos· h k n = subst (0 <_) (sym (pres· h k))
  (≤-trans {1} {deg h} {deg h + deg k} n (k≤k+n {n = deg k} (deg h)))

degSplit : ∀ {u v w} → u · v ≡ w → deg u + deg v ≡ deg w
degSplit {u} {v} p = sym (pres· u v) ∙ cong deg p

module _ (A : Fam.ob) {w : ⟨ M ⟩} where
  private
    ▷A = ⟨ ▷ A (tt , w) ⟩

  ▷-cong : (β : ▷A) {m m' z : ⟨ M ⟩} (e : m ≡ m') (p : m · z ≡ w) (p' : m' · z ≡ w)
    (n : 0 < deg m) (n' : 0 < deg m') → β m z p n ≡ β m' z p' n'
  ▷-cong β {z = z} e p p' n n' i =
    β (e i) z (isProp→PathP (λ i → is-set (e i · z) w) p p' i)
      (isProp→PathP (λ i → isProp≤ {1} {deg (e i)}) n n' i)

  ▷Fam≅▷ : Iso ⟨ (▷FamF ⟅ A ⟆) (tt , w) ⟩ ▷A
  ▷Fam≅▷ .Iso.fun α u v p n =
    α .N-ob (tt , v) ((u , p) , pos→< (deg u) (deg v) (deg w) (degSplit p) n) (tt , v) S.id
  ▷Fam≅▷ .Iso.inv β .N-ob (_ , y) ((h , p) , q) (_ , z) (k , r) =
    β (h · k) z (sym (·Assoc h k z) ∙ cong (h ·_) r ∙ p)
      (pos· h k (<→pos (deg h) (deg y) (deg w) (degSplit p) q))
  ▷Fam≅▷ .Iso.inv β .N-hom (_ , y') (_ , y) (f , s) ((h , p) , q) ((h' , p') , q') eq =
    funExt λ (_ , z) → funExt λ (k , r) →
      ▷-cong β (·Assoc h f k ∙ cong (_· k) (cong (λ e → e .fst .fst) eq)) _ _ _ _
  ▷Fam≅▷ .Iso.sec β = funExt λ u → funExt λ v → funExt λ p → funExt λ n →
    ▷-cong β (·IdR u) _ _ _ _
  ▷Fam≅▷ .Iso.ret α = makePshHomStrictPath (funExt λ (_ , y) → funExt λ ((h , p) , q) →
    funExt λ (_ , z) → funExt λ (k , r) →
        cong (λ e → α .N-ob (tt , z) e (tt , z) S.id)
          (Σ≡Prop (λ _ → isProp≤ {suc (deg z)} {deg w}) (Σ≡Prop (λ _ → is-set _ _) refl))
      ∙ sym (funExt⁻ (funExt⁻ (α .N-hom (tt , z) (tt , y) (k , r) ((h , p) , q) _ refl) (tt , z)) S.id)
      ∙ cong (α .N-ob (tt , y) ((h , p) , q) (tt , z)) (S.⋆IdL (k , r)))

NonNullable : Fam.ob → Type
NonNullable A = ∀ u → ⟨ A (tt , u) ⟩ → 0 < deg u

_⊗- : Fam.ob → Functor Fam Fam
(A ⊗-) .F-ob X = A ⊗ X
(A ⊗-) .F-hom f _ (u , v , p , a , x) = u , v , p , a , f (tt , v) x
(A ⊗-) .F-id = refl
(A ⊗-) .F-seq f g = refl

module _ (A : Fam.ob) (nn : NonNullable A) where
  ⊗-strength : FamStrength (A ⊗-)
  ⊗-strength .FamStrength.st (_ , w) e (u , v , p , a , x) =
    u , v , p , a , e (tt , v) (u , p) (pos→< (deg u) (deg v) (deg w) (degSplit p) (nn u a)) x
  ⊗-strength .FamStrength.st-seq _ _ _ _ = refl
  ⊗-strength .FamStrength.st-hom _ _ = refl

  ⊗-LC : isLocallyContractive pshGuarded famEnrichment famEnrichment (A ⊗-)
  ⊗-LC = strength→LC ⊗-strength

⌈⌉-NN : ∀ m → 0 < deg m → NonNullable ⌈ m ⌉
⌈⌉-NN m n u p = subst (λ z → 0 < deg z) (sym p) n

NonNullable-⊗ˡ : ∀ {A} B → NonNullable A → NonNullable (A ⊗ B)
NonNullable-⊗ˡ B nn w (u , v , s , a , b) =
  subst (0 <_) (degSplit s) (≤-trans {1} {deg u} {deg u + deg v} (nn u a) (k≤k+n {n = deg v} (deg u)))

⌈_⌉⊗-LC : ∀ m → 0 < deg m → isLocallyContractive pshGuarded famEnrichment famEnrichment (⌈ m ⌉ ⊗-)
⌈ m ⌉⊗-LC n = ⊗-LC ⌈ m ⌉ λ u p → subst (λ z → 0 < deg z) (sym p) n

N⊗-LC : isLocallyContractive pshGuarded famEnrichment famEnrichment (N ⊗-)
N⊗-LC = ⊗-LC N λ u n → n

module _ (A B C : Fam.ob) (w : ⟨ M ⟩) where
  √⊗ : Iso ⟨ √ (A ⊗ B) C (tt , w) ⟩ ⟨ √ A (√ B C) (tt , w) ⟩
  √⊗ .Iso.fun f u y p a u' v q b =
    f (u · u') v (sym (·Assoc u u' v) ∙ cong (u ·_) q ∙ p) (u , u' , refl , a , b)
  √⊗ .Iso.inv g x v p (u , u' , r , a , b) =
    g u (u' · v) (·Assoc u u' v ∙ cong (_· v) r ∙ p) a u' v refl b
  √⊗ .Iso.sec g = funExt λ u → funExt λ y → funExt λ p → funExt λ a → funExt λ u' →
    funExt λ v → funExt λ q → funExt λ b →
      J (λ y' q' → (p' : u · y' ≡ w)
           → g u (u' · v) (·Assoc u u' v ∙ refl ∙ (sym (·Assoc u u' v) ∙ cong (u ·_) q' ∙ p'))
               a u' v refl b
             ≡ g u y' p' a u' v q' b)
        (λ p' → cong (λ π → g u (u' · v) π a u' v refl b) (is-set _ _ _ _)) q p
  √⊗ .Iso.ret f = funExt λ x → funExt λ v → funExt λ p → funExt λ (u , u' , r , a , b) →
    J (λ x' r' → (p' : x' · v ≡ w)
         → f (u · u') v (sym (·Assoc u u' v) ∙ refl ∙ (·Assoc u u' v ∙ cong (_· v) r' ∙ p'))
             (u , u' , refl , a , b)
           ≡ f x' v p' (u , u' , r' , a , b))
      (λ p' → cong (λ π → f (u · u') v π (u , u' , refl , a , b)) (is-set _ _ _ _)) r p

▷▷ : ∀ C w → Iso ⟨ ▷ (▷ C) (tt , w) ⟩ ⟨ √ (N ⊗ N) C (tt , w) ⟩
▷▷ C w = invIso (√⊗ N N C w)

√-cong : ∀ {A B} C w → (∀ u → Iso ⟨ A (tt , u) ⟩ ⟨ B (tt , u) ⟩)
  → Iso ⟨ √ A C (tt , w) ⟩ ⟨ √ B C (tt , w) ⟩
√-cong C w e .Iso.fun f u v p b = f u v p (e u .Iso.inv b)
√-cong C w e .Iso.inv g u v p a = g u v p (e u .Iso.fun a)
√-cong C w e .Iso.sec g = funExt λ u → funExt λ v → funExt λ p → funExt λ b →
  cong (g u v p) (e u .Iso.sec b)
√-cong C w e .Iso.ret f = funExt λ u → funExt λ v → funExt λ p → funExt λ a →
  cong (f u v p) (e u .Iso.ret a)

𝟏 : Fam.ob
𝟏 _ = Unit , isSetUnit

_⊕_ : Fam.ob → Fam.ob → Fam.ob
(A ⊕ B) x = (⟨ A x ⟩ ⊎ ⟨ B x ⟩) , isSet⊎ (A x .snd) (B x .snd)

private
  isContrSingl' : ∀ {ℓ} {X : Type ℓ} (x : X) → isContr (Σ[ y ∈ X ] y ≡ x)
  isContrSingl' x = (x , refl) , λ (y , p) i → p (~ i) , λ j → p (~ i ∨ j)

module _ (C : Fam.ob) (w : ⟨ M ⟩) where
  √ε : Iso ⟨ √ ⌈ ε ⌉ C (tt , w) ⟩ ⟨ C (tt , w) ⟩
  √ε = compIso reorder
      (compIso (Π-contractDomIso (isContrSingl' ε))
      (compIso unit
      (compIso curryV (Π-contractDomIso (isContrSingl' w)))))
    where
    reorder : Iso ⟨ √ ⌈ ε ⌉ C (tt , w) ⟩ (∀ ((u , _) : Σ[ u ∈ ⟨ M ⟩ ] u ≡ ε) v → u · v ≡ w → ⟨ C (tt , v) ⟩)
    reorder = iso (λ f (u , q) v p → f u v p q) (λ g u v p q → g (u , q) v p) (λ _ → refl) (λ _ → refl)
    unit : Iso (∀ v → ε · v ≡ w → ⟨ C (tt , v) ⟩) (∀ v → v ≡ w → ⟨ C (tt , v) ⟩)
    unit = iso (λ g v p → g v (·IdL v ∙ p)) (λ h v p → h v (sym (·IdL v) ∙ p))
      (λ h → funExt λ v → funExt λ p → cong (h v) (is-set _ _ _ _))
      (λ g → funExt λ v → funExt λ p → cong (g v) (is-set _ _ _ _))
    curryV : Iso (∀ v → v ≡ w → ⟨ C (tt , v) ⟩) (∀ ((v , _) : Σ[ v ∈ ⟨ M ⟩ ] v ≡ w) → ⟨ C (tt , v) ⟩)
    curryV = iso (λ h (v , p) → h v p) (λ k v p → k (v , p)) (λ _ → refl) (λ _ → refl)

module _ (A B C : Fam.ob) (w : ⟨ M ⟩) where
  √⊕ : Iso ⟨ √ (A ⊕ B) C (tt , w) ⟩ (⟨ √ A C (tt , w) ⟩ × ⟨ √ B C (tt , w) ⟩)
  √⊕ .Iso.fun f = (λ u v p a → f u v p (inl a)) , (λ u v p b → f u v p (inr b))
  √⊕ .Iso.inv (g , h) u v p (inl a) = g u v p a
  √⊕ .Iso.inv (g , h) u v p (inr b) = h u v p b
  √⊕ .Iso.sec _ = refl
  √⊕ .Iso.ret f = funExt λ u → funExt λ v → funExt λ p → funExt λ { (inl a) → refl ; (inr b) → refl }

module _ (u : ⟨ M ⟩) where
  N≅↡ε : Iso ⟨ N (tt , u) ⟩ ⟨ ↡Psh (tt , u) .F-ob (tt , ε) ⟩
  N≅↡ε .Iso.fun n = (u , ·IdR u) , subst (_< deg u) (sym presε) n
  N≅↡ε .Iso.inv (_ , q) = subst (_< deg u) presε q
  N≅↡ε .Iso.sec ((h , p) , q) = ΣPathP
    ( ΣPathP (sym (sym (·IdR h) ∙ p) , isProp→PathP (λ i → is-set _ _) _ _)
    , isProp→PathP (λ i → isProp≤ {suc (deg ε)} {deg u}) _ _)
  N≅↡ε .Iso.ret n = isProp≤ {1} {deg u} _ _

isConical : Type
isConical = ∀ x → deg x ≡ 0 → x ≡ ε

module _ (conical : isConical) where
  private
    classify : ∀ u n → deg u ≡ n → ⟨ (⌈ ε ⌉ ⊕ N) (tt , u) ⟩
    classify u zero    p = inl (conical u p)
    classify u (suc n) p = inr (subst (0 <_) (sym p) tt)

    disjoint : ∀ u → u ≡ ε → 0 < deg u → ⊥.⊥
    disjoint u q n = subst (0 <_) (cong deg q ∙ presε) n

  𝟏≅⌈ε⌉⊕N : ∀ u → Iso ⟨ 𝟏 (tt , u) ⟩ ⟨ (⌈ ε ⌉ ⊕ N) (tt , u) ⟩
  𝟏≅⌈ε⌉⊕N u = iso (λ _ → classify u (deg u) refl) (λ _ → tt)
    (λ x → isProp⊎ (is-set u ε) (isProp≤ {1} {deg u}) (disjoint u) _ x) (λ _ → refl)

  √𝟏≅Id×▷ : ∀ C w → Iso ⟨ √ 𝟏 C (tt , w) ⟩ (⟨ C (tt , w) ⟩ × ⟨ ▷ C (tt , w) ⟩)
  √𝟏≅Id×▷ C w = compIso (√-cong C w 𝟏≅⌈ε⌉⊕N)
    (compIso (√⊕ ⌈ ε ⌉ N C w) (prodIso (√ε C w) idIso))
