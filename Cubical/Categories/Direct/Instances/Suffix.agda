-- Minimal test of Löb for the poset of strings with suffix ordering
-- More substantive use is left for grammars-and-semantic-actions
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Cubical.Categories.Direct.Instances.Suffix
  {ℓ} (Alphabet : Type ℓ) (isSetAlphabet : isSet Alphabet) where

open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; suc ; _+_)
open import Cubical.Data.Nat.Order.Recursive as NatOrd using (_<_ ; ≤-+k)
open import Cubical.Data.List
open import Cubical.Data.List.Properties
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary
open import Cubical.Induction.WellFounded

open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Instances.Poset

private
  Str : Type ℓ
  Str = List Alphabet

  isSetStr : isSet Str
  isSetStr = isOfHLevelList 0 isSetAlphabet

_<ˢ_ : Str → Str → Type ℓ
w <ˢ w' = Σ[ u ∈ Str ] (¬ (u ≡ [])) × (u ++ w ≡ w')

++-cancelˡ : (xs : Str) {ys zs : Str} → xs ++ ys ≡ xs ++ zs → ys ≡ zs
++-cancelˡ []       p = p
++-cancelˡ (x ∷ xs) p = ++-cancelˡ xs (cons-inj₂ p)

++-cancelʳ : {xs ys : Str} (zs : Str) → xs ++ zs ≡ ys ++ zs → xs ≡ ys
++-cancelʳ {xs} {ys} zs p =
  sym (rev-rev xs)
  ∙∙ cong rev (++-cancelˡ (rev zs)
       (sym (rev-++ xs zs) ∙∙ cong rev p ∙∙ rev-++ ys zs))
  ∙∙ rev-rev ys

isProp<ˢ : ∀ w w' → isProp (w <ˢ w')
isProp<ˢ w w' (u₁ , ne₁ , e₁) (u₂ , ne₂ , e₂) =
  Σ≡Prop (λ u → isProp× (isProp¬ _) (isSetStr _ _))
         (++-cancelʳ w (e₁ ∙ sym e₂))

++≡[]ˡ : {xs ys : Str} → xs ++ ys ≡ [] → xs ≡ []
++≡[]ˡ {[]}     p = refl
++≡[]ˡ {x ∷ xs} p = ⊥.rec (¬cons≡nil p)

trans<ˢ : ∀ {w w' w''} → w <ˢ w' → w' <ˢ w'' → w <ˢ w''
trans<ˢ {w} (u₁ , ne₁ , e₁) (u₂ , ne₂ , e₂) =
  (u₂ ++ u₁)
  , (λ p → ne₂ (++≡[]ˡ p))
  , (++-assoc u₂ u₁ w ∙ cong (u₂ ++_) e₁ ∙ e₂)

private
  shorter : ∀ (u w : Str) → ¬ (u ≡ []) → length w < length u + length w
  shorter []       w ne = ⊥.rec (ne refl)
  shorter (a ∷ u') w _  = ≤-+k {m = 0} {n = length u'} {k = length w} _

<ˢ→length< : ∀ {w w'} → w <ˢ w' → length w < length w'
<ˢ→length< {w} (u , ne , e) =
  subst (length w <_) (cong length e)
        (subst (length w <_) (sym (length++ u w)) (shorter u w ne))

private
  suffixAcc : ∀ w → Acc _<_ (length w) → Acc _<ˢ_ w
  suffixAcc w (acc f) = acc (λ w' r → suffixAcc w' (f (length w') (<ˢ→length< r)))

wf<ˢ : WellFounded _<ˢ_
wf<ˢ w = suffixAcc w (NatOrd.WellFounded.wf-< (length w))

SuffixWFOrder : WFOrder ℓ ℓ
SuffixWFOrder = record
  { D       = Str
  ; isSetD  = isSetStr
  ; _<_     = _<ˢ_
  ; isProp< = isProp<ˢ
  ; trans<  = trans<ˢ
  ; wf<     = wf<ˢ
  }

SuffixCat = PosetCat SuffixWFOrder

SuffixDirect : DirectStr {C = SuffixCat} SuffixWFOrder
SuffixDirect = PosetDirect SuffixWFOrder
