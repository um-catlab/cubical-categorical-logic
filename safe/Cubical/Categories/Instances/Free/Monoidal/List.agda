{-

  The free monoidal category can be constructed "explicitly" by having
  the objects be lists. This can be thought of as a kind of "normal
  form" for monoidal category expressions.

  Currently, we only need this for the coherence theorem, for which we
  (1) only need the recursion principle, not the uniqueness principle
  and (2) assume the generating objects form an hSet, which simplifies
  the monoidal structure. I'm not sure how much of this carries over
  if the generating objects are only assumed to be a groupoid.

-}

module Cubical.Categories.Instances.Free.Monoidal.List where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.List as List hiding ([_]; rec)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.HLevels
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Discrete
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.Monoidal.Properties
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More


private
  variable
    ℓ ℓQ ℓQ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open Functor
open NatTrans
open NatIso
open isIso
module _ (X : hSet ℓ) where
  |LIST| : Category ℓ ℓ
  |LIST| = DiscreteCategory
    ((List ⟨ X ⟩) , (isSet→isGroupoid (isOfHLevelList 0 (X .snd))))

  isThin|LIST| : hasPropHoms |LIST|
  isThin|LIST| = isOfHLevelList 0 (X .snd) _ _

    -- todo: generalize, discreteCat of any monoid is monoidal
  LIST : MonoidalCategory ℓ ℓ
  LIST = MonoidalPreorder→MonoidalCategory (record
      { C = |LIST|
      ; isPropHom = isThin|LIST|
      ; unit = []
      ; ─⊗─ = mkFunctor |LIST| isThin|LIST|
        (λ x → x .fst ++ x .snd)
        λ x → cong₂ _++_ (x .fst) (x .snd)
      ; α⟨_,_,_⟩ = λ x y z → sym (++-assoc x y z)
      ; α⁻¹⟨_,_,_⟩ = ++-assoc
      ; η⟨_⟩ = λ _ → refl
      ; η⁻¹⟨_⟩ = λ _ → refl
      ; ρ⟨_⟩ = λ x → ++-unit-r x
      ; ρ⁻¹⟨_⟩ = λ x → sym (++-unit-r x)
      })
  private
    module L = MonoidalCategory LIST

  module _ (M : MonoidalCategory ℓC ℓC') where
    private
      module M = MonoidalCategory M

    module _ (ı : ⟨ X ⟩ → M.ob) where
      rec-ob : List ⟨ X ⟩ → M.ob
      rec-ob [] = M.unit
      rec-ob (x ∷ xs) = ı x M.⊗ rec-ob xs

      |rec| : Functor L.C M.C
      |rec| = DiscFunc rec-ob

      open StrongMonoidalFunctor
      open StrongMonoidalStr
      open LaxMonoidalStr

      |μ| : ∀ xs ys
        → CatIso M.C
            ((|rec| ⟅ xs ⟆) M.⊗ (|rec| ⟅ ys ⟆)) -- (x ⊗ xs) ⊗ ys
            (|rec| ⟅ xs ++ ys ⟆) -- x ⊗ (xs ⊗ ys)
      |μ| [] ys = NatIsoAt M.η (|rec| ⟅ ys ⟆)
      |μ| (x ∷ xs) ys =
        ⋆Iso
          (invIso (NatIsoAt M.α _))
          (F-Iso {F = M.─⊗─} (CatIso× M.C M.C idCatIso (|μ| xs ys)))

      μ-nat-goal : ∀ xs xs' (p : xs ≡ xs') ys ys' (q : ys ≡ ys') → Type ℓC'
      μ-nat-goal xs xs' p ys ys' q =
        ((|rec| ⟪ p ⟫) M.⊗ₕ (|rec| ⟪ q ⟫)) M.⋆ |μ| xs' ys' .fst
          ≡ |μ| xs ys .fst M.⋆ (|rec| ⟪ cong₂ _++_ p q ⟫)

      μ-nat : ∀ {xs xs'} (p : xs ≡ xs') {ys ys'} (q : ys ≡ ys')
        → μ-nat-goal xs xs' p ys ys' q
      μ-nat {xs} =
        J (λ xs' (p : xs ≡ xs') →
          ∀ {ys} {ys'} → (q : ys ≡ ys') → μ-nat-goal xs xs' p ys ys' q)
        λ {ys} →
        J (λ ys' (q : ys ≡ ys') → μ-nat-goal xs xs refl ys ys' q)
        (cong₂ M._⋆_ ((M.─⊗─ ∘F (|rec| ×F |rec|)) .F-id {x = (xs , ys)}) refl
        ∙ M.⋆IdL _
        ∙ sym (M.⋆IdR _)
        ∙ cong₂ M._⋆_ refl (sym (|rec| .F-id {x = xs ++ ys})))

      ρ∷ : ∀ x xs → L.ρ⟨ x ∷ xs ⟩ ≡ (L.id L.⊗ₕ L.ρ⟨ xs ⟩)
      ρ∷ x xs = refl

      rec∷ : ∀ {x}{xs ys} (ps : xs ≡ ys)
        → |rec| ⟪ cong (x ∷_) ps ⟫
          ≡ M.id M.⊗ₕ |rec| ⟪ ps ⟫
      rec∷ {x}{xs}{ys} =
        J (λ ys ps → |rec| ⟪ cong (x ∷_) ps ⟫ ≡ M.id M.⊗ₕ |rec| ⟪ ps ⟫ )
          (|rec| .F-id {x ∷ xs}
          ∙ sym (M.─⊗─ .F-id)
          ∙ cong₂ M._⊗ₕ_ refl (sym (|rec| .F-id {xs})))

      opaque
        μ-pf : ∀ xs ys zs →
          (M.α⟨ _ , _ , _ ⟩ M.⋆ (|μ| xs ys .fst M.⊗ₕ M.id))
          M.⋆ |μ| (xs ++ ys) zs .fst
            ≡
          ((M.id M.⊗ₕ |μ| ys zs .fst) M.⋆ |μ| xs (ys ++ zs) .fst)
          M.⋆ |rec| ⟪ L.α⟨ xs , ys , zs ⟩ ⟫
        μ-pf [] ys zs =
          cong₂ M._⋆_ (η⟨⊗⟩ M (|rec| ⟅ ys ⟆) (|rec| ⟅ zs ⟆)) refl
          ∙ sym (M.η .trans .N-hom _)
          ∙ sym (M.⋆IdR _) ∙ cong₂ M._⋆_ refl (sym (|rec| .F-id {ys ++ zs}))
        μ-pf (x ∷ xs) ys zs =
          cong₂ M._⋆_
            (cong₂ M._⋆_ refl
              (cong₂ M._⊗ₕ_ refl (sym (M.⋆IdL _)) ∙ M.─⊗─ .F-seq _ _)
              ∙ sym (M.⋆Assoc _ _ _))
            refl
          ∙ M.⋆Assoc _ _ _
          ∙ cong₂ M._⋆_ refl
            (sym (M.⋆Assoc _ _ _)
            ∙ cong₂ M._⋆_ (symNatIso M.α .trans .N-hom _) refl
            ∙ (M.⋆Assoc _ _ _))
          ∙ sym (M.⋆Assoc _ _ _)
          ∙ cong₂ M._⋆_ (pentagon' M _ _ _ _) refl
          ∙ M.⋆Assoc _ _ _
          ∙ cong₂ M._⋆_ refl
            (cong₂ M._⋆_ refl (sym (M.─⊗─ .F-seq _ _))
            ∙ sym (M.─⊗─ .F-seq _ _)
            ∙ cong₂ M._⊗ₕ_
              (M.⋆IdL _ ∙ M.⋆IdL _ ∙ sym (M.⋆IdL _))
              (sym (M.⋆Assoc _ _ _) ∙ μ-pf xs ys zs ∙ M.⋆Assoc _ _ _)
            ∙ M.─⊗─ .F-seq _ _)
          ∙ sym (M.⋆Assoc _ _ _)
          ∙ cong₂ M._⋆_ (sym (symNatIso M.α .trans .N-hom _)) refl
          ∙ M.⋆Assoc _ _ _
          ∙ cong₂ M._⋆_
            (cong₂ M._⊗ₕ_ (M.─⊗─ .F-id) refl)
            (cong₂ M._⋆_ refl
              (cong₂ M._⊗ₕ_ (sym (M.⋆IdL _)) refl ∙ M.─⊗─ .F-seq _ _)
            ∙ sym (M.⋆Assoc _ _ _))
          ∙ sym (M.⋆Assoc _ _ _)
          ∙ cong₂ M._⋆_ refl (sym (rec∷ {x = x} L.α⟨ xs , ys , zs ⟩))

        ρε-pf : ∀ xs →
          (|μ| xs [] .fst) M.⋆ (|rec| ⟪ L.ρ⟨ xs ⟩ ⟫) ≡ M.ρ⟨ |rec| ⟅ xs ⟆ ⟩
        -- famous property: ρ⟨ unit ⟩ ≡ η⟨ unit ⟩
        ρε-pf [] = cong₂ M._⋆_ refl (|rec| .F-id {x = []}) ∙ M.⋆IdR _
          ∙ sym (ρ⟨unit⟩≡η⟨unit⟩ M)
        ρε-pf (x ∷ xs) =
          cong₂ M._⋆_ refl (rec∷ L.ρ⟨ xs ⟩)
          ∙ M.⋆Assoc _ _ _
          ∙ cong₂ M._⋆_ refl (sym (M.─⊗─ .F-seq _ _)
          ∙ cong₂ M._⊗ₕ_ (M.⋆IdL _) (ρε-pf xs))
          ∙ cong₂ M._⋆_ refl (sym (ρ⟨⊗⟩ M) )
          ∙ sym (M.⋆Assoc _ _ _)
          ∙ cong₂ M._⋆_ (M.α .nIso _ .sec) refl
          ∙ M.⋆IdL _

      rec : StrongMonoidalFunctor LIST M
      rec .F = |rec|
      rec .strmonstr .laxmonstr .ε = M.id
      rec .strmonstr .laxmonstr .μ .NatTrans.N-ob x = |μ| (x .fst) (x .snd) .fst
      rec .strmonstr .laxmonstr .μ .NatTrans.N-hom f = μ-nat (f .fst) (f .snd)
      rec .strmonstr .laxmonstr .αμ-law = μ-pf
      rec .strmonstr .laxmonstr .ηε-law xs =
        cong₂ M._⋆_
          (cong₂ M._⋆_ (M.─⊗─ .F-id) refl ∙ M.⋆IdL _)
          (|rec| .F-id {x = xs})
        ∙ M.⋆IdR _
      rec .strmonstr .laxmonstr .ρε-law xs =
        cong₂ M._⋆_ (cong₂ M._⋆_ (M.─⊗─ .F-id) refl ∙ M.⋆IdL _) refl ∙ ρε-pf xs
      rec .strmonstr .ε-isIso = idCatIso .snd
      rec .strmonstr .μ-isIso x = |μ| (x .fst) (x .snd) .snd
