{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Direct.Base
module Cubical.Categories.Direct.Guarded.Family
  {ℓ ℓ' ℓD : Level} {A : Category ℓ ℓ'} {Wo : WFOrder ℓD ℓ'}
  (dir : DirectStr A Wo) where


open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base
import Cubical.Categories.Presheaf.Family.Base as FamBase
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Direct.StrictDownset dir using (▷ ; nextFam ; ↡Psh)
open import Cubical.Categories.Direct.Guarded.Presheaf dir using (pshGuarded ; ▷Psh-LC)
open import Cubical.Categories.Enriched.Enrichment.LocallyContractive
import Cubical.Categories.Enriched.Enrichment.Functor.Base as FE
open import Cubical.Categories.Enriched.Enrichment.Instances.Power using (Setᴬ)
open import Cubical.Categories.Enriched.Enrichment.Instances.Presheaf.StrictHom.Self A ℓ
  using (selfEnrichment)
open import Cubical.Categories.Enriched.Enrichment.Instances.Family.Limits A ℓ
  using (famEnrichment ; Γ×Fam- ; ×Fam-Enr)
open import Cubical.Categories.Enriched.Enrichment.Base using (Enrichment)
open import Cubical.Categories.Enriched.Enrichment.Instances.FullSubcategory
  using (FullSubcategoryEnrichment)
open import Cubical.Categories.Enriched.Enrichment.LocallyContractive.Bifunctor pshGuarded
  using (isLocallyContractiveˡʳ ; isLocallyContractiveˡ ; isLocallyContractiveʳ)
open import Cubical.Categories.Instances.FullSubcategory
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Foundations.HLevels

open Functor
open PshHomStrict
open PshMon A ℓ using (𝓟Mon ; ℓm)
open Category A using (ob ; id ; _⋆_ ; ⋆IdL ; ⋆Assoc)
open DirectNotation dir using (_≺_ ; ≺-postcomp ; isProp≺)

private
  U = FamBase.PSH→Fam {ℓ = ℓ-zero} A
  G = FamBase.Cofree {ℓ = ℓ-zero} A
  □ = FamBase.□ {ℓ = ℓ-zero} A
  Fam = Setᴬ ob ℓm
  module Fam = Category Fam

U-Enr : FE.Enrichment 𝓟Mon selfEnrichment famEnrichment U
U-Enr .FE.Enrichment.F[_,_] P Q .N-ob c α y h p = α .N-ob y (h , p)
U-Enr .FE.Enrichment.F[_,_] P Q .N-hom c c' f α' α eq =
  funExt λ y → funExt λ h → funExt λ p → λ i → eq i .N-ob y (h , p)
U-Enr .FE.Enrichment.F-id = makePshHomStrictPath refl
U-Enr .FE.Enrichment.F-seq = makePshHomStrictPath (funExt λ c → funExt λ (α , β) →
  funExt λ y → funExt λ h → funExt λ p →
    cong₂ (λ k x → β .N-ob y (k , x)) (sym (⋆IdL h)) (cong (λ k → α .N-ob y (k , p)) (sym (⋆IdL h))))
U-Enr .FE.Enrichment.agree f = makePshHomStrictPath refl

G-Enr : FE.Enrichment 𝓟Mon famEnrichment selfEnrichment G
G-Enr .FE.Enrichment.F[_,_] P Q .N-ob c t .N-ob d (g , s) z h = t z (h ⋆ g) (s z h)
G-Enr .FE.Enrichment.F[_,_] P Q .N-ob c t .N-hom d' d k (g , s) (g' , s') eq =
  funExt λ z → funExt λ h →
    cong₂ (t z) (⋆Assoc h k g ∙ cong (h ⋆_) (cong fst eq)) (λ i → eq i .snd z h)
G-Enr .FE.Enrichment.F[_,_] P Q .N-hom c c' f t' t eq =
  makePshHomStrictPath (funExt λ d → funExt λ (g , s) → funExt λ z → funExt λ h →
    cong (λ m → t' z m (s z h)) (sym (⋆Assoc h g f))
    ∙ (λ i → eq i z (h ⋆ g) (s z h)))
G-Enr .FE.Enrichment.F-id = makePshHomStrictPath (funExt λ c → funExt λ _ →
  makePshHomStrictPath refl)
G-Enr .FE.Enrichment.F-seq = makePshHomStrictPath (funExt λ c → funExt λ (t , u) →
  makePshHomStrictPath (funExt λ d → funExt λ (g , s) → funExt λ z → funExt λ h →
    cong (λ k → u z (h ⋆ k) (t z (h ⋆ k) (s z h))) (⋆IdL g)))
G-Enr .FE.Enrichment.agree f = makePshHomStrictPath (funExt λ c → funExt λ _ →
  makePshHomStrictPath refl)

▷FamF : Functor Fam Fam
▷FamF = U ∘F ▷ ∘F G

▷Fam-LC : isLocallyContractive pshGuarded famEnrichment famEnrichment ▷FamF
▷Fam-LC = LC-postcomp pshGuarded {F = ▷ ∘F G} {H = U}
  (LC-precomp pshGuarded {H = G} {F = ▷} G-Enr ▷Psh-LC) U-Enr

module FamFix (B : Fam.ob) (Γ : Presheaf A ℓm)
  (f : Fam [ U ⟅ Γ ⟆ , ▷FamF ⟅ B ⟆ FamBase.⇒Fam B ]) where
  private
    UΓ = U .F-ob Γ
    module L = Hylo pshGuarded {F = Γ×Fam- UΓ ∘F ▷FamF}
      (LC-postcomp pshGuarded {F = ▷FamF} {H = Γ×Fam- UΓ} ▷Fam-LC (×Fam-Enr UΓ))
      {X = UΓ} {B = B}
      (λ x γ → γ , nextFam {ℓF = ℓ-zero} UΓ x (λ y h → Γ .F-hom h γ))
      (λ x (γ , b) → f x γ b)

  fix : Fam [ U ⟅ Γ ⟆ , B ]
  fix = L.hylo

  fix-fix : ∀ x γ
    → fix x γ ≡ f x γ (nextFam {ℓF = ℓ-zero} B x (λ y h → fix y (Γ .F-hom h γ)))
  fix-fix x γ = (λ i → L.hylo-eq i x γ) ∙ cong (f x γ) (makePshHomStrictPath refl)

  fix-uniq : (s : Fam [ U ⟅ Γ ⟆ , B ])
    → (∀ x γ → s x γ ≡ f x γ (nextFam {ℓF = ℓ-zero} B x (λ y h → s y (Γ .F-hom h γ))))
    → s ≡ fix
  fix-uniq s s-fix = L.hylo-uniq s (funExt λ x → funExt λ γ →
    s-fix x γ ∙ cong (f x γ) (makePshHomStrictPath refl))

module _ (B : Fam.ob) where
  private
    module B = FamFix B (G ⟅ ▷FamF ⟅ B ⟆ FamBase.⇒Fam B ⟆) (λ y t → t y id)

  löbFam' : Fam [ □ ⟅ ▷FamF ⟅ B ⟆ FamBase.⇒Fam B ⟆ , B ]
  löbFam' = B.fix

  löbFam'-fix : ∀ x t
    → löbFam' x t ≡ t x id (nextFam {ℓF = ℓ-zero} B x (λ y h → löbFam' y (λ z k → t z (k ⋆ h))))
  löbFam'-fix = B.fix-fix

  löbFam'-uniq : (s : Fam [ □ ⟅ ▷FamF ⟅ B ⟆ FamBase.⇒Fam B ⟆ , B ])
    → (∀ x t → s x t ≡ t x id (nextFam {ℓF = ℓ-zero} B x (λ y h → s y (λ z k → t z (k ⋆ h)))))
    → s ≡ löbFam'
  löbFam'-uniq = B.fix-uniq

Earlier : Fam.ob → Fam.ob → ob → Type ℓm
Earlier X Y x = ∀ y → A [ y , x ] → y ≺ x → ⟨ X y ⟩ → ⟨ Y y ⟩

record FamStrength (H : Functor Fam Fam) : Type (ℓ-suc ℓm) where
  field
    st : ∀ {X Y} x → Earlier X Y x → ⟨ (H ⟅ X ⟆) x ⟩ → ⟨ (H ⟅ Y ⟆) x ⟩
    st-seq : ∀ {X Y Z} x (e : Earlier X Y x) (e' : Earlier Y Z x) (h : ⟨ (H ⟅ X ⟆) x ⟩)
      → st {X} {Z} x (λ y g q a → e' y g q (e y g q a)) h ≡ st {Y} {Z} x e' (st {X} {Y} x e h)
    st-hom : ∀ {X Y} (f : Fam [ X , Y ]) x → (H ⟪ f ⟫) x ≡ st {X} {Y} x (λ y _ _ → f y)

module _ {H : Functor Fam Fam} (S : FamStrength H) where
  open FamStrength S

  strength→LC : isLocallyContractive pshGuarded famEnrichment famEnrichment H
  strength→LC .fst .FE.EnrichmentFor.f[_,_] X Y .N-ob c β y h =
    st y λ y' g q → β .N-ob y' ((g ⋆ h) , ≺-postcomp q h) y' id
  strength→LC .fst .FE.EnrichmentFor.f[_,_] X Y .N-hom c c' k β' β eq =
    funExt λ y → funExt λ h → cong (st y) (funExt λ y' → funExt λ g → funExt λ q →
      cong (λ m → β' .N-ob y' m y' id) (Σ≡Prop (λ _ → isProp≺ _ _) (sym (⋆Assoc g h k)))
      ∙ λ i → eq i .N-ob y' ((g ⋆ h) , ≺-postcomp q h) y' id)
  strength→LC .fst .FE.EnrichmentFor.fid {X} = makePshHomStrictPath (funExt λ c → funExt λ _ →
    funExt λ y → funExt λ h → sym (st-hom (Fam.id {X}) y) ∙ funExt⁻ (H .F-id) y)
  strength→LC .fst .FE.EnrichmentFor.f-seq {X} {Y} {Z} = makePshHomStrictPath (funExt λ c →
    funExt λ (β , β') → funExt λ y → funExt λ h → funExt λ a → sym (st-seq y _ _ a))
  strength→LC .snd {X} {Y} f = makePshHomStrictPath (funExt λ c → funExt λ _ →
    funExt λ y → funExt λ h → st-hom f y)

Upto : Fam.ob → Fam.ob → ob → Type ℓm
Upto X Y x = ∀ y → A [ y , x ] → ⟨ X y ⟩ → ⟨ Y y ⟩

module _ {ℓC ℓC' : Level} {C : Category ℓC ℓC'}
  (S : hSet ℓm) (F : ⟨ S ⟩ → Functor C Fam) where
  ΣFam : Functor C Fam
  ΣFam .F-ob c x = (Σ[ s ∈ ⟨ S ⟩ ] ⟨ (F s ⟅ c ⟆) x ⟩) , isSetΣ (S .snd) λ s → (F s ⟅ c ⟆) x .snd
  ΣFam .F-hom f x (s , a) = s , (F s ⟪ f ⟫) x a
  ΣFam .F-id = funExt λ x → funExt λ (s , a) i → s , F s .F-id i x a
  ΣFam .F-seq {c} {c'} {c''} f g = funExt λ x → funExt λ (s , a) i → s , F s .F-seq f g i x a

  LC-Σ : {ℰC : Enrichment C 𝓟Mon} → (∀ s → isLocallyContractive pshGuarded ℰC famEnrichment (F s))
    → isLocallyContractive pshGuarded ℰC famEnrichment ΣFam
  LC-Σ lc .fst .FE.EnrichmentFor.f[_,_] c c' .N-ob a β x h (s , u) =
    s , lc s .fst .FE.EnrichmentFor.f[_,_] c c' .N-ob a β x h u
  LC-Σ lc .fst .FE.EnrichmentFor.f[_,_] c c' .N-hom a a' k β' β eq =
    funExt λ x → funExt λ h → funExt λ (s , u) i →
      s , lc s .fst .FE.EnrichmentFor.f[_,_] c c' .N-hom a a' k β' β eq i x h u
  LC-Σ lc .fst .FE.EnrichmentFor.fid = makePshHomStrictPath (funExt λ a → funExt λ t →
    funExt λ x → funExt λ h → funExt λ (s , u) i →
      s , lc s .fst .FE.EnrichmentFor.fid i .N-ob a t x h u)
  LC-Σ lc .fst .FE.EnrichmentFor.f-seq = makePshHomStrictPath (funExt λ a → funExt λ (β , β') →
    funExt λ x → funExt λ h → funExt λ (s , u) i →
      s , lc s .fst .FE.EnrichmentFor.f-seq i .N-ob a (β , β') x h u)
  LC-Σ lc .snd f = makePshHomStrictPath (funExt λ a → funExt λ t →
    funExt λ x → funExt λ h → funExt λ (s , u) i →
      s , lc s .snd f i .N-ob a t x h u)

module _ (K : Fam.ob) where
  Restrict : Functor Fam Fam
  Restrict .F-ob X x = (⟨ X x ⟩ × ⟨ K x ⟩) , isSet× (X x .snd) (K x .snd)
  Restrict .F-hom f x (a , k) = f x a , k
  Restrict .F-id = refl
  Restrict .F-seq f g = refl

  Restrict-Enr : FE.Enrichment 𝓟Mon famEnrichment famEnrichment Restrict
  Restrict-Enr .FE.Enrichment.F[_,_] X Y .N-ob c t x h (a , k) = t x h a , k
  Restrict-Enr .FE.Enrichment.F[_,_] X Y .N-hom c c' f t' t eq =
    funExt λ x → funExt λ h → funExt λ (a , k) i → eq i x h a , k
  Restrict-Enr .FE.Enrichment.F-id = makePshHomStrictPath refl
  Restrict-Enr .FE.Enrichment.F-seq = makePshHomStrictPath refl
  Restrict-Enr .FE.Enrichment.agree f = makePshHomStrictPath refl

module _ {P₁ P₂ : Fam.ob → Type ℓm} where
  private
    D₁ = FullSubcategory Fam P₁
    D₂ = FullSubcategory Fam P₂
    ℰ₁ = FullSubcategoryEnrichment famEnrichment P₁
    ℰ₂ = FullSubcategoryEnrichment famEnrichment P₂

  record FamStrengthˡʳ (Φ : Functor (D₁ ×C D₂) Fam) : Type (ℓ-suc ℓm) where
    field
      st : ∀ {X X' Y Y'} x → Earlier (X .fst) (X' .fst) x → Earlier (Y .fst) (Y' .fst) x
        → ⟨ (Φ ⟅ X , Y ⟆) x ⟩ → ⟨ (Φ ⟅ X' , Y' ⟆) x ⟩
      st-seq : ∀ {X X' X'' Y Y' Y''} x
        (e : Earlier (X .fst) (X' .fst) x) (e' : Earlier (X' .fst) (X'' .fst) x)
        (d : Earlier (Y .fst) (Y' .fst) x) (d' : Earlier (Y' .fst) (Y'' .fst) x)
        (h : ⟨ (Φ ⟅ X , Y ⟆) x ⟩)
        → st {X} {X''} {Y} {Y''} x (λ y g q a → e' y g q (e y g q a)) (λ y g q a → d' y g q (d y g q a)) h
          ≡ st {X'} {X''} {Y'} {Y''} x e' d' (st {X} {X'} {Y} {Y'} x e d h)
      st-hom : ∀ {X X' Y Y'} (f : Fam [ X .fst , X' .fst ]) (g : Fam [ Y .fst , Y' .fst ]) x
        → (Φ ⟪ f , g ⟫) x ≡ st {X} {X'} {Y} {Y'} x (λ y _ _ → f y) (λ y _ _ → g y)

  module _ {Φ : Functor (D₁ ×C D₂) Fam} (S : FamStrengthˡʳ Φ) where
    open FamStrengthˡʳ S

    strengthˡʳ→LC : isLocallyContractiveˡʳ {ℰD₁ = ℰ₁} {ℰD₂ = ℰ₂} {ℰE = famEnrichment} Φ
    strengthˡʳ→LC .fst .FE.EnrichmentFor.f[_,_] (X , Y) (X' , Y') .N-ob c (β , γ) y h =
      st y (λ y' g q → β .N-ob y' ((g ⋆ h) , ≺-postcomp q h) y' id)
           (λ y' g q → γ .N-ob y' ((g ⋆ h) , ≺-postcomp q h) y' id)
    strengthˡʳ→LC .fst .FE.EnrichmentFor.f[_,_] (X , Y) (X' , Y') .N-hom c c' k (β' , γ') (β , γ) eq =
      funExt λ y → funExt λ h → cong₂ (st y)
        (funExt λ y' → funExt λ g → funExt λ q →
          cong (λ m → β' .N-ob y' m y' id) (Σ≡Prop (λ _ → isProp≺ _ _) (sym (⋆Assoc g h k)))
          ∙ λ i → eq i .fst .N-ob y' ((g ⋆ h) , ≺-postcomp q h) y' id)
        (funExt λ y' → funExt λ g → funExt λ q →
          cong (λ m → γ' .N-ob y' m y' id) (Σ≡Prop (λ _ → isProp≺ _ _) (sym (⋆Assoc g h k)))
          ∙ λ i → eq i .snd .N-ob y' ((g ⋆ h) , ≺-postcomp q h) y' id)
    strengthˡʳ→LC .fst .FE.EnrichmentFor.fid {X , Y} = makePshHomStrictPath (funExt λ c → funExt λ _ →
      funExt λ y → funExt λ h → sym (st-hom (Fam.id {X .fst}) (Fam.id {Y .fst}) y) ∙ funExt⁻ (Φ .F-id) y)
    strengthˡʳ→LC .fst .FE.EnrichmentFor.f-seq = makePshHomStrictPath (funExt λ c →
      funExt λ ((β , γ) , (β' , γ')) → funExt λ y → funExt λ h → funExt λ a → sym (st-seq y _ _ _ _ a))
    strengthˡʳ→LC .snd (f , g) = makePshHomStrictPath (funExt λ c → funExt λ _ →
      funExt λ y → funExt λ h → st-hom f g y)

  record FamStrengthˡ (Φ : Functor (D₁ ×C D₂) Fam) : Type (ℓ-suc ℓm) where
    field
      st : ∀ {X X' Y Y'} x → Earlier (X .fst) (X' .fst) x → Upto (Y .fst) (Y' .fst) x
        → ⟨ (Φ ⟅ X , Y ⟆) x ⟩ → ⟨ (Φ ⟅ X' , Y' ⟆) x ⟩
      st-seq : ∀ {X X' X'' Y Y' Y''} x
        (e : Earlier (X .fst) (X' .fst) x) (e' : Earlier (X' .fst) (X'' .fst) x)
        (d : Upto (Y .fst) (Y' .fst) x) (d' : Upto (Y' .fst) (Y'' .fst) x)
        (h : ⟨ (Φ ⟅ X , Y ⟆) x ⟩)
        → st {X} {X''} {Y} {Y''} x (λ y g q a → e' y g q (e y g q a)) (λ y g a → d' y g (d y g a)) h
          ≡ st {X'} {X''} {Y'} {Y''} x e' d' (st {X} {X'} {Y} {Y'} x e d h)
      st-hom : ∀ {X X' Y Y'} (f : Fam [ X .fst , X' .fst ]) (g : Fam [ Y .fst , Y' .fst ]) x
        → (Φ ⟪ f , g ⟫) x ≡ st {X} {X'} {Y} {Y'} x (λ y _ _ → f y) (λ y _ → g y)

  module _ {Φ : Functor (D₁ ×C D₂) Fam} (S : FamStrengthˡ Φ) where
    open FamStrengthˡ S

    strengthˡ→LC : isLocallyContractiveˡ {ℰD₁ = ℰ₁} {ℰD₂ = ℰ₂} {ℰE = famEnrichment} Φ
    strengthˡ→LC .fst .FE.EnrichmentFor.f[_,_] (X , Y) (X' , Y') .N-ob c (β , γ) y h =
      st y (λ y' g q → β .N-ob y' ((g ⋆ h) , ≺-postcomp q h) y' id)
           (λ y' g → γ y' (g ⋆ h))
    strengthˡ→LC .fst .FE.EnrichmentFor.f[_,_] (X , Y) (X' , Y') .N-hom c c' k (β' , γ') (β , γ) eq =
      funExt λ y → funExt λ h → cong₂ (st y)
        (funExt λ y' → funExt λ g → funExt λ q →
          cong (λ m → β' .N-ob y' m y' id) (Σ≡Prop (λ _ → isProp≺ _ _) (sym (⋆Assoc g h k)))
          ∙ λ i → eq i .fst .N-ob y' ((g ⋆ h) , ≺-postcomp q h) y' id)
        (funExt λ y' → funExt λ g →
          cong (γ' y') (sym (⋆Assoc g h k))
          ∙ λ i → eq i .snd y' (g ⋆ h))
    strengthˡ→LC .fst .FE.EnrichmentFor.fid {X , Y} = makePshHomStrictPath (funExt λ c → funExt λ _ →
      funExt λ y → funExt λ h → sym (st-hom (Fam.id {X .fst}) (Fam.id {Y .fst}) y) ∙ funExt⁻ (Φ .F-id) y)
    strengthˡ→LC .fst .FE.EnrichmentFor.f-seq = makePshHomStrictPath (funExt λ c →
      funExt λ ((β , γ) , (β' , γ')) → funExt λ y → funExt λ h → funExt λ a → sym (st-seq y _ _ _ _ a))
    strengthˡ→LC .snd (f , g) = makePshHomStrictPath (funExt λ c → funExt λ _ →
      funExt λ y → funExt λ h → st-hom f g y)

  record FamStrengthʳ (Φ : Functor (D₁ ×C D₂) Fam) : Type (ℓ-suc ℓm) where
    field
      st : ∀ {X X' Y Y'} x → Upto (X .fst) (X' .fst) x → Earlier (Y .fst) (Y' .fst) x
        → ⟨ (Φ ⟅ X , Y ⟆) x ⟩ → ⟨ (Φ ⟅ X' , Y' ⟆) x ⟩
      st-seq : ∀ {X X' X'' Y Y' Y''} x
        (e : Upto (X .fst) (X' .fst) x) (e' : Upto (X' .fst) (X'' .fst) x)
        (d : Earlier (Y .fst) (Y' .fst) x) (d' : Earlier (Y' .fst) (Y'' .fst) x)
        (h : ⟨ (Φ ⟅ X , Y ⟆) x ⟩)
        → st {X} {X''} {Y} {Y''} x (λ y g a → e' y g (e y g a)) (λ y g q a → d' y g q (d y g q a)) h
          ≡ st {X'} {X''} {Y'} {Y''} x e' d' (st {X} {X'} {Y} {Y'} x e d h)
      st-hom : ∀ {X X' Y Y'} (f : Fam [ X .fst , X' .fst ]) (g : Fam [ Y .fst , Y' .fst ]) x
        → (Φ ⟪ f , g ⟫) x ≡ st {X} {X'} {Y} {Y'} x (λ y _ → f y) (λ y _ _ → g y)

  module _ {Φ : Functor (D₁ ×C D₂) Fam} (S : FamStrengthʳ Φ) where
    open FamStrengthʳ S

    strengthʳ→LC : isLocallyContractiveʳ {ℰD₁ = ℰ₁} {ℰD₂ = ℰ₂} {ℰE = famEnrichment} Φ
    strengthʳ→LC .fst .FE.EnrichmentFor.f[_,_] (X , Y) (X' , Y') .N-ob c (β , γ) y h =
      st y (λ y' g → β y' (g ⋆ h))
           (λ y' g q → γ .N-ob y' ((g ⋆ h) , ≺-postcomp q h) y' id)
    strengthʳ→LC .fst .FE.EnrichmentFor.f[_,_] (X , Y) (X' , Y') .N-hom c c' k (β' , γ') (β , γ) eq =
      funExt λ y → funExt λ h → cong₂ (st y)
        (funExt λ y' → funExt λ g →
          cong (β' y') (sym (⋆Assoc g h k))
          ∙ λ i → eq i .fst y' (g ⋆ h))
        (funExt λ y' → funExt λ g → funExt λ q →
          cong (λ m → γ' .N-ob y' m y' id) (Σ≡Prop (λ _ → isProp≺ _ _) (sym (⋆Assoc g h k)))
          ∙ λ i → eq i .snd .N-ob y' ((g ⋆ h) , ≺-postcomp q h) y' id)
    strengthʳ→LC .fst .FE.EnrichmentFor.fid {X , Y} = makePshHomStrictPath (funExt λ c → funExt λ _ →
      funExt λ y → funExt λ h → sym (st-hom (Fam.id {X .fst}) (Fam.id {Y .fst}) y) ∙ funExt⁻ (Φ .F-id) y)
    strengthʳ→LC .fst .FE.EnrichmentFor.f-seq = makePshHomStrictPath (funExt λ c →
      funExt λ ((β , γ) , (β' , γ')) → funExt λ y → funExt λ h → funExt λ a → sym (st-seq y _ _ _ _ a))
    strengthʳ→LC .snd (f , g) = makePshHomStrictPath (funExt λ c → funExt λ _ →
      funExt λ y → funExt λ h → st-hom f g y)

module _ (S : Fam.ob) (t : ∀ x → ⟨ S x ⟩ → Σ[ y ∈ ob ] ⟨ ↡Psh x .F-ob y ⟩) where
  Reindex↡ : Functor Fam Fam
  Reindex↡ .F-ob X x = (Σ[ s ∈ ⟨ S x ⟩ ] ⟨ X (t x s .fst) ⟩) , isSetΣ (S x .snd) λ s → X _ .snd
  Reindex↡ .F-hom f x (s , a) = s , f (t x s .fst) a
  Reindex↡ .F-id = refl
  Reindex↡ .F-seq f g = refl

  Reindex↡-strength : FamStrength Reindex↡
  Reindex↡-strength .FamStrength.st x e (s , a) =
    s , e (t x s .fst) (t x s .snd .fst) (t x s .snd .snd) a
  Reindex↡-strength .FamStrength.st-seq _ _ _ _ = refl
  Reindex↡-strength .FamStrength.st-hom _ _ = refl

  Reindex↡-LC : isLocallyContractive pshGuarded famEnrichment famEnrichment Reindex↡
  Reindex↡-LC = strength→LC Reindex↡-strength
