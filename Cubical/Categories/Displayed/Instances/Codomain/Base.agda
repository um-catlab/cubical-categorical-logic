{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Codomain.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Instances.BinProduct using (Sym)
open import Cubical.Categories.Instances.TotalCategory using (∫C)
open import Cubical.Categories.Displayed.Instances.Arrow.Base using (Arrow)
open import Cubical.Categories.Displayed.Instances.TotalCategory using (∫Cᴰ)
open import Cubical.Categories.Displayed.Instances.Reindex.Eq.Base
open import Cubical.Categories.Displayed.Instances.Weaken.Base
open import Cubical.Categories.Displayed.Instances.Weaken.Properties
  using (∫wk→×)
open import Cubical.Categories.Displayed.ChosenReind
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import
  Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Exponential

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

module _ (C : Category ℓC ℓC') where
  private
    module C = Category C

  Slice∫wk : Categoryᴰ (∫C (weaken C C)) ℓC' ℓC'
  Slice∫wk =
    EqReindex.reindex (Arrow C) (Sym ∘F ∫wk→×) Eq.refl λ _ _ → Eq.refl

  Codomain : Categoryᴰ C (ℓ-max ℓC ℓC') (ℓ-max ℓC' ℓC')
  Codomain = ∫Cᴰ (weaken C C) Slice∫wk

  private
    module Codomain = Categoryᴰ Codomain

  _ : ∀ {x} → Codomain.ob[ x ] ≡ (Σ[ e ∈ C.ob ] C [ e , x ])
  _ = refl

  _ : ∀ {x y} {h : C [ x , y ]} {a : Codomain.ob[ x ]} {b : Codomain.ob[ y ]}
    → Codomain.Hom[ h ][ a , b ]
      ≡ (Σ[ k ∈ C [ a .fst , b .fst ] ] (k C.⋆ b .snd ≡ a .snd C.⋆ h))
  _ = refl

  Codomain≡ : ∀ {x y} {h h' : C [ x , y ]} {a b} (q : h ≡ h')
    {φ : Codomain.Hom[ h ][ a , b ]} {ψ : Codomain.Hom[ h' ][ a , b ]}
    → φ .fst ≡ ψ .fst → PathP (λ i → Codomain.Hom[ q i ][ a , b ]) φ ψ
  Codomain≡ q p i .fst = p i
  Codomain≡ q {φ} {ψ} p i .snd =
    isProp→PathP (λ i → C.isSetHom (p i C.⋆ _) (_ C.⋆ q i)) (φ .snd) (ψ .snd) i

  open ChosenReind

  CodomainReind : ChosenReind Codomain
  CodomainReind .reind⟨_⟩ {a = a} e φ .fst = φ .fst
  CodomainReind .reind⟨_⟩ {a = a} e φ .snd = φ .snd ∙ cong (a .snd C.⋆_) e
  CodomainReind .reind-filler e φ = Codomain≡ e refl

  _ : ∀ {x y z} {f : C [ x , y ]} {g : C [ y , z ]} {a b c}
    (φ : Codomain.Hom[ f ][ a , b ]) (ψ : Codomain.Hom[ g ][ b , c ])
    → (φ Codomain.⋆ᴰ ψ) .fst ≡ φ .fst C.⋆ ψ .fst
  _ = λ φ ψ → refl

  open Section

  Δ : GlobalSection Codomain
  Δ .F-obᴰ x = x , C.id
  Δ .F-homᴰ h = h , C.⋆IdR h ∙ sym (C.⋆IdL h)
  Δ .F-idᴰ = Codomain≡ refl refl
  Δ .F-seqᴰ f g = Codomain≡ refl refl

instance
  CodomainReindInst : {C : Category ℓC ℓC'} → ChosenReind (Codomain C)
  CodomainReindInst = CodomainReind _

module _ {ℓC ℓC' ℓCᴰ ℓCᴰ'} {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {x} (xᴰ : Categoryᴰ.ob[_] Cᴰ x)
  (lr : isLRⱽObᴰ Cᴰ xᴰ) where
  private
    module LR = LRⱽPresheafᴰNotation Cᴰ (LRⱽObᴰ→LRⱽ Cᴰ (xᴰ , lr))
    module Pᴰ = PresheafᴰNotation Cᴰ (C [-, x ]) (Cᴰ [-][-, xᴰ ])
    module Cᴰ = Fibers Cᴰ

  module _ {Δ Γ} {Δᴰ : Cᴰ.ob[ Δ ]} {Γᴰ : Cᴰ.ob[ Γ ]}
    {δ : C [ Δ , x ]} {γ : C [ Γ , x ]}
    (m : (Cᴰ / (C [-, x ])) [ (Δ , Δᴰ , δ) , (Γ , Γᴰ , γ) ]) where
    ×LRⱽPshᴰ-β₂ⱽ :
      (((×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ Cᴰ (xᴰ , lr)) ^opF) ⟪ m ⟫) .snd .fst
        LR.⋆π₂ⱽ)
      Pᴰ.∫≡ LR.π₂ⱽ
    ×LRⱽPshᴰ-β₂ⱽ = LR.β₂ⱽ' _ _ ∙ Cᴰ.reind-filler⁻ _ ∙ Cᴰ.reind-filler⁻ _
