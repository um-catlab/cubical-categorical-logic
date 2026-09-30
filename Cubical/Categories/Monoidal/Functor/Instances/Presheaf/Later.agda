{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude hiding (_▷_)
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation hiding (_∘ˡ_)
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.StrictHom.CartesianClosed
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Constructions.BinProduct using (_×Psh_)
open import Cubical.Categories.Limits.BinProduct.More using (binProdComparison)
module Cubical.Categories.Monoidal.Functor.Instances.Presheaf.Later
  {ℓ ℓ' ℓO : Level} {A : Category ℓ ℓ'} {Wo : WFOrder ℓO ℓ'} (dir : DirectStr A Wo)
  where

open import Cubical.Categories.Direct.StrictDownset dir

open Functor
open NatTrans
open PshHomStrict
open PshIsoStrict
open LaxMonoidalStr
open StrongMonoidalStr
open StrongMonoidalFunctor

private
  module M = MonoidalCategory (PshMon.𝓟Mon A ℓ)
  open PshMon A ℓ using (𝟙)

  -- TODO: These follow from right adjoints preserving limits:
  -- ▷ is right adjoint to the realization Lan_y(∂y_•), sending yo(a) ↦ ∂y(a) = strictdownset
-- ▷ 𝟙 ≅ 𝟙 : both are terminal in 𝓟 (contractible pointwise).
▷𝟙≅𝟙 : PshIsoStrict (▷ .F-ob 𝟙) 𝟙
▷𝟙≅𝟙 .trans .N-ob _ _ = lift tt
▷𝟙≅𝟙 .trans .N-hom _ _ _ _ _ _ = refl
▷𝟙≅𝟙 .nIso c .fst _ .N-ob _ _ = lift tt
▷𝟙≅𝟙 .nIso c .fst _ .N-hom _ _ _ _ _ _ = refl
▷𝟙≅𝟙 .nIso c .snd .fst _ = refl
▷𝟙≅𝟙 .nIso c .snd .snd α = makePshHomStrictPath refl

-- ▷(P × Q) ≅ ▷ P × ▷ Q.
-- Forward direction: the canonical `binProdComparison` map ⟨F(π₁), F(π₂)⟩,
-- which exists for any functor into a category with the relevant BinProduct.
-- Inverse direction: specific to ▷, uses ×PshIntroStrict on the exponential
-- structure of ▷Psh (α, β) ↦ ×PshIntroStrict α β.
▷×-iso : ∀ {P Q : Presheaf A (PshMon.ℓm A ℓ)}
       → PshIsoStrict (▷ .F-ob (P ×Psh Q)) (▷ .F-ob P ×Psh ▷ .F-ob Q)
▷×-iso {P}{Q} .trans =
  binProdComparison (▷) (PSHBP A (PshMon.ℓm A ℓ) (P , Q))
                      (PSHBP A (PshMon.ℓm A ℓ) (▷ .F-ob P , ▷ .F-ob Q))
▷×-iso .nIso c .fst (α , β) = ×PshIntroStrict α β
▷×-iso .nIso c .snd .fst _ = refl
▷×-iso .nIso c .snd .snd _ = makePshHomStrictPath refl

▷-strong : StrongMonoidalFunctor (PshMon.𝓟Mon A ℓ) (PshMon.𝓟Mon A ℓ)
▷-strong .F = ▷
▷-strong .strmonstr .laxmonstr .ε = invPshIsoStrict ▷𝟙≅𝟙 .trans
▷-strong .strmonstr .laxmonstr .μ =
  natTrans (λ _ → invPshIsoStrict ▷×-iso .trans)
           (λ _ → makePshHomStrictPath refl)
▷-strong .strmonstr .laxmonstr .αμ-law _ _ _ = makePshHomStrictPath refl
▷-strong .strmonstr .laxmonstr .ηε-law _ = makePshHomStrictPath refl
▷-strong .strmonstr .laxmonstr .ρε-law _ = makePshHomStrictPath refl
▷-strong .strmonstr .ε-isIso =
  isiso (▷𝟙≅𝟙 .trans) (makePshHomStrictPath refl) (makePshHomStrictPath refl)
▷-strong .strmonstr .μ-isIso _ =
  isiso (▷×-iso .trans) (makePshHomStrictPath refl) (makePshHomStrictPath refl)

open import Cubical.Foundations.Isomorphism using () renaming (isIso to isTypeIso)
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)
open PshMon A ℓ using (𝓟Mon)
open import Cubical.Categories.Direct.Base
open DirectNotation dir
open import Cubical.Categories.Category using (Category)
private module A = Category A

-- ▷ preserves the "underlying category" (i.e., ε̂ = ε ⋆ ▷⟪_⟫ is iso as a
-- function `Hom(𝟙, P) → Hom(𝟙, ▷P)`) whenever the directing category has
-- no ≺-maximal objects (every A-object x has a strictly-greater successor
-- y with a chosen hom x → y in A), AND for any two such choices there is
-- a common upper bound over which they agree (filteredness for spans out
-- of a common source).
--
-- These two assumptions together hold e.g. when A is (a subcategory of)
-- ω with successors, or more generally any directed WFO.

module _
  (succ  : ∀ (x : A.ob) → Σ[ y ∈ A.ob ] Σ[ g ∈ A [ x , y ] ] (x ≺ y))
  (join  : ∀ (y : A.ob) (c₁ c₂ : A.ob) (g₁ : A [ y , c₁ ]) (g₂ : A [ y , c₂ ])
         → Σ[ c₃ ∈ A.ob ] Σ[ h₁ ∈ A [ c₁ , c₃ ] ] Σ[ h₂ ∈ A [ c₂ , c₃ ] ]
             ((g₁ A.⋆ h₁) ≡ (g₂ A.⋆ h₂)))
  where
  private
    ▷-lax : LaxMonoidalFunctor (PshMon.𝓟Mon A ℓ) (PshMon.𝓟Mon A ℓ)
    ▷-lax = record { F = ▷ ; laxmonstr = ▷-strong .strmonstr .laxmonstr }

    -- Given β : 𝟙 → ▷P, the inverse extracts α y from β at the succ of y.
    inv-fn : ∀ (P : Presheaf A (PshMon.ℓm A ℓ))
           → PshHomStrict 𝟙 (▷Psh P) → PshHomStrict 𝟙 P
    inv-fn P β .N-ob y _ =
      let (c , g , q) = succ y in β .N-ob c _ .N-ob y (g , q)
    inv-fn P β .N-hom y' y f _ _ _ =
      let (c₁ , g₁ , q₁) = succ y'
          (c₂ , g₂ , q₂) = succ y
          (c₃ , h₁ , h₂ , eq) = join y' c₁ c₂ g₁ (f A.⋆ g₂)
      in
        P .F-hom f (β .N-ob c₂ _ .N-ob y (g₂ , q₂))
          ≡⟨ β .N-ob c₂ _ .N-hom y' y f (g₂ , q₂) _ refl ⟩
        β .N-ob c₂ _ .N-ob y' (f A.⋆ g₂ , ≺-precomp f q₂)
          ≡⟨ (λ i → sym (β .N-hom c₂ c₃ h₂ _ _ refl) i .N-ob y'
                      (f A.⋆ g₂ , ≺-precomp f q₂)) ⟩
        β .N-ob c₃ _ .N-ob y' ((f A.⋆ g₂) A.⋆ h₂ , ≺-postcomp (≺-precomp f q₂) h₂)
          ≡⟨ cong (β .N-ob c₃ _ .N-ob y')
                  (Σ≡Prop (λ _ → isProp≺ _ _) (sym eq)) ⟩
        β .N-ob c₃ _ .N-ob y' (g₁ A.⋆ h₁ , ≺-postcomp q₁ h₁)
          ≡⟨ (λ i → β .N-hom c₁ c₃ h₁ _ _ refl i .N-ob y' (g₁ , q₁)) ⟩
        β .N-ob c₁ _ .N-ob y' (g₁ , q₁)
          ∎

  ▷-preservesUnderlying : LaxMonoidalFunctor.preservesUnderlyingCategories ▷-lax
  ▷-preservesUnderlying P .fst = inv-fn P
  ▷-preservesUnderlying P .snd .fst β =
    -- sec: ε̂ (inv-fn P β) ≡ β.  Both are `PshHomStrict 𝟙 (▷P)`; peel two
    -- makePshHomStrictPath layers to reduce to `.N-ob c _ .N-ob y (g,q)`
    -- equality, then bridge with join.
    makePshHomStrictPath (funExt λ c → funExt λ _ →
      makePshHomStrictPath (funExt λ y → funExt λ (g , q) →
        let (c₂ , g₂ , q₂) = succ y
            (c₃ , h₁ , h₂ , eq) = join y c₂ c g₂ g
        in
          β .N-ob c₂ _ .N-ob y (g₂ , q₂)
            ≡⟨ (λ i → sym (β .N-hom c₂ c₃ h₁ _ _ refl) i .N-ob y (g₂ , q₂)) ⟩
          β .N-ob c₃ _ .N-ob y (g₂ A.⋆ h₁ , ≺-postcomp q₂ h₁)
            ≡⟨ cong (β .N-ob c₃ _ .N-ob y)
                    (Σ≡Prop (λ _ → isProp≺ _ _) eq) ⟩
          β .N-ob c₃ _ .N-ob y (g A.⋆ h₂ , ≺-postcomp q h₂)
            ≡⟨ (λ i → β .N-hom c c₃ h₂ _ _ refl i .N-ob y (g , q)) ⟩
          β .N-ob c _ .N-ob y (g , q)
            ∎))
  ▷-preservesUnderlying P .snd .snd α =
    -- ret: inv-fn P (ε̂ α) ≡ α.  Definitional: `ε̂ α .N-ob c _ .N-ob y (g,q)`
    -- reduces to `α .N-ob y _`, independent of c, g, q.
    makePshHomStrictPath refl
