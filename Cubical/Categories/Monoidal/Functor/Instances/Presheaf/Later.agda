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
