module Cubical.Categories.Displayed.Constructions.Weaken.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
import      Cubical.Foundations.Isomorphism as FIso

open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct as BP
open import Cubical.Categories.Constructions.TotalCategory as TotalCat
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Exponentials
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Limits.CartesianD
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Exponentials.Small
open import Cubical.Categories.Displayed.Constructions.Weaken.Base as Wk
open import Cubical.Categories.Displayed.Presheaf

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Categoryᴰ
open UniversalElementᴰ
open UniversalElement
open isIsoOver
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  module _ (termC : Terminal' C) (termD : Terminal' D) where
    termWeaken : Terminalᴰ (weaken C D) termC
    termWeaken .vertexᴰ = termD .vertex
    termWeaken .elementᴰ = termD .element
    termWeaken .universalᴰ {xᴰ = d} .inv _ _ =
      UniversalElementNotation.intro termD _
    termWeaken .universalᴰ {xᴰ = d} .rightInv _ _ = refl
    termWeaken .universalᴰ {xᴰ = d} .leftInv f g =
      sym $ UniversalElementNotation.η termD
  module _ (prodC : BinProducts C)(prodD : BinProducts D) where
    private module B = BinProductsNotation prodD
    binprodWeaken : BinProductsᴰ (weaken C D) prodC
    binprodWeaken _ .vertexᴰ = prodD _ .vertex
    binprodWeaken _ .elementᴰ = prodD _ .element
    binprodWeaken _ .universalᴰ .inv _ (g₁ , g₂) = g₁ B.,p g₂
    binprodWeaken _ .universalᴰ .rightInv _ (g₁ , g₂) =
      UniversalElementNotation.β (prodD _)
    binprodWeaken _ .universalᴰ .leftInv _ g = sym $ B.×ue.η _ _

    bp×bp : BinProducts (∫C (weaken C D))
    bp×bp = BinProductsᴰNotation.∫bp binprodWeaken

  module _ (bpC : BinProducts C)(bpD : BinProducts D)
           (expC : AllExponentiable C bpC)(expD : AllExponentiable D bpD) where
    private
      module wkD = Fibers (weaken C D)
      module expD-ue {cᴰ dᴰ} = ExponentialNotation (λ d₁ → bpD (d₁ , cᴰ)) (expD cᴰ dᴰ)
    expWeaken : Exponentialsᴰ (weaken C D) bpC expC (binprodWeaken bpC bpD)
    expWeaken cᴰ dᴰ .vertexᴰ = expD cᴰ dᴰ .vertex
    expWeaken cᴰ dᴰ .elementᴰ = expD cᴰ dᴰ .element
    expWeaken cᴰ dᴰ .universalᴰ .inv _ qᴰ = expD-ue.lda qᴰ
    expWeaken cᴰ dᴰ .universalᴰ .rightInv _ qᴰ = expD-ue.⇒ue.β
    expWeaken cᴰ dᴰ .universalᴰ .leftInv _ fᴰ = sym $ expD-ue.⇒ue.η

    exp×exp : AllExponentiable (∫C (weaken C D)) (bp×bp bpC bpD)
    exp×exp (_ , cᴰ) (_ , dᴰ) .vertex = (expC _ _ .vertex , expD cᴰ dᴰ .vertex)
    exp×exp (_ , cᴰ) (_ , dᴰ) .element = (expC _ _ .element , expD cᴰ dᴰ .element)
    exp×exp (_ , cᴰ) (_ , dᴰ) .universal (Γ , Γᴰ) =
      FIso.isoToIsEquiv (FIso.iso _
        (λ q → invEq e₁ (q .fst) , invEq e₂ (q .snd))
        (λ q → ΣPathP (secEq e₁ (q .fst) , secEq e₂ (q .snd)))
        (λ f → ΣPathP (retEq e₁ (f .fst) , retEq e₂ (f .snd))))
      where
        e₁ = _ , expC _ _ .universal Γ
        e₂ = _ , expD cᴰ dᴰ .universal Γᴰ

module _ (C : CartesianCategory ℓC ℓC') (D : CartesianCategory ℓD ℓD') where
  open CartesianCategory renaming (C to Cat)
  open CartesianCategoryᴰ
  weakenCartesianCategory : CartesianCategoryᴰ C ℓD ℓD'
  weakenCartesianCategory .Cᴰ = weaken (C .Cat) (D .Cat)
  weakenCartesianCategory .termᴰ = termWeaken (C .term) (D .term)
  weakenCartesianCategory .bpᴰ = binprodWeaken (C .bp) (D .bp)

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  module _ (initC : Initial' C)(initD : Initial' D) where
    private
      init×init' : Terminal' (∫C (weaken (C ^op) (D ^op)))
      init×init' =
        TerminalᴰNotation.∫term (weaken (C ^op) (D ^op)) (termWeaken initC initD)
    init×init : Initial' (∫C (weaken C D))
    init×init .vertex = init×init' .vertex
    init×init .element = init×init' .element
    init×init .universal = init×init' .universal

  ×→∫wk : Functor (C ×C D) (∫C (weaken C D))
  ×→∫wk = intro (BP.Fst C D) (introS (BP.Fst C D) (BP.Snd C D))

  ∫wk→× : Functor (∫C (weaken C D)) (C ×C D)
  ∫wk→× = TotalCat.Fst ,F introS⁻ TotalCat.Snd
