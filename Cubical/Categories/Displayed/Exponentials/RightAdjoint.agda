
{-
  Displayed and Vertical Exponentials

  Displayed Exponentials are fairly straightforward but Vertical Exponentials
  are less nice. Here we have defined them in the textbook way: exponential in
  each fiber that's preserved by reindexing.

  NOTE : This implementation of Displayed/Vertical Exponentials is
  deprecated, and the implementation at Displayed.Exponentials.Small is preferred
-}
module Cubical.Categories.Displayed.Exponentials.RightAdjoint where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Exponentials.RightAdjoint
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Constructions hiding (π₁; π₂)
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Limits.BinProduct.Base
open import Cubical.Categories.Displayed.Limits.BinProduct.Fiberwise
open import Cubical.Categories.Displayed.BinProduct hiding (_×ᴰ_)
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Displayed.Presheaf.Constructions.Exponential

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
  Exponentialᴰ :
    ∀ {c d} { -×c : BinProductsWith C c}
    cᴰ (dᴰ : Cᴰ.ob[ d ]) (-×ᴰcᴰ : BinProductsWithᴰ Cᴰ -×c cᴰ)
    → (c⇒d : Exponential C c d -×c)
    → Type _
  Exponentialᴰ cᴰ dᴰ -×ᴰcᴰ c⇒d = RightAdjointAtᴰ (BinProductWithFᴰ Cᴰ _ -×ᴰcᴰ) c⇒d dᴰ

  Exponentialsᴰ : ∀ bp
    → Exponentials C bp
    → BinProductsᴰ Cᴰ bp
    → Type _
  Exponentialsᴰ bp exps bpᴰ = ∀ {c d} (cᴰ : Cᴰ.ob[ c ])(dᴰ : Cᴰ.ob[ d ])
    → Exponentialᴰ cᴰ dᴰ (λ _ xᴰ → bpᴰ (xᴰ , cᴰ)) (AnExponential C bp exps)

  module ExponentialsᴰNotation
    {bps : BinProducts C}
    {exps : Exponentials C bps}
    {bpsᴰ : BinProductsᴰ Cᴰ bps}
    (expsᴰ : Exponentialsᴰ bps exps bpsᴰ) where
    open ExponentialsNotation bps (Exponentials→AllExponentiable _ bps exps)
    open BinProductsNotation bps
    open BinProductsᴰNotation bpsᴰ

    _⇒ᴰ_ : ∀{c c'} → Cᴰ.ob[ c ] → Cᴰ.ob[ c' ] →
      Cᴰ.ob[ c ⇒ c' ]
    cᴰ ⇒ᴰ c'ᴰ = UniversalElementᴰ.vertexᴰ (expsᴰ cᴰ c'ᴰ)

    appᴰ : ∀{c c'} {cᴰ : Cᴰ.ob[ c ]} {c'ᴰ : Cᴰ.ob[ c' ]} →
      Cᴰ.Hom[ app ][ (cᴰ ⇒ᴰ c'ᴰ) ×ᴰ cᴰ , c'ᴰ ]
    appᴰ = UniversalElementᴰ.elementᴰ (expsᴰ _ _)

    ldaᴰ : ∀{Γ c c'} {f : C [ Γ × c , c' ]} →
      {Γᴰ : Cᴰ.ob[ Γ ]} {cᴰ : Cᴰ.ob[ c ]} {c'ᴰ : Cᴰ.ob[ c' ]} →
      Cᴰ.Hom[ f ][ Γᴰ ×ᴰ cᴰ , c'ᴰ ] →
      Cᴰ.Hom[ lda f ][ Γᴰ , cᴰ ⇒ᴰ c'ᴰ ]
    ldaᴰ = UniversalElementᴰ.introᴰ (expsᴰ _ _)

    βᴰ : ∀{Γ c c'} {f : C [ Γ × c , c' ]} →
      {Γᴰ : Cᴰ.ob[ Γ ]} {cᴰ : Cᴰ.ob[ c ]} {c'ᴰ : Cᴰ.ob[ c' ]} →
      {fᴰ : Cᴰ.Hom[ f ][ Γᴰ ×ᴰ cᴰ , c'ᴰ ]} →
      (_ , (((π₁ᴰ Cᴰ.⋆ᴰ ldaᴰ fᴰ) ,pᴰ π₂ᴰ) Cᴰ.⋆ᴰ appᴰ)) ≡ (f , fᴰ)
    βᴰ = UniversalElementᴰ.βᴰ (expsᴰ _ _)

    ηᴰ : ∀{Γ c c'} {f : C [ Γ , c ⇒ c' ]} →
      {Γᴰ : Cᴰ.ob[ Γ ]} {cᴰ : Cᴰ.ob[ c ]} {c'ᴰ : Cᴰ.ob[ c' ]} →
      {fᴰ : Cᴰ.Hom[ f ][ Γᴰ , cᴰ ⇒ᴰ c'ᴰ ]} →
      (f , fᴰ) ≡ (_ , ldaᴰ (((π₁ᴰ Cᴰ.⋆ᴰ fᴰ) ,pᴰ π₂ᴰ) Cᴰ.⋆ᴰ appᴰ))
    ηᴰ = UniversalElementᴰ.ηᴰ (expsᴰ _ _)

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  Exponentialⱽ :
    ∀ {c} (cᴰ dᴰ : Cᴰ.ob[ c ])
    → (-×ⱽcᴰ : LocallyRepresentableⱽ (Cᴰ [-][-, cᴰ ]))
    → Type _
  Exponentialⱽ {c} cᴰ dᴰ -×ⱽcᴰ = UniversalElementⱽ Cᴰ c
    ((_ , -×ⱽcᴰ) ⇒PshSmallⱽ (Cᴰ [-][-, dᴰ ]))

  module _ (bpⱽ : BinProductsⱽ Cᴰ) (isFib : isFibration Cᴰ)
    where
    open UniversalElementⱽ
    bpⱽ+fib⇒AllReprLocallyRepresentableⱽ :
      ∀ {c} (cᴰ : Cᴰ.ob[ c ]) → LocallyRepresentableⱽ (Cᴰ [-][-, cᴰ ])
    bpⱽ+fib⇒AllReprLocallyRepresentableⱽ cᴰ Γᴰ γ =
      bpⱽ _ (Γᴰ , isFib cᴰ γ .vertexⱽ)
      ◁PshIsoⱽ (idPshIsoᴰ ×ⱽIso yoRecIsoⱽ (isFib cᴰ γ))

    Exponentialsⱽ : Type _
    Exponentialsⱽ =
      ∀ {c} cᴰ dᴰ →
      Exponentialⱽ {c} cᴰ dᴰ (bpⱽ+fib⇒AllReprLocallyRepresentableⱽ cᴰ)
