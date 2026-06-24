module Cubical.Categories.Displayed.Instances.Algebras where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.StructureOver
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Limits.Terminal.More

private
  variable ℓC ℓC' : Level

module _ {C : Category ℓC ℓC'} (F : Functor C C) where

  open Category C
  open Functor F

  AlgStructureOver : StructureOver C ℓC' ℓC'
  StructureOver.ob[_] AlgStructureOver x = C [ F-ob x , x ]
  StructureOver.Hom[_][_,_] AlgStructureOver f α β = α ⋆⟨ C ⟩ f ≡ F-hom f ⋆⟨ C ⟩ β
  StructureOver.idᴰ AlgStructureOver = ⋆IdR _ ∙ sym (cong (_⋆ _) F-id ∙ ⋆IdL _)
  StructureOver._⋆ᴰ_ AlgStructureOver {f = f} {g = g} {xᴰ = α} {yᴰ = β} {zᴰ = γ} pf pg =
    sym (⋆Assoc α f g)
    ∙ cong (_⋆ g) pf
    ∙ ⋆Assoc (F-hom f) β g
    ∙ cong (F-hom f ⋆_) pg
    ∙ sym (⋆Assoc (F-hom f) (F-hom g) γ)
    ∙ cong (_⋆ γ) (sym (F-seq f g))
  StructureOver.isPropHomᴰ AlgStructureOver = isSetHom _ _

  AlgCatᴰ : Categoryᴰ C ℓC' ℓC'
  AlgCatᴰ = StructureOver→Catᴰ AlgStructureOver

  AlgebrasCategory : Category _ _
  AlgebrasCategory = ∫C AlgCatᴰ

  InitialAlgebra : Type (ℓ-max ℓC ℓC')
  InitialAlgebra = Initial' AlgebrasCategory

module InitialAlgebraNotation {C : Category ℓC ℓC'} {F : Functor C C}
  (initAlg : InitialAlgebra F) where

  open InitialNotation initAlg public
    renaming (𝟘 to μF)

  μF-carrier : Category.ob C
  μF-carrier = fst μF

  in-alg : C [ Functor.F-ob F μF-carrier , μF-carrier ]
  in-alg = snd μF

  fold : ∀ (B : Category.ob (∫C (AlgCatᴰ F))) → (∫C (AlgCatᴰ F)) [ μF , B ]
  fold B = absurd

  fold-unique : ∀ {B : Category.ob (∫C (AlgCatᴰ F))}
    (f g : (∫C (AlgCatᴰ F)) [ μF , B ]) → f ≡ g
  fold-unique f g = 𝟘extensionality
