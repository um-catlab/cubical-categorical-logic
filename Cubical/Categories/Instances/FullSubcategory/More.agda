module Cubical.Categories.Instances.FullSubcategory.More where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Exponentials
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.FullSubcategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable

private
  variable
    ℓC ℓC' ℓP ℓQ : Level

open Category
open Functor
open UniversalElement

module _
  {C : Category ℓC ℓC'}
  {Q : C .ob → Type ℓQ}
  {P : Presheaf C ℓP}
  where

  private
    SubC = FullSubcategory C Q
    Include = FullInclusion C Q

  FullSubUniversalElement :
    (ue : UniversalElement C P) →
    Q (ue .vertex) →
    UniversalElement SubC (reindPsh Include P)
  FullSubUniversalElement ue vertex-in-Q .vertex =
    ue .vertex , vertex-in-Q
  FullSubUniversalElement ue vertex-in-Q .element =
    ue .element
  FullSubUniversalElement ue vertex-in-Q .universal (c , _) =
    ue .universal c

  reindFullSubRepresentable : (c : C .ob) (c-in-Q : Q c) →
    PshIso
      (reindPsh Include (C [-, c ]))
      (SubC [-, (c , c-in-Q) ])
  reindFullSubRepresentable c c-in-Q .PshIso.trans .PshHom.N-ob _ f = f
  reindFullSubRepresentable c c-in-Q .PshIso.trans .PshHom.N-hom =
    λ _ _ _ _ → refl
  reindFullSubRepresentable c c-in-Q .PshIso.nIso _ .fst f = f
  reindFullSubRepresentable c c-in-Q .PshIso.nIso _ .snd .fst _ = refl
  reindFullSubRepresentable c c-in-Q .PshIso.nIso _ .snd .snd _ = refl

module _
  (CCC : CartesianClosedCategory ℓC ℓC')
  (Q : (CCC .CartesianClosedCategory.CC .CartesianCategory.C) .ob →
    Type ℓQ)
  where

  private
    module CCC = CartesianClosedCategory CCC
    SubC = FullSubcategory CCC.C Q

  FullSubCCC :
    Q (CCC.term .vertex) →
    (∀ {A B} → Q A → Q B → Q (CCC.bp (A , B) .vertex)) →
    (∀ {A B} → Q A → Q B → Q (CCC.exps A B .vertex)) →
    CartesianClosedCategory (ℓ-max ℓC ℓQ) ℓC'
  FullSubCCC Q-⊤ Q-× Q-⇒ .CartesianClosedCategory.CC
    .CartesianCategory.C = SubC
  FullSubCCC Q-⊤ Q-× Q-⇒ .CartesianClosedCategory.CC
    .CartesianCategory.term .vertex = CCC.term .vertex , Q-⊤
  FullSubCCC Q-⊤ Q-× Q-⇒ .CartesianClosedCategory.CC
    .CartesianCategory.term .element = CCC.term .element
  FullSubCCC Q-⊤ Q-× Q-⇒ .CartesianClosedCategory.CC
    .CartesianCategory.term .universal (A , _) = CCC.term .universal A
  FullSubCCC Q-⊤ Q-× Q-⇒ .CartesianClosedCategory.CC
    .CartesianCategory.bp ((A , A-in-Q) , (B , B-in-Q)) .vertex =
      CCC.bp (A , B) .vertex , Q-× A-in-Q B-in-Q
  FullSubCCC Q-⊤ Q-× Q-⇒ .CartesianClosedCategory.CC
    .CartesianCategory.bp ((A , _) , (B , _)) .element =
      CCC.bp (A , B) .element
  FullSubCCC Q-⊤ Q-× Q-⇒ .CartesianClosedCategory.CC
    .CartesianCategory.bp ((A , _) , (B , _)) .universal (X , _) =
      CCC.bp (A , B) .universal X
  FullSubCCC Q-⊤ Q-× Q-⇒ .CartesianClosedCategory.exps
    (A , A-in-Q) (B , B-in-Q) .vertex =
      CCC.exps A B .vertex , Q-⇒ A-in-Q B-in-Q
  FullSubCCC Q-⊤ Q-× Q-⇒ .CartesianClosedCategory.exps
    (A , _) (B , _) .element = CCC.exps A B .element
  FullSubCCC Q-⊤ Q-× Q-⇒ .CartesianClosedCategory.exps
    (A , _) (B , _) .universal (X , _) = CCC.exps A B .universal X
