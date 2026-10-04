module Cubical.Categories.Enriched.Enrichment.BaseChange.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Monoidal.Base hiding (MonoidalStr)
open import Cubical.Categories.Monoidal.Functor

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monoidal.NaturalTransformation.Base
open import Cubical.Categories.Enriched.Enrichment.Base
import Cubical.Categories.Enriched.Enrichment.Functor.Base as EnrF
open import Cubical.Categories.Reasoning.Core
import Cubical.Categories.Enriched.BaseChange.Base as EnrBC

open import Cubical.Foundations.Isomorphism
open Iso

module _
  {ℓC ℓC' ℓV ℓV' ℓU ℓU' : Level}
  {C : Category ℓC ℓC'}
  {V : MonoidalCategory ℓV ℓV'} {U : MonoidalCategory ℓU ℓU'}
  (Fl : LaxMonoidalFunctor V U)
  (isIsoε̂  : LaxMonoidalFunctor.preservesUnderlyingCategories Fl)
  (ℰC : Enrichment C V)
  where
    private
      module ℰC = Enrichment ℰC
      module V = MonoidalCategory V
      module U = MonoidalCategory U

    open LaxMonoidalFunctor Fl
    open EnrBC Fl hiding (BaseChange)
    open Enrichment

    BaseChange : Enrichment C U
    BaseChange .VE[_,_] x y = F-ob ℰC.VE[ x , y ]
    BaseChange .id = ε̂ ℰC.id
    BaseChange .seq x y z = μ̂ (ℰC.seq x y z)
    BaseChange .⇄-agree {x} {y} = compIso (ℰC.⇄-agree {x} {y})
      (isIsoToIso (isIsoε̂ ℰC.VE[ x , y ]))
    BaseChange .⋆IdL x y =
        lem-411-L ℰC.id V.id (ℰC.seq x x y) (ℰC.⋆IdL x y)
      ∙ cong (λ k → (ε̂ ℰC.id U.⊗ₕ k) U.⋆ μ̂ (ℰC.seq x x y)) F-id
    BaseChange .⋆IdR x y =
        lem-411-R V.id ℰC.id (ℰC.seq x y y) (ℰC.⋆IdR x y)
      ∙ cong (λ k → (k U.⊗ₕ ε̂ ℰC.id) U.⋆ μ̂ (ℰC.seq x y y)) F-id
    BaseChange .⋆Assoc x y z w =
        sym (U.⋆Assoc _ _ _)
      ∙ lem-413 (ℰC.seq x y z) (ℰC.seq y z w) (ℰC.seq x z w) (ℰC.seq x y w)
        (V.⋆Assoc _ _ _ ∙ ℰC.⋆Assoc x y z w)
    BaseChange .⌜id⌝ = cong ε̂ ℰC.⌜id⌝
    BaseChange .⌜⋆⌝ {X} {Y} {Z} f g =
        cong ε̂ (ℰC.⌜⋆⌝ f g)
      ∙ lem-⌜⋆⌝ ℰC.⌜ f ⌝ ℰC.⌜ g ⌝ (ℰC.seq X Y Z)

-- Prop 4.3.1 (Cruttwell 2008): a monoidal natural transformation
-- α : N ⇒ M induces, for each V-enrichment X on C, a W-functor
-- α*(X) : N*(X) ⇒ M*(X) between the base changes, whose underlying
-- functor is `Id` and whose strength at (x, y) is `α ⟦ X(x,y) ⟧`.
--
-- (The second half of Prop 4.3.1 — 2-naturality — is deferred because
-- BaseChange is not yet a 2-functor here, only its action on objects.)

module _
  {ℓC ℓC' ℓV ℓV' ℓU ℓU' : Level}
  {C : Category ℓC ℓC'}
  {V : MonoidalCategory ℓV ℓV'} {U : MonoidalCategory ℓU ℓU'}
  {Nl Ml : LaxMonoidalFunctor V U}
  (φ : MonoidalNatTrans V U Nl Ml)
  (isIsoε̂-N : LaxMonoidalFunctor.preservesUnderlyingCategories Nl)
  (isIsoε̂-M : LaxMonoidalFunctor.preservesUnderlyingCategories Ml)
  (ℰC : Enrichment C V)
  where
  private
    module φ = MonoidalNatTrans φ
    module Nl = LaxMonoidalFunctor Nl
    module Ml = LaxMonoidalFunctor Ml
    module V = MonoidalCategory V
    module U = MonoidalCategory U
    module ℰC = Enrichment ℰC
    open Reasoning U.C

    N* : Enrichment C U
    N* = BaseChange Nl isIsoε̂-N ℰC
    M* : Enrichment C U
    M* = BaseChange Ml isIsoε̂-M ℰC

  -- Prop 4.3.1: α*(ℰC) is a W-functor.
  α*ℰC : EnrF.Enrichment U N* M* Id
  α*ℰC .EnrF.Enrichment.F[_,_] x y = φ.φ ⟦ ℰC.VE[ x , y ] ⟧
  α*ℰC .EnrF.Enrichment.F-id {X} =
    glueTriL (φ.φ .NatTrans.N-hom ℰC.id) φ.ε-law
  α*ℰC .EnrF.Enrichment.F-seq {X}{Y}{Z} =
    glue (φ.μ-law ℰC.VE[ X , Y ] ℰC.VE[ Y , Z ])
         (sym (φ.φ .NatTrans.N-hom (ℰC.seq X Y Z)))
  α*ℰC .EnrF.Enrichment.agree f =
    sym (glueTriL (φ.φ .NatTrans.N-hom ℰC.⌜ f ⌝) φ.ε-law)
