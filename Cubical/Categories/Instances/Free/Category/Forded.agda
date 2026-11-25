-- Free category generated from base objects and generators
--
-- This time without Indexed Inductives

module Cubical.Categories.Instances.Free.Category.Forded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Quiver.Base as Quiver
open import Cubical.Data.Graph.Base as Graph
open import Cubical.Data.Graph.Displayed as Graph hiding (Section)
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct as BP
open import Cubical.Categories.UnderlyingGraph hiding (Interp)
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Path
open import Cubical.Categories.Displayed.Instances.Reindex.ChosenReind
open import Cubical.Categories.Displayed.ChosenReind
open import Cubical.Categories.Displayed.ChosenReind
  public using (TransportReindInst)
open import Cubical.Categories.Displayed.Instances.Weaken.Base as Wk

open import Cubical.Categories.Displayed.Section.Base as Cat

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓh ℓh' ℓj ℓ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

open Category
open Functor
open QuiverOver

module _ (Q : Quiver ℓg ℓg') where
  data Exp (A B : Q .fst) : Type (ℓ-max ℓg ℓg') where
    ↑   : ∀ g → (Q .snd .dom g Eq.≡ A) → ((Q .snd .cod g) Eq.≡ B) → Exp A B
    idₑ  : A Eq.≡ B → Exp A B
    _⋆ₑ_ : ∀ {C} → (e : Exp A C) → (e' : Exp C B) → Exp A B
    ⋆ₑIdL : (e : Exp A B) → idₑ Eq.refl ⋆ₑ e ≡ e
    ⋆ₑIdR : (e : Exp A B) → e ⋆ₑ idₑ Eq.refl ≡ e
    ⋆ₑAssoc : ∀ {C D} (e : Exp A C)(f : Exp C D)(g : Exp D B)
            → (e ⋆ₑ f) ⋆ₑ g ≡ e ⋆ₑ (f ⋆ₑ g)
    isSetExp : isSet (Exp A B)

  FreeCat : Category _ _
  FreeCat .ob = Q .fst
  FreeCat .Hom[_,_] = Exp
  FreeCat .id = idₑ Eq.refl
  FreeCat ._⋆_ = _⋆ₑ_
  FreeCat .⋆IdL = ⋆ₑIdL
  FreeCat .⋆IdR = ⋆ₑIdR
  FreeCat .⋆Assoc = ⋆ₑAssoc
  FreeCat .isSetHom = isSetExp

  Interp : (𝓒 : Category ℓc ℓc') → Type (ℓ-max (ℓ-max (ℓ-max ℓg ℓg') ℓc) ℓc')
  Interp 𝓒 = HetQG Q (Cat→Graph 𝓒)

  ⇑ : ∀ g → Exp (Q .snd .dom g) (Q .snd .cod g)
  ⇑ g = ↑ g Eq.refl Eq.refl

  η : Interp FreeCat
  η HetQG.$g x = x
  η HetQG.<$g> e = ⇑ e

  module _ {C : Category ℓC ℓC'}
           (ı : Interp C)
           (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
    Interpᴰ : Type _
    Interpᴰ = HetSection ı (Categoryᴰ→Graphᴰ Cᴰ)

  -- -- the eliminator constructs a *global* section. Use reindexing if
  -- you want a local section
  module _ (Cᴰ : Categoryᴰ FreeCat ℓCᴰ ℓCᴰ')
           (ıᴰ : Interpᴰ η Cᴰ)
           where
    open HetSection
    open Section
    private module Cᴰ = Categoryᴰ Cᴰ

    elim-F-homᴰ : ∀ {d d'} → (f : FreeCat .Hom[_,_] d d') →
      Cᴰ.Hom[ f ][ ıᴰ $gᴰ d , (ıᴰ $gᴰ d') ]
    elim-F-homᴰ (↑ g Eq.refl Eq.refl) = ıᴰ <$g>ᴰ g
    elim-F-homᴰ (idₑ Eq.refl) = Cᴰ.idᴰ
    elim-F-homᴰ (f ⋆ₑ g) = elim-F-homᴰ f Cᴰ.⋆ᴰ elim-F-homᴰ g
    elim-F-homᴰ (⋆ₑIdL f i) = Cᴰ.⋆IdLᴰ (elim-F-homᴰ f) i
    elim-F-homᴰ (⋆ₑIdR f i) = Cᴰ.⋆IdRᴰ (elim-F-homᴰ f) i
    elim-F-homᴰ (⋆ₑAssoc f f₁ f₂ i) =
      Cᴰ.⋆Assocᴰ (elim-F-homᴰ f) (elim-F-homᴰ f₁) (elim-F-homᴰ f₂) i
    elim-F-homᴰ (isSetExp f g p q i j) = isOfHLevel→isOfHLevelDep 2
      (λ x → Cᴰ.isSetHomᴰ)
      (elim-F-homᴰ f) (elim-F-homᴰ g)
      (cong elim-F-homᴰ p) (cong elim-F-homᴰ q)
      (isSetExp f g p q)
      i j

    elim : GlobalSection Cᴰ
    elim .F-obᴰ = ıᴰ $gᴰ_
    elim .F-homᴰ = elim-F-homᴰ
    elim .F-idᴰ = refl
    elim .F-seqᴰ _ _ = refl

  -- The elimination principle for global sections implies an
  -- elimination principle for local sections, this requires reindex
  -- so caveat utilitor
  module _ {C : Category ℓC ℓC'}
           (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
           ⦃ cr : ChosenReind Cᴰ ⦄
           (F : Functor FreeCat C)
           (ıᴰ : Interpᴰ (compGrHomHetQG (Functor→GraphHom F) η) Cᴰ)
           where
    private
      open HetSection
      F*Cᴰ = reindexChosenReind Cᴰ F
      ıᴰ' : Interpᴰ η F*Cᴰ
      ıᴰ' ._$gᴰ_ = ıᴰ $gᴰ_
      ıᴰ' ._<$g>ᴰ_ = ıᴰ <$g>ᴰ_

    elimLocal : Section F Cᴰ
    elimLocal = GlobalSectionReindex→SectionChosenReind Cᴰ F (elim F*Cᴰ ıᴰ')

  -- Elimination principle implies the recursion principle, which
  -- allows for non-dependent functors to be defined
  module _ {C : Category ℓC ℓC'} (ı : Interp C) where
    open HetQG
    private
      ıᴰ : Interpᴰ η (weaken FreeCat C)
      ıᴰ .HetSection._$gᴰ_ = ı .HetQG._$g_
      ıᴰ .HetSection._<$g>ᴰ_ = ı .HetQG._<$g>_

    rec : Functor FreeCat C
    rec = Wk.introS⁻ (elim (weaken FreeCat C) ıᴰ)

  -- Elimination principle also implies the uniqueness principle,
  -- i.e., η law for functors out of the free category
  module _
    {C : Category ℓC ℓC'}
    (F G : Functor FreeCat C)
    (agree-on-gen : Interpᴰ (compGrHomHetQG (Functor→GraphHom (F BP.,F G)) η) (PathC C))
    where
    FreeCatFunctor≡ : F ≡ G
    FreeCatFunctor≡ = PathReflection (elimLocal (PathC C) _ agree-on-gen)
