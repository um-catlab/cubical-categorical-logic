-- Free category generated from base objects and generators

-- This time using a "quiver" as the presentation of the generators,
-- which is better in some applications

module Cubical.Categories.Constructions.Free.Category.QuiverPath where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Quiver.Base as Quiver
open import Cubical.Data.Graph.Base as Graph
open import Cubical.Data.Graph.Displayed as Graph hiding (Section)
open import Cubical.HITs.SetTruncation using (∥_∥₂; ∣_∣₂)
import Cubical.HITs.SetTruncation as Trunc

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct as BP
open import Cubical.Categories.UnderlyingGraph hiding (Interp)
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Displayed.Instances.Path
open import Cubical.Categories.Displayed.Constructions.Reindex.Base as Reindex
open import Cubical.Categories.Displayed.Constructions.Weaken.Base as Wk

open import Cubical.Categories.Displayed.Section.Base as Cat
open import Cubical.Categories.Constructions.Free.Category.Quiver using (Interp; Interpᴰ)
open import Cubical.Categories.Constructions.Free.Category.UniversalProperty

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓh ℓh' ℓj ℓ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

open Category
open Functor
open QuiverOver

module _ (Q : Quiver ℓg ℓg') where
  data Exp : Q .fst → Q .fst → Type (ℓ-max ℓg ℓg') where
    [] : ∀ {a} → Exp a a
    _∷_ : ∀ {a} g (e : Exp (Q .snd .cod g) a) → Exp (Q .snd .dom g) a

  ∣Exp∣ : Q .fst → Q .fst → Type (ℓ-max ℓg ℓg')
  ∣Exp∣ a b = ∥ Exp a b ∥₂

  ∣[]∣ : ∀ {a} → ∣Exp∣ a a
  ∣[]∣ = ∣ [] ∣₂

  _∣∷∣_ : ∀ {a} g (e : ∣Exp∣ (Q .snd .cod g) a) → ∣Exp∣ (Q .snd .dom g) a
  _∣∷∣_ g = Trunc.map (g ∷_)

  ExpGraph : Graph ℓg (ℓ-max ℓg ℓg')
  ExpGraph = (record { Node = Q .fst ; Edge = ∣Exp∣ })

  ı : HetQG Q ExpGraph
  ı $g x = x
  ı <$g> e = ∣ e ∷ [] ∣₂

  -- This is the "definitional" eliminator for Ob/Exp.
  module _
    (Ob[_] : Q .fst → Type ℓCᴰ)
    (Hom[_][_,_] : ∀ {a b}(f : ∣Exp∣ a b) → Ob[ a ] → Ob[ b ] → Type ℓCᴰ')
    (ı-ob : ∀ a → Ob[ a ])
    (ı-[] : ∀ {a} → Hom[ ∣ [] ∣₂ ][ ı-ob a , ı-ob a ])
    (ı-∷  : ∀ {a} g {e : ∣Exp∣ (Q .snd .cod g) a} (eᴰ : Hom[ e ][ ı-ob (Q .snd .cod g) , ı-ob a ])
      → Hom[ g ∣∷∣ e ][ ı-ob (Q .snd .dom g) , ı-ob a ])
    (ı-trunc : ∀ {a b}{f : ∣Exp∣ a b}{aᴰ bᴰ} → isSet Hom[ f ][ aᴰ , bᴰ ])
    where
    elim' : ∀ {a b}(f : Exp a b) → Hom[ ∣ f ∣₂ ][ ı-ob a , ı-ob b ]
    elim' [] = ı-[]
    elim' (g ∷ f) = ı-∷ g (elim' f)

    elim : ∀ {a b}(f : ∣Exp∣ a b) → Hom[ f ][ ı-ob a , ı-ob b ]
    elim = Trunc.elim (λ x → ı-trunc) elim'

    -- This is probably the downside to using truncation rather than
    -- building in isSetExp as a HIT
    elim-∷ : ∀ {c} g (e : ∣Exp∣ _ c)
      → Path (Σ[ e ∈ ∣Exp∣ _ c ] Hom[ e ][ _ , _ ])
          (_ , elim (g ∣∷∣ e))
          (_ , ı-∷ g (elim e))
    elim-∷ g =
      Trunc.elim
        (λ _ → isProp→isSet (isSetΣ Trunc.isSetSetTrunc (λ _ → ı-trunc) _ _))
        (λ _ → refl)

  module _
    (Hom[_] : ∀ {a b}(f : ∣Exp∣ a b) → Type ℓCᴰ')
    (ı-[] : ∀ {a} → Hom[ ∣ [] {a} ∣₂ ])
    (ı-∷  : ∀ {a} g {e : ∣Exp∣ (Q .snd .cod g) a} (eᴰ : Hom[ e ]) → Hom[ g ∣∷∣ e ])
    (ı-trunc : ∀ {a b}{f : ∣Exp∣ a b} → isSet Hom[ f ])
    where
    elimExp : ∀ {a b} (f : ∣Exp∣ a b) → Hom[ f ]
    elimExp = elim (λ _ → Unit) (λ f _ _ → Hom[ f ]) _ ı-[] ı-∷ ı-trunc

  module _
    (Hom[_] : ∀ {a b}(f : ∣Exp∣ a b) → Type ℓCᴰ')
    (ı-[] : ∀ {a} → Hom[ ∣ [] {a} ∣₂ ])
    (ı-∷  : ∀ {a} g {e : ∣Exp∣ (Q .snd .cod g) a} (eᴰ : Hom[ e ]) → Hom[ g ∣∷∣ e ])
    (ı-trunc : ∀ {a b}{f : ∣Exp∣ a b} → isProp Hom[ f ])
    where
    indExp : ∀ {a b} (f : ∣Exp∣ a b) → Hom[ f ]
    indExp = elimExp Hom[_] ı-[] ı-∷ (isProp→isSet ı-trunc)

  module _
    (Ob : Type ℓCᴰ)
    (Hom[_,_] : Ob → Ob → Type ℓCᴰ')
    (ı-ob : Q .fst → Ob)
    (ı-[] : ∀ {a} → Hom[ ı-ob a , ı-ob a ])
    (ı-∷  : ∀ {a} g (eᴰ : Hom[ ı-ob (Q .snd .cod g) , ı-ob a ])
      → Hom[ ı-ob (Q .snd .dom g) , ı-ob a ])
    (ı-trunc : ∀ {a b} → isSet Hom[ ı-ob a , ı-ob b ])
    where
    rec : ∀ {a b} → (f : ∣Exp∣ a b) → Hom[ ı-ob a , ı-ob b ]
    rec = elim (λ _ → Unit) (λ {a}{b} _ _ _ → Hom[ ı-ob a , ı-ob b ]) _
      ı-[] (λ {a = a₁} g {e} → ı-∷ g) ı-trunc

  module _
    (Hom[_,_] : Q .fst → Q .fst → Type ℓCᴰ')
    (ı-[] : ∀ {a} → Hom[ a , a ])
    (ı-∷  : ∀ {a} g (eᴰ : Hom[ (Q .snd .cod g) , a ])
      → Hom[ (Q .snd .dom g) , a ])
    (ı-trunc : ∀ {a b} → isSet Hom[ a , b ])
    where
    recExp : ∀ {a b} (f : ∣Exp∣ a b) → Hom[ a , b ]
    recExp = rec (Q .fst) Hom[_,_] (λ a → a) ı-[] ı-∷ ı-trunc

  _++_ : ∀ {a b c} → ∣Exp∣ a b → ∣Exp∣ b c → ∣Exp∣ a c
  _++_ {c = c} = recExp ((λ a b → ∣Exp∣ b c → ∣Exp∣ a c))
    (λ g → g)
    (λ g rec e → g ∣∷∣ rec e)
    (isSet→ Trunc.isSetSetTrunc)
  opaque
    []++_ : ∀ {a b} (f : ∣Exp∣ a b) → ∣[]∣ ++ f ≡ f
    []++ f = refl

    ∷++ : ∀ {b c} g e (f : ∣Exp∣ b c)
      → ((g ∣∷∣ e) ++ f) ≡ (g ∣∷∣ (e ++ f))
    ∷++ g = Trunc.elim (λ _ → isSetΠ λ _ → isProp→isSet (Trunc.isSetSetTrunc _ _))
      λ _ _ → refl

    _++[] : ∀ {a b} (f : ∣Exp∣ a b) → f ++ ∣[]∣ ≡ f
    _++[] = indExp (λ f → f ++ ∣[]∣ ≡ f)
      refl (λ g {e} ih → ∷++ _ e _ ∙ cong (g ∣∷∣_) ih)
        (Trunc.isSetSetTrunc _ _)

    ++Assoc : ∀ {a b c d} (f : ∣Exp∣ a b)(g : ∣Exp∣ b c)(h : ∣Exp∣ c d)
      → ((f ++ g) ++ h) ≡ (f ++ (g ++ h))
    ++Assoc f g h =
      indExp (λ {a} {b} f → ∀ {c d} (g : ∣Exp∣ b c)(h : ∣Exp∣ c d) → ((f ++ g) ++ h) ≡ (f ++ (g ++ h)))
        (λ _ _ → refl)
        (λ q {e} ih g h →
          cong (_++ h) (∷++ _ e _)
          ∙ ∷++ _ (e ++ g) _
          ∙ cong (q ∣∷∣_) (ih g h)
          ∙ (sym $ ∷++ _ e _))
        (isPropImplicitΠ λ _ → isPropImplicitΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → Trunc.isSetSetTrunc _ _)
        f g h

  FreeCategory : Category ℓg (ℓ-max ℓg ℓg')
  FreeCategory .ob = Q .fst
  FreeCategory .Hom[_,_] = ∣Exp∣
  FreeCategory .id = ∣[]∣
  FreeCategory ._⋆_ = _++_
  FreeCategory .⋆IdL f = refl
  FreeCategory .⋆IdR f = f ++[]
  FreeCategory .⋆Assoc = ++Assoc
  FreeCategory .isSetHom = Trunc.isSetSetTrunc

  module _ (Cᴰ : Categoryᴰ FreeCategory ℓCᴰ ℓCᴰ') (ıᴰ : Interpᴰ Q ı Cᴰ) where
    open Section
    open HetSection
    private
      module Cᴰ = Fibers Cᴰ
    elim-F-homᴰ : ∀ {d d'} →
      (f : ∣Exp∣ d d') →
      Cᴰ [ f ][ ıᴰ $gᴰ d , ıᴰ $gᴰ d' ]
    elim-F-homᴰ = elim Cᴰ.ob[_] Cᴰ.Hom[_][_,_]
      (ıᴰ ._$gᴰ_)
      Cᴰ.idᴰ
      (λ g eᴰ → (ıᴰ <$g>ᴰ g) Cᴰ.⋆ᴰ eᴰ)
      Cᴰ.isSetHomᴰ

    elim-F-homᴰ⟨_⟩ :
      ∀ {d d'} →
      {f g : ∣Exp∣ d d'}
      → f ≡ g
      → Path Cᴰ.Hom[ _ , _ ]
          (f , elim-F-homᴰ f )
          (g , elim-F-homᴰ g )
    elim-F-homᴰ⟨ p ⟩ i .fst = p i
    elim-F-homᴰ⟨ p ⟩ i .snd = elim-F-homᴰ (p i)

    elim-F-homᴰ-ı : ∀ g →
      elim-F-homᴰ (ı <$g> g) ≡ (ıᴰ <$g>ᴰ g)
    elim-F-homᴰ-ı g = Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdR _

    -- Why doesn't this hold definitionally?
    elim-F-homᴰ∷ :
      ∀ {c} g (e : ∣Exp∣ _ c)
      → Path Cᴰ.Hom[ _ , _ ]
          (g ∣∷∣ e , elim-F-homᴰ (g ∣∷∣ e))
          (g ∣∷∣ e , ((ıᴰ <$g>ᴰ g) Cᴰ.⋆ᴰ elim-F-homᴰ e))
    elim-F-homᴰ∷ =
      elim-∷ Cᴰ.ob[_] Cᴰ.Hom[_][_,_] _ Cᴰ.idᴰ ((λ g eᴰ → (ıᴰ <$g>ᴰ g) Cᴰ.⋆ᴰ eᴰ))
        Cᴰ.isSetHomᴰ

    elim-F-seqᴰ-motive : ∀ {a b} (f : ∣Exp∣ a b) → Type _
    elim-F-seqᴰ-motive f =
      ∀ {c} → (g : ∣Exp∣ _ c)
      → Path Cᴰ.Hom[ _ , _ ]
          (f ++ g , elim-F-homᴰ (f ++ g))
          (f ++ g , (elim-F-homᴰ f Cᴰ.⋆ᴰ elim-F-homᴰ g))

    elim-F-seqᴰ : ∀ {a b} (f : ∣Exp∣ a b) → elim-F-seqᴰ-motive f
    elim-F-seqᴰ = indExp elim-F-seqᴰ-motive
      (λ g → sym $ Cᴰ.⋆IdL _)
      (λ q {f} ih g →
         elim-F-homᴰ⟨ ∷++ _ f _ ⟩
         ∙ elim-F-homᴰ∷ q (f ++ g)
         ∙ Cᴰ.⟨ refl ⟩⋆⟨ ih g ⟩
         ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
         ∙ Cᴰ.⟨ sym $ elim-F-homᴰ∷ _ _ ⟩⋆⟨ refl ⟩)
      (isPropImplicitΠ λ _ → isPropΠ λ _ → Cᴰ.isSetHom _ _)

    elimFreeCat : GlobalSection Cᴰ
    elimFreeCat .F-obᴰ d = ıᴰ HetSection.$gᴰ d
    elimFreeCat .F-homᴰ = elim-F-homᴰ
    elimFreeCat .F-idᴰ = refl
    elimFreeCat .F-seqᴰ f g =
      Cᴰ.rectify $ Cᴰ.≡out $ elim-F-seqᴰ f g

    extends-ıᴰ-hom : (g : Q .snd .mor) →
      (ıᴰ <$g>ᴰ g) ≡
      ((ıᴰ <$g>ᴰ g) Cᴰ.⋆ᴰ Cᴰ.idᴰ)
    extends-ıᴰ-hom g = Cᴰ.rectify $ Cᴰ.≡out $ sym $ Cᴰ.⋆IdR _

  isFreeCat : isFreeCategory Q FreeCategory ı
  isFreeCat Cᴰ ıᴰ .fst = elimFreeCat Cᴰ ıᴰ
  isFreeCat Cᴰ ıᴰ .snd .fst q = refl
  isFreeCat Cᴰ ıᴰ .snd .snd = extends-ıᴰ-hom Cᴰ ıᴰ
