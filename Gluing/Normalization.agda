{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Gluing.Normalization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Relation.Nullary hiding (⟪_⟫)
open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.HITs.GroupoidTruncation
open import Cubical.HITs.SetTruncation
open import Cubical.Data.Unit.Properties

open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.CCC
open import Cubical.Categories.Instances.Discrete
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct.More
open import
  Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
  hiding (_×_)
open import Cubical.Categories.Constructions.Free.CartesianCategory.Base
  hiding (rec)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Presheaf.Base
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Presheaf using (UniversalElementᴰ)
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.Displayed.Instances.Presheaf.Properties

open import Cubical.Categories.Constructions.Free.CartesianCategory.Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.NaturalTransformation

private variable
  ℓq ℓq' : Level

open Category
open Functor
--open ProductQuiver

module _ (Q : ×Quiver ℓq ℓq') where
  private module Q = ×QuiverNotation Q
  module _ (isGroupoidQ : isGroupoid Q.Ob) where
    Cl : CartesianCategory _ _
    Cl = FreeCartesianCategory Q
    private
      module Cl = CartesianCategoryNotation Cl
    data NormalForm : (τ : Cl .fst .ob) (Γ : Cl .fst .ob) → Type (ℓ-max ℓq ℓq')
    data NeutralTerm : (τ : Cl .fst .ob) (Γ : Cl .fst .ob) → Type (ℓ-max ℓq ℓq')
    data NeutralTerm where
      var : ∀{τ : Cl .fst .ob} → NeutralTerm τ τ
      proj₁ : ∀{τ₁ τ₂ Γ} → NeutralTerm (τ₁ Cl.×bp τ₂) Γ → NeutralTerm τ₁ Γ
      proj₂ : ∀{τ₁ τ₂ Γ} → NeutralTerm (τ₁ Cl.×bp τ₂) Γ → NeutralTerm τ₂ Γ
      symb : ∀(f : Q.mor){Γ}(M : NormalForm (Q.dom f) Γ) → NeutralTerm (↑ (Q.cod f)) Γ
      isSetNe : ∀{τ Γ} → isSet (NeutralTerm τ Γ)
    data NormalForm where
      shift : ∀{τ : Q .fst} {Γ} → NeutralTerm (↑ τ) Γ → NormalForm (↑ τ) Γ
      pair : ∀{τ₁ τ₂ Γ} → NormalForm τ₁ Γ → NormalForm τ₂ Γ → NormalForm (τ₁ Cl.×bp τ₂) Γ
      uniq : ∀{Γ} → NormalForm Cl.𝟙 Γ
      isSetNf : ∀{τ Γ} → isSet (NormalForm τ Γ)
    ReadbackNe : (τ : Cl .fst .ob) (Γ : Cl .fst .ob) → NeutralTerm τ Γ → Cl .fst [ Γ , τ ]
    ReadbackNf : (τ : Cl .fst .ob) (Γ : Cl .fst .ob) → NormalForm τ Γ → Cl .fst [ Γ , τ ]
    ReadbackNe τ Γ var = Cl .fst .id
    ReadbackNe τ Γ (proj₁ N) = Cl.π₁ ∘⟨ Cl .fst ⟩ ReadbackNe _ _ N
    ReadbackNe τ Γ (proj₂ N) = Cl.π₂ ∘⟨ Cl .fst ⟩ ReadbackNe _ _ N
    ReadbackNe τ Γ (symb f M) = (↑ₑ f) ∘⟨ Cl .fst ⟩ ReadbackNf _ _ M
    ReadbackNe τ Γ (isSetNe x y p q i j) = Cl.isSetHom (ReadbackNe _ _ x) (ReadbackNe _ _ y) (congS (ReadbackNe _ _) p) (congS (ReadbackNe _ _) q) i j
    ReadbackNf τ Γ (shift x) = ReadbackNe _ _ x
    ReadbackNf τ Γ (pair x y) = ReadbackNf _ _ x Cl.,p ReadbackNf _ _ y
    ReadbackNf τ Γ uniq = Cl.!t
    ReadbackNf τ Γ (isSetNf x y p q i j) = Cl.isSetHom (ReadbackNf _ _ x) (ReadbackNf _ _ y) (congS (ReadbackNf _ _) p) (congS (ReadbackNf _ _) q) i j
    Ren : Category _ _
    Ren = DiscreteCategory (Cl .fst .ob , isGroupoidQ)
    ⊆ : Functor Ren (Cl .fst)
    ⊆ = DiscFunc (idfun _)
    --test : {x y : ob Ren} → Ren [ x , y ] → Cl .fst [ ⊆ .F-ob x , ⊆ .F-ob y ]
    --test = ⊆ .F-hom
    𝓟Ren : Category _ _
    𝓟Ren = PresheafCategory Ren (ℓ-max ℓq ℓq')
    𝓟→Fam : Presheaf Ren (ℓ-max ℓq ℓq') → (Cl .fst .ob → hSet (ℓ-max ℓq ℓq'))
    𝓟→Fam = F-ob
    Fam→𝓟 : (Cl .fst .ob → hSet (ℓ-max ℓq ℓq')) → Presheaf Ren (ℓ-max ℓq ℓq')
    Fam→𝓟 F .F-ob = F
    Fam→𝓟 F .F-hom p = subst (λ Γ → ⟨ F Γ ⟩) (sym p)
    Fam→𝓟 F .F-id = funExt (substRefl {B = λ Γ → ⟨ F Γ ⟩})
    Fam→𝓟 F .F-seq p q = congS (subst _) (symDistr q p) ∙
      funExt (substComposite (λ Γ → ⟨ F Γ ⟩) (sym p) (sym q))
    private
      module 𝓟Ren = CartesianCategoryNotation (𝓟Ren , ⊤𝓟 _ _ , ×𝓟 _ _)
    R : Cl .fst .ob → Presheaf Ren (ℓ-max ℓq ℓq')
    R (↑ τ) = Fam→𝓟 (λ Γ → NormalForm (↑ τ) Γ , isSetNf)
    R (Γ × Δ) = R Γ 𝓟Ren.×bp R Δ
    R ⊤ = 𝓟Ren.𝟙
    nerve : Functor (Cl .fst) 𝓟Ren
    nerve = CurryBifunctor (Sym (HomBif (Cl .fst) ∘Fl (⊆ ^opF)))
    𝓟Renᴰ : Categoryᴰ 𝓟Ren _ _
    𝓟Renᴰ = PRESHEAFᴰ Ren _ (ℓ-max ℓq ℓq')
    LiftedBinProducts-𝒫Renᴰ : LiftedBinProducts 𝓟Renᴰ (BinProductsToBinProducts' _ (×𝓟 _ _))
    LiftedBinProducts-𝒫Renᴰ = PRESHEAFᴰ-LiftedBinProducts _ _ _
    reify : ∀ τ {Γ} → ⟨ R τ ⟅ Γ ⟆ ⟩ → NormalForm τ Γ
    reify (↑ τ) = idfun _
    reify (Γ × Δ) pr = pair (reify Γ (pr .fst)) (reify Δ (pr .snd))
    reify ⊤ _ = uniq
    reflect : ∀ τ {Γ} → NeutralTerm τ Γ → ⟨ R τ ⟅ Γ ⟆ ⟩
    reflect (↑ τ) = shift
    reflect (Γ × Δ) neu = reflect Γ (proj₁ neu) , reflect Δ (proj₂ neu)
    reflect ⊤ _ = tt*
    --test' : ∀ τ Γ ne → (ReadbackNf τ Γ ∘S (reify τ ∘S reflect τ)) ne ≡ ReadbackNe τ Γ ne
    --test' _ _ var = {!!}
    --test' _ _ (proj₁ ne) = {!!}
    --test' _ _ (proj₂ ne) = {!!}
    --test' _ _ (symb f M) = {!!}
    --test' _ _ (isSetNe ne ne₁ x y i i₁) = {!!}
    private
      module 𝓟Renᴰ = Categoryᴰ 𝓟Renᴰ
    S : Section nerve 𝓟Renᴰ
    S = elimLocal' Q
      (LiftedTerminalReindex (PRESHEAFᴰ-VerticalTerminals Ren _ _ _))
      (LiftedBinProductsReindex'
        (BinProductsToBinProducts' _ (Cl .snd .snd))
        (PRESHEAFᴰ-isFibration _ _ _) (PRESHEAFᴰ-VerticalProducts _ _ _))
      OB HOM
      where
      OB : (τ : Q .fst) → 𝓟Renᴰ.ob[ nerve ⟅ ⊆ ⟅ ↑ τ ⟆ ⟆ ]
      OB τ .F-ob (Γ , e) = NormalForm (↑ τ) Γ , isSetNf
      OB τ .F-hom {-{x = Δ,e'} {Δ',e''}-} (p , q) = subst (NormalForm (↑ τ)) (sym p)
      OB τ .F-id {x = (Γ , e)} = funExt λ nf → goal nf
        where
        -- It doesn't type check if I inline this?
        goal : ∀ nf → subst (NormalForm (↑ τ)) refl nf ≡ nf
        goal nf = substRefl nf
      OB τ .F-seq f g = funExt (λ nf → goal nf)
        where
        goal : ∀ nf → subst (NormalForm (↑ τ)) (sym (g .fst ∙ f .fst)) nf ≡
          subst (NormalForm (↑ τ)) (sym (g .fst)) (subst (NormalForm (↑ τ)) (sym (f .fst)) nf)
        goal nf = congS (λ x → subst (NormalForm _) x nf) (symDistr _ _) ∙ substComposite _ _ _ _
      --OB* : (Γ : Cl .fst .ob) → 𝓟Renᴰ.ob[ nerve ⟅ Γ ⟆ ]
      --OB* (↑ τ) = OB τ
      --OB* (Γ × Δ) = {!OB* Γ , OB* Δ!}
      HOM : (f : Q.mor) →
        𝓟Renᴰ.Hom[ nerve ⟪ ↑ₑ f ⟫ ][
          elim-F-ob Q (reindex 𝓟Renᴰ nerve , LiftedTerminalReindex (PRESHEAFᴰ-VerticalTerminals Ren _ _ _) , LiftedBinProductsReindex' (BinProductsToBinProducts' _ (Cl .snd .snd)) (PRESHEAFᴰ-isFibration _ _ _) (PRESHEAFᴰ-VerticalProducts _ _ _)) OB (Q.Dom f)
          , OB (Q.Cod f) ]
      HOM f = natTrans (λ (Γ , e) p → {!!}) {!!}
