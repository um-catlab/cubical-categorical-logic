{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Constructions.Free.BiCartesianClosedCategory.Forded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation hiding (_⇒_)
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.BiCartesianClosed.Base
open import Cubical.Categories.Limits.Terminal as Term
open import Cubical.Categories.Limits.Terminal.More as Term
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Limits.BiCartesianClosedV
open import Cubical.Categories.Displayed.Limits.CartesianSection
open import Cubical.Categories.Displayed.Limits.CartesianClosedSection
open import Cubical.Categories.Displayed.Limits.BiCartesianClosedSection
open import Cubical.Categories.Displayed.Constructions.Comma
open import Cubical.Categories.Displayed.Section.Base as Cat
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Constructions.Reindex.Base as Reindex
open import Cubical.Categories.Displayed.Constructions.Reindex.Cartesian
open import Cubical.Categories.Displayed.Constructions.Reindex.CartesianClosed
open import Cubical.Categories.Displayed.Constructions.Weaken.Base as Wk
open import Cubical.Categories.Displayed.Constructions.Weaken.UncurriedProperties

open import Cubical.Categories.Constructions.Free.BiCartesianClosedCategory.Quiver

private
  variable
    ℓQ ℓQ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' : Level

open Category hiding (_∘_)
open Functor
open Section
open UniversalElement

module _ (Q : +×⇒Quiver ℓQ ℓQ') where
  private module Q = +×⇒Quiver Q

  -- Expression type with equality constraints for canonical forms
  data Expr (A B : Q.obExpr) : Type (ℓ-max ℓQ ℓQ') where
    -- Freely added Category structure
    genₑ : ∀ t → (Q.dom t Eq.≡ A) → (Q.cod t Eq.≡ B) → Expr A B
    idₑ : A Eq.≡ B → Expr A B
    _⋆ₑ_ : ∀ {C} → (e : Expr A C) → (e' : Expr C B) → Expr A B
    ⋆ₑIdL : (e : Expr A B) → idₑ Eq.refl ⋆ₑ e ≡ e
    ⋆ₑIdR : (e : Expr A B) → e ⋆ₑ idₑ Eq.refl ≡ e
    ⋆ₑAssoc : ∀ {C D} (e : Expr A C)(f : Expr C D)(g : Expr D B)
            → (e ⋆ₑ f) ⋆ₑ g ≡ e ⋆ₑ (f ⋆ₑ g)
    isSetExpr : isSet (Expr A B)
    -- Freely added Terminal structure
    !ₑ : (⊤ Eq.≡ B) → Expr A B
    ⊤η : (p : ⊤ Eq.≡ B) (t : Expr A B) → t ≡ !ₑ p
    -- Freely added Initial structure
    absurd : (⊥ Eq.≡ A) → Expr A B
    ⊥η : (p : ⊥ Eq.≡ A) (t : Expr A B) → t ≡ absurd p
    -- Freely added BinProducts structure
    π₁ : ∀ {Γ Δ} → ((Γ × Δ) Eq.≡ A) → (Γ Eq.≡ B) → Expr A B
    π₂ : ∀ {Γ Δ} → ((Γ × Δ) Eq.≡ A) → (Δ Eq.≡ B) → Expr A B
    ⟨_,_⟩ : ∀ {Δ Δ'} → Expr A Δ → Expr A Δ' → ((Δ × Δ') Eq.≡ B) → Expr A B
    ×β₁ : ∀ {Δ'}{t : Expr A B}{t' : Expr A Δ'}
        → ⟨ t , t' ⟩ Eq.refl ⋆ₑ π₁ Eq.refl Eq.refl ≡ t
    ×β₂ : ∀ {Δ}{t : Expr A Δ}{t' : Expr A B}
        → ⟨ t , t' ⟩ Eq.refl ⋆ₑ π₂ Eq.refl Eq.refl ≡ t'
    ×η : ∀ {Δ Δ'}(p : (Δ × Δ') Eq.≡ B)(t : Expr A B)
       → t ≡ ⟨ t ⋆ₑ π₁ p Eq.refl , t ⋆ₑ π₂ p Eq.refl ⟩ p
    -- Freely added BinCoProducts structure
    σ₁ : ∀ {Γ Δ} → (Γ Eq.≡ A) → ((Γ + Δ) Eq.≡ B) → Expr A B
    σ₂ : ∀ {Γ Δ} → (Δ Eq.≡ A) → ((Γ + Δ) Eq.≡ B) → Expr A B
    [_,_] : ∀ {Δ Δ'} → Expr Δ B → Expr Δ' B → ((Δ + Δ') Eq.≡ A) → Expr A B
    +β₁ : ∀ {Δ}{t : Expr A B}{t' : Expr Δ B} → (σ₁ Eq.refl Eq.refl  ⋆ₑ [ t , t' ] Eq.refl) ≡ t
    +β₂ : ∀ {Δ}{t : Expr Δ B}{t' : Expr A B} → (σ₂ Eq.refl Eq.refl  ⋆ₑ [ t , t' ] Eq.refl) ≡ t'
    +η : ∀ {Δ Δ'}(p : (Δ + Δ') Eq.≡ A)(t : Expr A B)
       → t ≡ [ σ₁ Eq.refl p ⋆ₑ t , σ₂ Eq.refl p ⋆ₑ t ] p
    -- Freely added Exponentials structure
    eval : ∀ {Δ Θ} → (((Δ ⇒ Θ) × Δ) Eq.≡ A) → (Θ Eq.≡ B) → Expr A B
    -- lam takes body : Expr (A × Δ) Θ and produces Expr A (Δ ⇒ Θ)
    lam : ∀ {Δ Θ} → Expr (A × Δ) Θ → ((Δ ⇒ Θ) Eq.≡ B) → Expr A B
    -- Lambda beta: context is Γ × Δ, need to transport to A
    -- When pA = Eq.refl, this reduces to the standard β rule
    λβ : ∀ {Γ Δ} (pA : (Γ × Δ) Eq.≡ A) (t : Expr (Γ × Δ) B)
       → Eq.transport (λ X → Expr X B) pA
           (⟨ π₁ Eq.refl Eq.refl ⋆ₑ lam t Eq.refl , π₂ Eq.refl Eq.refl ⟩ Eq.refl
            ⋆ₑ eval Eq.refl Eq.refl)
         ≡ Eq.transport (λ X → Expr X B) pA t
    -- Lambda eta: B = Δ ⇒ Θ, need to transport t to use in body
    λη : ∀ {Δ Θ} (pB : (Δ ⇒ Θ) Eq.≡ B) (t : Expr A B)
       → t ≡ lam (⟨ π₁ Eq.refl Eq.refl ⋆ₑ Eq.transport (Expr A) (Eq.sym pB) t
                  , π₂ Eq.refl Eq.refl ⟩ Eq.refl
               ⋆ₑ eval Eq.refl Eq.refl) pB

  ↑ₑ : ∀ t → Expr (Q.dom t) (Q.cod t)
  ↑ₑ t = genₑ t Eq.refl Eq.refl

  π₁' : ∀ {Γ Δ} → Expr (Γ × Δ) Γ
  π₁' = π₁ Eq.refl Eq.refl

  π₂' : ∀ {Γ Δ} → Expr (Γ × Δ) Δ
  π₂' = π₂ Eq.refl Eq.refl

  σ₁' : ∀ {Γ Δ} → Expr Γ (Γ + Δ)
  σ₁' = σ₁ Eq.refl Eq.refl

  σ₂' : ∀ {Γ Δ} → Expr Δ (Γ + Δ)
  σ₂' = σ₂ Eq.refl Eq.refl

  ⟨_,_⟩' : ∀ {Γ Δ Δ'} → Expr Γ Δ → Expr Γ Δ' → Expr Γ (Δ × Δ')
  ⟨ t , t' ⟩' = ⟨ t , t' ⟩ Eq.refl

  [_,_]' : ∀ {Γ Δ Δ'} → Expr Δ Γ → Expr Δ' Γ → Expr (Δ + Δ') Γ
  [ t , t' ]' = [ t , t' ] Eq.refl

  !ₑ' : ∀ {Γ} → Expr Γ ⊤
  !ₑ' = !ₑ Eq.refl

  absurd' : ∀ {B} → Expr ⊥ B
  absurd' = absurd Eq.refl

  eval' : ∀ {Δ Θ} → Expr ((Δ ⇒ Θ) × Δ) Θ
  eval' = eval Eq.refl Eq.refl

  lam' : ∀ {Γ Δ Θ} → Expr (Γ × Δ) Θ → Expr Γ (Δ ⇒ Θ)
  lam' t = lam t Eq.refl

  open CartesianCategory using (C; term; bp)
  open CartesianClosedCategory using (CC; exps)

  |FreeBiCartesianClosedCategory| : Category _ _
  |FreeBiCartesianClosedCategory| .ob = Q.obExpr
  |FreeBiCartesianClosedCategory| .Hom[_,_] = Expr
  |FreeBiCartesianClosedCategory| .id = idₑ Eq.refl
  |FreeBiCartesianClosedCategory| ._⋆_ = _⋆ₑ_
  |FreeBiCartesianClosedCategory| .⋆IdL = ⋆ₑIdL
  |FreeBiCartesianClosedCategory| .⋆IdR = ⋆ₑIdR
  |FreeBiCartesianClosedCategory| .⋆Assoc = ⋆ₑAssoc
  |FreeBiCartesianClosedCategory| .isSetHom = isSetExpr

  open BiCartesianClosedCategory using (CCC; sums; init)

  FreeBiCartesianClosedCategory : BiCartesianClosedCategory _ _
  FreeBiCartesianClosedCategory .CCC .CC .C = |FreeBiCartesianClosedCategory|
  FreeBiCartesianClosedCategory .CCC .CC .term .vertex = ⊤
  FreeBiCartesianClosedCategory .CCC .CC .term .element = tt
  FreeBiCartesianClosedCategory .CCC .CC .term .universal _ =
    isIsoToIsEquiv ((λ z → !ₑ') , ((λ b → refl) , λ _ → sym $ ⊤η Eq.refl _))
  FreeBiCartesianClosedCategory .CCC .CC .bp (Γ , Δ) .vertex = Γ × Δ
  FreeBiCartesianClosedCategory .CCC .CC .bp (Γ , Δ) .element = π₁' , π₂'
  FreeBiCartesianClosedCategory .CCC .CC .bp (Γ , Δ) .universal Θ = isIsoToIsEquiv
    ( (λ z → ⟨ z .fst , z .snd ⟩')
    , (λ _ → ΣPathP (×β₁ , ×β₂))
    , (λ _ → sym $ ×η Eq.refl _))
  FreeBiCartesianClosedCategory .CCC .exps Δ Θ .vertex = Δ ⇒ Θ
  FreeBiCartesianClosedCategory .CCC .exps Δ Θ .element = eval'
  FreeBiCartesianClosedCategory .CCC .exps Δ Θ .universal Γ = isIsoToIsEquiv
    (lam' , (λ t → λβ Eq.refl t) , (λ t → sym $ λη Eq.refl t))
  FreeBiCartesianClosedCategory .sums (Γ , Δ) .vertex = Γ + Δ
  FreeBiCartesianClosedCategory .sums (Γ , Δ) .element = σ₁' , σ₂'
  FreeBiCartesianClosedCategory .sums (Γ , Δ) .universal Θ = isIsoToIsEquiv
    ( (λ z → [ z .fst , z .snd ]')
    , (λ _ → ΣPathP (+β₁ , +β₂))
    , (λ _ → sym $ +η Eq.refl _))
  FreeBiCartesianClosedCategory .init .vertex = ⊥
  FreeBiCartesianClosedCategory .init .element = tt
  FreeBiCartesianClosedCategory .init .universal _ =
    isIsoToIsEquiv ((λ z → absurd') , ((λ b → refl) , λ _ → sym $ ⊥η Eq.refl _))

  private
    module FreeBCCC = BiCartesianClosedCategory FreeBiCartesianClosedCategory

  module _ (BCCCᴰ : BiCartesianClosedCategoryᴰ FreeBiCartesianClosedCategory ℓCᴰ ℓCᴰ') where
    open BiCartesianClosedCategoryᴰ BCCCᴰ

    private
      module initᴰ = UniversalElementᴰNotation (Cᴰ ^opᴰ) _ _ initᴰ

    module _ (ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]) where
      elimOb : ∀ A → Cᴰ.ob[ A ]
      elimOb (↑ o) = ı-ob o
      elimOb ⊤ = termᴰ .fst
      elimOb ⊥ = initᴰ .fst
      elimOb (A × B) = bpᴰ (elimOb A) (elimOb B) .fst
      elimOb (A + B) = bcpᴰ (elimOb A) (elimOb B) .fst
      elimOb (A ⇒ B) = expᴰ (elimOb A) (elimOb B) .fst

    record ElimInterpᴰ : Type (ℓ-max (ℓ-max ℓQ ℓQ') (ℓ-max ℓCᴰ ℓCᴰ')) where
      constructor mkElimInterpᴰ
      field
        ı-ob : ∀ o → Cᴰ.ob[ ↑ o ]
        ı-hom : ∀ e → Cᴰ.Hom[ ↑ₑ e ][ elimOb ı-ob (Q.dom e) , elimOb ı-ob (Q.cod e) ]

    module _ (ı : ElimInterpᴰ) where
      open ElimInterpᴰ ı

      elimHom : ∀ {A B} (e : Expr A B)
        → Cᴰ.Hom[ e ][ elimOb ı-ob A , elimOb ı-ob B ]
      elimHom (genₑ t Eq.refl Eq.refl) = ı-hom t
      elimHom (idₑ Eq.refl) = Cᴰ.idᴰ
      elimHom (e ⋆ₑ e') = elimHom e Cᴰ.⋆ᴰ elimHom e'
      elimHom (⋆ₑIdL f i) = Cᴰ.⋆IdLᴰ (elimHom f) i
      elimHom (⋆ₑIdR f i) = Cᴰ.⋆IdRᴰ (elimHom f) i
      elimHom (⋆ₑAssoc f g h i) = Cᴰ.⋆Assocᴰ (elimHom f) (elimHom g) (elimHom h) i
      elimHom (isSetExpr f g p q i j) =
        isSetHomᴰ' Cᴰ (elimHom f) (elimHom g) (λ i → elimHom (p i)) (λ i → elimHom (q i)) i j
      -- Terminal
      elimHom (!ₑ Eq.refl) = termᴰ.introᴰ tt
      elimHom (⊤η Eq.refl f i) = Cᴰ.rectify {e' = ⊤η Eq.refl f} (termᴰ.ηᴰ (elimHom f)) i
      -- Initial (dual of terminal via Cᴰ ^opᴰ)
      elimHom (absurd Eq.refl) = initᴰ.introᴰ tt
      elimHom (⊥η Eq.refl f i) = Cᴰ.rectify {e' = ⊥η Eq.refl f} (initᴰ.ηᴰ (elimHom f)) i
      -- Products
      elimHom (π₁ Eq.refl Eq.refl) = bpᴰ.πᴰ₁
      elimHom (π₂ Eq.refl Eq.refl) = bpᴰ.πᴰ₂
      elimHom (⟨ f , g ⟩ Eq.refl) = bpᴰ.introᴰ ((elimHom f) , (elimHom g))
      elimHom (×β₁ {t = t} {t' = t'} i) = Cᴰ.rectify {e' = ×β₁} (bpᴰ.×βᴰ₁ (elimHom t) (elimHom t')) i
      elimHom (×β₂ {t = t} {t' = t'} i) = Cᴰ.rectify {e' = ×β₂} (bpᴰ.×βᴰ₂ (elimHom t) (elimHom t')) i
      elimHom (×η {Δ} {Δ'} Eq.refl t i) = Cᴰ.rectify {e' = ×η Eq.refl t} (bpᴰ.×ηᴰ (elimHom t)) i
      -- Coproducts (dual of products via Cᴰ ^opᴰ)
      elimHom (σ₁ Eq.refl Eq.refl) = πᴰ₁
      elimHom (σ₂ Eq.refl Eq.refl) = πᴰ₂
      elimHom ([ f , g ] Eq.refl) = introᴰ ((elimHom f) , (elimHom g))
      elimHom (+β₁ {t = t} {t' = t'} i) = Cᴰ.rectify {e' = +β₁} (×βᴰ₁ (elimHom t) (elimHom t')) i
      elimHom (+β₂ {t = t} {t' = t'} i) = Cᴰ.rectify {e' = +β₂} (×βᴰ₂ (elimHom t) (elimHom t')) i
      elimHom (+η {Δ} {Δ'} Eq.refl t i) = Cᴰ.rectify {e' = +η Eq.refl t} (×ηᴰ (elimHom t)) i
      -- Exponentials
      elimHom (eval Eq.refl Eq.refl) = appᴰ
      elimHom (lam e Eq.refl) = λᴰ (elimHom e)
      elimHom (λβ Eq.refl t i) = Cᴰ.rectify {e' = λβ Eq.refl t} (Cᴰ.≡out $ ⇒βᴰ (elimHom t)) i
      elimHom (λη Eq.refl t i) = Cᴰ.rectify {e' = λη Eq.refl t} (Cᴰ.≡out $ ⇒ηᴰ (elimHom t)) i

      elim : GlobalSection Cᴰ
      elim .F-obᴰ = elimOb ı-ob
      elim .F-homᴰ = elimHom
      elim .F-idᴰ = refl
      elim .F-seqᴰ = λ _ _ → refl

      elimBiCartesianClosed : BiCartesianClosedSection BCCCᴰ
      elimBiCartesianClosed .BiCartesianClosedSection.cartesianClosedSection
        .CartesianClosedSection.cartesianSection
        .CartesianSection.section = elim
      elimBiCartesianClosed .BiCartesianClosedSection.cartesianClosedSection
        .CartesianClosedSection.cartesianSection
        .CartesianSection.F-obᴰ-⊤ = refl
      elimBiCartesianClosed .BiCartesianClosedSection.cartesianClosedSection
        .CartesianClosedSection.cartesianSection
        .CartesianSection.F-obᴰ-× _ _ = refl
      elimBiCartesianClosed .BiCartesianClosedSection.cartesianClosedSection
        .CartesianClosedSection.F-obᴰ-⇒ _ _ = refl
      elimBiCartesianClosed .BiCartesianClosedSection.F-obᴰ-⊥ = refl
      elimBiCartesianClosed .BiCartesianClosedSection.F-obᴰ-+ _ _ = refl

  module _
    {D : CartesianCategory ℓD ℓD'}
    (F : CartesianFunctor (FreeBiCartesianClosedCategory .CCC .CC) (D .CartesianCategory.C))
    (BCCCⱽ : BiCartesianClosedCategoryⱽ D ℓCᴰ ℓCᴰ')
    where
    private
      module BCCCⱽ' = BiCartesianClosedCategoryⱽ BCCCⱽ
      module D' = CartesianCategory D

      -- Simpler opposite functor avoiding toOpOp overhead
      F-op : Functor (FreeBCCC.C ^op) (D'.C ^op)
      F-op .F-ob = F .fst .F-ob
      F-op .F-hom = F .fst .F-hom
      F-op .F-id = F .fst .F-id
      F-op .F-seq f g = F .fst .F-seq g f

      opDⱽ : CartesianCategoryⱽ (D'.C ^op) _ _
      opDⱽ .CartesianCategoryⱽ.Cᴰ = BCCCⱽ'.Cᴰ ^opᴰ
      opDⱽ .CartesianCategoryⱽ.termⱽ = BCCCⱽ'.initⱽ
      opDⱽ .CartesianCategoryⱽ.bpⱽ = BCCCⱽ'.bcpⱽ
      opDⱽ .CartesianCategoryⱽ.cartesianLifts = BCCCⱽ'.opcartesianLifts

      reindexedOpⱽ = CartesianCategoryⱽReindex opDⱽ F-op

      reindexedBCCCⱽ : BiCartesianClosedCategoryⱽ FreeBCCC.CC _ _
      reindexedBCCCⱽ .BiCartesianClosedCategoryⱽ.CCCⱽ = CCCⱽReindex BCCCⱽ'.CCCⱽ F
      reindexedBCCCⱽ .BiCartesianClosedCategoryⱽ.initⱽ x =
        initⱽ' .fst ,
        pshiso (pshhom (λ y → initⱽ' .snd .PshIso.trans .PshHom.N-ob y)
               (λ _ _ _ _ → refl))
               (initⱽ' .snd .PshIso.nIso)
        where initⱽ' = reindexedOpⱽ .CartesianCategoryⱽ.termⱽ x
      reindexedBCCCⱽ .BiCartesianClosedCategoryⱽ.bcpⱽ x y =
        bcpⱽ' .fst ,
        pshiso (pshhom (λ z → bcpⱽ' .snd .PshIso.trans .PshHom.N-ob z )
                       λ c c' f p → bcpⱽ' .snd .PshIso.trans .PshHom.N-hom c c' f p)
               (bcpⱽ' .snd .PshIso.nIso)
        where bcpⱽ' = reindexedOpⱽ .CartesianCategoryⱽ.bpⱽ x y
      reindexedBCCCⱽ .BiCartesianClosedCategoryⱽ.opcartesianLifts x y z =
        opcartlift' .fst ,
        pshiso (pshhom (λ y → opcartlift' .snd .PshIso.trans .PshHom.N-ob y)
                       (λ c c' f p → opcartlift' .snd .PshIso.trans .PshHom.N-hom c c' f p))
                (opcartlift' .snd .PshIso.nIso)
        where opcartlift' = reindexedOpⱽ .CartesianCategoryⱽ.cartesianLifts x y z

    elimLocalMotive : BiCartesianClosedCategoryᴰ FreeBiCartesianClosedCategory _ _
    elimLocalMotive = BiCartesianClosedCategoryⱽ→BiCartesianClosedCategoryᴰ
      FreeBiCartesianClosedCategory reindexedBCCCⱽ

    elimLocal : (ı : ElimInterpᴰ elimLocalMotive)
      → Section (F .fst) (BCCCⱽ'.Cᴰ)
    elimLocal ı = GlobalSectionReindex→Section _ _ (elim elimLocalMotive ı)

  -- Recursion (non-dependent functors)
  module _ (BCCC : BiCartesianClosedCategory ℓC ℓC') where
    private
      wkC = weakenBCCC FreeBiCartesianClosedCategory BCCC
      module BCCC' = BiCartesianClosedCategory BCCC

    rec : (ı : ElimInterpᴰ wkC) → Functor FreeBCCC.C BCCC'.C
    rec ı = introS⁻ (elim wkC ı)

  -- -- -- BCCC functors out of the FreeBiCartesianClosedCategory
  -- -- -- are naturally isomorphic to each other
  -- -- -- TODO: uncomment once IsoCommaBinProductsᴰ etc. are defined
  -- -- module _
  -- --   {D : Category ℓD ℓD'}
  -- --   ((F , F-bp) (G , G-bp) :
  -- --     CartesianFunctor (FreeBiCartesianClosedCategory .CCC .CC) D)
  -- --   (F-1 : Term.preservesTerminal |FreeBiCartesianClosedCategory| D F)
  -- --   (G-1 : Term.preservesTerminal |FreeBiCartesianClosedCategory| D G)
  -- --   (F-0 : isTerminal (D ^op) (F ⟅ ⊥ ⟆))
  -- --   (G-0 : isTerminal (D ^op) (G ⟅ ⊥ ⟆))
  -- --   (+-iso : ∀ {A B} → CatIso D (F ⟅ A ⟆) (G ⟅ A ⟆)
  -- --                     → CatIso D (F ⟅ B ⟆) (G ⟅ B ⟆)
  -- --                     → CatIso D (F ⟅ A + B ⟆) (G ⟅ A + B ⟆))
  -- --   (+-σ₁ : ∀ {A B} (f : CatIso D (F ⟅ A ⟆) (G ⟅ A ⟆))
  -- --                    (g : CatIso D (F ⟅ B ⟆) (G ⟅ B ⟆))
  -- --          → D ._⋆_ (F ⟪ σ₁' ⟫) (+-iso f g .fst)
  -- --            ≡ D ._⋆_ (f .fst) (G ⟪ σ₁' ⟫))
  -- --   (+-σ₂ : ∀ {A B} (f : CatIso D (F ⟅ A ⟆) (G ⟅ A ⟆))
  -- --                    (g : CatIso D (F ⟅ B ⟆) (G ⟅ B ⟆))
  -- --          → D ._⋆_ (F ⟪ σ₂' ⟫) (+-iso f g .fst)
  -- --            ≡ D ._⋆_ (g .fst) (G ⟪ σ₂' ⟫))
  -- --   (+-cocase : ∀ {A B Γ} (f : CatIso D (F ⟅ A ⟆) (G ⟅ A ⟆))
  -- --                          (g : CatIso D (F ⟅ B ⟆) (G ⟅ B ⟆))
  -- --                          (γ : CatIso D (F ⟅ Γ ⟆) (G ⟅ Γ ⟆))
  -- --             → (h : Expr (A + B) Γ)
  -- --             → D ._⋆_ (F ⟪ h ⟫) (γ .fst)
  -- --               ≡ D ._⋆_ (+-iso f g .fst) (G ⟪ h ⟫))
  -- --   (⇒-iso : ∀ {A B} → CatIso D (F ⟅ A ⟆) (G ⟅ A ⟆)
  -- --                      → CatIso D (F ⟅ B ⟆) (G ⟅ B ⟆)
  -- --                      → CatIso D (F ⟅ A ⇒ B ⟆) (G ⟅ A ⇒ B ⟆))
  -- --   (⇒-lam : ∀ {A B Γ} (f : CatIso D (F ⟅ A ⟆) (G ⟅ A ⟆))
  -- --                       (g : CatIso D (F ⟅ B ⟆) (G ⟅ B ⟆))
  -- --                       (γ : CatIso D (F ⟅ Γ ⟆) (G ⟅ Γ ⟆))
  -- --            → (h : Expr (Γ × A) B)
  -- --            → (D ._⋆_ (F ⟪ lam' h ⟫) (⇒-iso f g .fst))
  -- --              ≡ (D ._⋆_ (γ .fst) (G ⟪ lam' h ⟫)))
  -- --   where
  -- --   open IsoCommaStructure F G
  -- --   private module D = Category D

  -- --   module _
  -- --     (⇒-eval : ∀ {A B} (f : CatIso D (F ⟅ A ⟆) (G ⟅ A ⟆))
  -- --                        (g : CatIso D (F ⟅ B ⟆) (G ⟅ B ⟆))
  -- --              → F ⟪ eval' ⟫ D.⋆ g .fst
  -- --                ≡ IsoCommaBinProductsᴰ
  -- --                    (FreeBiCartesianClosedCategory .CCC .CC .bp) F-bp G-bp
  -- --                    (⇒-iso f g) f .fst .fst
  -- --                  D.⋆ G ⟪ eval' ⟫)
  -- --     where

  -- --     private
  -- --       BCCCᴰF,G-IsoC : BiCartesianClosedCategoryᴰ FreeBiCartesianClosedCategory _ _
  -- --       BCCCᴰF,G-IsoC .BiCartesianClosedCategoryᴰ.CCCᴰ
  -- --         .CartesianClosedCategoryᴰ.CCᴰ .CartesianCategoryᴰ.Cᴰ = IsoCommaᴰΔ
  -- --       BCCCᴰF,G-IsoC .BiCartesianClosedCategoryᴰ.CCCᴰ
  -- --         .CartesianClosedCategoryᴰ.CCᴰ .CartesianCategoryᴰ.termᴰ =
  -- --         IsoCommaTerminalᴰ (FreeBCCC.term) F-1 G-1
  -- --       BCCCᴰF,G-IsoC .BiCartesianClosedCategoryᴰ.CCCᴰ
  -- --         .CartesianClosedCategoryᴰ.CCᴰ .CartesianCategoryᴰ.bpᴰ =
  -- --         IsoCommaBinProductsᴰ (FreeBCCC.bp) F-bp G-bp
  -- --       BCCCᴰF,G-IsoC .BiCartesianClosedCategoryᴰ.CCCᴰ
  -- --         .CartesianClosedCategoryᴰ.expᴰ {A = A} f {B = B} g =
  -- --         ⇒-iso f g , (⇒-eval f g , tt) , isUniv
  -- --         where
  -- --         isUniv : isUniversalᴰ IsoCommaᴰΔ _ _
  -- --           (FreeBCCC.exps A B) (⇒-eval f g , tt)
  -- --         isUniv Γ Γᴰ .inv u uᴰ .fst = ⇒-lam f g Γᴰ u
  -- --         isUniv Γ Γᴰ .inv _ _ .snd = tt
  -- --         isUniv Γ Γᴰ .rightInv _ _ =
  -- --           isProp→PathP (λ _ → isPropΣ (D.isSetHom _ _) λ _ → isPropUnit) _ _
  -- --         isUniv Γ Γᴰ .leftInv _ _ =
  -- --           isProp→PathP (λ _ → isPropΣ (D.isSetHom _ _) λ _ → isPropUnit) _ _
  -- --       BCCCᴰF,G-IsoC .BiCartesianClosedCategoryᴰ.initᴰ =
  -- --         IsoCommaInitialᴰ FreeBCCC.init F-0 G-0
  -- --       BCCCᴰF,G-IsoC .BiCartesianClosedCategoryᴰ.bcpᴰ =
  -- --         IsoCommaBinCoProductsᴰ FreeBCCC.sums +-iso +-σ₁ +-σ₂ +-cocase

  -- --     module _ (ı : ElimInterpᴰ BCCCᴰF,G-IsoC) where
  -- --       FreeBCCCFunctor≅ : NatIso F G
  -- --       FreeBCCCFunctor≅ =
  -- --         sectionToNatIso (elimBiCartesianClosed BCCCᴰF,G-IsoC ı
  -- --           .BiCartesianClosedSection.section)
