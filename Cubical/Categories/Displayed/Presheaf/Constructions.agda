{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.More

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory using (∫C)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
  renaming (π to Reindexπ; reindex to CatReindex)
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Representable

open Bifunctorᴰ
open Functor
open Functorᴰ
open isIsoOver
open PshHomᴰ
private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module _ {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ
    LiftPshᴰ : (ℓ' : Level) → Presheafᴰ P Cᴰ (ℓ-max ℓPᴰ ℓ')
    LiftPshᴰ ℓ' = LiftFᴰ ℓ' ∘Fⱽᴰ Pᴰ

  UnitPshᴰ : ∀ {P : Presheaf C ℓP} → Presheafᴰ P Cᴰ ℓ-zero
  UnitPshᴰ .F-obᴰ _ _ = Unit , isSetUnit
  UnitPshᴰ .F-homᴰ _ _ _ = tt
  UnitPshᴰ .F-idᴰ = refl
  UnitPshᴰ .F-seqᴰ _ _ = refl

  -- External product: (Pᴰ ×ᴰ Qᴰ) over (P × Q)
  PshProd'ᴰ :
    Functorᴰ PshProd' (PRESHEAFᴰ Cᴰ ℓA ℓAᴰ ×Cᴰ PRESHEAFᴰ Cᴰ ℓB ℓBᴰ)
                      (PRESHEAFᴰ Cᴰ (ℓ-max ℓA ℓB) (ℓ-max ℓAᴰ ℓBᴰ))
  PshProd'ᴰ = postcomposeFᴰ (C ^op) (Cᴰ ^opᴰ) ×Setsᴰ ∘Fᴰ ,Fᴰ-functorᴰ

  PshProdᴰ :
    Bifunctorᴰ PshProd (PRESHEAFᴰ Cᴰ ℓA ℓAᴰ) (PRESHEAFᴰ Cᴰ ℓB ℓBᴰ)
                       (PRESHEAFᴰ Cᴰ (ℓ-max ℓA ℓB) (ℓ-max ℓAᴰ ℓBᴰ))
  PshProdᴰ = ParFunctorᴰToBifunctorᴰ PshProd'ᴰ

  _×ᴰPsh_ : ∀ {P : Presheaf C ℓA}{Q : Presheaf C ℓB}
            → (Pᴰ : Presheafᴰ P Cᴰ ℓAᴰ)(Qᴰ : Presheafᴰ Q Cᴰ ℓBᴰ)
            → Presheafᴰ (P ×Psh Q) Cᴰ _
  _×ᴰPsh_ = PshProdᴰ .Bif-obᴰ

  ∫×ᴰ≅× : ∀ {P : Presheaf C ℓA}{Q : Presheaf C ℓB}
            → {Pᴰ : Presheafᴰ P Cᴰ ℓAᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓBᴰ}
        → PshIso (∫P (Pᴰ ×ᴰPsh Qᴰ)) (∫P Pᴰ ×Psh ∫P Qᴰ)
  ∫×ᴰ≅× .fst .fst _ ((p , q) , (pᴰ , qᴰ)) = (p , pᴰ) , (q , qᴰ)
  ∫×ᴰ≅× .fst .snd _ _ _ _ = refl
  ∫×ᴰ≅× .snd _ .fst ((p , pᴰ) , (q , qᴰ)) = (p , q) , (pᴰ , qᴰ)
  ∫×ᴰ≅× .snd _ .snd .fst _ = refl
  ∫×ᴰ≅× .snd _ .snd .snd _ = refl

  -- Internal product: Pᴰ ×ⱽ Qᴰ over P
  PshProdⱽ :
    Functorⱽ (PRESHEAFᴰ Cᴰ ℓA ℓAᴰ ×ᴰ PRESHEAFᴰ Cᴰ ℓA ℓBᴰ)
             (PRESHEAFᴰ Cᴰ ℓA (ℓ-max ℓAᴰ ℓBᴰ))
  PshProdⱽ = postcomposeFⱽ (C ^op) (Cᴰ ^opᴰ) ×Setsⱽ ∘Fⱽ ,Fⱽ-functorⱽ

  _×ⱽPsh_ : ∀ {P : Presheaf C ℓA}
            → (Pᴰ : Presheafᴰ P Cᴰ ℓAᴰ)(Qᴰ : Presheafᴰ P Cᴰ ℓBᴰ)
            → Presheafᴰ P Cᴰ _
  Pᴰ ×ⱽPsh Qᴰ = PshProdⱽ .F-obᴰ (Pᴰ , Qᴰ)

  LocallyRepresentableᴰ :
    ((P , _×P) : Σ[ P ∈ Presheaf C ℓP ] LocallyRepresentable P)
    → Presheafᴰ P Cᴰ ℓPᴰ
    → Type _
  LocallyRepresentableᴰ (P , _×P) Pᴰ = ∀ {c} cᴰ → UniversalElementᴰ Cᴰ (c ×P) ((Cᴰ [-][-, cᴰ ]) ×ᴰPsh Pᴰ)

  open UniversalElement
  ∫LocallyRepresentable :
    {(P , _×P) : Σ[ P ∈ Presheaf C ℓP ] LocallyRepresentable P}
    → ((Pᴰ , _×ᴰPᴰ) : Σ[ Pᴰ ∈ Presheafᴰ P Cᴰ ℓPᴰ ] LocallyRepresentableᴰ (P , _×P) Pᴰ)
    → LocallyRepresentable (∫P Pᴰ)
  ∫LocallyRepresentable (Pᴰ , _×ᴰPᴰ) (Γ , Γᴰ) = UniversalElementᴰ.∫ue (Γᴰ ×ᴰPᴰ) ◁PshIso ∫×ᴰ≅×

  module _ {(P , _×P) : Σ[ P ∈ Presheaf C ℓP ] ∀ c → UniversalElement C ((C [-, c ]) ×Psh P)}
           {Q : Presheaf C ℓQ}
           ((Pᴰ , _×ᴰPᴰ) : Σ[ Pᴰ ∈ Presheafᴰ P Cᴰ ℓPᴰ ] LocallyRepresentableᴰ (P , _×P) Pᴰ)
           (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
           where
    open UniversalElement
    open UniversalElementᴰ
    private
      module Pᴰ = PresheafᴰNotation Pᴰ
      module Qᴰ = PresheafᴰNotation Qᴰ
      ∫⇒Small = (_ , (∫LocallyRepresentable ((Pᴰ , _×ᴰPᴰ)))) ⇒PshSmall ∫P Qᴰ
      module ∫⇒Small = PresheafNotation ∫⇒Small
    _⇒PshSmallᴰ_ : Presheafᴰ ((P , _×P) ⇒PshSmall Q) Cᴰ ℓQᴰ
    _⇒PshSmallᴰ_ .F-obᴰ {Γ} Γᴰ = Qᴰ .F-obᴰ ((Γᴰ ×ᴰPᴰ) .vertexᴰ)
    _⇒PshSmallᴰ_ .F-homᴰ {Γ} {Δ} {γ} {Γᴰ} {Δᴰ} γᴰ q qᴰ =
      ((γ , γᴰ) ∫⇒Small.⋆ (q , qᴰ)) .snd
    _⇒PshSmallᴰ_ .F-idᴰ {Γ} {Γᴰ} = funExt λ q → funExt λ qᴰ → Qᴰ.rectify $ Qᴰ.≡out $
      funExt⁻ (∫⇒Small .F-id) (q , qᴰ)
    _⇒PshSmallᴰ_ .F-seqᴰ γᴰ δᴰ = funExt λ q → funExt λ qᴰ → Qᴰ.rectify $ Qᴰ.≡out $
      funExt⁻ (∫⇒Small .F-seq (_ , γᴰ) (_ , δᴰ)) (q , qᴰ)

  -- Reindexing presheaves
  -- There are 3 different notions of reindexing a presheaf we consider here.
  -- 1. Reindexing a presheaf Qᴰ over Q along a homomorphism α : P ⇒ Q to be over P
  -- 2. Reindexing a presheaf Qᴰ over Q along a functor F to be over (Q ∘ F^op)
  -- 3. The combination of those two, reindexing a presheaf Qᴰ over Q along a heteromorphism α : P =[ F ]=> Q to be over P.
  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
           (α : PshHom P Q) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
           where
    private
      module Qᴰ = PresheafᴰNotation Qᴰ
    open Functorᴰ
    reind : Presheafᴰ P Cᴰ ℓQᴰ
    reind .F-obᴰ {x} xᴰ p = Qᴰ .F-obᴰ xᴰ (α .fst x p)
    reind .F-homᴰ {y} {x} {f} {yᴰ} {xᴰ} fᴰ p qᴰ =
      Qᴰ.reind (sym $ α .snd _ _ _ _) (fᴰ Qᴰ.⋆ᴰ qᴰ)
    reind .F-idᴰ = funExt λ p → funExt λ qᴰ → Qᴰ.rectify $ Qᴰ.≡out $
      (sym $ Qᴰ.reind-filler _ _)
      ∙ Qᴰ.⋆IdL _
    reind .F-seqᴰ fᴰ gᴰ = funExt λ p → funExt λ qᴰ → Qᴰ.rectify $ Qᴰ.≡out $
      (sym $ Qᴰ.reind-filler _ _)
      ∙ Qᴰ.⋆Assoc _ _ _
      ∙ Qᴰ.⟨ refl ⟩⋆⟨ Qᴰ.reind-filler _ _ ⟩
      ∙ Qᴰ.reind-filler _ _

  module _ {Q : Presheaf C ℓQ} where
    private
      module Q = PresheafNotation Q
    module _ {c : C.ob} (q : Q.p[ c ]) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where
      private
        module Qᴰ = PresheafᴰNotation Qᴰ
        open Functorᴰ
      reindYo : Presheafⱽ c Cᴰ ℓQᴰ
      reindYo = reind (yoRec Q q) Qᴰ

  LocallyRepresentableⱽ : {P : Presheaf C ℓP} → (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) → Type _
  LocallyRepresentableⱽ {P = P} Pᴰ = ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) (p : P.p[ Γ ])
    → UniversalElementⱽ Cᴰ Γ ((Cᴰ [-][-, Γᴰ ]) ×ⱽPsh reindYo p Pᴰ)
    where module P = PresheafNotation P

  module LocallyRepresentableⱽNotation {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (_×ⱽ_*Pᴰ : LocallyRepresentableⱽ Pᴰ) where
    private
      module P = PresheafNotation P
      module Pᴰ = PresheafᴰNotation Pᴰ
    open UniversalElementⱽ

    ⌈_×ⱽ_*Pᴰ⌉ : ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) (p : P.p[ Γ ]) → Cᴰ.ob[ Γ ]
    ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ = vertexⱽ $ Γᴰ ×ⱽ p *Pᴰ

    introLR : ∀
      {Γ}{Γᴰ}{p : P.p[ Γ ]}
      {Δ}{Δᴰ}{γ : C [ Δ , Γ ]}
      → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])
      → (pᴰ : Pᴰ.p[ γ P.⋆ p ][ Δᴰ ])
      → Cᴰ [ γ ][ Δᴰ , ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ ]
    introLR {Γᴰ = Γᴰ}{p} γᴰ pᴰ = (introᴰ $ (Γᴰ ×ⱽ p *Pᴰ)) (γᴰ , pᴰ)

    introLR⟨_⟩⟨_⟩ : ∀
      {Γ}{Γᴰ}{p p' : P.p[ Γ ]}{p≡p'}
      {Δ}{Δᴰ}{γ γ' : C [ Δ , Γ ]}{γ≡γ'}
      {γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ]}
      {γᴰ' : Cᴰ [ γ' ][ Δᴰ , Γᴰ ]}
      {pᴰ : Pᴰ.p[ γ P.⋆ p ][ Δᴰ ]}
      {pᴰ' : Pᴰ.p[ γ' P.⋆ p' ][ Δᴰ ]}
      → (γᴰ Cᴰ.≡[ γ≡γ' ] γᴰ')
      → (pᴰ Pᴰ.≡[ P.⟨ γ≡γ' ⟩⋆⟨ p≡p' ⟩ ] pᴰ')
      → PathP (λ i → Cᴰ [ γ≡γ' i ][ Δᴰ , ⌈ Γᴰ ×ⱽ p≡p' i *Pᴰ⌉ ])
          (introLR γᴰ pᴰ)
          (introLR γᴰ' pᴰ')
    introLR⟨ γᴰ≡γᴰ' ⟩⟨ pᴰ≡pᴰ' ⟩ i = introLR (γᴰ≡γᴰ' i) (pᴰ≡pᴰ' i)

    π₁LR : ∀ {Γ} Γᴰ (p : P.p[ Γ ]) → Cᴰ.v[ Γ ] [ ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ , Γᴰ ]
    π₁LR Γᴰ p = fst $ elementⱽ $ (Γᴰ ×ⱽ p *Pᴰ)

    π₂LR : ∀ {Γ} Γᴰ (p : P.p[ Γ ]) → Pᴰ.p[ C.id P.⋆ p ][ ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ ]
    π₂LR Γᴰ p = snd $ elementⱽ $ (Γᴰ ×ⱽ p *Pᴰ)

    π₁LR_⟨_⟩ : ∀ {Γ} {p q : P.p[ Γ ]} Γᴰ → (p≡q : p ≡ q)
      → PathP (λ i → Cᴰ.v[ Γ ] [ ⌈ Γᴰ ×ⱽ p≡q i *Pᴰ⌉ , Γᴰ ])
          (π₁LR Γᴰ p)
          (π₁LR Γᴰ q)
    π₁LR Γᴰ ⟨ p≡q ⟩ i = π₁LR Γᴰ $ p≡q i

    π₂LR_⟨_⟩ : ∀ {Γ} {p q : P.p[ Γ ]} Γᴰ → (p≡q : p ≡ q)
      → PathP (λ i → Pᴰ.p[ C.id P.⋆ p≡q i ][ ⌈ Γᴰ ×ⱽ p≡q i *Pᴰ⌉ ])
          (π₂LR Γᴰ p)
          (π₂LR Γᴰ q)
    π₂LR Γᴰ ⟨ p≡q ⟩ i = π₂LR Γᴰ $ p≡q i

    funcLR : ∀
      {Γ}{Γᴰ}{p : P.p[ Γ ]}
      {Δ}{Δᴰ}{γ : C [ Δ , Γ ]}
      → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])
      → Cᴰ [ γ ][ ⌈ Δᴰ ×ⱽ (γ P.⋆ p) *Pᴰ⌉ , ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ ]
    funcLR {p = p}{γ = γ} γᴰ =
      introLR (π₁LR _ (γ P.⋆ p) Cᴰ.⋆ⱽᴰ γᴰ) (Pᴰ.reind (P.⋆IdL _) $ (π₂LR _ (γ P.⋆ p)))

--     funcLR⟨_⟩ : ∀
--       {Γ}{Γᴰ}{p : P.p[ Γ ]}
--       {Δ}{Δᴰ}{γ γ' : C [ Δ , Γ ]}{γ≡γ'}
--       → {γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ]}
--       → {γᴰ' : Cᴰ [ γ' ][ Δᴰ , Γᴰ ]}
--       → γᴰ Cᴰ.≡[ γ≡γ' ] γᴰ'
--       → PathP (λ i → Cᴰ [ γ≡γ' i ][ ⌈ Δᴰ ×ⱽ γ≡γ' i P.⋆ p *Pᴰ⌉ , ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ ])
--           (funcLR γᴰ)
--           (funcLR γᴰ')
--     funcLR⟨ x ⟩ i = funcLR (x i)

    foo : ∀
      {Γ}
      {Δ}(Δᴰ : Cᴰ.ob[ Δ ])
      (γ : C [ Δ , Γ ])
      (p : P.p[ Γ ])
      (p' : P.p[ Δ ])
      → Type _
    foo Δᴰ γ p p' = Pᴰ.p[ γ P.⋆ p ][ ⌈ Δᴰ ×ⱽ p' *Pᴰ⌉ ]

    funcLR-id : ∀ {Γ}{Γᴰ}{p : P.p[ Γ ]}
      → PathP (λ i → Cᴰ [ C.id ][ ⌈ Γᴰ ×ⱽ P.⋆IdL p i *Pᴰ⌉ , ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ ])
          (funcLR {Γᴰ = Γᴰ}{p = p} Cᴰ.idᴰ)
          Cᴰ.idᴰ
    funcLR-id {Γ}{Γᴰ}{p} =
      (λ i → introLR (left i) (right i))
      ▷ (sym $ weak-ηⱽ (Γᴰ ×ⱽ p *Pᴰ))
      where
        foo' : (p : P.p[ Γ ])(p' : P.p[ Γ ]) → Type _
        foo' = foo Γᴰ C.id

        foo'^ :(p' : P.p[ Γ ])(p : P.p[ Γ ]) → Type _
        foo'^ p' p = foo' p p'

        left : PathP (λ i → Cᴰ.v[ Γ ] [ ⌈ Γᴰ ×ⱽ P.⋆IdL p i *Pᴰ⌉ , Γᴰ ])
          (π₁LR Γᴰ (C.id P.⋆ p) Cᴰ.⋆ⱽᴰ Cᴰ.idᴰ)
          (π₁LR Γᴰ p)
        left = (Cᴰ.rectify $ Cᴰ.≡out $ sym (Cᴰ.reind-filler _ _) ∙ Cᴰ.⋆IdR _)
          ◁ π₁LR _ ⟨ P.⋆IdL _ ⟩

        right' : PathP (λ i → cong₂ foo' (P.⋆IdL p) (P.⋆IdL p) i)
          (π₂LR Γᴰ (C.id P.⋆ p))
          (π₂LR Γᴰ p)
        right' = π₂LR _ ⟨ P.⋆IdL p ⟩

        right-lem : Path (foo' p (C.id P.⋆ p) ≡ foo' p p)
          (cong (foo'^ (C.id P.⋆ p)) (sym $ P.⋆IdL p) ∙ cong₂ foo' (P.⋆IdL p) (P.⋆IdL p))
          (cong (foo' p) (P.⋆IdL p))          
        right-lem =
          (cong (foo'^ (C.id P.⋆ p)) (sym $ P.⋆IdL p) ∙ cong₂ foo' (P.⋆IdL p) (P.⋆IdL p))
            ≡⟨ cong₂ _∙_ refl (cong₂Funct foo' _ _) ⟩
          (cong (foo'^ (C.id P.⋆ p)) (sym $ P.⋆IdL p)
          ∙ cong (foo'^ (C.id P.⋆ p)) (P.⋆IdL p)
          ∙ cong (foo' p) (λ i → P.⋆IdL p i))
            ≡⟨ assoc _ _ _ ∙ cong₂ _∙_ (sym (sym (rCancel _))) refl ∙ (sym $ lUnit _) ⟩
          (cong (foo' p) (P.⋆IdL p))
            ∎

        thing : (pth : (C.id P.⋆ p) ≡ (C.id P.⋆ (C.id P.⋆ p)))
          → Pᴰ.p[ C.id P.⋆ p ][ ⌈ Γᴰ ×ⱽ (C.id P.⋆ p) *Pᴰ⌉ ]
            ≡ Pᴰ.p[ C.id P.⋆ (C.id P.⋆ p) ][ ⌈ Γᴰ ×ⱽ (C.id P.⋆ p) *Pᴰ⌉ ]
        thing pth = (cong Pᴰ.p[_][ ⌈ Γᴰ ×ⱽ (C.id P.⋆ p) *Pᴰ⌉ ]) pth

        right : PathP (λ i → cong (foo' p) (P.⋆IdL p) i)
          (Pᴰ.reind (P.⋆IdL _) $ π₂LR Γᴰ (C.id P.⋆ p))
          (π₂LR Γᴰ p)
        right = rectify (cong₂ _∙_
          (thing (sym $ P.⋆IdL _) ≡⟨ cong thing (P.isSetPsh _ _ _ _ ) ⟩ thing P.⟨⟩⋆⟨ sym $ P.⋆IdL _ ⟩ ∎)
          refl
          ∙ right-lem)
          (compPathP
            (Pᴰ.≡out $ sym $ Pᴰ.reind-filler _ _)
            right')
          -- compPathP {!!} {!!} {!!}
          -- (Pᴰ.rectify $ Pᴰ.≡out $ sym (Pᴰ.reind-filler _ _) ∙ (Pᴰ.≡in $ {!!}))
          -- ◁ {!!}
          
  module _ {P : Presheaf C ℓP}
    ((Pᴰ , _×ⱽ_*Pᴰ) : Σ[ Pᴰ ∈ Presheafᴰ P Cᴰ ℓPᴰ ] LocallyRepresentableⱽ Pᴰ)
    (Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ)
    where
    open UniversalElementⱽ
    private
      module P = PresheafNotation P
      module Pᴰ = PresheafᴰNotation Pᴰ
      module Qᴰ = PresheafᴰNotation Qᴰ
    open LocallyRepresentableⱽNotation Pᴰ _×ⱽ_*Pᴰ
    -- Γᴰ ⊢ (Pᴰ ⇒ Qᴰ)(p) := Γᴰ , Pᴰ(p) ⊢ Qᴰ(p)
    ⇒PshSmallⱽ : Presheafᴰ P Cᴰ ℓQᴰ
    ⇒PshSmallⱽ .F-obᴰ {Γ} Γᴰ p = Qᴰ .F-obᴰ ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ p
    ⇒PshSmallⱽ .F-homᴰ {Γ} {Δ} {γ} {Γᴰ} {Δᴰ} γᴰ p qᴰ =
      funcLR γᴰ Qᴰ.⋆ᴰ qᴰ
    ⇒PshSmallⱽ .F-idᴰ {Γ}{Γᴰ} = funExt λ p → funExt λ qᴰ →
      {!!} ▷
      (Qᴰ.rectify $ Qᴰ.≡out $ (sym $ Qᴰ.reind-filler (P.⋆IdL _) _) ∙ Qᴰ.⋆IdL _)
      -- fromPathP (Qᴰ.rectify $ Qᴰ.≡out $
      --   Qᴰ.⋆IdL _
      --   ∙ sym (Qᴰ.reind-filler {!!} _))
      -- symP $ toPathP $ sym $
      --   (Qᴰ.rectify $ Qᴰ.≡out $ Qᴰ.⟨ introᴰ≡ (Γᴰ ×ⱽ p *Pᴰ) $ {!!} ⟩⋆⟨⟩
      --     ∙ {!!})
      --   ∙ {!!}
        -- Qᴰ.⟨ introᴰ≡ (Γᴰ ×ⱽ p *Pᴰ) 
        --   (ΣPathP ((sym $ C.⋆IdL _) , (ΣPathP
        --   ( (Cᴰ.rectify $ Cᴰ.≡out $ sym (Cᴰ.reind-filler _ _) ∙ Cᴰ.⋆IdR _ ∙ {!Cᴰ.⟨ ? ⟩⋆⟨ ? ⟩!})
        --   , {!!}
        --   ))))
        --   ⟩⋆⟨⟩
        -- ∙ {!!}
    ⇒PshSmallⱽ .F-seqᴰ = λ fᴰ gᴰ i x x₁ → {!!}

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {Q : Presheaf D ℓQ}
  (F : Functor C D) (Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ)
  where
  reindFunc : Presheafᴰ (Q ∘F (F ^opF)) (CatReindex Dᴰ F) ℓQᴰ
  reindFunc = Qᴰ ∘Fᴰ (Reindexπ _ _ ^opFᴰ)

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  {P : Presheaf C ℓP}{Q : Presheaf D ℓQ}
  (α : PshHet F P Q)(Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ)
  where
  reindHet : Presheafᴰ P (CatReindex Dᴰ F) ℓQᴰ
  reindHet = reind α $ reindFunc F Qᴰ
