{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.LocalRepresentability where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Properties
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Properties
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Bifunctorᴰ
open Functorᴰ

open PshHom
open PshIso

module _ {C : Category ℓC ℓC'} where
  LocallyRepresentableⱽPresheafᴰ
    : (P : Presheaf C ℓP) (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (ℓPᴰ : Level) → Type _
  LocallyRepresentableⱽPresheafᴰ P Cᴰ ℓPᴰ =
    Σ[ Pᴰ ∈ Presheafᴰ P Cᴰ ℓPᴰ ] LocallyRepresentableⱽ Pᴰ

module _
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf D ℓQ}
  {F : Functor C D}
  {α : PshHet F P Q}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ)
  (αᴰ : PshHetᴰ α Fᴰ Pᴰ Qᴰ)
  where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ
  preservesLocalReprⱽCone : ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) (p : P.p[ Γ ]) →
    PshHetⱽ Fᴰ ((Cᴰ [-][-, Γᴰ ]) ×ⱽPsh reindYo p Pᴰ)
               ((Dᴰ [-][-, Fᴰ .F-obᴰ Γᴰ ]) ×ⱽPsh reindYo (α .N-ob _ p) Qᴰ)
  preservesLocalReprⱽCone Γᴰ p =
    ×ⱽ-introHet Fᴰ (×ⱽ-π₁ ⋆PshHomⱽᴰ Functorᴰ→PshHetᴰ Fᴰ Γᴰ)
                   (×ⱽ-π₂ ⋆PshHomⱽᴰ reind-introHet (PshHomPathPshHomᴰ lem (reind-π {α = yoRec P p} ⋆PshHomᴰ αᴰ)))
    where
      lem :
        (yoRec P p ⋆PshHom α)
        ≡ 
        (Functor→PshHet F _ ⋆PshHom (yoRec Q (α .N-ob _ p) ∘ˡ F))
      lem = makePshHomPath (funExt λ x → funExt λ γ → α .N-hom _ _ _ _)

  preservesLocalReprⱽ : LocallyRepresentableⱽ Pᴰ → Type _
  preservesLocalReprⱽ _×ⱽ_*Pᴰ = ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) (p : P.p[ Γ ])
    → preservesUEⱽ (preservesLocalReprⱽCone Γᴰ p) (Γᴰ ×ⱽ p *Pᴰ)

  preservesLocalReprⱽ→UEⱽ :
    (_×ⱽ_*Pᴰ : LocallyRepresentableⱽ Pᴰ)
    → preservesLocalReprⱽ _×ⱽ_*Pᴰ
    → ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) (p : P.p[ Γ ])
    → UniversalElementⱽ Dᴰ (F ⟅ Γ ⟆) ((Dᴰ [-][-, Fᴰ .F-obᴰ Γᴰ ]) ×ⱽPsh reindYo (α .N-ob _ p) Qᴰ)
  preservesLocalReprⱽ→UEⱽ _×ⱽ_*Pᴰ pres-⟨_×ⱽ_*Pᴰ⟩ Γᴰ p =
    preservesUEⱽ→UEⱽ (preservesLocalReprⱽCone Γᴰ p) (Γᴰ ×ⱽ p *Pᴰ) pres-⟨ Γᴰ ×ⱽ p *Pᴰ⟩

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

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
      {Δ}{Δᴰ Δᴰ'}{Δᴰ≡Δᴰ' : Δᴰ ≡ Δᴰ'}
      {γ γ' : C [ Δ , Γ ]}{γ≡γ'}
      {γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ]}
      {γᴰ' : Cᴰ [ γ' ][ Δᴰ' , Γᴰ ]}
      {pᴰ : Pᴰ.p[ γ P.⋆ p ][ Δᴰ ]}
      {pᴰ' : Pᴰ.p[ γ' P.⋆ p' ][ Δᴰ' ]}
      → (γᴰ ≡[ cong₂ (Cᴰ [_][_, Γᴰ ]) γ≡γ' Δᴰ≡Δᴰ' ] γᴰ')
      → (pᴰ ≡[ cong₂ Pᴰ.p[_][_] P.⟨ γ≡γ' ⟩⋆⟨ p≡p' ⟩ Δᴰ≡Δᴰ' ] pᴰ')
      → introLR γᴰ pᴰ ≡[ (λ i → Cᴰ [ γ≡γ' i ][ Δᴰ≡Δᴰ' i , ⌈ Γᴰ ×ⱽ p≡p' i *Pᴰ⌉ ]) ] introLR γᴰ' pᴰ'
    introLR⟨ x ⟩⟨ x₁ ⟩ i = introLR (x i) (x₁ i)

    π₁LR : ∀ {Γ} Γᴰ (p : P.p[ Γ ]) → Cᴰ.v[ Γ ] [ ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ , Γᴰ ]
    π₁LR Γᴰ p = fst $ elementⱽ $ (Γᴰ ×ⱽ p *Pᴰ)

    π₂LR : ∀ {Γ} Γᴰ (p : P.p[ Γ ]) → Pᴰ.p[ C.id P.⋆ p ][ ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ ]
    π₂LR Γᴰ p = snd $ elementⱽ $ (Γᴰ ×ⱽ p *Pᴰ)

    opaque
      β₁LR : ∀ {Γ}{Γᴰ}{p : P.p[ Γ ]}
        {Δ}{Δᴰ}{γ : C [ Δ , Γ ]}
        → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])
        → (pᴰ : Pᴰ.p[ γ P.⋆ p ][ Δᴰ ])
        → introLR γᴰ pᴰ Cᴰ.⋆ᴰⱽ π₁LR _ _ ≡ γᴰ
      β₁LR {_}{Γᴰ}{p} γᴰ pᴰ = Cᴰ.rectify $ Cᴰ.≡out $
        (sym $ Cᴰ.reind-filler _ _)
        ∙ (Cᴰ.≡in $ λ i → βᴰ (Γᴰ ×ⱽ p *Pᴰ) {p = _ , γᴰ , pᴰ} i .snd .fst)

      β₂LR : ∀ {Γ}{Γᴰ}{p : P.p[ Γ ]}
        {Δ}{Δᴰ}{γ : C [ Δ , Γ ]}
        → (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])
        → (pᴰ : Pᴰ.p[ γ P.⋆ p ][ Δᴰ ])
        → (introLR γᴰ pᴰ Pᴰ.⋆ᴰ (Pᴰ.reind (P.⋆IdL _) $ π₂LR _ _)) ≡ pᴰ
      β₂LR {Γ} {Γᴰ} {p} {Δ} {Δᴰ} {γ} γᴰ pᴰ = Pᴰ.rectify $ Pᴰ.≡out $
        (Pᴰ.⟨⟩⋆⟨ sym $ Pᴰ.reind-filler _ _ ⟩
        ∙ Pᴰ.reind-filler _ _)
        ∙ (Pᴰ.≡in $ λ i → βᴰ (Γᴰ ×ⱽ p *Pᴰ) {p = _ , γᴰ , pᴰ} i .snd .snd)
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

    -- TODO: this is very slow, figure out how to stay in the reasoning machine
    funcLR-seq : ∀
      {Γ}{Γᴰ}{p : P.p[ Γ ]}
      {Δ}{Δᴰ}{γ : C [ Δ , Γ ]}
      {Θ}{Θᴰ}{δ : C [ Θ , Δ ]}
      (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])(δᴰ : Cᴰ [ δ ][ Θᴰ , Δᴰ ])
      → PathP (λ i → Cᴰ [ δ C.⋆ γ ][ ⌈ Θᴰ ×ⱽ (P.⋆Assoc δ γ p i) *Pᴰ⌉ , ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ ])
          (funcLR {p = p} (δᴰ Cᴰ.⋆ᴰ γᴰ))
          (funcLR δᴰ Cᴰ.⋆ᴰ funcLR γᴰ)
    funcLR-seq {Γ} {Γᴰ} {p} {Δ} {Δᴰ} {γ} {Θ} {Θᴰ} {δ} γᴰ δᴰ =
      introLR⟨
        (λ i → π₁LR Θᴰ ⟨ P.⋆Assoc _ _ _ ⟩ i Cᴰ.⋆ⱽᴰ (δᴰ Cᴰ.⋆ᴰ γᴰ))
          ▷ (sym Cᴰ.⋆Assocⱽᴰᴰ
          ∙ (Cᴰ.≡out $ Cᴰ.⟨ Cᴰ.≡in (sym $ β₁LR _ _) ⟩⋆⟨ refl ⟩)
          ∙ (Cᴰ.⋆Assocᴰⱽᴰ))
      ⟩⟨
        -- solver?
        rectify
          ((congS₂ _∙_ refl (congS₂ _∙_ refl (sym $ congS₂Bifunct Pᴰ~ _ _ _ _) ∙ ((sym $ congS₂Bifunct Pᴰ~ _ _ _ _)))
          ∙ (sym $ congS₂Bifunct Pᴰ~ _ _ _ _))
          ∙ congS₂ (congS₂ Pᴰ~) (P.isSetPsh _ _ _ _) (P.isSetPsh _ _ _ _))
        $
        compPathP (Pᴰ.≡out $ sym (Pᴰ.reind-filler _ _)) $
        compPathP (π₂LR Θᴰ ⟨ P.⋆Assoc _ _ _ ⟩) $
        compPathP ((Pᴰ.≡out $ Pᴰ.reind-filler _ _) ▷ (sym $ β₂LR _ _)) $
        (Pᴰ.≡out $ Pᴰ.reind-filler _ _)
      ⟩ ▷ (Cᴰ.rectify $ Cᴰ.≡out $ sym $ introᴰ-natural (Γᴰ ×ⱽ p *Pᴰ))
      where
        Pᴰ~ : P.p[ Θ ] → P.p[ Θ ] → Type _
        Pᴰ~ p p' = Pᴰ.p[ p ][ ⌈ Θᴰ ×ⱽ p' *Pᴰ⌉ ]

        Pᴰ~' : P.p[ Θ ] → P.p[ Θ ] → Type _
        Pᴰ~' p' p = Pᴰ~ p p'

    funcLR-id : ∀ {Γ}{Γᴰ}{p : P.p[ Γ ]}
      → PathP (λ i → Cᴰ [ C.id ][ ⌈ Γᴰ ×ⱽ P.⋆IdL p i *Pᴰ⌉ , ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ ])
          (funcLR {Γᴰ = Γᴰ}{p = p} Cᴰ.idᴰ)
          Cᴰ.idᴰ
    funcLR-id {Γ}{Γᴰ}{p} =
      introLR⟨
        (Cᴰ.rectify $ Cᴰ.≡out $ sym (Cᴰ.reind-filler _ _) ∙ Cᴰ.⋆IdR _)
        ◁ π₁LR _ ⟨ P.⋆IdL _ ⟩
        ⟩⟨
        rectify
          (sym (congS₂Bifunct Pᴰ~ _ _ _ _) ∙ (congS₂ (congS₂ Pᴰ~) (P.isSetPsh _ _ _ _) (P.isSetPsh _ _ _ _)))
          $
          compPathP (Pᴰ.≡out $ sym $ Pᴰ.reind-filler _ _) $
          π₂LR _ ⟨ P.⋆IdL p ⟩
        ⟩
      ▷ (sym $ weak-ηⱽ (Γᴰ ×ⱽ p *Pᴰ))
      where
        Pᴰ~ : (p : P.p[ Γ ])(p' : P.p[ Γ ]) → Type _
        Pᴰ~ p p' = Pᴰ.p[ p ][ ⌈ Γᴰ ×ⱽ p' *Pᴰ⌉ ]

    -- I need an η principle here
    app-naturality-lemma :
      ∀ {Δ Γ Δᴰ Γᴰ}{γ : C [ Δ , Γ ]}{γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ]}
        {p : P.p[ Γ ]}{pᴰ : Pᴰ.p[ p ][ Γᴰ ]}
      → Path (Σ[ γ' ∈ C [ Δ , Γ ] ] (Cᴰ [ γ' ][ Δᴰ , ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ ]))
          (C.id C.⋆ γ ,
            (introLR Cᴰ.idᴰ (Pᴰ.reind (sym $ P.⋆IdL _) (γᴰ Pᴰ.⋆ᴰ pᴰ)) Cᴰ.⋆ᴰ funcLR γᴰ))
          (γ C.⋆ C.id ,
            (γᴰ Cᴰ.⋆ᴰ introLR Cᴰ.idᴰ (Pᴰ.reind (sym $ P.⋆IdL p) pᴰ)))
    app-naturality-lemma {Δ} {Γ} {Δᴰ} {Γᴰ} {γ} {γᴰ} {p} {pᴰ} = sym $
        ∫ue.intro-natural (Γᴰ ×ⱽ p *Pᴰ)
        ∙ ∫ue.intro≡ (Γᴰ ×ⱽ p *Pᴰ) (×≡Snd-hSet C.isSetHom
          (Cᴰ.⋆IdR _
          ∙ (sym $ Cᴰ.⋆IdL _)
          ∙ Cᴰ.⟨ (sym $ ≡×Snd (∫ue.β (Δᴰ ×ⱽ (γ P.⋆ p) *Pᴰ)) .fst) ⟩⋆⟨ refl ⟩
          ∙ Cᴰ.⋆Assoc _ _ _
          ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.reind-filler _ _ ∙ (sym $ ≡×Snd (∫ue.β (Γᴰ ×ⱽ p *Pᴰ)) .fst) ⟩
          ∙ sym (Cᴰ.⋆Assoc _ _ _) )
          (chacha-slide (P._⋆ p) P.isSetPsh C.⟨ sym $ C.⋆IdL γ ⟩⋆⟨ refl ⟩ $ sym $
            sym (Pᴰ.reind-filler _ _)
            ∙ Pᴰ.⋆Assoc _ _ _
            ∙ Pᴰ.⟨⟩⋆⟨ Pᴰ.reind-filler _ _ ∙ chacha-slide⁻ (P._⋆ p) (≡×Snd (∫ue.β (Γᴰ ×ⱽ p *Pᴰ)) .snd)  ⟩
            ∙ Pᴰ.⟨⟩⋆⟨ sym $ Pᴰ.reind-filler _ _ ⟩
            ∙ Pᴰ.reind-filler _ _ ∙ (chacha-slide⁻ (P._⋆ (γ P.⋆ p)) $ ≡×Snd (∫ue.β (Δᴰ ×ⱽ (γ P.⋆ p) *Pᴰ)) .snd)
            ∙ sym (Pᴰ.reind-filler _ _)
            ∙ Pᴰ.⟨⟩⋆⟨ Pᴰ.reind-filler (sym $ P.⋆IdL p) pᴰ ⟩
            ∙ Pᴰ.reind-filler _ _
          ))
      -- -- TODO: test perf vs this original version
      -- sym $
      --   ∫ue.intro-natural (Γᴰ ×ⱽ p *Pᴰ)
      --   ∙ ∫ue.intro≡ (Γᴰ ×ⱽ p *Pᴰ) (ΣPathPSnd
      --     (Cᴰ.⋆IdR _
      --     ∙ (sym $ Cᴰ.⋆IdL _)
      --     ∙ Cᴰ.⟨ (sym $ PathPΣSnd (∫ue.β (Δᴰ ×ⱽ (γ P.⋆ p) *Pᴰ)) .fst) ⟩⋆⟨ refl ⟩
      --     ∙ Cᴰ.⋆Assoc _ _ _
      --     ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.reind-filler _ _ ∙ (sym $ PathPΣSnd (∫ue.β (Γᴰ ×ⱽ p *Pᴰ)) .fst) ⟩
      --     ∙ sym (Cᴰ.⋆Assoc _ _ _) )
      --     (Pᴰ.rectify $ Pᴰ.≡out $ sym $
      --       sym (Pᴰ.reind-filler _ _)
      --       ∙ Pᴰ.⋆Assoc _ _ _
      --       ∙ Pᴰ.⟨⟩⋆⟨ Pᴰ.reind-filler _ _ ∙ (Pᴰ.≡in $ PathPΣSnd (∫ue.β (Γᴰ ×ⱽ p *Pᴰ)) .snd) ⟩
      --       ∙ Pᴰ.⟨⟩⋆⟨ sym $ Pᴰ.reind-filler _ _ ⟩
      --       ∙ Pᴰ.reind-filler _ _ ∙ (Pᴰ.≡in $ PathPΣSnd (∫ue.β (Δᴰ ×ⱽ (γ P.⋆ p) *Pᴰ)) .snd)
      --       ∙ sym (Pᴰ.reind-filler _ _)
      --       ∙ Pᴰ.⟨⟩⋆⟨ Pᴰ.reind-filler (sym $ P.⋆IdL p) pᴰ ⟩
      --       ∙ Pᴰ.reind-filler _ _))

-- Goal: (C.id C.⋆ γ ,
--        introLR Cᴰ.idᴰ
--        (Pᴰ.reind (λ i → P.⋆IdL (γ P.⋆ p) (~ i)) (γᴰ Pᴰ.⋆ᴰ pᴰ))
--        Cᴰ.⋆ᴰ funcLR γᴰ)
--       ≡
--       (γ C.⋆ C.id ,
--        γᴰ Cᴰ.⋆ᴰ introLR Cᴰ.idᴰ (Pᴰ.reind (λ i → P.⋆IdL p (~ i)) pᴰ))

