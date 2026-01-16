{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Representable where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.HLevels.More

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base as Curried hiding (_[-][-,_])
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf
import Cubical.Categories.Displayed.Presheaf.Base as Curried
  hiding (Presheafᴰ; Presheafⱽ; module PresheafᴰNotation)
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.Curry
import Cubical.Categories.Displayed.Presheaf.Representable as Curried

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Category
open Functor
open Functorᴰ
open PshHom
open PshIso
open NatTrans
open NatIso
open Iso
open isIsoOver

module _ {C : Category ℓC ℓC'}{x : C .ob} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module Cᴰ = Fibers Cᴰ
  _[-][-,_] : Cᴰ.ob[ x ] → Presheafⱽ x Cᴰ ℓCᴰ'
  _[-][-,_] xᴰ = UncurryPshᴰ (C [-, x ]) Cᴰ (Cᴰ Curried.[-][-, xᴰ ])

  ∫Repr-iso : ∀ {xᴰ}
    → PshIso (PresheafᴰNotation.∫ Cᴰ (C [-, x ]) (_[-][-,_] xᴰ))
             ((∫C Cᴰ) [-, x , xᴰ ])
  ∫Repr-iso {xᴰ} .trans .N-ob (y , yᴰ) (f , fᴰ) = f , fᴰ
  ∫Repr-iso {xᴰ} .trans .N-hom = λ _ _ _ _ → sym $ Cᴰ.reind-filler _
  ∫Repr-iso {xᴰ} .nIso (y , yᴰ) .fst (f , fᴰ) = f , fᴰ
  ∫Repr-iso {xᴰ} .nIso (y , yᴰ) .snd .fst _ = refl
  ∫Repr-iso {xᴰ} .nIso (y , yᴰ) .snd .snd _ = refl

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  module _ {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
    private
      module P = PresheafNotation P
      module Pᴰ = PresheafᴰNotation Cᴰ _ Pᴰ
    yoRecᴰ : ∀ {x}{xᴰ}{p : P.p[ x ]} (pᴰ : Pᴰ.p[ p ][ xᴰ ]) → PshHomᴰ (yoRec P p) (Cᴰ [-][-, xᴰ ]) Pᴰ
    yoRecᴰ pᴰ = Uncurry-recᴰ (Cᴰ Curried.[-][-, _ ]) Pᴰ (Curried.yoRecᴰ (CurryPshᴰ P Cᴰ Pᴰ) pᴰ)
  module _ {x : C .ob} (Pⱽ : Presheafⱽ x Cᴰ ℓPᴰ) where
    private
      module Pⱽ = PresheafᴰNotation Cᴰ _ Pⱽ
    yoRecⱽ : ∀ {xᴰ} → Pⱽ.p[ C.id ][ xᴰ ] → PshHomⱽ (Cᴰ [-][-, xᴰ ]) Pⱽ
    yoRecⱽ pⱽ .N-ob (Γ , Γᴰ , f) gᴰ = Pⱽ .F-hom (f , gᴰ , C.⋆IdR _) pⱽ
    yoRecⱽ pⱽ .N-hom (Γ , Γᴰ , f) (Δ , Δᴰ , g) (h , hᴰ , h⋆g≡f) gᴰ =
      congS (λ z → Pⱽ .F-hom z pⱽ)
        (ΣPathP ((sym h⋆g≡f) ,
                 (ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ sym $ Cᴰ.reind-filler _) ,
                 isProp→PathP (λ _ → C.isSetHom _ _) _ _))))
      ∙ funExt⁻ (Pⱽ .F-seq (g , gᴰ , C.⋆IdR g) (h , hᴰ , h⋆g≡f)) pⱽ

    yoRecⱽ-UMP :
      ∀ {xᴰ}
      → Iso (PshHomⱽ (Cᴰ [-][-, xᴰ ]) Pⱽ) (Pⱽ.p[ C.id ][ xᴰ ])
    yoRecⱽ-UMP = compIso
      (Uncurry-recⱽ-Iso (Cᴰ Curried.[-][-, _ ]) Pⱽ)
      (Curried.yoRecⱽ-UMP (CurryPshᴰ (C [-, x ]) Cᴰ Pⱽ))

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
         (x : C .Category.ob) (Pⱽ : Presheafⱽ x Cᴰ ℓPᴰ) where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module Pⱽ = PresheafᴰNotation Cᴰ (C [-, x ]) Pⱽ

  Representableⱽ : Type _
  Representableⱽ = Σ[ xᴰ ∈ Cᴰ.ob[ x ] ] PshIsoⱽ (Cᴰ [-][-, xᴰ ]) Pⱽ

  record UniversalElementⱽ'
    : Type (ℓ-max ℓC $ ℓ-max ℓC' $ ℓ-max ℓCᴰ $ ℓ-max ℓCᴰ' $ ℓPᴰ) where
    field
      vertexⱽ : Cᴰ.ob[ x ]
      elementⱽ : Pⱽ.p[ C.id ][ vertexⱽ ]
      universalⱽ : isPshIsoⱽ (Cᴰ [-][-, vertexⱽ ]) Pⱽ (yoRecⱽ Pⱽ elementⱽ)

    toPshIsoⱽ : PshIsoⱽ (Cᴰ [-][-, vertexⱽ ]) Pⱽ
    toPshIsoⱽ = pshiso (yoRecⱽ Pⱽ elementⱽ) universalⱽ

    REPRⱽ : Representableⱽ
    REPRⱽ .fst = vertexⱽ
    REPRⱽ .snd = toPshIsoⱽ

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
         (P : Presheaf C ℓP) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Cᴰ P Pᴰ
  open UniversalElementNotation

  isUniversalᴰ : ∀ (ue : UniversalElement C P) {vᴰ} (eᴰ : Pᴰ.p[ ue .element ][ vᴰ ]) → Type _
  isUniversalᴰ ue eᴰ = isPshIsoᴰ (asPshIso ue) (Cᴰ [-][-, _ ]) Pᴰ (yoRecᴰ Pᴰ eᴰ)

  UniversalElementᴰ : UniversalElement C P → Type _
  UniversalElementᴰ ue =
    Σ[ vᴰ ∈ _ ] Σ[ eᴰ ∈ Pᴰ.p[ ue .element ][ vᴰ ] ] isUniversalᴰ ue eᴰ

  Representableᴰ : (RepresentationPshIso P) → Type _
  Representableᴰ (x , yx≅P) =
    Σ[ xᴰ ∈ Cᴰ.ob[ x ] ] PshIsoᴰ yx≅P (Cᴰ [-][-, xᴰ ]) Pᴰ

  module UniversalElementᴰNotation {ue : UniversalElement C P} (ueᴰ : UniversalElementᴰ ue) where
    module ue = UniversalElementNotation ue
    vertexᴰ = ueᴰ .fst
    elementᴰ = ueᴰ .snd .fst
    asReprᴰ : Representableᴰ (ue .vertex , asPshIso ue)
    asReprᴰ = (ueᴰ .fst) , ((yoRecᴰ Pᴰ (ueᴰ .snd .fst)) , (ueᴰ .snd .snd))

    introᴰ : ∀ {Γ Γᴰ}
        → {p : P.p[ Γ ]}
        → (pᴰ : Pᴰ.p[ p ][ Γᴰ ])
        → Cᴰ [ ue.intro p ][ Γᴰ , ueᴰ .fst ]
    introᴰ = ueᴰ .snd .snd _ _ .inv _

    opaque
      cong-introᴰ :
        ∀ {Γ Γᴰ}
        → {p p' : P.p[ Γ ]} {pᴰ : Pᴰ.p[ p ][ Γᴰ ]}{p'ᴰ : Pᴰ.p[ p' ][ Γᴰ ]}
        → pᴰ Pᴰ.∫≡ p'ᴰ
        → introᴰ pᴰ Cᴰ.∫≡ introᴰ p'ᴰ
      cong-introᴰ pᴰ≡p'ᴰ i =
        (ue.intro (pᴰ≡p'ᴰ i .fst))
        , (introᴰ {p = pᴰ≡p'ᴰ i .fst} (pᴰ≡p'ᴰ i .snd))

      βᴰ : ∀ {Γ Γᴰ}{p : P.p[ Γ ]}
        → (pᴰ : Pᴰ.p[ p ][ Γᴰ ])
        → (introᴰ pᴰ Pᴰ.⋆ᴰ ueᴰ .snd .fst) Pᴰ.≡[ ue.β ] pᴰ
      βᴰ {Γ}{Γᴰ}{p} pᴰ = Pᴰ.rectify $ ueᴰ .snd .snd Γ Γᴰ .rightInv p pᴰ

      ∫βᴰ : ∀ {Γ Γᴰ}{p : P.p[ Γ ]}
        → (pᴰ : Pᴰ.p[ p ][ Γᴰ ])
        → (introᴰ pᴰ Pᴰ.⋆ᴰ ueᴰ .snd .fst) Pᴰ.∫≡ pᴰ
      ∫βᴰ pᴰ = Pᴰ.≡in $ βᴰ pᴰ

      ηᴰ : ∀ {Γ Γᴰ}{f : C [ Γ , ue.vertex ]}
        → (fᴰ : Cᴰ [ f ][ Γᴰ , ueᴰ .fst ])
        → fᴰ Cᴰ.≡[ ue.η ] introᴰ (fᴰ Pᴰ.⋆ᴰ ueᴰ .snd .fst)
      ηᴰ {Γ}{Γᴰ}{f} fᴰ = symP $ Cᴰ.rectify $ ueᴰ .snd .snd Γ Γᴰ .leftInv f fᴰ
      ∫ηᴰ : ∀ {Γ Γᴰ}{f : C [ Γ , ue.vertex ]}
        → (fᴰ : Cᴰ [ f ][ Γᴰ , ueᴰ .fst ])
        → fᴰ Cᴰ.∫≡ introᴰ (fᴰ Pᴰ.⋆ᴰ ueᴰ .snd .fst)
      ∫ηᴰ fᴰ = Cᴰ.≡in $ ηᴰ fᴰ

  -- Could be more compositional but too lazy
  Representableᴰ→UniversalElementᴰOverUE : (ue : UniversalElement C P)
    → Representableᴰ (ue .vertex , asPshIso ue)
    → UniversalElementᴰ ue
  Representableᴰ→UniversalElementᴰOverUE ue yᴰxᴰ≅Pᴰ = (yᴰxᴰ≅Pᴰ .fst)
    , ((Pᴰ.reind (P.⋆IdL _) (yᴰxᴰ≅Pᴰ .snd .fst .N-ob (ue .UniversalElement.vertex , yᴰxᴰ≅Pᴰ .fst , C.id) Cᴰ.idᴰ))
    , λ Γ Γᴰ → isisoover
      (yᴰxᴰ≅Pᴰ .snd .snd Γ Γᴰ .inv)
      (λ p pᴰ → Pᴰ.rectify $ Pᴰ.≡out $
        Pᴰ.⟨⟩⋆⟨ sym $ Pᴰ.reind-filler _ ⟩
        ∙ sym (∫PshHomᴰ (yᴰxᴰ≅Pᴰ .snd .fst) .N-hom _ _ _ _)
        ∙ cong (∫PshHomᴰ (yᴰxᴰ≅Pᴰ .snd .fst) .N-ob _) ((sym $ Cᴰ.reind-filler _) ∙ Cᴰ.⋆IdR _)
        ∙ Pᴰ.≡in (yᴰxᴰ≅Pᴰ .snd .snd Γ Γᴰ .rightInv _ _))
      λ f fᴰ → Cᴰ.rectify $ Cᴰ.≡out $
        cong (invPshIso (∫PshIsoᴰ (yᴰxᴰ≅Pᴰ .snd)) .trans .N-ob _)
          (Pᴰ.⟨⟩⋆⟨ (sym $ Pᴰ.reind-filler _) ⟩ ∙ sym (∫PshHomᴰ (yᴰxᴰ≅Pᴰ .snd .fst) .N-hom _ _ _ _)
          ∙ cong (∫PshHomᴰ (yᴰxᴰ≅Pᴰ .snd .fst) .N-ob _) (sym (Cᴰ.reind-filler _) ∙ Cᴰ.⋆IdR _))
          ∙ (Cᴰ.≡in $ yᴰxᴰ≅Pᴰ .snd .snd Γ Γᴰ .leftInv _ _))

  Representableⱽ→UniversalElementᴰ : (ue : UniversalElement C P)
    → Representableⱽ Cᴰ (ue .vertex) (reindPshᴰNatTrans (yoRec P (ue .element)) Pᴰ)
    → UniversalElementᴰ ue
  Representableⱽ→UniversalElementᴰ ue reprⱽ = Representableᴰ→UniversalElementᴰOverUE ue (reprⱽ .fst , FiberwisePshIsoᴰ→PshIsoᴰ (reprⱽ .snd))

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D} (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  where
  private
    module Cᴰ = Fibers Cᴰ
    module Dᴰ = Fibers Dᴰ
  Functorᴰ→PshHetᴰ : ∀ {x} (xᴰ : Cᴰ.ob[ x ])
    → PshHomⱽ (Cᴰ [-][-, xᴰ ]) (reindPsh (Fᴰ /FᴰYo x) (Dᴰ [-][-, Fᴰ .F-obᴰ xᴰ ]))
  Functorᴰ→PshHetᴰ xᴰ .N-ob (Γ , Γᴰ , f) fᴰ = Fᴰ .F-homᴰ fᴰ
  Functorᴰ→PshHetᴰ xᴰ .N-hom (Δ , Δᴰ , f) (Γ , Γᴰ , f') (γ , γᴰ , γf≡f') f'ᴰ = Dᴰ.rectify $ Dᴰ.≡out $
    cong (∫F Fᴰ .F-hom) (sym $ Cᴰ.reind-filler _)
    ∙ ∫F Fᴰ .F-seq _ _
    ∙ Dᴰ.reind-filler _

  FFFunctorᴰ→PshIsoᴰ : ∀ {x} (xᴰ : Cᴰ.ob[ x ])
    → FullyFaithfulᴰ Fᴰ → PshIsoⱽ (Cᴰ [-][-, xᴰ ]) (reindPsh (Fᴰ /FᴰYo x) (Dᴰ [-][-, Fᴰ .F-obᴰ xᴰ ]))
  FFFunctorᴰ→PshIsoᴰ xᴰ FFFᴰ = pshiso (Functorᴰ→PshHetᴰ xᴰ)
    (λ (Γ , Γᴰ , f) → (FFFᴰ f Γᴰ xᴰ .fst) , FFFᴰ f Γᴰ xᴰ .snd)

  --                Fᴰ / F-hom
  -- Cᴰ / C [-, x ] ---> Dᴰ / D [-, F x ]
  --    |                  |
  --    | Cᴰ / (_⋆ f)      | Dᴰ / (_⋆ F f)
  --    |                  |
  -- Cᴰ / C [-, y ] ---> Dᴰ / D [-, F y ]
  --                Fᴰ / F-hom
  reindexRepresentable-seq : ∀ {x y f}
    → NatIso ((Idᴰ /Fⱽ yoRec (D [-, F-ob F y ]) (F ⟪ f ⟫)) ∘F (Fᴰ /Fᴰ Functor→PshHet F x))
             ((Fᴰ /Fᴰ Functor→PshHet F y) ∘F (Idᴰ /Fⱽ yoRec (C [-, y ]) f))
  reindexRepresentable-seq = /NatIso
    -- TODO: eqToNatIso didn't type check even though it did interactively
    (record { trans = natTrans (λ _ → D .id) (λ _ → idTrans Id .N-hom _) ; nIso = λ _ → idNatIso Id .nIso _ })
    (record { transᴰ = record { N-obᴰ = λ _ → Dᴰ.idᴰ ; N-homᴰ = λ _ → Dᴰ.rectify $ Dᴰ.≡out $ Dᴰ.⋆IdR _ ∙ sym (Dᴰ.⋆IdL _) } ; nIsoᴰ = λ _ → idᴰCatIsoᴰ Dᴰ .snd })
    λ _ → D .⋆IdL _ ∙ F .F-seq _ _

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {x}
  {Pⱽ : Presheafⱽ x Cᴰ ℓPᴰ}{Qⱽ : Presheafⱽ x Cᴰ ℓQᴰ}
  where
  _◁PshIsoⱽ_ : Representableⱽ Cᴰ x Pⱽ → PshIsoⱽ Pⱽ Qⱽ → Representableⱽ Cᴰ x Qⱽ
  (xᴰ , α) ◁PshIsoⱽ β = (xᴰ , (α ⋆PshIso β))
