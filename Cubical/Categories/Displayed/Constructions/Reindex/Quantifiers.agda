{-# OPTIONS --lossy-unification #-}
{-
  The projection reindex Dᴰ G → Dᴰ reflects universal quantifiers if G preserves the projections
-}
module Cubical.Categories.Displayed.Constructions.Reindex.Quantifiers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Limits.Pullback.More
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Presheaf.Morphism.Alt hiding (_∘ˡ_)
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Morphism

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base hiding (_[-][-,_])
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Constructions.Reindex.Base as Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties hiding (isFibrationReindex)
open import Cubical.Categories.Displayed.Constructions.Reindex.UniversalProperties
open import Cubical.Categories.Displayed.Constructions.Reindex.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.UniversalQuantifier
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.NaturalTransformation.Cartesian

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Functor
open PshHom
open PshIso
open NatIso
open NatTrans
open isIso

-- The setup is
--
-- π : F ⇒ C on C
-- π' : F' ⇒ D on D
-- G : C → D
-- swap : GF≅F'G
-- swap ⋆ π' ≡ G ⟪ π ⟫
module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (F : Functor C C)
  ((π , πCart) : CartesianNatTrans F Id) -- pat0
  (F' : Functor D D)
  ((π' , π'Cart) : CartesianNatTrans F' Id) -- pat1
  (G : Functor C D)
  ((swap , swapπ'≡Gπ) : preservesCartNatTrans G (π , πCart) (π' , π'Cart)) -- pat2
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ')
  (cartLifts : isFibration Dᴰ)
  where

  private
    module C = Category C
    module D = Category D
    module Dᴰ = Fibers Dᴰ
    module cartLifts = FibrationNotation Dᴰ cartLifts
    π-Quant : QuantTrans F (reindex Dᴰ G)
    π-Quant = π , (πCart , ((λ x yᴰ → reindexCartesianLift Dᴰ G (π ⟦ x ⟧) yᴰ
                          (cartLifts yᴰ (G ⟅ F ⟅ x ⟆ ⟆) (G ⟪ π ⟦ x ⟧ ⟫)))))
    π'-Quant : QuantTrans F' Dᴰ
    π'-Quant = (π' , (π'Cart , λ x yᴰ → cartLifts yᴰ (F' ⟅ x ⟆) (π' ⟦ x ⟧)))

  opaque
    π'≡swap⁻Gπ : ∀ Δ → π' ⟦ G ⟅ Δ ⟆ ⟧ ≡ swap .nIso Δ .inv D.⋆ G ⟪ π ⟦ Δ ⟧ ⟫
    π'≡swap⁻Gπ Δ = invMoveL {C = D} (isIso→areInv (swap .nIso Δ)) (swapπ'≡Gπ Δ)

  module _ {Γ : C.ob} where
    UniversalQuantifier-commute-lemma : NatIso
      (((Idᴰ /Fⱽ yoRec (D [-, G ⟅ F ⟅ Γ ⟆ ⟆ ]) (swap .nIso Γ .inv))
      ∘F wkF π'-Quant (G ⟅ Γ ⟆))
      ∘F reindex-π-/ Dᴰ G Γ)
      (reindex-π-/ Dᴰ G (F ⟅ Γ ⟆) ∘F wkF π-Quant Γ)
    UniversalQuantifier-commute-lemma =
      (/NatIso (record { trans = natTrans (λ (Δ , _ , _) → symNatIso swap .trans ⟦ Δ ⟧) λ _ → symNatIso swap .trans .N-hom _
                      ; nIso = λ _ → symNatIso swap .nIso _ })
        (record { transᴰ = record { N-obᴰ = λ {(Δ , Δᴰ , _)} _ → cartLifts.sq-filler Dᴰ.idᴰ (D.⋆IdR _ ∙ π'≡swap⁻Gπ Δ) -- todo: use tri-filler
          ; N-homᴰ = λ {(Θ , Θᴰ , _)}{(Δ , Δᴰ , _)}{(δ , δᴰ , _)} _ → Dᴰ.rectify $ Dᴰ.≡out $
            _ , (cartLifts.sq-filler δᴰ _ Dᴰ.⋆ᴰ cartLifts.sq-filler Dᴰ.idᴰ _)
              ≡⟨ cartLifts.sq-collapse _ _
                ∙ cartLifts.cong-introᴰ (symNatIso swap .trans .N-hom δ) (Dᴰ.cong-reind _ _ Dᴰ.⟨⟩⋆⟨ Dᴰ.⋆IdR (_ , δᴰ) ∙ sym (Dᴰ.⋆IdL (_ , δᴰ)) ⟩)
                ∙ sym (cartLifts.sq-collapse _ _) ⟩
            _ , cartLifts.sq-filler Dᴰ.idᴰ _ Dᴰ.⋆ᴰ cartLifts.sq-filler δᴰ (sym $ (G ∘ʳ π) .N-hom δ)
              ≡⟨ Dᴰ.⟨⟩⋆⟨ cartLifts.cong-introᴰ refl (Dᴰ.cong-reind _ _ (Dᴰ.⟨ cartLifts.⟨ Dᴰ.reind-filler _ _ ⟩⋆πⱽ ∙ Dᴰ.reind-filler _ _ ⟩⋆⟨⟩ ∙ Dᴰ.reind-filler _ _ ∙ Dᴰ.reind-filler _ _)) ⟩ ⟩
            _ , (cartLifts.sq-filler _ _ Dᴰ.⋆ᴰ _)
            ∎
          } ; nIsoᴰ =
          λ {(Δ , Δᴰ , γ)} _ →
            isisoᴰ (cartLifts.sq-filler Dᴰ.idᴰ (D.⋆IdR _ ∙ sym (swapπ'≡Gπ Δ)))
            (Dᴰ.rectify $ Dᴰ.≡out $
              _ , (cartLifts.sq-filler _ _ Dᴰ.⋆ᴰ cartLifts.sq-filler _ _) ≡⟨ cartLifts.sq-collapse _ _
                ∙ cartLifts.cong-introᴰ (swap .nIso Δ .ret) (Dᴰ.cong-reind _ (D.⋆IdR _) Dᴰ.⟨⟩⋆⟨ Dᴰ.⋆IdL _ ⟩)
                ∙ cartLifts.sq-id refl ⟩ D.id , Dᴰ.idᴰ ∎)
            (Dᴰ.rectify $ Dᴰ.≡out $
              cartLifts.sq-collapse _ _
              ∙ cartLifts.cong-introᴰ (swap .nIso Δ .sec) (Dᴰ.cong-reind _ (D.⋆IdR _) Dᴰ.⟨⟩⋆⟨ Dᴰ.⋆IdL _ ⟩)
              ∙ cartLifts.sq-id refl) })
        λ (_ , _ , γ) → sym $ symNatIso swap .trans .N-hom γ)

  module _ {Γ : C.ob}(Aᴰ : Dᴰ.ob[ G ⟅ F ⟅ Γ ⟆ ⟆ ])
    (∀Aᴰ : ∀FOb {F = F'}{Cᴰ = Dᴰ} π'-Quant (swap .nIso Γ .inv cartLifts.* Aᴰ))
    where
    reflectsUniversalQuantifiers : ∀FOb π-Quant Aᴰ
    reflectsUniversalQuantifiers .fst = ∀Aᴰ .fst
    reflectsUniversalQuantifiers .snd =
      -- reindex Dᴰ G [-][-, ∀Aᴰ .fst ]
      reindexRepresentableIsoⱽ Dᴰ G Γ (∀Aᴰ .fst)
      -- reindexPsh (G , Id , G-hom) $ Dᴰ [-][-, ∀Aᴰ .fst ]
      -- reindPsh-square
      ⋆PshIsoⱽ reindPshIso (reindex-π-/ Dᴰ G Γ)
        (∀Aᴰ .snd
        ⋆PshIsoⱽ (reindPshIso _ $ cartLifts Aᴰ (F' ⟅ G ⟅ Γ ⟆ ⟆) (swap .nIso Γ .inv) .snd)
        ⋆PshIsoⱽ reindPsh∘F≅ (wkF π'-Quant (G ⟅ Γ ⟆)) (Idᴰ /Fⱽ yoRec (D [-, G ⟅ F ⟅ Γ ⟆ ⟆ ]) (swap .nIso Γ .inv)) (Dᴰ [-][-, Aᴰ ]))
      -- reindexPsh (G , Id , G-hom) $ reindPsh (wkF π'-Quant $ G ⟅ Γ ⟆) $ reindPsh (Id , Id , swap Γ) $ Dᴰ [-][-, Aᴰ ]
      ⋆PshIsoⱽ reindPsh-square
        (reindex-π-/ Dᴰ G Γ) ((Idᴰ /Fⱽ yoRec (D [-, G ⟅ F ⟅ Γ ⟆ ⟆ ]) (swap .nIso Γ .inv)) ∘F wkF π'-Quant (G ⟅ Γ ⟆))
        (wkF π-Quant Γ) (reindex-π-/ Dᴰ G (Functor.F-ob F Γ)) (Dᴰ [-][-, Aᴰ ])
        UniversalQuantifier-commute-lemma
      -- reindPsh (wk G ⟅ Γ ⟆) $ reindPsh (G , Id , G-hom) $ Dᴰ [-][-, Aᴰ ]
      ⋆PshIsoⱽ reindPshIso (wkF π-Quant Γ) (invPshIsoⱽ (reindexRepresentableIsoⱽ Dᴰ G (F ⟅ Γ ⟆) Aᴰ))
      -- reindPsh (wk G ⟅ Γ ⟆) $ reindex Dᴰ G [-][-, Aᴰ ]
