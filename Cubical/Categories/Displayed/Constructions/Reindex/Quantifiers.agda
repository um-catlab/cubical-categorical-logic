{-# OPTIONS --lossy-unification #-}
{-
  The projection reindex Dᴰ G → Dᴰ reflects universal quantifiers if G preserves the projections
-}
module Cubical.Categories.Displayed.Constructions.Reindex.Quantifiers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Presheaf.Morphism.Alt
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

  module _ {Γ : C.ob} where
    --
    UniversalQuantifier-commute-mate : NatIso
      (reindex-π-/ Dᴰ G Γ ∘F ((Idᴰ /Fⱽ yoRec (C [-, Γ ]) (π ⟦ Γ ⟧))))
      (((Idᴰ /Fⱽ yoRec (D [-, G ⟅ Γ ⟆ ]) (π' ⟦ G ⟅ Γ ⟆ ⟧)))
      ∘F (Idᴰ /Fⱽ yoRec (D [-, F' ⟅ G ⟅ Γ ⟆ ⟆ ]) (swap .trans ⟦ Γ ⟧))
      ∘F (reindex-π-/ Dᴰ G (F ⟅ Γ ⟆)))
    UniversalQuantifier-commute-mate = /NatIso
      (record { trans = natTrans (λ _ → D.id) (λ _ → idTrans G .N-hom _)
              ; nIso = λ _ → idNatIso G .nIso _ })
      (record { transᴰ = record { N-obᴰ = λ _ → Dᴰ.idᴰ ; N-homᴰ = λ _ → Dᴰ.rectify $ Dᴰ.≡out $ Dᴰ.⋆IdR _ ∙ sym (Dᴰ.⋆IdL _) }
        ; nIsoᴰ = λ xᴰ → isisoᴰ Dᴰ.idᴰ (Dᴰ.⋆IdLᴰ _) (Dᴰ.⋆IdLᴰ _) })
      -- G ⟪ γ ⟫ ⋆ swap ⋆ π' ≡ G ⟪ γ ⋆ π ⟫
      λ (x , xᴰ , γ) → D.⋆IdL _ ∙ D.⋆Assoc _ _ _ ∙ D.⟨ refl ⟩⋆⟨ swapπ'≡Gπ Γ ⟩ ∙ (sym $ G .F-seq _ _ )

    UniversalQuantifier-commute-lemma' : NatIso
      -- (F' , π'* , F') ∘F (G , Id , G)
      ((wkF π'-Quant (G ⟅ Γ ⟆)) ∘F reindex-π-/ Dᴰ G Γ)
      -- ≅ (Id , Id , swap Γ) ∘F (G , Id , G)  ∘F (F , π* , F)
      (((Idᴰ /Fⱽ yoRec (D [-, F' ⟅ G ⟅ Γ ⟆ ⟆ ]) (swap .trans ⟦ Γ ⟧)) ∘F reindex-π-/ Dᴰ G (F ⟅ Γ ⟆)) ∘F wkF π-Quant Γ)
    UniversalQuantifier-commute-lemma' = symNatIso
      (record { trans =
        improveNatTrans (Mate {!!} (symNatIso UniversalQuantifier-commute-mate .trans) {!!})
          {!!}
      ; nIso = {!!} })
      -- record { trans = Mate {!!} {!UniversalQuantifier-commute-mate!} {!!}
      -- ; nIso = {!!} }
    --   -- F' ∘ G ≅ G ∘ F
    --   (record { trans = natTrans (λ _ → symNatIso swap .trans .N-ob _)
    --                              (λ _ → symNatIso swap .trans .N-hom _)
    --           ; nIso = λ _ → symNatIso swap .nIso _ })
    --   (record { transᴰ = record { N-obᴰ = λ {(Δ , Δᴰ , _)} _ → {!!} ; N-homᴰ = {!!} } ; nIsoᴰ = {!!} })
    --   -- swap ⋆ G γ ⋆ π' ≡ F' (G γ)
    --   λ (Δ , _ , γ) → (sym $ D.⋆Assoc _ _ _)
    --     ∙ D.⟨ sym $ symNatIso swap .trans .N-hom _ ⟩⋆⟨ refl ⟩
    --     ∙ D.⋆Assoc _ _ _ ∙ D.⟨ refl ⟩⋆⟨ swap .nIso Γ .sec ⟩ ∙ D.⋆IdR _

    UniversalQuantifier-commute-lemma : NatIso
      (((Idᴰ /Fⱽ yoRec (D [-, G ⟅ F ⟅ Γ ⟆ ⟆ ]) (swap .nIso Γ .inv))
      ∘F wkF π'-Quant (G ⟅ Γ ⟆))
      ∘F reindex-π-/ Dᴰ G Γ)
      (reindex-π-/ Dᴰ G (F ⟅ Γ ⟆) ∘F wkF π-Quant Γ)
    UniversalQuantifier-commute-lemma =
      improveNatIso
        (symNatIso (CAT⋆Assoc _ _ _) ⋆NatIso symNatIso (retrMovePost
          -- ez just need a lemma here
          {!!}
          (CAT⋆Assoc _ _ _ ⋆NatIso symNatIso UniversalQuantifier-commute-lemma')))
        {!!}
        {!!}
      -- improveNatIso
      --   -- ((Id , Id , swap⁻) ∘F wk (G Γ)) ∘F (G , Id , G)
      --   (symNatIso $
      --     retrMovePost
      --      {H = Idᴰ /Fⱽ yoRec (D [-, (F' ∘F G) ⟅ Γ ⟆ ]) (swap .trans ⟦ Γ ⟧)}
      --      {!!}
      --      (symNatIso $ UniversalQuantifier-commute-lemma')
      --     ⋆NatIso CAT⋆Assoc _ _ _)
      --   -- (symNatIso $ (CAT⋆Assoc _ _ _)
      --   -- -- (Id , Id , swap⁻) ∘F (wk (G Γ) ∘F (G , Id , G))
      --   -- ⋆NatIso symNatIso (retrMovePost {H = Idᴰ /Fⱽ yoRec (D [-, (F' ∘F G) ⟅ Γ ⟆ ]) (swap .trans ⟦ Γ ⟧)} {!!} (symNatIso $ UniversalQuantifier-commute-lemma')))
      --   -- ((Id , Id , swap⁻) ∘F wk (G Γ)) ∘F (G , Id , G)
      --   {!!}
      --   {!!}
  --   UniversalQuantifier-commute-lemma = /NatIso
  --     -- F' ∘ G ≅ G ∘ F
  --     (record { trans = natTrans (λ _ → symNatIso swap .trans .N-ob _)
  --                                (λ _ → symNatIso swap .trans .N-hom _)
  --             ; nIso = λ _ → symNatIso swap .nIso _ })
  --     (record { transᴰ = record { N-obᴰ = λ {(Δ , Δᴰ , _)} _ →
  --         cartLifts.tri-filler (invMoveL {C = D} (isIso→areInv (swap .nIso _)) (swapπ'≡Gπ Δ))
  --       ; N-homᴰ = λ {(Θ , Θᴰ , _)}{(Δ , Δᴰ , _)}{(δ , δᴰ , _)} _ →
  --         Dᴰ.rectify $ Dᴰ.≡out $
  --           (_ , cartLifts.sq-filler δᴰ _ Dᴰ.⋆ᴰ cartLifts.tri-filler _
  --             ≡⟨ {!!} ⟩
  --           _ , cartLifts.tri-filler _ Dᴰ.⋆ᴰ cartLifts.sq-filler δᴰ (sym (G .F-seq _ _) ∙ cong (G .F-hom) (sym $ π .N-hom _) ∙ (G .F-seq _ _))
  --             ≡⟨ Dᴰ.⟨⟩⋆⟨ cartLifts.cong-introᴰ refl (Dᴰ.cong-reind _ _ (Dᴰ.⟨ cartLifts.⟨ Dᴰ.reind-filler _ _ ⟩⋆πⱽ ∙ Dᴰ.reind-filler _ _ ⟩⋆⟨⟩ ∙ Dᴰ.reind-filler _ _ ∙ Dᴰ.reind-filler _ _)) ⟩ ⟩
  --           _ , cartLifts.tri-filler _ Dᴰ.⋆ᴰ _
  --           ∎)
  --           -- Dᴰ.⟨⟩⋆⟨ cartLifts.tri-filler≡sq-filler ⟩
  --           -- ∙ cartLifts.sq-collapse δᴰ Dᴰ.idᴰ
  --           -- ∙ {!!}
  --           -- ∙ {!!} --
  --           --     -- {!!} -- (cartLifts Θᴰ (F' ⟅ G ⟅ Θ ⟆ ⟆) (π' ⟦ G ⟅ Θ ⟆ ⟧))
  --           --     -- {!!} -- (cartLifts Θᴰ (G ⟅ F ⟅ Θ ⟆ ⟆) (G ⟪ π ⟦ Θ ⟧ ⟫))
  --           --     -- {!cartLifts ? ? ?!}
  --           --     -- {!!}
  --           --     -- {!!})
  --           -- ∙ Dᴰ.⟨ sym $ cartLifts.tri-filler≡sq-filler ⟩⋆⟨⟩

  --                                 -- Dᴰ.rectify $ Dᴰ.≡out $
  --                                 -- -- cartLifts.introᴰ (Dᴰ.reind _ ?) ⋆ᴰ cartLifts.introᴰ (Dᴰ.reind _ ?)
  --                                 -- {!!}
  --                                 -- cartLifts.extensionalityᴰ (symNatIso swap .trans .N-hom _)
  --                                 --   (cartLifts.⋆πⱽ-natural
  --                                 --   ∙ Dᴰ.⟨⟩⋆⟨ cartLifts.βᴰ _ ∙ sym (Dᴰ.reind-filler _ _) ∙ sym (Dᴰ.reind-filler _ _) ⟩
  --                                 --   ∙ {!!})
  --                               }
  --             ; nIsoᴰ = λ {(Δ , Δᴰ , _)} _ → isisoᴰ (cartLifts.tri-filler (sym $ swapπ'≡Gπ Δ))
  --               (Dᴰ.rectify $ Dᴰ.≡out $ {!!})
  --               (Dᴰ.rectify $ Dᴰ.≡out $ {!!}) })
  --     -- swap ⋆ G γ ⋆ π' ≡ F' (G γ)
  --     λ (Δ , _ , γ) → sym $ symNatIso swap .trans .N-hom _

  -- module _ {Γ : C.ob}(Aᴰ : Dᴰ.ob[ G ⟅ F ⟅ Γ ⟆ ⟆ ])
  --   (∀Aᴰ : ∀FOb {F = F'}{Cᴰ = Dᴰ} π'-Quant (swap .nIso Γ .inv cartLifts.* Aᴰ))
  --   where
  --   reflectsUniversalQuantifiers : ∀FOb π-Quant Aᴰ
  --   reflectsUniversalQuantifiers .fst = ∀Aᴰ .fst
  --   reflectsUniversalQuantifiers .snd =
  --     -- reindex Dᴰ G [-][-, ∀Aᴰ .fst ]
  --     reindexRepresentableIsoⱽ Dᴰ G Γ (∀Aᴰ .fst)
  --     -- reindexPsh (G , Id , G-hom) $ Dᴰ [-][-, ∀Aᴰ .fst ]

  --     -- reindPsh-square
  --     ⋆PshIsoⱽ reindPshIso (reindex-π-/ Dᴰ G Γ)
  --       (∀Aᴰ .snd
  --       ⋆PshIsoⱽ (reindPshIso _ $ cartLifts Aᴰ (F' ⟅ G ⟅ Γ ⟆ ⟆) (swap .nIso Γ .inv) .snd)
  --       ⋆PshIsoⱽ reindPsh∘F≅ (wkF π'-Quant (G ⟅ Γ ⟆)) (Idᴰ /Fⱽ yoRec (D [-, G ⟅ F ⟅ Γ ⟆ ⟆ ]) (swap .nIso Γ .inv)) (Dᴰ [-][-, Aᴰ ]))
  --     -- reindexPsh (G , Id , G-hom) $ reindPsh (wkF π'-Quant $ G ⟅ Γ ⟆) $ reindPsh (Id , Id , swap Γ) $ Dᴰ [-][-, Aᴰ ]
  --     ⋆PshIsoⱽ reindPsh-square
  --       (reindex-π-/ Dᴰ G Γ) ((Idᴰ /Fⱽ yoRec (D [-, G ⟅ F ⟅ Γ ⟆ ⟆ ]) (swap .nIso Γ .inv)) ∘F wkF π'-Quant (G ⟅ Γ ⟆))
  --       (wkF π-Quant Γ) (reindex-π-/ Dᴰ G (Functor.F-ob F Γ)) (Dᴰ [-][-, Aᴰ ])
  --       UniversalQuantifier-commute-lemma
  --     -- reindPsh (wk G ⟅ Γ ⟆) $ reindPsh (G , Id , G-hom) $ Dᴰ [-][-, Aᴰ ]
  --     ⋆PshIsoⱽ reindPshIso (wkF π-Quant Γ) (invPshIsoⱽ (reindexRepresentableIsoⱽ Dᴰ G (F ⟅ Γ ⟆) Aᴰ))
  --     -- reindPsh (wk G ⟅ Γ ⟆) $ reindex Dᴰ G [-][-, Aᴰ ]
