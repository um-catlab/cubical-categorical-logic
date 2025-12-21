{-

-- Let Cᴰ displayed over C.

-- Given an object A : C such that all products Γ × A exist, and π₁ :
-- Γ × A → A is quadrable, and an object Aᴰ over some Γ × A, the
-- universal quantifier ∀ Aᴰ is specified by the universal property
-- that
--
--  Cᴰ [-][-, ∀ Aᴰ ] ≅ reindPsh (wk A) Cᴰ [-][-, Aᴰ ]
--
-- where wk A : (Cᴰ / C [-, Γ ]) → (Cᴰ / C [-, Γ × A ])
-- is the functor defined by wk A (Δ , Δᴰ , γ) = (Δ × A , π₁*Δᴰ , γ × A)

-- For performance reasons, we define this as an instance of the
-- following more general situation:
--
-- Again let Cᴰ displayed over C.
-- Let F be an endofunctor on C with a projection natural transformation π : F ⇒ C such that
-- 1. π is *Cartesian*, i.e. its naturality squares are pullbacks
-- 2. π is *Cᴰ-quadrable* i.e., all cartesian lifts π* Aᴰ exist.
-- Then given some Aᴰ over FΓ, the universal quantifier ∀ Aᴰ is specified by
--  Cᴰ [-][-, ∀ Aᴰ ] ≅ reindPsh wkF Cᴰ [-][-, Aᴰ ]
--
-- where wkF : (Cᴰ / C [-, Γ ]) → (Cᴰ / C [-, F Γ ])
-- is the functor defined by wk (Δ , Δᴰ , γ) = (F Δ , π*Δᴰ , F γ)
-- Note that this weakening functor is itself right adjoint to the projection map
-- (Id / π) : Cᴰ / C [-, F Γ ] → Cᴰ / C [-, Γ ]

-- TODO: This means that the restriction operation
--   wkF* : 𝓟 (Cᴰ / C [-, F Γ ]) → 𝓟 (Cᴰ / C [-, Γ ])
-- is right adjoint to the restriction by projection
--   (Id/π)* : 𝓟 (Cᴰ / C [-, Γ ]) → 𝓟 (Cᴰ / C [-, F Γ ])
--
-- meaning Qᴰ → wkF* Pᴰ ≅ (Id/π)*Qᴰ → Pᴰ
-}

{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.UniversalQuantifier where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Equiv.Dependent.More
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Limits.Pullback.More
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.Cartesian
open import Cubical.Categories.NaturalTransformation.Reind
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functors.More
open import Cubical.Categories.Functors.Constant.More
open import Cubical.Categories.FunctorComprehension.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory as TotalCat hiding (intro)
open import Cubical.Categories.HLevels
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Props
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions hiding (ΣPsh)
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions.RightAdjoint
open import Cubical.Categories.Profunctor.Constructions.Extension
open import Cubical.Categories.Yoneda.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Profunctor.General

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓS ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ ℓSᴰ : Level

open Category
open Functor
open Functorᴰ
open Iso
open NatTrans
open NatIso
open PshHom
open PshIso
open UniversalElement

module _ {C : Category ℓC ℓC'} {F : Functor C C} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (π : NatTrans F Id) where
  -- Weakening is right adjoint to projection
  wkProf : ∀ Γ → Profunctor (Cᴰ / (C [-, Γ ])) (Cᴰ / (C [-, F ⟅ Γ ⟆ ])) (ℓ-max ℓC' (ℓ-max ℓC' ℓCᴰ'))
  wkProf Γ = RightAdjointProf (Idᴰ /Fⱽ yoRec (C [-, Γ ]) (π ⟦ Γ ⟧))

module _ {C : Category ℓC ℓC'} (F : Functor C C) (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  -- A Cᴰ-"quantifiable" natural transformation from F to Id is one that is cartesian and Cᴰ-quadrable
  QuantTrans : Type _
  QuantTrans = Σ[ π ∈ NatTrans F Id ] isCartesian π × (∀ Γ → Quadrable Cᴰ (π ⟦ Γ ⟧))

module _ {C : Category ℓC ℓC'} {F : Functor C C} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  ((π , π-Cart , π*) : QuantTrans F Cᴰ)
  where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module π* {Γ} = QuadrableNotation Cᴰ (π* Γ)

  wkF-ReprIso : ∀ Γ ((Δ , Δᴰ , γ) : ((Cᴰ / (C [-, Γ ])) .ob))
    → PshIso ((Cᴰ / (C [-, F ⟅ Γ ⟆ ])) [-, F ⟅ Δ ⟆ , π* Δ Δᴰ .fst , F ⟪ γ ⟫ ]) (wkProf Cᴰ π Γ ⟅ Δ , Δᴰ , γ ⟆)
  wkF-ReprIso Γ (Δ , Δᴰ , γ) = Isos→PshIso
    (λ (Θ , Θᴰ , γ~) →
      -- Σ[ δ~ ] Cᴰ.Hom[ δ~ ][ Θᴰ , π* Δᴰ ] × δ~⋆F⟪γ⟫≡γ~
      compIso (invIso Σ-assoc-IsoR) $
      compIso
        (IsoOver→Iso
        (isPullback→ΣIso C (CartesianNatTrans→PBSq (π , π-Cart) γ) Θ γ~)
        (isoover
          (λ (δ~ , δ~Fγ≡γ~) → π*._⋆πⱽ)
          (λ (δ , δγ≡γ~π) δᴰ → π*.introᴰ (Cᴰ.reind (pullbackArrowPr₂ C (CartesianNatTrans→PBSq (π , π-Cart) γ) γ~ δ (sym $ δγ≡γ~π)) δᴰ))
          (λ (δ , δγ≡γ~π) δᴰ → Cᴰ.rectify $ Cᴰ.≡out $
            π*.βᴰ _
            ∙ (sym $ Cᴰ.reind-filler _ _) )
          λ (δ~ , δ~Fγ≡γ~) δ~ᴰ → Cᴰ.rectify $ Cᴰ.≡out $
            π*.cong-introᴰ (Pullback.pullbackArrowUnique (CartesianNatTrans→PBSq (π , π-Cart) γ) (sym $ δ~Fγ≡γ~) refl) (sym $ Cᴰ.reind-filler _ _)
            ∙ (sym $ π*.ηᴰ δ~ᴰ))
                 ) $ Σ-assoc-IsoR
      -- Σ[ δ ] Cᴰ.Hom[ δ ][ Θᴰ , Δᴰ ] × δ⋆γ≡γ~⋆π
      )
    λ (H , Hᴰ , γ~') (Θ , Θᴰ , γ~) (θ , θᴰ , θγ~≡γ~') (δ~ , δ~ᴰ , δ~Fγ≡γ~) →
      ΣPathP (C.⋆Assoc θ δ~ _ , ΣPathPProp (λ _ → C.isSetHom _ _)
      (Cᴰ.rectify $ Cᴰ.≡out $ π*.⋆πⱽ-natural))

  wkF-UE : ∀ Γ → UniversalElements (wkProf Cᴰ π Γ)
  wkF-UE Γ (Δ , Δᴰ , γ) = RepresentationPshIso→UniversalElement ((wkProf Cᴰ π Γ) .F-ob (Δ , Δᴰ , γ))
    ((F ⟅ Δ ⟆ , π* Δ Δᴰ .fst , F ⟪ γ ⟫) , wkF-ReprIso Γ (Δ , Δᴰ , γ))

  -- Should use FunctorComprehensionᴰ for this!
  wkF-ugly : ∀ Γ → Functor (Cᴰ / (C [-, Γ ])) (Cᴰ / (C [-, F ⟅ Γ ⟆ ]))
  wkF-ugly Γ = FunctorComprehension (wkProf Cᴰ π Γ) (wkF-UE Γ)

  wkFᴰ-homᴰ : {x y : C.ob} {f : C [ x , y ]} {xᴰ : Cᴰ.ob[ x ]}
    {yᴰ : Cᴰ.ob[ y ]} →
    Cᴰ [ f ][ xᴰ , yᴰ ] →
    Cᴰ [ F .F-hom f ][ π* x xᴰ .fst , π* y yᴰ .fst ]
  wkFᴰ-homᴰ {f = f} fᴰ = cartLift-sq-filler Cᴰ (π* _ _) (π* _ _) fᴰ (sym $ π .N-hom f)
--   opaque
--     wkFᴰ-id : ∀ {x : C.ob}{xᴰ : Cᴰ.ob[ x ]} →
--       Path (Cᴰ.Hom[ _ , _ ])
--         (_ , wkFᴰ-homᴰ Cᴰ.idᴰ)
--         (_ , Cᴰ.idᴰ {p = π* x xᴰ .fst})
--     wkFᴰ-id = π*.cong-introᴰ (F .F-id) (sym (Cᴰ.reind-filler _ _) ∙ Cᴰ.⋆IdR _) ∙ (sym $ π*.ηᴰ _)
--     wkFᴰ-idᴰ : {x : C.ob} {xᴰ : Cᴰ.ob[ x ]} →
--       wkFᴰ-homᴰ Cᴰ.idᴰ Cᴰ.≡[ F .F-id ] Cᴰ.idᴰ {p = π* x xᴰ .fst}
--     wkFᴰ-idᴰ = Cᴰ.rectify $ Cᴰ.≡out $ wkFᴰ-id

--     wkFᴰ-seq : {x y z : C.ob} {f : C [ x , y ]} {g : C [ y , z ]}
--       {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} {zᴰ : Cᴰ.ob[ z ]}
--       (fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]) (gᴰ : Cᴰ [ g ][ yᴰ , zᴰ ]) →
--       Path Cᴰ.Hom[ _ , _ ]
--         (_ , wkFᴰ-homᴰ (fᴰ Cᴰ.⋆ᴰ gᴰ))
--         (_ , wkFᴰ-homᴰ fᴰ Cᴰ.⋆ᴰ wkFᴰ-homᴰ gᴰ)
--     wkFᴰ-seq fᴰ gᴰ =
--       π*.cong-introᴰ (F .F-seq _ _)
--         (sym (Cᴰ.reind-filler _ _)
--         ∙ (sym $
--           π*.⋆πⱽ-natural
--           ∙ Cᴰ.⟨⟩⋆⟨ π*.βᴰ _ ∙ sym (Cᴰ.reind-filler _ _) ∙ refl ⟩
--           ∙ sym (Cᴰ.⋆Assoc _ _ _)
--           ∙ Cᴰ.⟨
--               sym π*.⋆πⱽ-natural
--               ∙ π*.⟨ Cᴰ.⋆IdR _ ⟩⋆πⱽ
--               ∙ π*.βᴰ _
--               ∙ sym (Cᴰ.reind-filler _ _)
--                ⟩⋆⟨⟩
--           ∙ Cᴰ.⋆Assoc _ _ _))
--       ∙ (sym $ π*.ηᴰ _)

--     wkFᴰ-seqᴰ : {x y z : C.ob} {f : C [ x , y ]} {g : C [ y , z ]}
--       {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} {zᴰ : Cᴰ.ob[ z ]}
--       (fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]) (gᴰ : Cᴰ [ g ][ yᴰ , zᴰ ]) →
--       wkFᴰ-homᴰ (fᴰ Cᴰ.⋆ᴰ gᴰ)
--         Cᴰ.≡[ F .F-seq f g ]
--       wkFᴰ-homᴰ fᴰ Cᴰ.⋆ᴰ wkFᴰ-homᴰ gᴰ
--     wkFᴰ-seqᴰ = λ fᴰ gᴰ → Cᴰ.rectify $ Cᴰ.≡out $ wkFᴰ-seq fᴰ gᴰ

  wkFᴰ : Functorᴰ F Cᴰ Cᴰ
  wkFᴰ = record { F-obᴰ = λ {Γ} Γᴰ → π* Γ Γᴰ .fst
    ; F-homᴰ = wkFᴰ-homᴰ
    ; F-idᴰ = λ {x}{xᴰ} → Cᴰ.rectify $ Cᴰ.≡out $ cartLift-sq-id Cᴰ (π* _ _) (F .F-id)
    ; F-seqᴰ = λ {x} {y} {z} {f} {g} {xᴰ} {yᴰ} {zᴰ} fᴰ gᴰ → Cᴰ.rectify $ Cᴰ.≡out $
      cartLift-sq-seq Cᴰ (π* _ xᴰ) (π* _ _) (π* _ _) fᴰ gᴰ (F .F-seq f g)
    }

  wkF : ∀ Γ → Functor (Cᴰ / (C [-, Γ ])) (Cᴰ / (C [-, F ⟅ Γ ⟆ ]))
  wkF Γ = _/Fᴰ_ {F = F} wkFᴰ (Functor→PshHet F Γ) --

  -- TODO: extract this from the universal element formulation of adjunction...
  -- wkF-ε : ∀ {Γ} → NatTrans ((Idᴰ /Fⱽ yoRec (C [-, Γ ]) (π ⟦ Γ ⟧)) ∘F wkF Γ) Id
  -- wkF-ε {Γ} = /NatTrans
  --   (natTrans (λ (Δ , _ , _) → π ⟦ Δ ⟧) (λ _ → π .N-hom _))
  --   (record { N-obᴰ = λ {(Δ , Δᴰ , _)} _ → Cᴰ.reind (C.⋆IdL (N-ob π Δ)) $ π*.πⱽ
  --           ; N-homᴰ = λ _ → Cᴰ.rectify $ Cᴰ.≡out $
  --             Cᴰ.⟨⟩⋆⟨ sym $ Cᴰ.reind-filler _ _ ⟩ ∙ sym π*.⋆πⱽ-natural
  --             ∙ π*.⟨ Cᴰ.⋆IdR _ ⟩⋆πⱽ
  --             ∙ π*.βᴰ _
  --             ∙ (sym $ Cᴰ.reind-filler _ _)
  --             ∙ Cᴰ.⟨ Cᴰ.reind-filler _ _ ⟩⋆⟨⟩
  --           })
  --   (λ (x , _ , γ) → sym $ π .N-hom _)

  opaque
    pb-naturality-lemma : ∀ {Θ Δ Γ : C.ob}
      {δ : C [ Θ , Δ ]}
      {γ~ : C [ Θ , F ⟅ Γ ⟆ ]}
      {γ~' : C [ Δ , F ⟅ Γ ⟆ ]}
      (δγ~'≡γ~ : δ C.⋆ γ~' ≡ γ~)
      → δ C.⋆ π-Cart (γ~' C.⋆ π ⟦ Γ ⟧) γ~' C.id (λ i → C.⋆IdL (γ~' C.⋆ π ⟦ Γ ⟧) (~ i)) .fst .fst
        ≡ π-Cart (γ~ C.⋆ π ⟦ Γ ⟧) γ~ C.id (λ i → C.⋆IdL (γ~ C.⋆ N-ob π Γ) (~ i)) .fst .fst C.⋆ F ⟪ δ ⟫
    pb-naturality-lemma {Θ} {Δ} {Γ} {δ} {γ~} {γ~'} δγ~'≡γ~ =
      pullbackExtensionality C (CartesianNatTrans→PBSq (π , π-Cart) (γ~' C.⋆ (π ⟦ Γ ⟧)))
        (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ sym $ pullbackArrowPr₁ C (CartesianNatTrans→PBSq (π , π-Cart) (γ~' C.⋆ (π ⟦ Γ ⟧))) _ C.id _ ⟩
          ∙ ((δγ~'≡γ~ ∙ pullbackArrowPr₁ C (CartesianNatTrans→PBSq (π , π-Cart) (γ~ C.⋆ (π ⟦ Γ ⟧))) γ~ C.id _)
          ∙ C.⟨ refl ⟩⋆⟨ cong (F .F-hom) (C.⟨ sym δγ~'≡γ~ ⟩⋆⟨ refl ⟩ ∙ C.⋆Assoc _ _ _) ∙ F .F-seq _ _ ⟩) ∙ (sym $ C.⋆Assoc _ _ _))
        (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ sym $ pullbackArrowPr₂ C (CartesianNatTrans→PBSq (π , π-Cart) (γ~' C.⋆ (π ⟦ Γ ⟧))) _ C.id _ ⟩
          ∙ ((C.⋆IdR _ ∙ (sym $ C.⋆IdL δ) ∙ C.⟨ pullbackArrowPr₂ C (CartesianNatTrans→PBSq (π , π-Cart) (γ~ C.⋆ (π ⟦ Γ ⟧))) γ~ C.id _ ⟩⋆⟨ refl ⟩) ∙ C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ sym $ π .N-hom δ ⟩ ) ∙ sym (C.⋆Assoc _ _ _))

  -- wkF-η : ∀ {Γ} → NatTrans Id (wkF Γ ∘F (Idᴰ /Fⱽ yoRec (C [-, Γ ]) (π ⟦ Γ ⟧)))
  -- wkF-η {Γ} = /NatTrans
  --   (natTrans (λ (Δ , _ , γ~) → Pullback.pullbackArrow (CartesianNatTrans→PBSq (π , π-Cart) (γ~ C.⋆ π ⟦ Γ ⟧)) γ~ C.id (sym $ C.⋆IdL _))
  --     λ (_ , _ , δγ~'≡γ~) → pb-naturality-lemma δγ~'≡γ~)
  --   (record
  --     { N-obᴰ = λ {(Δ , Δᴰ , γ~)} _ → π*.introᴰ (Cᴰ.reind (pullbackArrowPr₂ C (CartesianNatTrans→PBSq (π , π-Cart) (γ~ C.⋆ π ⟦ Γ ⟧)) γ~ C.id _) Cᴰ.idᴰ)
  --     ; N-homᴰ = λ {(Θ , Θᴰ , γ~)}{(Δ , Δᴰ , γ~')}{(δ , δᴰ , δγ~'≡γ~)} _ → Cᴰ.rectify $ Cᴰ.≡out $
  --       π*.extensionalityᴰ (pb-naturality-lemma δγ~'≡γ~) (π*.⋆πⱽ-natural
  --         ∙ Cᴰ.⟨⟩⋆⟨ π*.βᴰ _ ∙ (sym $ Cᴰ.reind-filler _ _) ⟩
  --         ∙ Cᴰ.⋆IdR (_ , δᴰ)
  --         ∙ (sym $ π*.⋆πⱽ-natural ∙ Cᴰ.⟨⟩⋆⟨ π*.βᴰ _ ∙ (sym $ Cᴰ.reind-filler _ _) ∙ refl ⟩ ∙ sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ π*.βᴰ' _ ∙ (sym $ Cᴰ.reind-filler _ _) ⟩⋆⟨⟩ ∙ Cᴰ.⋆IdL _)) })
  --   λ (Δ , _ , γ~) → sym $ pullbackArrowPr₁ C (CartesianNatTrans→PBSq (π , π-Cart) (γ~ C.⋆ π ⟦ Γ ⟧)) γ~ C.id _

  ∀FPshⱽ : ∀ {Γ} → Cᴰ.ob[ F ⟅ Γ ⟆ ] → Presheafⱽ Γ Cᴰ ℓCᴰ'
  ∀FPshⱽ Aᴰ = reindPsh (wkF _) (Cᴰ [-][-, Aᴰ ])

  ∀FOb : ∀ {Γ} → Cᴰ.ob[ F ⟅ Γ ⟆ ] → Type _
  ∀FOb {Γ} Aᴰ = Representableⱽ Cᴰ Γ (reindPsh (wkF Γ) (Cᴰ [-][-, Aᴰ ]))

--   -- The Universal property is as follows. What do we need it for?
--   -- It should follow from a general property: reindPsh is a 2-functor and so preserves adjunctions.
--   --
--   -- UniversalQuantifier-UMP : ∀ {Γ} (Aᴰ : Cᴰ.ob[ F ⟅ Γ ⟆ ])
--   --   {Rᴰ : Presheafⱽ Γ Cᴰ ℓRᴰ}
--   --   → Iso (PshHomⱽ Rᴰ (∀Pshⱽ Aᴰ))
--   --         (PshHomⱽ (reindPsh ((Idᴰ /Fⱽ yoRec (C [-, Γ ]) (π ⟦ Γ ⟧))) Rᴰ) (Cᴰ [-][-, Aᴰ ]))
--   -- UniversalQuantifier-UMP = {!!}

-- -- The "ordinary" Universal Quantifier

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  module _ (A : C.ob) (-×A : BinProductsWith C A) where
    private
      module -×A = BinProductsWithNotation -×A

    wkASpec : ∀ Γ → Profunctor (Cᴰ / (C [-, Γ ])) (Cᴰ / (C [-, Γ -×A.×a ])) _
    wkASpec Γ = RightAdjointProf (Idᴰ /Fⱽ yoRec (C [-, Γ ]) -×A.π₁)

    module _ (π* : ∀ Γ → Quadrable Cᴰ (-×A.π₁ {b = Γ})) where
      π₁Quant : QuantTrans -×A.×aF Cᴰ
      π₁Quant = -×A.π₁Nat , (-×A.π₁CartNat .snd) , π*

      wkA : ∀ Γ → Functor (Cᴰ / (C [-, Γ ])) (Cᴰ / (C [-, Γ -×A.×a ]))
      wkA Γ = wkF {F = BinProductWithF C -×A}{Cᴰ = Cᴰ} π₁Quant Γ

      ∀Pshⱽ : ∀ {Γ} → Cᴰ.ob[ Γ -×A.×a ] → Presheafⱽ Γ Cᴰ _
      ∀Pshⱽ {Γ = Γ} Aᴰ = reindPsh (wkA Γ) (Cᴰ [-][-, Aᴰ ])

      UniversalQuantifier : ∀ {Γ} → Cᴰ.ob[ Γ -×A.×a ] → Type _
      UniversalQuantifier = ∀FOb π₁Quant

  module _ (bp : BinProducts C) (isFib : isFibration Cᴰ) where
    private
      module bp = BinProductsNotation bp
    UniversalQuantifiers : Type _
    UniversalQuantifiers = ∀ {Γ A} (Aᴰ : Cᴰ.ob[ Γ bp.× A ])
      → UniversalQuantifier A (λ c → bp (c , A))
          (λ Δ yᴰ → isFib yᴰ (Δ bp.× A) bp.π₁) Aᴰ
