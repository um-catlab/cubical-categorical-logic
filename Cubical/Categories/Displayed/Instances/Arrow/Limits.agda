{-# OPTIONS --lossy-unification #-}
{-
  Displayed categorical structure on Iso D over D × D.

  The category Iso D (from Arrow/Base.agda) has displayed terminal,
  products, initial, and coproducts. These are purely D-internal
  constructions independent of any functors F, G.

  Also provides IsoComma constructions: given functors F, G : C → D,
  the IsoComma displayed category (reindexing of Iso D along F × G)
  inherits these limits.
-}
module Cubical.Categories.Displayed.Instances.Arrow.Limits where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Isomorphism hiding (Iso)
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Category.More
open import Cubical.Categories.Functor
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Morphism
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Limits.Terminal as Term
open import Cubical.Categories.Limits.Terminal.More as Term
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Exponentials.Small
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Constructions.BinProduct.LocalRepresentability
open import Cubical.Categories.Profunctor.General

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Constructions.Comma
open import Cubical.Categories.Displayed.Constructions.Weaken
open import Cubical.Categories.Displayed.Constructions.Reindex.Base as Reindex
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.Displayed.Constructions.Reindex.Cartesian
open import Cubical.Categories.Displayed.Instances.Arrow.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Limits.CartesianV'
import Cubical.Categories.Displayed.Limits.BinProduct.Base as BP
import Cubical.Categories.Displayed.Limits.Terminal as Termᴰ
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Exponential
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialV->D
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialD
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Constructions.Reindex.UniversalProperties

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open Functor
open isIso
open isIsoOver
open UniversalElement

module _ (D : Category ℓD ℓD') where
  private
    module D = Category D

  module _ (term : Terminal' D) where
    private
      module ⊤D = TerminalNotation term

    -- TODO should probably have and use ∫ue for UniversalElementᴰ for uncurried presheaves
    term×term : Terminal' (∫C (weaken D D))
    term×term = Termᴰ.TerminalᴰNotation.∫term (weaken D D) (termWeaken term term)

    Iso∫wkTerminalᴰ : Terminalᴰ (Iso∫wk D) term×term
    Iso∫wkTerminalᴰ .fst = D.id , isiso D.id (D.⋆IdL D.id) (D.⋆IdL D.id)
    Iso∫wkTerminalᴰ .snd .fst = tt
    Iso∫wkTerminalᴰ .snd .snd Γ Γᴰ .inv _ _ .fst = ⊤D.𝟙extensionality
    Iso∫wkTerminalᴰ .snd .snd Γ Γᴰ .inv _ _ .snd = tt
    Iso∫wkTerminalᴰ .snd .snd Γ Γᴰ .rightInv = λ _ _ → refl
    Iso∫wkTerminalᴰ .snd .snd Γ Γᴰ .leftInv u v =
      isProp→PathP (λ _ → isPropΣ (D.isSetHom _ _) λ _ → isPropUnit) _ _

  module _ (bp : BinProducts D) where
    private
      module bp = BinProductsNotation bp
    module _ {a b c d : D.ob} (f : CatIso D a c) (g : CatIso D b d) where
      private
        module -×b = BinProductsWithNotation (BinProducts→BinProductsWith D b bp)
        module c×- = BinProductsWithNotation
          (BinProducts→BinProductsWith D c (λ (x , y) → SwapBinProduct D (bp (y , x))))
      -- TODO move to BinProducts.More
      ×Iso : CatIso D (a bp.× b) (c bp.× d)
      ×Iso = preserveIsosF {F = -×b.×aF} f
             ⋆CatIso preserveIsosF {F = c×-.×aF} g

    Iso∫wkBinProductsᴰ : BinProductsᴰ (Iso∫wk D) (bp×bp bp bp)
    Iso∫wkBinProductsᴰ {A = (a , c)}{B = (b , d)} f g =
      ×Iso f g ,
      ((sym c×b.×β₁
        ∙ D.⟨ refl ⟩⋆⟨ sym c×d.×β₁ ⟩
        ∙ sym (D.⋆Assoc _ _ _) , _) ,
       (D.⟨ sym c×b.×β₂ ⟩⋆⟨ refl ⟩
       ∙ D.⋆Assoc _ _ _
        ∙ D.⟨ refl ⟩⋆⟨ sym c×d.×β₂ ⟩
        ∙ sym (D.⋆Assoc _ _ _) , _)) ,
      isUniv
      where

      module a×b = BinProductNotation (bp (a , b))
      module c×d = BinProductNotation (bp (c , d))
      module c×b = BinProductNotation (bp (c , b))

      isUniv : isUniversalᴰ (Iso∫wk D) _ _ (bp×bp bp bp _) _
      isUniv Γ Γᴰ .inv _ ((sq₁ , _) , (sq₂ , _)) .fst =
        c×d.,p-extensionality
          (D.⋆Assoc _ _ _
          ∙ D.⟨ refl ⟩⋆⟨ D.⋆Assoc _ _ _ ∙ D.⟨ refl ⟩⋆⟨ c×d.×β₁ ⟩ ∙ c×b.×β₁ ⟩
          ∙ sym (D.⋆Assoc _ _ _)
          ∙ D.⟨ a×b.×β₁ ⟩⋆⟨ refl ⟩
          ∙ sq₁
          ∙ D.⟨ refl ⟩⋆⟨ sym c×d.×β₁ ⟩
          ∙ sym (D.⋆Assoc _ _ _))
          (D.⋆Assoc _ _ _
          ∙ D.⟨ refl ⟩⋆⟨ D.⋆Assoc _ _ _ ∙ D.⟨ refl ⟩⋆⟨ c×d.×β₂ ⟩
              ∙ sym (D.⋆Assoc _ _ _) ∙ D.⟨ c×b.×β₂ ⟩⋆⟨ refl ⟩ ⟩
          ∙ sym (D.⋆Assoc _ _ _)
          ∙ D.⟨ a×b.×β₂ ⟩⋆⟨ refl ⟩
          ∙ sq₂
          ∙ D.⟨ refl ⟩⋆⟨ sym c×d.×β₂ ⟩
          ∙ sym (D.⋆Assoc _ _ _))
      isUniv Γ Γᴰ .inv _ _ .snd = tt
      isUniv Γ Γᴰ .rightInv _ _ =
        isProp→PathP (λ _ → isProp×
          (isPropΣ (D.isSetHom _ _) λ _ → isPropUnit)
          (isPropΣ (D.isSetHom _ _) λ _ → isPropUnit)) _ _
      isUniv Γ Γᴰ .leftInv _ _ =
        isProp→PathP (λ _ → isPropΣ (D.isSetHom _ _) λ _ → isPropUnit) _ _

    module _ (exp : AllExponentiable D bp) where
      private
        module exp = ExponentialsNotation bp exp
      module _ {a b c d : D.ob} (f : CatIso D a c) (g : CatIso D b d) where
        private
          module a⇒b = ExponentialNotation (λ d₁ → bp (d₁ , a)) (exp a b)
          module c⇒d = ExponentialNotation (λ d₁ → bp (d₁ , c)) (exp c d)

        -- TODO move this into the Exponentials.Small
        ExpProf : D.ob → Profunctor D D _
        ExpProf x .F-ob d = (D [-, d ]) ∘F (LRPsh→Functor ((D [-, x ]) , (λ d₁ → bp (d₁ , x))) ^opF)
        ExpProf x .F-hom f = natTrans (λ x₁ z → z D.⋆ f) λ _ → funExt λ _ → D.⋆Assoc _ _ _
        ExpProf x .F-id = makeNatTransPath (funExt₂ λ _ _ → D.⋆IdR _)
        ExpProf x .F-seq _ _ = makeNatTransPath (funExt₂ λ _ _ → sym $ D.⋆Assoc _ _ _)

        ⇒F : D.ob → Functor D D
        ⇒F x = FunctorComprehension (ExpProf x) (exp x)

        ⇒Iso : CatIso D (a exp.⇒ b) (c exp.⇒ d)
        ⇒Iso = preserveIsosF {F = ⇒F a} g ⋆CatIso a⇒d≅c⇒d
          where

          p : ∀ {x} →
            bp.×F ⟪ D.id {x = x} , f .snd .inv ⟫ D.⋆ bp.×F ⟪ D.id , f .fst ⟫ ≡ D.id
          p = (sym $ bp.×F .F-seq _ _)
              ∙ cong (bp.×F .F-hom) (ΣPathP ((D.⋆IdL _) , (f .snd .sec)))
              ∙ bp.×F .F-id

          q : ∀ {x} →
            bp.×F ⟪ D.id {x = x} , f .fst ⟫ D.⋆ bp.×F ⟪ D.id , f .snd .inv ⟫ ≡ D.id
          q = (sym $ bp.×F .F-seq _ _)
              ∙ cong (bp.×F .F-hom) (ΣPathP ((D.⋆IdL _) , (f .snd .ret)))
              ∙ bp.×F .F-id

          a⇒F≅c⇒F : NatIso (⇒F a) (⇒F c)
          a⇒F≅c⇒F = FunctorComprehension-NatIso (ExpProf a) (ExpProf c) (exp a) (exp c)
                      (Isos→PshIso (λ _ → iso (λ x → bp.×F ⟪ D.id , f .snd .inv ⟫ D.⋆ x)
                                              (λ x → bp.×F ⟪ D.id , f .fst ⟫ D.⋆ x)
                                              (λ x → sym (D.⋆Assoc _ _ _)
                                                     ∙ D.⟨ p ⟩⋆⟨ refl ⟩
                                                     ∙ D.⋆IdL _)
                                              (λ x → sym (D.⋆Assoc _ _ _)
                                                     ∙ D.⟨ q ⟩⋆⟨ refl ⟩
                                                     ∙ D.⋆IdL _))
                                   (λ x y g p →
                                     (sym $ D.⋆Assoc _ _ _)
                                      ∙ D.⟨ (sym $ D.⋆Assoc _ _ _)
                                            ∙ D.⟨ bp.,p-extensionality
                                                    (D.⋆Assoc _ _ _
                                                    ∙ D.⟨ refl ⟩⋆⟨ bp.×β₁ ⟩
                                                    ∙ sym (D.⋆Assoc _ _ _)
                                                    ∙ D.⟨ bp.×β₁ ∙ D.⋆IdR _ ⟩⋆⟨ refl ⟩
                                                    ∙ sym bp.×β₁
                                                    ∙ D.⟨ refl ⟩⋆⟨ (sym $ D.⋆IdR _)
                                                                   ∙ sym bp.×β₁ ⟩
                                                    ∙ (sym $ D.⋆Assoc _ _ _))
                                                    (D.⋆Assoc _ _ _
                                                    ∙ D.⟨ refl ⟩⋆⟨ bp.×β₂ ⟩
                                                    ∙ bp.×β₂
                                                    ∙ D.⟨ sym bp.×β₂ ⟩⋆⟨ refl ⟩
                                                    ∙ D.⋆Assoc _ _ _
                                                    ∙ D.⟨ refl ⟩⋆⟨ sym bp.×β₂ ⟩
                                                    ∙ (sym $ D.⋆Assoc _ _ _))
                                                ⟩⋆⟨ refl ⟩
                                            ∙ D.⋆Assoc _ _ _ ⟩⋆⟨ refl ⟩))

          a⇒d≅c⇒d : CatIso D (a exp.⇒ d) (c exp.⇒ d)
          a⇒d≅c⇒d = _ , (a⇒F≅c⇒F .NatIso.nIso d)

      -- Iso∫wkExponentialsᴰ : AllExponentiableᴰ (Iso∫wk D) (bp×bp bp bp)
      --   Iso∫wkBinProductsᴰ (exp×exp bp bp exp exp)
      -- Iso∫wkExponentialsᴰ {A = (a , b)} f {B = (c , d)} g =
      --   ⇒Iso f g ,
      --   (? , tt) ,
      --   isUniv
      --   where

      --   isUniv : isUniversalᴰ (Iso∫wk D) _ _ (exp×exp bp bp exp exp _ _) _
      --   isUniv Γ Γᴰ .inv _ (pᴰ , _) .fst = {!1!}
      --   isUniv Γ Γᴰ .inv _ _ .snd = tt
      --   isUniv Γ Γᴰ .rightInv _ _ =
      --     isProp→PathP (λ _ → isPropΣ (D.isSetHom _ _) λ _ → isPropUnit) _ _
      --   isUniv Γ Γᴰ .leftInv _ _ =
      --     isProp→PathP (λ _ → isPropΣ (D.isSetHom _ _) λ _ → isPropUnit) _ _

-- module IsoCommaStructure {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
--   (F G : Functor C D) where
--   private
--     module D = Category D
--     module C = Category C
--     FG : Functor C (∫C (weaken D D))
--     FG = ×→∫wk ∘F (F ,F G)

--   IsoCommaᴰΔ : Categoryᴰ C ℓD' ℓD'
--   IsoCommaᴰΔ = Reindex.reindex (Iso∫wk D) FG

--   sectionToNatIso : GlobalSection IsoCommaᴰΔ → F ≅ᶜ G
--   sectionToNatIso s = record
--     { trans = natTrans (λ c → sect.F-obᴰ c .fst)
--                        (λ f → sect.F-homᴰ f .fst)
--     ; nIso = λ c → sect.F-obᴰ c .snd
--     }
--     where module sect = Section (GlobalSectionReindex→Section _ _ s)

--   module _ (termC : Terminal' C)
--            (F-1 : Term.preservesTerminal C D F)
--            (G-1 : Term.preservesTerminal C D G) where

--     private
--       FG-1 : Term.preservesTerminal C (∫C (weaken D D)) FG
--       FG-1 = {!!}

--     -- reindex-reflects-UMPᴰ doesn't work directly
--     -- need to think onwhat lemma wouldbe needed
--     IsoCommaTerminalᴰ : Terminalᴰ IsoCommaᴰΔ termC
--     IsoCommaTerminalᴰ =
--       reindex-reflects-UMPᴰ {!!} {!!} {!!} {!!} {!!} {!!} {!!}
--       -- (pshhom (λ _ _ → _) (λ _ _ _ _ → refl))
--       -- (Iso∫wk D) termC
--       -- (λ _ → isoToIsEquiv (iso (λ _ → tt)
--       --                     (λ _ → F-1 (Terminal'ToTerminal termC) _ .fst ,
--       --                            G-1 (Terminal'ToTerminal termC) _ .fst)
--       --                     (λ _ → refl)
--       --                     (λ a → ΣPathP
--       --                       ((F-1 (vertex termC ,
--       --                          Terminal'ToTerminal termC .snd) _ .snd (a .fst)) ,
--       --                        (G-1 (vertex termC ,
--       --                          Terminal'ToTerminal termC .snd) _ .snd (a .snd))))))
--       {!!} {!Iso∫wkTerminalᴰ ? ? !}

--   -- module _ (bpC : BinProducts C)
--   --          (F-bp : preservesProvidedBinProducts F bpC)
--   --          (G-bp : preservesProvidedBinProducts G bpC) where
--   --   IsoCommaBinProductsᴰ : BinProductsᴰ IsoCommaᴰΔ bpC
--   --   IsoCommaBinProductsᴰ = {!!}

--   -- module _ (initC : Initial' C)
--   --          (F-0 : isTerminal (D ^op) (F .F-ob (initC .vertex)))
--   --          (G-0 : isTerminal (D ^op) (G .F-ob (initC .vertex))) where
--   --   IsoCommaInitialᴰ : Initialᴰ IsoCommaᴰΔ initC
--   --   IsoCommaInitialᴰ = {!!}

--   -- module _ (bcpC : BinCoProducts C)
--   --          (F-cp : preservesProvidedBinProducts (Functor→Functorᴼᵖ F) bcpC)
--   --          (G-cp : preservesProvidedBinProducts (Functor→Functorᴼᵖ G) bcpC) where
--   --   IsoCommaBinCoProductsᴰ : BinCoProductsᴰ IsoCommaᴰΔ bcpC
--   --   IsoCommaBinCoProductsᴰ = {!!}
