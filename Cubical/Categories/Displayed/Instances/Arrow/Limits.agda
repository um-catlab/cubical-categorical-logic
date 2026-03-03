{-# OPTIONS --lossy-unification #-}
{-
  Displayed categorical structure on Iso D over D × D.

  The category Iso D (from Arrow/Base.agda) has displayed terminal,
  products, initial, and coproducts if D does.

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

    term×term : Terminal' (∫C (weaken D D))
    term×term = Termᴰ.TerminalᴰNotation.∫term (weaken D D) (termWeaken term term)

  module _ (∫wkterm : Terminal' (∫C (weaken D D))) where
    private
      module ∫wk⊤ = TerminalNotation ∫wkterm
    Iso∫wkTerminalᴰ : Terminalᴰ (Iso∫wk D) ∫wkterm
    Iso∫wkTerminalᴰ .fst =
      ∫wk⊤.!t {a = ∫wk⊤.𝟙 .snd , ∫wk⊤.𝟙 .fst} .snd ,
      isiso (∫wk⊤.!t {a = ∫wk⊤.𝟙 .snd , ∫wk⊤.𝟙 .fst} .fst)
        (cong {x = D.id , ∫wk⊤.!t .fst D.⋆ ∫wk⊤.!t .snd}
              {y = D.id , D.id}
              snd (∫wk⊤.𝟙extensionality  {a = ∫wk⊤.𝟙}))
        (cong {x = ∫wk⊤.!t .snd D.⋆ ∫wk⊤.!t .fst , D.id}
              {y = D.id , D.id}
              fst (∫wk⊤.𝟙extensionality  {a = ∫wk⊤.𝟙}))
    Iso∫wkTerminalᴰ .snd .fst = tt
    Iso∫wkTerminalᴰ .snd .snd Γ Γᴰ .inv _ _ .fst =
      cong {x = D.id , _} {y = D.id , _} snd ∫wk⊤.𝟙extensionality
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

module _ (D : Category ℓD ℓD') where
  private
    module D = Category D
  module _ (bcp : BinCoProducts D) where
    private
      module bcp = BinCoProductsNotation bcp

    bcp×bcp' : BinProducts (∫C (weaken (D ^op) (D ^op)))
    bcp×bcp' = bp×bp bcp bcp

    bcp×bcp : BinCoProducts (∫C (weaken D D))
    bcp×bcp x .vertex = bcp×bcp' x .vertex
    bcp×bcp x .element = bcp×bcp' x .element
    bcp×bcp x .universal = bcp×bcp' x .universal

    Iso∫wkBinCoProductsᴰ' : BinProductsᴰ (Iso∫wk (D ^op)) bcp×bcp'
    Iso∫wkBinCoProductsᴰ' = Iso∫wkBinProductsᴰ (D ^op) bcp

    Iso∫wkBinCoProductsᴰ : BinCoProductsᴰ (Iso∫wk D) bcp×bcp
    Iso∫wkBinCoProductsᴰ x y =
      (isobcpᴰ .fst .fst , isiso (isobcpᴰ .fst .snd .inv)
                                 (isobcpᴰ .fst .snd .ret)
                                 (isobcpᴰ .fst .snd .sec)) ,
      (((sym $ isobcpᴰ .snd .fst .fst .fst) , _) ,
       ((sym $ isobcpᴰ .snd .fst .snd .fst) , _)) ,
      isUniv
      where
      isobcpᴰ =
        Iso∫wkBinCoProductsᴰ'
          (x .fst , isiso (x .snd .inv) (x .snd .ret) (x .snd .sec))
          (y .fst , isiso (y .snd .inv) (y .snd .ret) (y .snd .sec))
      isUniv : _
      isUniv Γ Γᴰ .inv a ((sq₁ , _) , (sq₂ , _)) .fst =
        sym $ isobcpᴰ .snd .snd (Γ .snd , Γ .fst)
          (Γᴰ .fst , isiso (Γᴰ .snd .inv) (Γᴰ .snd .ret) (Γᴰ .snd .sec))
          .inv ((a .fst .snd , a .fst .fst) , a .snd .snd , a .snd .fst)
          ((sym sq₁ , _) , (sym sq₂ , _))
          .fst
        where
        module u+v = BinCoProductNotation (bcp Γ)
      isUniv Γ Γᴰ .inv _ _ .snd = tt
      isUniv Γ Γᴰ .rightInv _ _ =
        isProp→PathP (λ _ → isProp×
          (isPropΣ (D.isSetHom _ _) λ _ → isPropUnit)
          (isPropΣ (D.isSetHom _ _) λ _ → isPropUnit)) _ _
      isUniv Γ Γᴰ .leftInv _ _ =
        isProp→PathP (λ _ → isPropΣ (D.isSetHom _ _) λ _ → isPropUnit) _ _

  module _ (init : Initial' D) where
    init×init' : Terminal' (∫C (weaken (D ^op) (D ^op)))
    init×init' = term×term (D ^op) init

    Iso∫wkInitialᴰ' : Terminalᴰ (Iso∫wk (D ^op)) init×init'
    Iso∫wkInitialᴰ' = Iso∫wkTerminalᴰ (D ^op) init×init'

    private
      module ⊥D = TerminalNotation init

    Iso∫wkInitialᴰ : Initialᴰ (Iso∫wk D) (init×init init init)
    Iso∫wkInitialᴰ =
      (Iso∫wkInitialᴰ' .fst .fst , isiso (Iso∫wkInitialᴰ' .fst .snd .inv)
                                         (Iso∫wkInitialᴰ' .fst .snd .ret)
                                         (Iso∫wkInitialᴰ' .fst .snd .sec)) ,
      _ ,
      isUniv
      where
      isUniv : _
      isUniv Γ Γᴰ .inv _ _ .fst = ⊥D.𝟙extensionality
      isUniv Γ Γᴰ .inv _ _ .snd = tt
      isUniv Γ Γᴰ .rightInv = λ _ _ → refl
      isUniv Γ Γᴰ .leftInv _ _ =
        isProp→PathP (λ _ → isPropΣ (D.isSetHom _ _) λ _ → isPropUnit) _ _

module IsoCommaStructure {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (F G : Functor C D) where
  private
    module D = Category D
    module C = Category C
    FG : Functor C (∫C (weaken D D))
    FG = ×→∫wk ∘F (F ,F G)

  IsoCommaᴰΔ : Categoryᴰ C ℓD' ℓD'
  IsoCommaᴰΔ = Reindex.reindex (Iso∫wk D) FG

  module _ (termC : Terminal' C)
           (F-1 : preservesUniversalElement {D = D} {F = F} {Q = UnitPsh}
             (pshhom (λ _ x → x) (λ _ _ _ _ → refl)) termC)
           (G-1 : preservesUniversalElement {D = D} {F = G} {Q = UnitPsh}
             (pshhom (λ _ x → x) (λ _ _ _ _ → refl)) termC)
           where

    private
      module F⊤ = TerminalNotation (preservesUniversalElement→UniversalElement {F = F}
         (pshhom (λ _ x → x) (λ _ _ _ _ → refl)) termC F-1)
      module G⊤ = TerminalNotation (preservesUniversalElement→UniversalElement {F = G}
         (pshhom (λ _ x → x) (λ _ _ _ _ → refl)) termC G-1)
      FG-1 : preservesUniversalElement {F = FG} {Q = UnitPsh}
               (pshhom (λ _ x → x) (λ _ _ _ _ → refl)) termC
      FG-1 (a , b) = isoToIsEquiv (iso (λ _ → tt)
        (λ _ → F⊤.!t , G⊤.!t)
        (λ _ → refl)
        λ _ → ΣPathP (F⊤.𝟙extensionality , G⊤.𝟙extensionality ))

    -- OIC This needs to parameterize the terminal in the base
    -- rather than fixing one
    IsoCommaTerminalᴰ : Terminalᴰ IsoCommaᴰΔ termC
    IsoCommaTerminalᴰ = ReindexTerminalᴰ UnitPsh UnitPsh FG termC FG-1
      (Iso∫wkTerminalᴰ D)
