module Cubical.Categories.LocallySmall.NaturalTransformation.SmallFibers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Reflection.RecordEquiv.More

import Cubical.Categories.Category as Small
import Cubical.Categories.Functor as SmallF
import Cubical.Categories.NaturalTransformation as SmallNT

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
import Cubical.Categories.LocallySmall.Functor.Base as LocallySmallF
import Cubical.Categories.LocallySmall.Functor.IntoFiberCategory as IntoFibCat
import Cubical.Categories.LocallySmall.NaturalTransformation.IntoFiberCategory as IntoFibCatNatTrans
open import Cubical.Categories.LocallySmall.Functor.SmallFibers
open import Cubical.Categories.LocallySmall.Instances.Indiscrete
open import Cubical.Categories.LocallySmall.Variables

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.LocallySmall.Displayed.Fibration.IsoFibration

open Category
open Categoryᴰ
open SmallCategory

module _
  {CTy : Type ℓC}
  {D : SmallCategory ℓD ℓD'}
  where
  private
    C = smallcat _ (Indiscrete (Liftω CTy))
    module C = SmallCategory C
    module D = SmallCategory D
  module NatTransDefs
    {Cobᴰ-ℓ Cobᴰ CHom-ℓᴰ}
    (Cᴰ : SmallFibersCategoryᴰ C.cat Cobᴰ-ℓ Cobᴰ CHom-ℓᴰ)
    {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
    (Dᴰ : SmallFibersCategoryᴰ D.cat Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ)
    where
    private
      module Cᴰ = CategoryᴰNotation Cᴰ
      module Dᴰ = CategoryᴰNotation Dᴰ

    open FunctorDefs Cᴰ Dᴰ public
    module IntoFibCatNT = IntoFibCatNatTrans.NatTransDefs

    module _ (isoOpFibCᴰ : isIsoOpFibration Cᴰ) where
      module _ {c c' : C.ob} where
        LiftF = IndiscreteIsoOpFibF Cᴰ (liftω c) (liftω c')
          (λ cᴰ → isoOpFibCᴰ cᴰ (mkIndiscreteIso (liftω c) (liftω c')))

      open opIsoLift
      open CatIsoᴰ
      module _ {c c' c'' : C.ob} where
        LiftF-seq :
          SmallNT.NatTrans
            (LocallySmallF.SmallLocallySmallFunctor→SmallFunctor (LiftF {c'} {c''})
             SmallF.∘F
             LocallySmallF.SmallLocallySmallFunctor→SmallFunctor (LiftF {c} {c'}))
            (LocallySmallF.SmallLocallySmallFunctor→SmallFunctor (LiftF {c} {c''}))
        LiftF-seq .SmallNT.NatTrans.N-ob cᴰ =
          isoOpFibCᴰ _ _ .f*cᴰIsoᴰ .invᴰ
          Cᴰ.⋆ᴰ isoOpFibCᴰ _ _ .f*cᴰIsoᴰ .invᴰ
          Cᴰ.⋆ᴰ isoOpFibCᴰ _ _ .f*cᴰIsoᴰ .funᴰ
        LiftF-seq .SmallNT.NatTrans.N-hom f =
          Cᴰ.rectify $ Cᴰ.≡out $
            (sym $ Cᴰ.reind-filler _ _)
            ∙ (sym $ Cᴰ.⋆Assocᴰ _ _ _)
            ∙ (sym $ Cᴰ.⋆Assocᴰ _ _ _)
            ∙ Cᴰ.⟨
              Cᴰ.⋆Assocᴰ _ _ _
              ∙ Cᴰ.⋆Assocᴰ _ _ _
              ∙ Cᴰ.⋆Assocᴰ _ _ _
              ∙ Cᴰ.⟨⟩⋆⟨ Cᴰ.⋆Assocᴰ _ _ _
                        ∙ Cᴰ.⟨⟩⋆⟨ Cᴰ.⟨⟩⋆⟨ (sym $ Cᴰ.⋆Assocᴰ _ _ _)
                                          ∙ Cᴰ.⟨ isoOpFibCᴰ _ _ .f*cᴰIsoᴰ .retᴰ ⟩⋆⟨⟩
                                        ∙ Cᴰ.⋆IdLᴰ _ ⟩
                                  ∙ isoOpFibCᴰ _ _ .f*cᴰIsoᴰ .retᴰ ⟩
                        ∙ Cᴰ.⋆IdRᴰ _
                        ∙ Cᴰ.⟨⟩⋆⟨ (sym $ Cᴰ.⋆IdLᴰ _)
                                  ∙ Cᴰ.⟨ sym $ isoOpFibCᴰ _ _ .f*cᴰIsoᴰ .retᴰ ⟩⋆⟨⟩
                                  ∙ Cᴰ.⋆Assocᴰ _ _ _ ⟩
                        ∙ (sym $ Cᴰ.⋆Assocᴰ _ _ _) ⟩
              ∙ (sym $ Cᴰ.⋆Assocᴰ _ _ _)
              ⟩⋆⟨⟩
            ∙ Cᴰ.⋆Assocᴰ _ _ _
            ∙ Cᴰ.reind-filler _ _

      module _
        {c c' : C.ob}
        {d d' : D.ob} (g : D.[ d , d' ])
        (F : Functor c d)
        (G : Functor c' d')
        where
        private
          module F = FunctorNotation F
          module G = FunctorNotation G

        NatTrans : Type _
        NatTrans =
          IntoFibCatNT.NatTrans
            (smallcat _ Cᴰ.v[ liftω c ]) Dᴰ g
              F (G LocallySmallF.∘F LiftF)

      open LocallySmallF.Functor
      open CatIsoᴰ
      open IntoFibCatNT.NatTrans
      open opIsoLift

      module _ {c}{d}(F : Functor c d) where
        private
          module F = FunctorNotation F
        idTrans : NatTrans D.id F F
        idTrans .N-ob cᴰ =
          F-hom F (isoOpFibCᴰ (liftω cᴰ) (mkIndiscreteIso (liftω _) (liftω _))
                               .f*cᴰIsoᴰ .funᴰ)
        idTrans .N-hom f =
          Dᴰ.reind-filler _ _
          ∙ (sym $ Dᴰ.≡in (F .F-seq _ _))
          ∙ ΣPathP (refl ,
            (cong (F .F-hom)
              (Cᴰ.rectify $ Cᴰ.≡out $
                (sym $ Cᴰ.reind-filler _ _)
                ∙ Cᴰ.⟨ sym (Cᴰ.⋆IdLᴰ _)
                       ∙ Cᴰ.⟨ sym $ isoOpFibCᴰ _ _ .f*cᴰIsoᴰ .retᴰ ⟩⋆⟨⟩ ⟩⋆⟨⟩
                ∙ Cᴰ.⟨ Cᴰ.⋆Assocᴰ _ _ _ ⟩⋆⟨⟩
                ∙ Cᴰ.⋆Assocᴰ _ _ _
                ∙ Cᴰ.reind-filler _ _
               )))
          ∙ Dᴰ.≡in (F .F-seq _ _)
          ∙ (sym $ Dᴰ.reind-filler _ _)

      module _ {c c' c''}{d d' d''}
        {g : D.Hom[ liftω d , liftω d' ]}
        {g' : D.Hom[ liftω d' , liftω d'' ]}
        {F : Functor c d} {G : Functor c' d'} {H : Functor c'' d''}
        (α : NatTrans g F G)
        (β : NatTrans g' G H)
        where
        private
          module F = FunctorNotation F
          module G = FunctorNotation G
          module H = FunctorNotation H

        seqTrans : NatTrans (g D.⋆ g') F H
        seqTrans =
          IntoFibCatNT.seqTrans
            (smallcat (Cobᴰ (liftω c)) Cᴰ.v[ liftω c ])
            Dᴰ
            α
            γ
          where
          open IntoFibCatNT.NatTrans

          γ' : IntoFibCatNT.NatTrans (smallcat (Cobᴰ (liftω c)) Cᴰ.v[ liftω c ]) Dᴰ g'
                (G LocallySmallF.∘F LiftF)
                ((H LocallySmallF.∘F LiftF) LocallySmallF.∘F LiftF)
          γ' = IntoFibCatNatTrans.whiskerL
                (smallcat (Cobᴰ (liftω c')) Cᴰ.v[ liftω c' ])
                Dᴰ (smallcat (Cobᴰ (liftω c)) Cᴰ.v[ liftω c ]) LiftF β

          γ : IntoFibCatNT.NatTrans (smallcat (Cobᴰ (liftω c)) Cᴰ.v[ liftω c ]) Dᴰ g'
                (G LocallySmallF.∘F LiftF)
                (H LocallySmallF.∘F LiftF)
          γ .N-ob cᴰ =
            Dᴰ.reind (D.⋆IdR _)
              (γ' .N-ob cᴰ Dᴰ.⋆ᴰ H.F-hom (LiftF-seq .SmallNT.NatTrans.N-ob cᴰ))
          γ .N-hom f =
            Dᴰ.⟨⟩⋆⟨ sym $ Dᴰ.reind-filler _ _ ⟩
            ∙ (sym $ Dᴰ.⋆Assocᴰ _ _ _)
            ∙ Dᴰ.⟨ γ' .N-hom f ⟩⋆⟨⟩
            ∙ Dᴰ.⋆Assocᴰ _ _ _
            ∙ Dᴰ.⟨⟩⋆⟨
              Dᴰ.reind-filler _ _
              ∙ (Dᴰ.≡in $ (sym $ H.F-seq _ _))
              ∙ (Dᴰ.≡in $
                   H.F-hom⟨ Cᴰ.rectify $ (LiftF-seq .SmallNT.NatTrans.N-hom f) ⟩)
              ∙ (Dᴰ.≡in $ (H.F-seq _ _))
              ∙ (sym $ Dᴰ.reind-filler _ _) ⟩
            ∙ (sym $ Dᴰ.⋆Assocᴰ _ _ _)
            ∙ Dᴰ.⟨ Dᴰ.reind-filler _ _ ⟩⋆⟨⟩

      module _
        {c c' : C.ob}
        {d d' : D.ob} {g g' : D.[ d , d' ]}
        {F : Functor c d}
        {G : Functor c' d'}
        {α : NatTrans g F G}
        {β : NatTrans g' F G}
        where
        private
          module F = FunctorNotation F
          module G = FunctorNotation G

        makeNatTransPathP :
          (g≡g' : g ≡ g')
          → PathP
              (λ i → ∀ x →
                Dᴰ.Hom[ g≡g' i ][ F.F-ob (liftω x) ,
                                  G.F-ob (isoOpFibCᴰ (liftω x)
                                    (mkIndiscreteIso (liftω c) (liftω c')) .f*cᴰ) ])
              (α .N-ob)
              (β .N-ob)
          → PathP (λ i → NatTrans (g≡g' i) F G) α β
        makeNatTransPathP g≡g' p i .N-ob x = p i x
        makeNatTransPathP g≡g' p i .N-hom {x = x} {y = y} f =
          isSet→SquareP (λ _ _ → isSetΣ D.isSetHom (λ _ → Dᴰ.isSetHomᴰ))
            (α .N-hom f) (β .N-hom f)
            (λ j → _ , (F.F-hom f Dᴰ.⋆ᴰ p j y))
            (λ j → _ , (p j x Dᴰ.⋆ᴰ G.F-hom (LiftF .F-hom f)))
            i

      module _
        {c c' : C.ob}
        {d d' : D.ob} {g g' : D.[ d , d' ]}
        {F : Functor c d}
        {G : Functor c' d'}
        {α : NatTrans g F G}
        {β : NatTrans g' F G}
        (g≡g' : g ≡ g')
        (p : ∀ x → α .N-ob x Dᴰ.∫≡ β .N-ob x)
        where
        private
          module F = FunctorNotation F
          module G = FunctorNotation G
          module C^op = SmallCategory (C ^opsmall)

        makeNatTransPath :
          Path (Σ[ (_ , h) ∈ (C^op.Hom[ liftω c , liftω c' ] × D.Hom[ liftω d , liftω d' ]) ] NatTrans h F G)
            (_ , α) (_ , β)
        makeNatTransPath =
          ΣPathP (ΣPathP (refl , g≡g') ,
            (makeNatTransPathP {G = G} g≡g'
              (funExt λ x → Dᴰ.rectify $ Dᴰ.≡out $ p x)))
