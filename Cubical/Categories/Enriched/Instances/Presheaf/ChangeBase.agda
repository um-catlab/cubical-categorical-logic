module Cubical.Categories.Enriched.Instances.Presheaf.ChangeBase where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Enriched.Functors.Base
open import Cubical.Categories.Enriched.Instances.Presheaf.Self
open import Cubical.Categories.Functor
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Monoidal.Instances.Presheaf
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Morphism.Alt hiding (_∘ˡ_)

open Category
open EnrichedCategory
open EnrichedFunctor
open Functor
open NatTrans

private
  variable
    ℓ ℓ' ℓS ℓE : Level

module _
  {C D : Category ℓ ℓ'}
  (F : Functor D C)
  (EC : EnrichedCategory (PshMon.𝓟Mon C ℓS) ℓE )
  where

  private
    module PMC = PshMon C ℓS
    module PMD = PshMon D ℓS
    module MC = MonoidalCategory PMC.𝓟Mon
    module MD = MonoidalCategory PMD.𝓟Mon

  EC[_,_] = EC .Hom[_,_]

  distrib^ : {X Y : MC.ob} →
    MD.Hom[ reindPsh F (Y PMC.^ X) , reindPsh F Y PMD.^ reindPsh F X ]
  distrib^ .N-ob d exp =
    pshhom
      (λ {d' (f , XFd') → exp .PshHom.N-ob (F .F-ob d') (F .F-hom f , XFd')})
      λ {d d' f (g , FXd') →
      cong (λ h → exp .PshHom.N-ob _ h) (cong₂ _,_ (F .F-seq _ _) refl)
      ∙ exp .PshHom.N-hom (F .F-ob d)(F .F-ob d')(F .F-hom f)
      (F .F-hom g , FXd')}
  distrib^ .N-hom {d}{d'} f = funExt λ p →
    makePshHomPath (funExt λ  d'' → funExt λ {(g , XFd'') →
      cong (λ h → p .PshHom.N-ob _ h) (cong₂ _,_ (sym ( F-seq F g f )) refl)})

  distrib : {x y z : ob EC} →
    PMD.𝓟 [ reindPsh F EC[ x , y ] MD.⊗ reindPsh F EC[ y , z ] ,
      reindPsh F (EC[ x , y ] MC.⊗ EC[ y , z ]) ]
  distrib = natTrans (λ _ x → x) λ _ → refl

  const : PMD.𝓟 [ MD.unit , reindPsh F MC.unit ]
  const = natTrans (λ _ _ → tt*) λ _ → refl

  Eid : {x : ob EC} → PMD.𝓟 [ MD.unit , reindPsh F EC[ x , x ] ]
  Eid = const ●ᵛ (EC .id ∘ˡ (F ^opF))

  Eseq : {x y z : ob EC} →
    PMD.𝓟 [ reindPsh F EC[ x , y ] MD.⊗ reindPsh F EC[ y , z ] ,
      reindPsh F EC[ x , z ] ]
  Eseq {x}{y}{z} = distrib ●ᵛ (EC .seq x y z ∘ˡ (F ^opF))

  BaseChange : EnrichedCategory PMD.𝓟Mon ℓE
  BaseChange .ob = ob EC
  BaseChange .Hom[_,_] c c' = reindPsh F (EC[ c , c' ])
  BaseChange .id {x} = Eid
  BaseChange .seq x y z = Eseq
  BaseChange .⋆IdL x y =
    makeNatTransPath (funExt λ d → funExt⁻
      (cong (N-ob) (EC .⋆IdL x y)) (F-ob F d))
  BaseChange .⋆IdR x y =
    makeNatTransPath (funExt λ d → funExt⁻
      (cong (N-ob) (EC .⋆IdR x y)) (F-ob F d))
  BaseChange .⋆Assoc x y z w =
    makeNatTransPath (funExt λ d → funExt⁻
      (cong N-ob (EC .⋆Assoc x y z w)) (F-ob F d))

module _
  {C D : Category ℓ ℓ'}
  (F : Functor D C)
  (ℓS : Level)
  where

  private
    module PMC = PshMon C ℓS
    module PMD = PshMon D ℓS

  module _
    {EC EC' : EnrichedCategory PMC.𝓟Mon ℓE}
    (EF : EnrichedFunctor PMC.𝓟Mon EC EC')
    where

    BaseChangeF : EnrichedFunctor PMD.𝓟Mon (BaseChange F EC) (BaseChange F EC')
    BaseChangeF .F-ob = EF .F-ob
    BaseChangeF .F-hom = EF .F-hom ∘ˡ (F ^opF)
    BaseChangeF .F-id =
      makeNatTransPath (funExt λ d → funExt⁻
        (cong N-ob (EF. F-id)) (F-ob F d))
    BaseChangeF .F-seq =
      makeNatTransPath (funExt λ d → funExt⁻
        (cong N-ob (EF .F-seq)) (F-ob F d))

  BaseChangeSelf : EnrichedFunctor PMD.𝓟Mon (BaseChange F (self C _)) (self D _)
  BaseChangeSelf .F-ob = reindPsh F
  BaseChangeSelf .F-hom = distrib^ {ℓS = ℓS} F (self C _)
  BaseChangeSelf .F-id =
    makeNatTransPath (funExt λ m → funExt λ {tt* →
    makePshHomPath (funExt λ n → funExt λ {(f , XFn) → refl})})
  BaseChangeSelf .F-seq =
    makeNatTransPath (funExt λ m → funExt λ{(f , x) →
    makePshHomPath (funExt λ n → funExt λ {(g , XFn) →
      cong (λ h → x . PshHom.N-ob _ h)
        (cong₂ _,_
          (cong (λ h → F .F-hom h) (D .⋆IdL _) ∙ sym (C .⋆IdL _))
          (cong (λ h → f .PshHom.N-ob _ (h , XFn))
          (cong (λ h → F .F-hom h) (D .⋆IdL _) ∙ sym (C .⋆IdL _))))})})
