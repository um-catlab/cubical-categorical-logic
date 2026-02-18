{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Presheaf.Eq.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport hiding (pathToIso)

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Constructions.Lift
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory.Base
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation hiding (_∘ˡ_; _∘ˡⁱ_)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Properties renaming (PshIso to PshIsoLift)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.BinProduct hiding (π₁ ; π₂)
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Yoneda

open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Isomorphism.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base
open import Cubical.Categories.Presheaf.StrictHom

open Functor
open Iso
open NatIso
open NatTrans
open Categoryᴰ
open PshHomStrict
open PshHom
open PshHomEq

private
  variable
    ℓ ℓ' ℓP ℓQ ℓR ℓS ℓS' ℓS'' : Level
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓPᴰ ℓQᴰ ℓRᴰ : Level
module _ {C : Category ℓC ℓC'} where
  PSHIdR : EqIdR (PRESHEAF C ℓP)
  PSHIdR = λ f → Eq.refl

  PSHIdL : EqIdL (PRESHEAF C ℓP)
  PSHIdL = λ f → Eq.refl

  PSHAssoc : ReprEqAssoc (PRESHEAF C ℓP)
  PSHAssoc _ f g h f⋆g Eq.refl = Eq.refl

  PSHπ₁NatEq : Allπ₁NatEq {C = PRESHEAF C ℓP} (PSHBP C ℓP)
  PSHπ₁NatEq X γ = Eq.refl

  PSH×aF-seq : All×aF-seq {C = PRESHEAF C ℓP} (PSHBP C ℓP)
  PSH×aF-seq X δ γ = Eq.refl

module _ {C : Category ℓC ℓC'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshHomStrict P Q)
  where

  -- Yikes but...who cares?
  PshHomStrict→Eq : PshHomEq P Q
  PshHomStrict→Eq .PshHomEq.N-ob c x = α .N-ob c x
  PshHomStrict→Eq .PshHomEq.N-hom c c' f p' p x =
    Eq.pathToEq (α .N-hom c c' f p' p (Eq.eqToPath x))
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  where
  _*_ : (α : PshHomEq P Q) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) → Presheafᴰ P Cᴰ ℓQᴰ
  α * Qᴰ = reindPsh (Idᴰ /Fⱽ α) Qᴰ

  _*Strict_ : (α : PshHomStrict P Q) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) → Presheafᴰ P Cᴰ ℓQᴰ
  α *Strict Qᴰ = PshHomStrict→Eq α * Qᴰ

  infixr 10 _*_
  infixr 10 _*Strict_

  private
    module P = PresheafNotation P
    module Q = PresheafNotation Q
  module _ (α : PshHomEq P Q) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ
    infixr 10 _Push_
    _Push_ : Presheafᴰ Q Cᴰ (ℓ-max (ℓ-max ℓP ℓQ) ℓPᴰ)
    _Push_ .F-ob (Γ , Γᴰ , q) .fst = Σ[ p ∈ P.p[ Γ ] ] (q Eq.≡ α .N-ob Γ p) × Pᴰ.p[ p ][ Γᴰ ]
    _Push_ .F-ob (Γ , Γᴰ , q) .snd = isSetΣ P.isSetPsh λ p → isSet× (isProp→isSet (Eq.isSet→isSetEq Q.isSetPsh)) Pᴰ.isSetPshᴰ
    _Push_ .F-hom (γ , γᴰ , e) (p , e' , pᴰ) =
      (γ P.⋆ p) ,
      (Eq.sym e Eq.∙ Eq.ap (γ Q.⋆_) e') Eq.∙ α .N-hom _ _ γ p (γ P.⋆ p) Eq.refl , (γᴰ Pᴰ.⋆ᴰ pᴰ )
    _Push_ .F-id = funExt λ _ →
      ΣPathP (P.⋆IdL _ ,
      ΣPathP ((isProp→PathP (λ _ → Eq.isSet→isSetEq Q.isSetPsh) _ _) ,
      (Pᴰ.rectifyOut (Pᴰ.⋆IdL _))))
    _Push_ .F-seq (_ , _ , Eq.refl) (_ , _ , Eq.refl) = funExt λ _ →
      ΣPathP ((P.⋆Assoc _ _ _) ,
        (ΣPathP (isProp→PathP (λ _ → Eq.isSet→isSetEq Q.isSetPsh) _ _ ,
        (Pᴰ.rectifyOut $ Pᴰ.⋆Assoc _ _ _))))

  module _  where
    infixr 10 _PushStrict_
    _PushStrict_ : (α : PshHomStrict P Q) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) → Presheafᴰ Q Cᴰ (ℓ-max (ℓ-max ℓP ℓQ) ℓPᴰ)
    α PushStrict Pᴰ = PshHomStrict→Eq α Push Pᴰ
  module _ (α : PshHomEq P Q) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ
      module Qᴰ = PresheafᴰNotation Qᴰ

    Push⊣* : Iso (PshHom Pᴰ (α * Qᴰ)) (PshHom (α Push Pᴰ) Qᴰ)
    Push⊣* .fun αᴰ .N-ob (Γ , Γᴰ , q) (p , e , pᴰ) =
      Qᴰ.reindEq (Eq.sym e) $ αᴰ .N-ob (Γ , Γᴰ , p) pᴰ
    Push⊣* .fun αᴰ .N-hom _ _ (_ , _ , Eq.refl) (_ , Eq.refl , _) =
      Qᴰ.rectifyOut $ Qᴰ.reindEq-filler⁻ _ ∙ (Qᴰ.≡in $ αᴰ .N-hom _ _ _ _) ∙ (sym $ Qᴰ.⋆ᴰ-reind _)
    Push⊣* .inv βⱽ .N-ob (Γ , Γᴰ , p) pᴰ = βⱽ .N-ob (Γ , Γᴰ , α .N-ob Γ p) (p , Eq.refl , pᴰ)
    Push⊣* .inv βⱽ .N-hom _ _ (_ , _ , Eq.refl) e =
      cong (βⱽ .N-ob _)
        (ΣPathP (refl , ΣPathP ((isProp→PathP (λ _ → Eq.isSet→isSetEq Q.isSetPsh) _ _) , refl)))
      ∙ βⱽ .N-hom _ _ (_ , _ , α .N-hom _ _ _ _ _ Eq.refl ) (_ , Eq.refl , e)
      ∙ Qᴰ.rectifyOut ((sym $ Qᴰ.⋆ᴰ-reind (α .N-hom _ _ _ _ _ Eq.refl)) ∙ Qᴰ.⋆ᴰ-reind _)
    Push⊣* .sec βⱽ = makePshHomPath (funExt₂ λ { (Γ , Γᴰ , q) (p , Eq.refl , pᴰ ) → refl })
    Push⊣* .ret αᴰ = makePshHomPath refl

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshHomEq P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
  private
    module Qᴰ = PresheafᴰNotation Qᴰ

  FrobeniusReciprocity : PshIso (α Push (Pᴰ ×Psh (α * Qᴰ))) ((α Push Pᴰ) ×Psh Qᴰ)
  FrobeniusReciprocity .PshIso.trans .N-ob (Γ , Γᴰ , q) (p , e , (pᴰ , qᴰ)) =
    (p , e , pᴰ) , Qᴰ.reindEq (Eq.sym e) qᴰ
  FrobeniusReciprocity .PshIso.trans .N-hom _ _ (γ , γᴰ , Eq.refl) (p , Eq.refl , (pᴰ , qᴰ)) =
    ΣPathP (refl , (Qᴰ.rectifyOut $ Qᴰ.reindEq-filler⁻ _ ∙ (sym $ Qᴰ.⋆ᴰ-reind _)))
  FrobeniusReciprocity .PshIso.nIso (Γ , Γᴰ , q) .fst ((p , Eq.refl , pᴰ) , qᴰ) =
    (p , Eq.refl , pᴰ , qᴰ)
  FrobeniusReciprocity .PshIso.nIso (Γ , Γᴰ , q) .snd .fst ((p , Eq.refl , pᴰ) , qᴰ) = refl
  FrobeniusReciprocity .PshIso.nIso (Γ , Γᴰ , q) .snd .snd (p , Eq.refl , (pᴰ , qᴰ)) = refl

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {R : Presheaf C ℓR}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshHomStrict R P)
  (Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ)
  where
  private
    module P = PresheafNotation P
    module Rᴰ = PresheafᴰNotation Rᴰ

  BeckChevalley :
    PshIso
      (×PshIntroStrict (π₁ R Q ⋆PshHomStrict α) (π₂ R Q) PushStrict π₁ R Q *Strict Rᴰ)
      (π₁Eq P Q * α PushStrict Rᴰ)
  BeckChevalley .PshIso.trans .N-ob (Γ , Γᴰ , p , q) ((r , q') , (e , rᴰ)) = r , (Eq.ap fst e , rᴰ)
  BeckChevalley .PshIso.trans .N-hom c c' (_ , _ , Eq.refl) p =
    ΣPathP (refl , ×≡Prop' (Eq.isSet→isSetEq P.isSetPsh) (Rᴰ.rectifyOut $ sym $ Rᴰ.⋆ᴰ-reind _))
  BeckChevalley .PshIso.nIso (Γ , Γᴰ , p , q) .fst (r , Eq.refl , rᴰ) = (r , q) , Eq.refl , rᴰ
  BeckChevalley .PshIso.nIso (Γ , Γᴰ , p , q) .snd .fst (r , Eq.refl , rᴰ) = refl
  BeckChevalley .PshIso.nIso (Γ , Γᴰ , p , q) .snd .snd ((r , q') , (Eq.refl , rᴰ)) = refl

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  {Pᴰ : Presheafᴰ Q Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where
  _*StrictF_ : (α : PshHomStrict P Q) (β : PshHom Pᴰ Qᴰ) → PshHom (α *Strict Pᴰ) (α *Strict Qᴰ)
  α *StrictF β = reindPshHom (Idᴰ /Fⱽ PshHomStrict→Eq α) β

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshHomStrict P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
  PshHomᴰ : Type _
  PshHomᴰ = PshHom Pᴰ (α *Strict Qᴰ)

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
  idPshHomᴰ : PshHomᴰ idPshHomStrict Pᴰ Pᴰ
  idPshHomᴰ .N-ob = λ c z → z
  idPshHomᴰ .N-hom c c' f p = Pᴰ.rectifyOut $ sym (Pᴰ.⋆ᴰ-reind _) ∙ Pᴰ.⋆ᴰ-reind _

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  {R : Presheaf C ℓR}
  {Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ}
  (α : PshHomStrict P Q)
  β
  where
  private
    module Rᴰ = PresheafᴰNotation Rᴰ
  *Strict-seq : PshHom (α *Strict (β *Strict Rᴰ)) ((α ⋆PshHomStrict β) *Strict Rᴰ)
  *Strict-seq .N-ob = λ c z → z
  *Strict-seq .N-hom c c' (γ , γᴰ , Eq.refl) p = Rᴰ.rectifyOut $
    sym (Rᴰ.⋆ᴰ-reind _) ∙ Rᴰ.⋆ᴰ-reind _

  *Strict-seq⁻ : PshHom ((α ⋆PshHomStrict β) *Strict Rᴰ) (α *Strict (β *Strict Rᴰ))
  *Strict-seq⁻ .N-ob = λ c z → z
  *Strict-seq⁻ .N-hom c c' (γ , γᴰ , Eq.refl) p = Rᴰ.rectifyOut $
    sym (Rᴰ.⋆ᴰ-reind _) ∙ Rᴰ.⋆ᴰ-reind _

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  {R : Presheaf C ℓR}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  {Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ}
  {α : PshHomStrict P Q}
  {β : PshHomStrict Q R}
  where
  _⋆PshHomᴰ_ : (αᴰ : PshHomᴰ α Pᴰ Qᴰ) (βᴰ : PshHomᴰ β Qᴰ Rᴰ)
    → PshHomᴰ (α ⋆PshHomStrict β) Pᴰ Rᴰ
  αᴰ ⋆PshHomᴰ βᴰ = αᴰ ⋆PshHom (α *StrictF βᴰ) ⋆PshHom *Strict-seq α β

module _
  {C : Category ℓC ℓC'}
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (ℓP : Level)
  (ℓPᴰ : Level)
  where
  private
    PSH = PRESHEAF C ℓP
    module PSH = Category PSH
    module Cᴰ = Fibers Cᴰ
  -- This is very slow without the annotations to refl.
  -- Think on that
  PRESHEAFᴰ : Categoryᴰ (PRESHEAF C ℓP) _ _
  PRESHEAFᴰ .ob[_] P = Presheaf (Cᴰ / P) ℓPᴰ
  PRESHEAFᴰ .Hom[_][_,_] α P Q = PshHom P (α *Strict Q)
  PRESHEAFᴰ .idᴰ = idPshHomᴰ
  PRESHEAFᴰ ._⋆ᴰ_ {f = α}{g = β} αᴰ βᴰ = αᴰ ⋆PshHomᴰ βᴰ
  PRESHEAFᴰ .⋆IdLᴰ {x = P}{xᴰ = Pᴰ}αᴰ = makePshHomPath (refl {x = αᴰ .N-ob})
  PRESHEAFᴰ .⋆IdRᴰ αᴰ = makePshHomPath (refl {x = αᴰ .N-ob})
  PRESHEAFᴰ .⋆Assocᴰ αᴰ βᴰ γᴰ = makePshHomPath
    (refl {x = ((αᴰ ⋆PshHomᴰ βᴰ) ⋆PshHomᴰ γᴰ) .N-ob})
  PRESHEAFᴰ .isSetHomᴰ = isSetPshHom _ _

module _
  {C : Category ℓC ℓC'}
  (P : Presheaf C ℓP)
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (ℓPᴰ : Level)
  where
  PRESHEAFⱽ : Category (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓP) ℓCᴰ) ℓCᴰ') (ℓ-suc ℓPᴰ))
                       (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓP) ℓCᴰ) ℓCᴰ') ℓPᴰ)
  PRESHEAFⱽ = PSHHOMCAT (Cᴰ / P) ℓPᴰ
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  where
  PushF : {P : Presheaf C ℓP} → Functor (PRESHEAFᴰ Cᴰ ℓP ℓPᴰ / (PRESHEAF C ℓP [-, P ])) (PSHHOMCAT (Cᴰ / P) (ℓ-max ℓP ℓPᴰ))
  PushF .F-ob (R , Rᴰ , α) = α PushStrict Rᴰ
  PushF .F-hom {x = S , Sᴰ , _} {y = R , Rᴰ , α}
    (β , βᴰ , e) .N-ob (Γ , Γᴰ , p) (s , e' , sᴰ) =
      β .N-ob Γ s , (e' Eq.∙ Eq.ap (λ z → z .N-ob Γ s) (Eq.sym e)) , (βᴰ .N-ob (Γ , Γᴰ , s) sᴰ)
  PushF {P = P} .F-hom {x = S , Sᴰ , _} {y = R , Rᴰ , α} (r , rᴰ , Eq.refl) .N-hom
    c c' (_ , _ , Eq.refl) (_ , Eq.refl , _) =
      ΣPathP ((sym $ r .N-hom _ _ _ _ _ refl) ,
        (ΣPathP (isProp→PathP (λ _ → Eq.isSet→isSetEq P.isSetPsh) _ _ ,
          (Rᴰ.rectifyOut $ (Rᴰ.≡in $ rᴰ .N-hom _ _ _ _) ∙ (sym $ Rᴰ.⋆ᴰ-reind _)))))
    where
    module P = PresheafNotation P
    module Rᴰ = PresheafᴰNotation Rᴰ
  PushF {P = P} .F-id = makePshHomPath (funExt₂ λ { _ (_ , Eq.refl , _) →
    ΣPathP (refl , ΣPathP (isProp→PathP (λ _ → Eq.isSet→isSetEq P.isSetPsh) _ _ , refl))
    })
   where module P = PresheafNotation P

  PushF {P = P} .F-seq (_ , _ , Eq.refl) (_ , _ , Eq.refl) =
    makePshHomPath (funExt₂ λ { _ (_ , Eq.refl , _) →
    ΣPathP (refl , ΣPathP (isProp→PathP (λ _ → Eq.isSet→isSetEq P.isSetPsh) _ _ , refl))
    })
   where module P = PresheafNotation P

  ℓPushF = ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ')
  module _ {P : Presheaf C ℓPushF} {Pᴰ : Presheaf (Cᴰ / P) ℓPushF} where
    PushF⊣* :
      PshIsoEq (PRESHEAFᴰ Cᴰ ℓPushF ℓPushF [-][-, Pᴰ ])
               (reindPsh PushF (PRESHEAFⱽ P Cᴰ ℓPushF [-, Pᴰ ]))
    PushF⊣* .PshIsoEq.isos (R , Rᴰ , α) = Push⊣* (PshHomStrict→Eq α) Rᴰ Pᴰ
    PushF⊣* .PshIsoEq.nat _ _ (_ , _ , Eq.refl) _ _ Eq.refl =
      Eq.pathToEq $ makePshHomPath (funExt₂ λ { _ (_ , Eq.refl , _) → refl})
