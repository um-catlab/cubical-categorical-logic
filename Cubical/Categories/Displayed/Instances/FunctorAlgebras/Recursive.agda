-- Recursive coalgebras and corecursive algebras of an endofunctor:
-- coalgebra-to-algebra morphisms
-- initial/final coincidence
module Cubical.Categories.Displayed.Instances.FunctorAlgebras.Recursive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Displayed.Instances.FunctorAlgebras
open import Cubical.Categories.Displayed.Instances.FunctorCoalgebras

private
  variable ℓC ℓC' : Level

module _ {C : Category ℓC ℓC'} (F : Functor C C) where
  private
    module C = Category C
  open Functor
  open Bifunctor

  Hylo : Coalgebra F → Algebra F → Type ℓC'
  Hylo (X , c) (B , a) =
    Σ[ h ∈ C [ X , B ] ] (h ≡ c C.⋆ (F .F-hom h C.⋆ a))

  isSetHylo : ∀ Xc Ba → isSet (Hylo Xc Ba)
  isSetHylo Xc Ba =
    isSetΣ C.isSetHom (λ _ → isProp→isSet (C.isSetHom _ _))

  HYLO : (COALG F) o-[ ℓC' ]-* (ALG F)
  HYLO = mkBifunctorSep Sep
    where
    open BifunctorSep
    Sep : BifunctorSep ((COALG F) ^op) (ALG F) (SET ℓC')
    Sep .Bif-ob Xc Ba = Hylo Xc Ba , isSetHylo Xc Ba
    Sep .Bif-homL {c = X , cX} {c' = X' , cX'} (m , msq) (B , a) (h , hsq) =
      (m C.⋆ h)
      , (cong (m C.⋆_) hsq
         ∙ sym (C.⋆Assoc _ _ _)
         ∙ cong (C._⋆ (F .F-hom h C.⋆ a)) msq
         ∙ C.⋆Assoc _ _ _
         ∙ cong (cX' C.⋆_)
             (sym (C.⋆Assoc _ _ _)
              ∙ cong (C._⋆ a) (sym (F .F-seq m h))))
    Sep .Bif-L-id = funExt λ (h , _) →
      Σ≡Prop (λ _ → C.isSetHom _ _) (C.⋆IdL h)
    Sep .Bif-L-seq (m , _) (m' , _) = funExt λ (h , _) →
      Σ≡Prop (λ _ → C.isSetHom _ _) (C.⋆Assoc m' m h)
    Sep .Bif-homR {d = B , a} {d' = B' , a'} (X , cX) (n , nsq) (h , hsq) =
      (h C.⋆ n)
      , (cong (C._⋆ n) hsq
         ∙ C.⋆Assoc _ _ _
         ∙ cong (cX C.⋆_)
             (C.⋆Assoc _ _ _
              ∙ cong (F .F-hom h C.⋆_) nsq
              ∙ sym (C.⋆Assoc _ _ _)
              ∙ cong (C._⋆ a') (sym (F .F-seq h n))))
    Sep .Bif-R-id = funExt λ (h , _) →
      Σ≡Prop (λ _ → C.isSetHom _ _) (C.⋆IdR h)
    Sep .Bif-R-seq (n , _) (n' , _) = funExt λ (h , _) →
      Σ≡Prop (λ _ → C.isSetHom _ _) (sym (C.⋆Assoc h n n'))
    Sep .SepBif-RL-commute (m , _) (n , _) = funExt λ (h , _) →
      Σ≡Prop (λ _ → C.isSetHom _ _) (sym (C.⋆Assoc m h n))

  isRecursiveCoalgebra : Coalgebra F → Type (ℓ-max ℓC ℓC')
  isRecursiveCoalgebra Xc = (Ba : Algebra F) → isContr (Hylo Xc Ba)

  isCorecursiveAlgebra : Algebra F → Type (ℓ-max ℓC ℓC')
  isCorecursiveAlgebra Ba = (Xc : Coalgebra F) → isContr (Hylo Xc Ba)

  HYLOTrivial : Type (ℓ-max ℓC ℓC')
  HYLOTrivial = (Xc : Coalgebra F) (Ba : Algebra F) → isContr (Hylo Xc Ba)

  HYLOTrivial→recursive : HYLOTrivial → ∀ Xc → isRecursiveCoalgebra Xc
  HYLOTrivial→recursive t Xc Ba = t Xc Ba

  HYLOTrivial→corecursive : HYLOTrivial → ∀ Ba → isCorecursiveAlgebra Ba
  HYLOTrivial→corecursive t Ba Xc = t Xc Ba

  private
    Unit*SET : hSet ℓC'
    Unit*SET = Unit* , isSetUnit*

  module _ (Xc : Coalgebra F) where
    open NatTrans

    recursive→trivial : isRecursiveCoalgebra Xc
      → NatIso (appL HYLO Xc) (Constant (ALG F) (SET ℓC') Unit*SET)
    recursive→trivial rec .NatIso.trans .N-ob Ba _ = tt*
    recursive→trivial rec .NatIso.trans .N-hom n = refl
    recursive→trivial rec .NatIso.nIso Ba = isiso
      (λ _ → rec Ba .fst)
      (funExt λ _ → refl)
      (funExt λ h → rec Ba .snd h)

    trivial→recursive :
        NatIso (appL HYLO Xc) (Constant (ALG F) (SET ℓC') Unit*SET)
      → isRecursiveCoalgebra Xc
    trivial→recursive ni Ba = isOfHLevelRespectEquiv 0
      (invEquiv (isoToEquiv (iso
        (ni .NatIso.trans .N-ob Ba)
        (ni .NatIso.nIso Ba .isIso.inv)
        (λ b → funExt⁻ (ni .NatIso.nIso Ba .isIso.sec) b)
        (λ h → funExt⁻ (ni .NatIso.nIso Ba .isIso.ret) h))))
      isContrUnit*

  module _ (Ba : Algebra F) where
    open NatTrans

    corecursive→trivial : isCorecursiveAlgebra Ba
      → NatIso (appR HYLO Ba)
               (Constant ((COALG F) ^op) (SET ℓC') Unit*SET)
    corecursive→trivial corec .NatIso.trans .N-ob Xc _ = tt*
    corecursive→trivial corec .NatIso.trans .N-hom m = refl
    corecursive→trivial corec .NatIso.nIso Xc = isiso
      (λ _ → corec Xc .fst)
      (funExt λ _ → refl)
      (funExt λ h → corec Xc .snd h)

    trivial→corecursive :
        NatIso (appR HYLO Ba)
               (Constant ((COALG F) ^op) (SET ℓC') Unit*SET)
      → isCorecursiveAlgebra Ba
    trivial→corecursive ni Xc = isOfHLevelRespectEquiv 0
      (invEquiv (isoToEquiv (iso
        (ni .NatIso.trans .N-ob Xc)
        (ni .NatIso.nIso Xc .isIso.inv)
        (λ b → funExt⁻ (ni .NatIso.nIso Xc .isIso.sec) b)
        (λ h → funExt⁻ (ni .NatIso.nIso Xc .isIso.ret) h))))
      isContrUnit*

  module FixpointRecursion
    (Fix : C.ob)
    (fixIso : CatIso C (F .F-ob Fix) Fix)
    (triv : HYLOTrivial)
    where

    private
      α    = fixIso .fst
      α⁻¹  = fixIso .snd .isIso.inv
      αsec = fixIso .snd .isIso.sec
      αret = fixIso .snd .isIso.ret

    terminalCoalgebra : TerminalCoalgebra F
    terminalCoalgebra = terminalToUniversalElement
      ( (Fix , α⁻¹)
      , λ (X , c) → isOfHLevelRespectEquiv 0
          (Σ-cong-equiv-snd (eqv X c)) (triv (X , c) (Fix , α)) )
      where
        eqv : ∀ X c (m : C [ X , Fix ])
            → (m ≡ c C.⋆ (F .F-hom m C.⋆ α))
              ≃ (m C.⋆ α⁻¹ ≡ c C.⋆ F .F-hom m)
        eqv X c m = propBiimpl→Equiv
          (C.isSetHom _ _) (C.isSetHom _ _)
          (λ p →
            cong (C._⋆ α⁻¹) p
            ∙ C.⋆Assoc _ _ _
            ∙ cong (c C.⋆_) (C.⋆Assoc _ _ _
                             ∙ cong (F .F-hom m C.⋆_) αret
                             ∙ C.⋆IdR _))
          (λ q →
            sym (C.⋆IdR m)
            ∙ cong (m C.⋆_) (sym αsec)
            ∙ sym (C.⋆Assoc _ _ _)
            ∙ cong (C._⋆ α) q
            ∙ C.⋆Assoc _ _ _)

    initialAlgebra : InitialAlgebra F
    initialAlgebra = terminalToUniversalElement
      ( (Fix , α)
      , λ (B , a) → isOfHLevelRespectEquiv 0
          (Σ-cong-equiv-snd (eqv B a)) (triv (Fix , α⁻¹) (B , a)) )
      where
        eqv : ∀ B a (m : C [ Fix , B ])
            → (m ≡ α⁻¹ C.⋆ (F .F-hom m C.⋆ a))
              ≃ (α C.⋆ m ≡ F .F-hom m C.⋆ a)
        eqv B a m = propBiimpl→Equiv
          (C.isSetHom _ _) (C.isSetHom _ _)
          (λ p →
            cong (α C.⋆_) p
            ∙ sym (C.⋆Assoc _ _ _)
            ∙ cong (C._⋆ (F .F-hom m C.⋆ a)) αret
            ∙ C.⋆IdL _)
          (λ q →
            sym (C.⋆IdL m)
            ∙ cong (C._⋆ m) (sym αsec)
            ∙ C.⋆Assoc _ _ _
            ∙ cong (α⁻¹ C.⋆_) q)
