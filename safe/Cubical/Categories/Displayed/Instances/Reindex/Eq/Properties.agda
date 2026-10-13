{-
   A variant of reindexing using J to avoid transport clutter.
-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Reindex.Eq.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import      Cubical.Data.Equality as Eq
import      Cubical.Data.Equality.Conversion as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.BinProduct
  renaming (Fst to FstBP ; Snd to SndBP)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Exponentials.Small as Small
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.StrictHom as StrictHom

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Instances.TotalCategory
  hiding (introF; introS)
open import Cubical.Categories.Instances.TotalCategory as TotalCat
  hiding (intro)
import Cubical.Categories.Displayed.Instances.Reindex.Base as Reindex
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Reindex.Eq.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialD
private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ'
      ℓP ℓQ ℓQᴰ : Level

open Category
open Functor
open isIsoOver
open UniversalElement

module EqReindexProperties
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ')
  (F : Functor C D)
  (F-id'  : {x : C .ob} → D .id {x = F .F-ob x} Eq.≡ F .F-hom (C .id))
  (F-seq' : {x y z : C .ob} (f : C [ x , y ]) (g : C [ y , z ])
          → (F .F-hom f) ⋆⟨ D ⟩ (F .F-hom g) Eq.≡ F .F-hom (f ⋆⟨ C ⟩ g))
  where
  open EqReindex Dᴰ F F-id' F-seq' public
  private
    module C = Category C
    module D = Category D
    module Dᴰ = Fibers Dᴰ
    F*Dᴰ = Reindex.reindex Dᴰ F

  forgetReindexFullyFaithfulᴰ : FullyFaithfulᴰ forgetReindex
  forgetReindexFullyFaithfulᴰ f xᴰ yᴰ = (λ z → z) , ((λ _ → refl) , (λ _ → refl))

  -- general theorem: reflects UMPᴰ
  --
  -- 1.
  forgetReindex/F : (x : C.ob)
    → Functor (reindex / (C [-, x ])) (Dᴰ / (D [-, F ⟅ x ⟆ ]))
  forgetReindex/F x = forgetReindex /Fᴰ Functor→PshHet F x

  reindexRepresentableIsoⱽ : ∀ (x : C.ob)(Fxᴰ : Dᴰ.ob[ F ⟅ x ⟆ ])
    → PshIsoⱽ (reindex [-][-, Fxᴰ ]) (reindPsh (forgetReindex/F x) (Dᴰ [-][-, Fxᴰ ]))
  reindexRepresentableIsoⱽ x Fxᴰ =
    FFFunctorᴰ→PshIsoᴰ forgetReindex Fxᴰ forgetReindexFullyFaithfulᴰ

  module _ {P : Presheaf C ℓP} {Q : Presheaf D ℓQ}{Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ}
    (α : PshHet F P Q)
    (ue : UniversalElement C P)
    (F⟨ue⟩ : preservesUniversalElement α ue)
    (ueᴰ⟨F⟨ue⟩⟩ : UniversalElementᴰ Dᴰ Q Qᴰ (becomesUniversal→UniversalElement α F⟨ue⟩))
    where
    private
      module Q = PresheafNotation Q
      module Qᴰ = PresheafᴰNotation Dᴰ Q Qᴰ

    reflect-UMPᴰ-square :
      NatIso
        ((Idᴰ /Fⱽ yoRec Q (α .PshHom.N-ob (ue .vertex) (ue .element))) ∘F forgetReindex/F (ue .vertex))
        ((forgetReindex /Fᴰ α) ∘F (Idᴰ /Fⱽ yoRec P (element ue)))
    reflect-UMPᴰ-square .NatIso.trans .NatTrans.N-ob x .fst = D.id
    reflect-UMPᴰ-square .NatIso.trans .NatTrans.N-ob x .snd .fst = Dᴰ.idᴰ
    reflect-UMPᴰ-square .NatIso.trans .NatTrans.N-ob x .snd .snd = Q.⋆IdL _ ∙
      α .PshHom.N-hom (x .fst) (ue .vertex) (snd (snd x)) (element ue)
    reflect-UMPᴰ-square .NatIso.trans .NatTrans.N-hom f = Hom/≡ ((Dᴰ.⋆IdR _ ∙ sym (Dᴰ.⋆IdL _)))
    reflect-UMPᴰ-square .NatIso.nIso x .isIso.inv .fst = D.id
    reflect-UMPᴰ-square .NatIso.nIso x .isIso.inv .snd .fst = Dᴰ.idᴰ
    reflect-UMPᴰ-square .NatIso.nIso x .isIso.inv .snd .snd = Q.⋆IdL _ ∙ sym (α .PshHom.N-hom (x .fst) (ue .vertex) (snd (snd x)) (element ue))
    reflect-UMPᴰ-square .NatIso.nIso x .isIso.sec = Hom/≡ (Dᴰ.⋆IdL _)
    reflect-UMPᴰ-square .NatIso.nIso x .isIso.ret = Hom/≡ (Dᴰ.⋆IdL _)

    reflectsUEᴰ : UniversalElementᴰ reindex P (reindPsh (forgetReindex /Fᴰ α) Qᴰ) ue
    reflectsUEᴰ = Representableᴰ→UniversalElementᴰOverUE reindex P (reindPsh (forgetReindex /Fᴰ α) Qᴰ) ue
      ((ueᴰ⟨F⟨ue⟩⟩ .fst)
      , (FiberwisePshIsoᴰ→PshIsoᴰ $
        reindexRepresentableIsoⱽ _ (ueᴰ⟨F⟨ue⟩⟩ .fst)
        ⋆PshIso reindPshIso (forgetReindex/F _) (PshIsoᴰ→FiberwisePshIsoᴰ (UniversalElementᴰ→PshIsoᴰ Dᴰ Q Qᴰ _ ueᴰ⟨F⟨ue⟩⟩))
        ⋆PshIso reindPsh-square _ _ _ _ _ reflect-UMPᴰ-square))

  module _ {term : Terminal' C} where
    -- TODO: add some combinators to make this a bit cleaner
    -- TODO: this is very similar to the proof for non-Eq-reindex and for vertical terminals.
    --   Can we share more of the code?
    reflectsTerminalᴰ :
      (F⟅term⟆ : preservesTerminal' F term)
      → Terminalᴰ Dᴰ (becomesUniversal→UniversalElement ((invPshIso (reindPsh-Unit F) .PshIso.trans)) F⟅term⟆)
      → Terminalᴰ reindex term
    reflectsTerminalᴰ F⟅term⟆ termᴰ = reflectsUEᴰ _ term F⟅term⟆ termᴰ ◁UEᴰⱽ
      reindPsh-Unit _

  module _ {A B Aᴰ Bᴰ} (bp : BinProduct C (A , B)) where
    reflectsBP-square₁ : NatIso
      ((Idᴰ /FⱽStrict StrictHom.π₁ (D [-, F-ob F A ]) (D [-, F-ob F B ]))
       ∘F (forgetReindex /Fᴰ preservesBinProdCones F A B))
      (forgetReindex/F A ∘F
       (Idᴰ /FⱽStrict StrictHom.π₁ (C [-, A ]) (C [-, B ])))
    reflectsBP-square₁ .NatIso.trans .NatTrans.N-ob = λ x → D.id , Dᴰ.idᴰ , D.⋆IdL _
    reflectsBP-square₁ .NatIso.trans .NatTrans.N-hom f3 = Hom/≡ (Dᴰ.⋆IdR _ ∙ (sym $ Dᴰ.⋆IdL _))
    reflectsBP-square₁ .NatIso.nIso x .isIso.inv = D.id , Dᴰ.idᴰ , D.⋆IdL _
    reflectsBP-square₁ .NatIso.nIso x .isIso.sec = Hom/≡ (Dᴰ.⋆IdL _)
    reflectsBP-square₁ .NatIso.nIso x .isIso.ret = Hom/≡ (Dᴰ.⋆IdL _)

    reflectsBP-square₂ : NatIso
      ((Idᴰ /FⱽStrict StrictHom.π₂ (D [-, F-ob F A ]) (D [-, F-ob F B ]))
       ∘F (forgetReindex /Fᴰ preservesBinProdCones F A B))
      (forgetReindex/F B ∘F
       (Idᴰ /FⱽStrict StrictHom.π₂ (C [-, A ]) (C [-, B ])))
    reflectsBP-square₂ .NatIso.trans .NatTrans.N-ob = λ x → D.id , Dᴰ.idᴰ , D.⋆IdL _
    reflectsBP-square₂ .NatIso.trans .NatTrans.N-hom f3 = Hom/≡ (Dᴰ.⋆IdR _ ∙ (sym $ Dᴰ.⋆IdL _))
    reflectsBP-square₂ .NatIso.nIso x .isIso.inv = D.id , Dᴰ.idᴰ , D.⋆IdL _
    reflectsBP-square₂ .NatIso.nIso x .isIso.sec = Hom/≡ (Dᴰ.⋆IdL _)
    reflectsBP-square₂ .NatIso.nIso x .isIso.ret = Hom/≡ (Dᴰ.⋆IdL _)

    reflectsBPᴰ :
      (F⟅bp⟆ : preservesBinProduct F bp)
      → BinProductᴰ Dᴰ (becomesUniversal→UniversalElement (preservesBinProdCones F A B) F⟅bp⟆) Aᴰ Bᴰ
      → BinProductᴰ reindex bp Aᴰ Bᴰ
    reflectsBPᴰ F⟅bp⟆ bpᴰ⟨F⟅bp⟆⟩ = reflectsUEᴰ (preservesBinProdCones F A B) bp F⟅bp⟆ bpᴰ⟨F⟅bp⟆⟩ ◁UEᴰⱽ (
      reindPsh× _ _ _
      ⋆PshIso ×PshIso
        (reindPsh-square _ _ _ _ _ reflectsBP-square₁
          ⋆PshIso reindPshIso _ (invPshIso (reindexRepresentableIsoⱽ _ _)))
        (reindPsh-square _ _ _ _ _ reflectsBP-square₂
          ⋆PshIso reindPshIso _ (invPshIso (reindexRepresentableIsoⱽ _ _))))

