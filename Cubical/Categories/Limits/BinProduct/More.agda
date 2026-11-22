{-

  This is one of several possible definitions of the binary product.
  It turns out to be the best.

-}
module Cubical.Categories.Limits.BinProduct.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma as Ty hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Instances.BinProduct
import Cubical.Categories.Instances.BinProduct.Redundant.Base as R
open import Cubical.Categories.Functor
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.Cartesian
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Bifunctor as R hiding (Fst; Snd)

open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions hiding (π₁; π₂)
open import Cubical.Categories.Yoneda

private
  variable
    ℓ ℓ' : Level

  _⊗_ = R._×C_

open Category
open Functor
open NatTrans
open NatIso
open PshHom

module _ (C : Category ℓ ℓ') where
  BinProductProf' : Bifunctor C C (PresheafCategory C (ℓ-max ℓ' ℓ'))
  BinProductProf' = PshProd ∘Flr (YO , YO)

  BinProductProf : Profunctor (C ⊗ C) C ℓ'
  BinProductProf = R.rec _ _ BinProductProf'

  BinProduct : ∀ (cc' : (C ⊗ C) .ob) → Type _
  BinProduct cc' = UniversalElement C (BinProductProf ⟅ cc' ⟆)

  BinProducts : Type _
  BinProducts = UniversalElements BinProductProf

  -- Product with a fixed object
  module _ (c : C .ob) where
    ProdWithAProf : Profunctor C C ℓ'
    ProdWithAProf = appR BinProductProf' c

    BinProductsWith : Type (ℓ-max ℓ ℓ')
    BinProductsWith = UniversalElements ProdWithAProf

    BinProductsWithRepr : Type (ℓ-max ℓ ℓ')
    BinProductsWithRepr = AllRepresentable ProdWithAProf

    BinProducts→BinProductsWith : BinProducts → BinProductsWith
    BinProducts→BinProductsWith bp c' = bp (c' , c)

  module _ (bp : BinProducts) where
    BinProductF : Functor (C R.×C C) C
    BinProductF = FunctorComprehension BinProductProf bp

    BinProductBif : Bifunctor C C C
    BinProductBif = R.Functor→Bifunctor BinProductF

    BinProductF' : Functor (C ×C C) C
    BinProductF' = BifunctorToParFunctor BinProductBif


  module _ {a b} (a×b : BinProduct (a , b)) where
    SwapBinProduct : BinProduct (b , a)
    SwapBinProduct = a×b ◁PshIso swap
      where
      -- TODO put this somewhere more general
      -- Could be cleaner using Sym
      swap : ∀ {a b} → PshIso (BinProductProf ⟅ (a , b) ⟆) (BinProductProf ⟅ (b , a) ⟆)
      swap = Isos→PshIso
        (λ c → iso (λ z → z .snd , z .fst) (λ z → z .snd , z .fst)
                   (λ _ → refl) λ _ → refl)
        λ _ _ _ _ → refl

  module _ {a} (bp : BinProductsWith a) where
    BinProductWithF : Functor C C
    BinProductWithF = FunctorComprehension (ProdWithAProf a) bp

module BinProductNotation {C : Category ℓ ℓ'} {a b} (bp : BinProduct C (a , b)) where
  private
    module C = Category C
  module ×ue = UniversalElementNotation bp
  open ×ue
  vert = vertex

  π₁ : C [ vert , a ]
  π₁ = element .fst

  π₂ : C [ vert , b ]
  π₂ = element .snd

  infixr 4 _,p_
  _,p_ : ∀ {Γ} → C [ Γ , a ] → C [ Γ , b ] → C [ Γ , vert ]
  f₁ ,p f₂ = intro (f₁ , f₂)

  opaque
    ⟨_⟩,p⟨_⟩ :
      ∀ {Γ}
        {f f' : C [ Γ , a ]}
        {g g' : C [ Γ , b ]}
      → f ≡ f'
      → g ≡ g'
      → (f ,p g) ≡ (f' ,p g')
    ⟨ f≡f' ⟩,p⟨ g≡g' ⟩ = intro⟨ ΣPathP (f≡f' , g≡g') ⟩

    ,p≡ : ∀ {Γ} {f₁ : C [ Γ , a ]} {f₂ : C [ Γ , b ]} {g}
      → (f₁ ≡ g C.⋆ π₁)
      → (f₂ ≡ g C.⋆ π₂)
      → (f₁ ,p f₂) ≡ g
    ,p≡ f1≡ f2≡ = intro≡ (ΣPathP (f1≡ , f2≡))

    ,p-extensionality : ∀ {Γ} {f g : C [ Γ , vert ]}
      → (f C.⋆ π₁ ≡ g C.⋆ π₁)
      → (f C.⋆ π₂ ≡ g C.⋆ π₂)
      → f ≡ g
    ,p-extensionality f≡g1 f≡g2 = extensionality (ΣPathP (f≡g1 , f≡g2))

    ×β₁ : ∀ {Γ}{f : C [ Γ , a ]}{g} → (f ,p g) C.⋆ π₁ ≡ f
    ×β₁ = cong fst β

    ×β₂ : ∀ {Γ}{f : C [ Γ , a ]}{g} → (f ,p g) C.⋆ π₂ ≡ g
    ×β₂ = cong snd β

module BinProductsNotation {C : Category ℓ ℓ'} (bp : BinProducts C) where
  private
    module C = Category C
  _×_ : C .ob → C .ob → C .ob
  a × b = BinProductNotation.vert  (bp (a , b))
  module _ {a b : C .ob} where
    open BinProductNotation (bp (a , b)) hiding (vert; module ×ue) public
  module ×ue (a b : C .ob) = BinProductNotation.×ue (bp (a , b))

  ×F' : Functor (C R.×C C) C
  ×F' = BinProductF C bp

  ×Bif : Bifunctor C C C
  ×Bif = BinProductBif C bp

  ×F : Functor (C ×C C) C
  ×F = BifunctorToParFunctor ×Bif

  _×p_ : ∀ {a b c d} → C [ a , b ] → C [ c , d ] → C [ a × c , b × d ]
  f ×p g = ×Bif ⟪ f , g ⟫×

  π₁Nat : BinProductF' C bp ⇒ Fst C C
  π₁Nat .NatTrans.N-ob _ = π₁
  π₁Nat .NatTrans.N-hom _ = ×β₁

module BinProductsWithNotation {C : Category ℓ ℓ'}{a} (bp : BinProductsWith C a) where
  _×a : C .ob → C .ob
  b ×a  = BinProductNotation.vert (bp b)
  private module C = Category C
  module _ {b : C .ob} where
    open BinProductNotation (bp b) hiding (vert) public

  ×aF : Functor C C
  ×aF = BinProductWithF C bp

  π₁Nat : ×aF ⇒ Id
  π₁Nat .NatTrans.N-ob _ = π₁
  π₁Nat .NatTrans.N-hom _ = ×β₁

  π₁CartNat : CartesianNatTrans ×aF Id
  π₁CartNat .fst = π₁Nat
  π₁CartNat .snd {x} {y} f {d} p p₁ p₁f≡pπ₁ =
    uniqueExists (p₁ ,p (p C.⋆ π₂))
      ((sym $ ,p-extensionality
        (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ ×β₁ ⟩ ∙ sym (C.⋆Assoc _ _ _) ∙ C.⟨ ×β₁ ⟩⋆⟨ refl ⟩ ∙ (sym p₁f≡pπ₁))
        (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ ×β₂ ⟩ ∙ ×β₂))
       , (sym ×β₁))
      (λ _ → isProp× (C.isSetHom _ _) (C.isSetHom _ _))
      λ p' (p≡p'⋆id×f , p₁≡p'π₁) → ,p≡ p₁≡p'π₁ (C.⟨ p≡p'⋆id×f ⟩⋆⟨ refl ⟩ ∙ C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ ×β₂ ⟩)

private
  variable
    C D : Category ℓ ℓ'
module _ (F : Functor C D) where
  private
    module D = Category D
  preservesBinProdCones : ∀ c c'
    → PshHet F (BinProductProf C ⟅ c , c' ⟆)
               (BinProductProf D ⟅ F ⟅ c ⟆ , F ⟅ c' ⟆ ⟆)
  preservesBinProdCones c c' .N-ob Γ (f , f') = F ⟪ f ⟫ , F ⟪ f' ⟫
  preservesBinProdCones c c' .N-hom Δ Γ γ (f , f') = ΣPathP ((F .F-seq γ f) , (F .F-seq γ f'))

  preservesBinProdWithCones : ∀ c
    → ProfunctorHom (ProdWithAProf C c)
      (reindPshF F ∘F ProdWithAProf D (F ⟅ c ⟆) ∘F F)
  preservesBinProdWithCones c .N-ob c' x =
    preservesBinProdCones _ _ .N-ob (c' .fst) x
  preservesBinProdWithCones c .N-hom
    (c1 , c2) (c1' , c2') (f1 , f2) (g1 , g2) =
      ΣPathP
          ( (F .F-seq _ _ ∙ D.⟨ F .F-seq f1 g1 ⟩⋆⟨ refl ⟩)
          , F .F-seq f1 g2)

  preservesBinProduct : ∀ {c c'} → BinProduct C (c , c') → Type _
  preservesBinProduct = preservesUniversalElement (preservesBinProdCones _ _)

  -- If you have all BinProductsWith, you should probably use the next
  -- one instead
  preservesBinProductsWith : ∀ (c : C .ob) → Type _
  preservesBinProductsWith c = ∀ c'
    → preservesUniversalElements (preservesBinProdCones c c')

  -- In practice this definition is usually nicer to work with than
  -- the previous.
  preservesProvidedBinProductsWith :
    ∀ {c : C .ob} → (-×c : BinProductsWith C c) → Type _
  preservesProvidedBinProductsWith -×c = ∀ c'
    → preservesUniversalElement (preservesBinProdCones c' _) (-×c c')

  preservesProvidedBinProducts :
    BinProducts C → Type _
  preservesProvidedBinProducts bp =
    ∀ c c'
    → preservesUniversalElement
        (preservesBinProdCones c c')
        (bp (c , c'))
  module _ {c}
      (-×c : BinProductsWith C c)
      (-×Fc : BinProductsWith D (F ⟅ c ⟆))
      (F⟨-×c⟩≅F⟨-⟩×Fc : preservesProvidedBinProductsWith -×c)
      where
    private
      module -×c = BinProductsWithNotation -×c
      module -×Fc = BinProductsWithNotation -×Fc
      module F⟪-×c⟫ {Γ} = BinProductNotation {C = D} (isUniversal→UniversalElement _ (F⟨-×c⟩≅F⟨-⟩×Fc Γ))
    preservesProvidedBinProductsWith→NatIso
      : NatIso (F ∘F -×c.×aF) (-×Fc.×aF ∘F F)
    preservesProvidedBinProductsWith→NatIso =
      improveNatIso
      (preserves-UE→NatIso (ProdWithAProf C c) (ProdWithAProf D (F ⟅ c ⟆) ∘F F) F (preservesBinProdWithCones c)
        -×c
        (λ c' → -×Fc (F ⟅ c' ⟆))
        F⟨-×c⟩≅F⟨-⟩×Fc
      ⋆NatIso record { trans = natTrans (λ x → D.id) (λ _ → idTrans (BinProductsWithNotation.×aF -×Fc ∘F F) .N-hom _)
        ; nIso = idNatIso (BinProductsWithNotation.×aF -×Fc ∘F F) .nIso })
      (_ , (funExt λ _ → D.⋆IdR _))
      (_ , funExt λ _ →
        D.⋆IdL _
        ∙ F⟪-×c⟫.,p≡ (D.⋆IdL _ ∙ (sym $ F⟪-×c⟫.×β₁)) (D.⋆IdL _ ∙ (sym $ F⟪-×c⟫.×β₂)))

    preservesProvidedBinProductsWith→preservesCartNatTrans :
      Σ[ swap ∈ NatIso (F ∘F -×c.×aF) (-×Fc.×aF ∘F F)]
      (∀ Γ → (swap .trans ⟦ Γ ⟧ D.⋆ -×Fc.π₁) ≡ F ⟪ -×c.π₁ ⟫)
    preservesProvidedBinProductsWith→preservesCartNatTrans = preservesProvidedBinProductsWith→NatIso
      , (λ Γ → -×Fc.×β₁)

module _ (C : Category ℓ ℓ') where
  private
    Cop = C ^op

  BinCoProduct : ∀ (cc' : (C ⊗ C) .ob) → Type _
  BinCoProduct cc' = BinProduct Cop cc'

  BinCoProducts : Type _
  BinCoProducts = BinProducts Cop

  module _ (c : C .ob) where
    BinCoProductsWith : Type (ℓ-max ℓ ℓ')
    BinCoProductsWith = BinProductsWith Cop c

    BinCoProducts→BinCoProductsWith : BinCoProducts → BinCoProductsWith
    BinCoProducts→BinCoProductsWith = BinProducts→BinProductsWith Cop c

  module _ (bcp : BinCoProducts) where
    BinCoProductF : Functor (C R.×C C) C
    BinCoProductF =
      fromOpOp ∘F (BinProductF Cop bcp ^opF) ∘F R.×-op-commute⁻
      ∘F R.rec C C (R.ηBif ((C ^op) ^op) ((C ^op) ^op) ∘Flr (toOpOp , toOpOp))

    BinCoProductBif : Bifunctor C C C
    BinCoProductBif =
      fromOpOp
      ∘Fb ((BinProductBif Cop bcp ^opBif) ∘Flr (toOpOp , toOpOp))

    BinCoProductF' : Functor (C ×C C) C
    BinCoProductF' = fromOpOp ∘F (BinProductF' Cop bcp ^opF)
      ∘F (((Fst C C ^opF) ,F (Snd C C ^opF)) ^opF) ∘F toOpOp

  module _ {a} (bcp : BinCoProductsWith a) where
    BinCoProductWithF : Functor C C
    BinCoProductWithF = fromOpOp ∘F (BinProductWithF Cop bcp ^opF) ∘F toOpOp

module _ {ℓ ℓ'} where
  module BinCoProductNotation {C : Category ℓ ℓ'} {a b} (bcp : BinCoProduct C (a , b)) =
    BinProductNotation bcp renaming
        (π₁ to σ₁ ; π₂ to σ₂ ; _,p_ to [_,p_] ; ⟨_⟩,p⟨_⟩ to [⟨_⟩,p⟨_⟩] ; module ×ue to +ue ;
        ,p-extensionality to [-,p-]-extensionality ; ,p≡ to [-,p-]≡ ; ×β₁ to +β₁ ; ×β₂ to +β₂)

  module BinCoProductsNotation {C : Category ℓ ℓ'} (bcp : BinCoProducts C) where
    private
      module bp' = BinProductsNotation bcp using (_×_ ; ×F' ; ×Bif ; ×F ; _×p_)
      module bp = bp' renaming
        (_×_ to _+_ ; ×F' to +F' ; ×Bif to +Bif ; ×F to +F ; _×p_ to _+p_)
    open bp public
    module _ {a b : C .ob} where
      open BinCoProductNotation (bcp (a , b)) hiding (vert; module +ue) public

module _ (C : Category ℓ ℓ') where
  private
    module C = Category C
  module _ (bp : BinProducts C) where
    private
      module bp = BinProductsNotation bp
    module _ {a b c d : C.ob} (f : CatIso C a c) (g : CatIso C b d) where
      private
        module -×b = BinProductsWithNotation (BinProducts→BinProductsWith C b bp)
        module c×- = BinProductsWithNotation
          (BinProducts→BinProductsWith C c (λ (x , y) → SwapBinProduct C (bp (y , x))))
      ×Iso : CatIso C (a bp.× b) (c bp.× d)
      ×Iso = ⋆Iso (preserveIsosF {F = -×b.×aF} f) (preserveIsosF {F = c×-.×aF} g)
