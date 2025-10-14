-- When can we define locally small functor categories? When the type
-- of natural transformations is a small type.
--   
-- Consider NatTrans F G for F, G : C → D

-- - If C is unrestricted, then this is large because C.ob is large
--   and because C.Hom[ x , y ] has no global bound

-- - If D is unrestricted then this is large because D.Hom[ F x , G x ]
--   has no *global* bound on the universe level of the Hom set.

-- So for NatTrans F G to be locally small, we need C to have a small
-- type of objects and
module Cubical.Categories.LocallySmall.NaturalTransformation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More
  using (isSet→Square)
  renaming (rectify to TypeRectify)

open import Cubical.Data.Prod using (_×ω_; _,_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Reflection.RecordEquiv.More

import Cubical.Categories.Category as Small
open import Cubical.Categories.LocallySmall.Base as LocallySmall
open import Cubical.Categories.LocallySmall.Functor
open import Cubical.Categories.LocallySmall.Variables

open Category
-- A Presheaf C ℓP is a functor C^op → hSet ℓP, not a functor C → SET, i.e.,
--   Cᵒ → SET.v[ ℓ ]

-- so each presheaf is not actually a functor C^op → SET but a choice
-- of ℓ and a functor C^op → Set ℓ (which is a small category)

-- the type of natural transformations between functors of locally
-- small categories is large because while each D.Hom[_,_] is small,
-- they can each be in a different universe, the natural
-- transformations have to be in the universe ⨆_x Hom-ℓ (F x) (G x),
-- which is ω.

-- This means we do *not* get a locally small category of functors
-- between arbitrary locally small categories, only a large category.
record LargeNatTrans {C : Category Cob CHom-ℓ}{D : Category Dob DHom-ℓ}
  (F G : Functor C D) : Typeω
  where
  no-eta-equality
  constructor natTrans
  private
    module F = FunctorNotation F
    module G = FunctorNotation G
    module C = CategoryNotation C
    module D = CategoryNotation D
  field
    N-ob : ∀ x → D.Hom[ F.F-ob x , G.F-ob x ]
    N-hom : ∀ {x y}(f : C.Hom[ x , y ])
      → (F.F-hom f D.⋆ N-ob y) ≡ (N-ob x D.⋆ G.F-hom f)

module _ {(Cob , C) : SmallCategory ℓC ℓC'} where
  record NatTrans 
    {D : GloballySmallCategory Dob ℓD'}
    (F G : Functor C D)
    : Type (ℓ-max ℓC $ ℓ-max ℓC' $ ℓD')
    where
    no-eta-equality
    constructor natTrans
    private
      module F = FunctorNotation F
      module G = FunctorNotation G
      module C = CategoryNotation C
      module D = CategoryNotation D
    field
      N-ob : ∀ x → D.Hom[ F.F-ob (liftω x) , G.F-ob (liftω x) ]
      N-hom : ∀ {x y}(f : C.Hom[ liftω x , liftω y ])
        → (F.F-hom f D.⋆ N-ob y) ≡ (N-ob x D.⋆ G.F-hom f)
open NatTrans

module _ {(Cob , C) : SmallCategory ℓC ℓC'}{D : GloballySmallCategory Dob ℓD'} where
  private
    module C = CategoryNotation C
    module D = CategoryNotation D
  idTrans : (F : Functor C D) → NatTrans F F
  idTrans F = natTrans (λ x → D.id) (λ f → D.⋆IdR _ ∙ (sym $ D.⋆IdL _))
    where module F = Functor F
  
  seqTrans :
    {F G H : Functor C D}
    (α : NatTrans F G)
    (β : NatTrans G H)
    → NatTrans F H
  seqTrans α β = natTrans
    (λ x → α .N-ob x D.⋆ β .N-ob x)
    λ f → sym (D.⋆Assoc _ _ _)
      ∙ D.⟨ α .N-hom f ⟩⋆⟨⟩
      ∙ D.⋆Assoc _ _ _
      ∙ D.⟨⟩⋆⟨ β .N-hom f ⟩
      ∙ sym (D.⋆Assoc _ _ _)

  module _ (F G : Functor C D) where
    private
      module F = Functor F
      module G = Functor G
    NatTransIsoΣ :
      Iso (NatTrans F G)
          (Σ[ N-ob ∈ (∀ x → D.Hom[ F.F-ob (liftω x) , G.F-ob (liftω x) ]) ]
            (∀ {x y}(f : C.Hom[ liftω x , liftω y ])
             → (F.F-hom f D.⋆ N-ob y) ≡ (N-ob x D.⋆ G.F-hom f)))
    unquoteDef NatTransIsoΣ = defineRecordIsoΣ NatTransIsoΣ (quote (NatTrans))

  makeNatTransPath : ∀ {F G : Functor C D}
    {α β : NatTrans F G}
    → α .N-ob ≡ β .N-ob
    → α ≡ β
  makeNatTransPath {α = α}{β} α≡β = isoFunInjective (NatTransIsoΣ _ _) α β
    (ΣPathPProp (λ _ → isPropImplicitΠ2 (λ _ _ → isPropΠ (λ _ → D.isSetHom _ _)))
    α≡β)

module _ ((Cob , C) : SmallCategory ℓC ℓC')(D : GloballySmallCategory Dob ℓD') where
  private
    module C = CategoryNotation C
    module D = CategoryNotation D
  FUNCTOR : GloballySmallCategory (Functor C D) (ℓ-max (ℓ-max ℓC ℓC') ℓD')
  FUNCTOR .Hom[_,_] F G = NatTrans F G
  FUNCTOR .Category.id = idTrans _
  FUNCTOR .Category._⋆_ = seqTrans
  FUNCTOR .Category.⋆IdL α = makeNatTransPath $ funExt λ _ → D.⋆IdL _
  FUNCTOR .Category.⋆IdR α = makeNatTransPath $ funExt λ _ → D.⋆IdR _
  FUNCTOR .Category.⋆Assoc α β γ = makeNatTransPath $ funExt λ _ →
    D.⋆Assoc (α .N-ob _) (β .N-ob _) (γ .N-ob _)
  FUNCTOR .Category.isSetHom = isSetIso (NatTransIsoΣ _ _)
    (isSetΣ
      (isSetΠ (λ _ → D.isSetHom))
      λ _ → isProp→isSet (isPropImplicitΠ2 (λ _ _ → isPropΠ (λ f → D.isSetHom _ _))))

-- record NatTransᴰ
--   {C : LocallySmallCategory Cob}{D : LocallySmallCategory Dob}
--   {Cᴰ : LocallySmallCategoryᴰ C Cobᴰ}{Dᴰ : LocallySmallCategoryᴰ D Dobᴰ}
--   {F G : Functor C D}
--   (α : NatTrans F G)
--   (Fᴰ : Functorᴰ F Cᴰ Dᴰ)(Gᴰ : Functorᴰ G Cᴰ Dᴰ) : Typeω
--   where
--   no-eta-equality
--   constructor natTransᴰ
--   private
--     module α = NatTrans α
--     module F = FunctorNotation F
--     module Fᴰ = FunctorᴰNotation Fᴰ
--     module G = FunctorNotation G
--     module Gᴰ = FunctorᴰNotation Gᴰ
--     module C = LocallySmallCategoryNotation C
--     module Cᴰ = LocallySmallCategoryᴰNotation Cᴰ
--     module D = LocallySmallCategoryNotation D
--     module Dᴰ = LocallySmallCategoryᴰNotation Dᴰ
    
--   field
--     N-obᴰ : ∀ {x}(xᴰ : Cobᴰ x) → Dᴰ.Hom[ α.N-ob x ][ Fᴰ.F-obᴰ xᴰ , Gᴰ.F-obᴰ xᴰ ]
--     N-homᴰ : ∀ {x y xᴰ yᴰ}{f : C.Hom[ x , y ]}(fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ])
--       → (Fᴰ.F-homᴰ fᴰ Dᴰ.⋆ᴰ N-obᴰ yᴰ) Dᴰ.∫≡ (N-obᴰ xᴰ Dᴰ.⋆ᴰ Gᴰ.F-homᴰ fᴰ)

