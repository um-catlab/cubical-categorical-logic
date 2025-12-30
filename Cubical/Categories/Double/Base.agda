module Cubical.Categories.Double.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More
import Cubical.Data.Equality as Eq
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
-- import Cubical.Categories.LocallySmall.Category.Base as LS
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Coend
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.Tensor
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Displayed.Base

private
  variable
    ℓC ℓV ℓH : Level

record DoubleCategory ℓC ℓH ℓV ℓS :
  Type (ℓ-max (ℓ-suc (ℓ-max (ℓ-max ℓC ℓS) ℓH)) (ℓ-suc ℓV))
  where
  no-eta-equality
  field
    ob : Type ℓC

    Homⱽ[_,_] : (x y : ob) → Type ℓV
    idⱽ   : ∀ {x} → Homⱽ[ x , x ]
    _⋆ⱽ_  : ∀ {x y z} (f : Homⱽ[ x , y ]) (g : Homⱽ[ y , z ]) → Homⱽ[ x , z ]
    ⋆ⱽIdL : ∀ {x y} (f : Homⱽ[ x , y ]) → idⱽ ⋆ⱽ f ≡ f
    ⋆ⱽIdR : ∀ {x y} (f : Homⱽ[ x , y ]) → f ⋆ⱽ idⱽ ≡ f
    ⋆ⱽAssoc : ∀ {x y z w} (f : Homⱽ[ x , y ]) (g : Homⱽ[ y , z ]) (h : Homⱽ[ z , w ])
           → (f ⋆ⱽ g) ⋆ⱽ h ≡ f ⋆ⱽ (g ⋆ⱽ h)
    -- isSetHomⱽ : ∀ {x y} → isSet Homⱽ[ x , y ]

    Homᴴ-ℓ : (x y : ob) → Level
    Homᴴ[_,_] : (x y : ob) → Type (Homᴴ-ℓ x y)
  --   idᴴ   : ∀ {x} → Homᴴ[ x , x ]
  --   _⋆ᴴ_  : ∀ {x y z} (f : Homᴴ[ x , y ]) (g : Homᴴ[ y , z ]) →
  --     Homᴴ[ x , z ]
  --   ⋆ᴴIdL : ∀ {x y} (f : Homᴴ[ x , y ]) → idᴴ ⋆ᴴ f ≡ f
  --   ⋆ᴴIdR : ∀ {x y} (f : Homᴴ[ x , y ]) → f ⋆ᴴ idᴴ ≡ f
  --   ⋆ᴴAssoc : ∀ {x y z w}
  --     (f : Homᴴ[ x , y ]) (g : Homᴴ[ y , z ]) (h : Homᴴ[ z , w ])
  --          → (f ⋆ᴴ g) ⋆ᴴ h ≡ f ⋆ᴴ (g ⋆ᴴ h)
  --   isSetHomᴴ : ∀ {x y} → isSet Homᴴ[ x , y ]

  -- infixr 9 _⋆ᴴ_
  -- infixr 9 _⋆ⱽ_

  -- field
  --   Sq : ∀ {x y z w} → Homᴴ[ x , y ] → Homᴴ[ z , w ] → Homⱽ[ x , z ] → Homⱽ[ y , w ] → Type ℓS

  --   idⱽSq : ∀ {x y} → {h : Homᴴ[ x , y ]} → Sq h h idⱽ idⱽ
  --   idᴴSq : ∀ {x y} → {v : Homⱽ[ x , y ]} → Sq idᴴ idᴴ v v

  --   _⋆ⱽSq_ : ∀ {l1 r1 l2 r2 l3 r3}
  --       {↑f : Homᴴ[ l1 , r1 ]} {←f : Homⱽ[ l1 , l2 ]} {↓f : Homᴴ[ l2 , r2 ]}
  --       {→f : Homⱽ[ r1 , r2 ]} {←f' : Homⱽ[ l2 , l3 ]} {↓f' : Homᴴ[ l3 , r3 ]} {→f' : Homⱽ[ r2 , r3 ]} →
  --     Sq ↑f ↓f ←f →f →
  --     Sq ↓f ↓f' ←f' →f' →
  --     Sq ↑f ↓f' (←f ⋆ⱽ ←f') (→f ⋆ⱽ →f')

  --   ⋆ⱽIdLSq : ∀ {u1 u2 d1 d2}
  --       {↑f : Homᴴ[ u1 , u2 ]} {←f : Homⱽ[ u1 , d1 ]} {↓f : Homᴴ[ d1 , d2 ]} {→f : Homⱽ[ u2 , d2 ]} →
  --       (α : Sq ↑f ↓f ←f →f) →
  --       PathP (λ i → Sq ↑f ↓f (⋆ⱽIdL ←f i) (⋆ⱽIdL →f i)) (idⱽSq ⋆ⱽSq α) α

  --   ⋆ⱽIdRSq : ∀ {u1 u2 d1 d2}
  --       {↑f : Homᴴ[ u1 , u2 ]} {←f : Homⱽ[ u1 , d1 ]} {↓f : Homᴴ[ d1 , d2 ]} {→f : Homⱽ[ u2 , d2 ]} →
  --       (α : Sq ↑f ↓f ←f →f) →
  --       PathP (λ i → Sq ↑f ↓f (⋆ⱽIdR ←f i) (⋆ⱽIdR →f i)) (α ⋆ⱽSq idⱽSq) α

  --   _⋆ᴴSq_ : ∀ {u1 u2 d1 d2 u3 d3}
  --       {↑f : Homᴴ[ u1 , u2 ]} {←f : Homⱽ[ u1 , d1 ]} {↓f : Homᴴ[ d1 , d2 ]} {→f : Homⱽ[ u2 , d2 ]}
  --       {↑f' : Homᴴ[ u2 , u3 ]} {↓f' : Homᴴ[ d2 , d3 ]} {→f' : Homⱽ[ u3 , d3 ]} →
  --     Sq ↑f ↓f ←f →f →
  --     Sq ↑f' ↓f' →f →f' →
  --     Sq (↑f ⋆ᴴ ↑f') (↓f ⋆ᴴ ↓f') ←f →f'

  --   ⋆ᴴIdLSq : ∀ {u1 u2 d1 d2}
  --       {↑f : Homᴴ[ u1 , u2 ]} {←f : Homⱽ[ u1 , d1 ]} {↓f : Homᴴ[ d1 , d2 ]} {→f : Homⱽ[ u2 , d2 ]} →
  --       (α : Sq ↑f ↓f ←f →f) →
  --       PathP (λ i → Sq (⋆ᴴIdL ↑f i) (⋆ᴴIdL ↓f i) ←f →f) (idᴴSq ⋆ᴴSq α) α

  --   ⋆ᴴIdRSq : ∀ {u1 u2 d1 d2}
  --       {↑f : Homᴴ[ u1 , u2 ]} {←f : Homⱽ[ u1 , d1 ]} {↓f : Homᴴ[ d1 , d2 ]} {→f : Homⱽ[ u2 , d2 ]} →
  --       (α : Sq ↑f ↓f ←f →f) →
  --       PathP (λ i → Sq (⋆ᴴIdR ↑f i) (⋆ᴴIdR ↓f i) ←f →f) (α ⋆ᴴSq idᴴSq) α

  -- infixr 9 _⋆ᴴSq_
  -- infixr 9 _⋆ⱽSq_

  -- field
  --   ⋆ⱽAssocSq : ∀ {l1 r1 l2 r2 r3 r4 l3 l4}
  --       {↑f : Homᴴ[ l1 , r1 ]} {←f : Homⱽ[ l1 , l2 ]} {↓f : Homᴴ[ l2 , r2 ]} {→f : Homⱽ[ r1 , r2 ]}
  --       {↑f' : Homᴴ[ l3 , r3 ]} {←f' : Homⱽ[ l3 , l4 ]} {↓f' : Homᴴ[ l4 , r4 ]} {→f' : Homⱽ[ r3 , r4 ]}
  --       {←f'' : Homⱽ[ l2 , l3 ]}{→f'' : Homⱽ[ r2 , r3 ]} →
  --       (α : Sq ↑f ↓f ←f →f) → (β : Sq ↓f ↑f' ←f'' →f'') → (γ : Sq ↑f' ↓f' ←f' →f') →
  --       PathP (λ i → Sq ↑f ↓f' (⋆ⱽAssoc ←f ←f'' ←f' i) (⋆ⱽAssoc →f →f'' →f' i))
  --         ((α ⋆ⱽSq β) ⋆ⱽSq γ) (α ⋆ⱽSq (β ⋆ⱽSq γ))

  --   ⋆ᴴAssocSq : ∀ {u1 u2 d1 d2 u4 d3 u3 d4}
  --       {↑f : Homᴴ[ u1 , u2 ]} {←f : Homⱽ[ u1 , d1 ]} {↓f : Homᴴ[ d1 , d2 ]} {→f : Homⱽ[ u2 , d2 ]}
  --       {↑f' : Homᴴ[ u3 , u4 ]} {←f' : Homⱽ[ u3 , d4 ]} {↓f' : Homᴴ[ d4 , d3 ]} {→f' : Homⱽ[ u4 , d3 ]}
  --       {↑f'' : Homᴴ[ u2 , u3 ]}{↓f'' : Homᴴ[ d2 , d4 ]} →
  --       (α : Sq ↑f ↓f ←f →f) → (β : Sq ↑f'' ↓f'' →f ←f') → (γ : Sq ↑f' ↓f' ←f' →f') →
  --       PathP (λ i → Sq (⋆ᴴAssoc ↑f ↑f'' ↑f' i) (⋆ᴴAssoc ↓f ↓f'' ↓f' i) ←f →f')
  --         ((α ⋆ᴴSq β) ⋆ᴴSq γ) (α ⋆ᴴSq (β ⋆ᴴSq γ))

  --   interchange : ∀ {u1 u2 u3 m1 m2 m3 d1 d2 d3}
  --       {↑f : Homᴴ[ u1 , u2 ]} {↑f' : Homᴴ[ u2 , u3 ]} {↓f : Homᴴ[ d1 , d2 ]} {↓f' : Homᴴ[ d2 , d3 ]}
  --       {←f : Homⱽ[ u1 , m1 ]} {←f' : Homⱽ[ m1 , d1 ]} {→f : Homⱽ[ u3 , m3 ]} {→f' : Homⱽ[ m3 , d3 ]}
  --       {←g : Homᴴ[ m1 , m2 ]} {↑g : Homⱽ[ u2 , m2 ]}
  --       {→g : Homᴴ[ m2 , m3 ]} {↓g : Homⱽ[ m2 , d2 ]}
  --       (ul : Sq ↑f ←g ←f ↑g) → (ur : Sq ↑f' →g ↑g →f) → (dl : Sq ←g ↓f ←f' ↓g) → (dr : Sq →g ↓f' ↓g →f') →
  --       (ul ⋆ⱽSq dl) ⋆ᴴSq (ur ⋆ⱽSq dr) ≡ (ul ⋆ᴴSq ur) ⋆ⱽSq (dl ⋆ᴴSq dr)

  -- ⟨_⟩⋆ⱽ⟨_⟩ : ∀ {x y z} {f f' : Homⱽ[ x , y ]} {g g' : Homⱽ[ y , z ]} →
  --   f ≡ f' → g ≡ g' → f ⋆ⱽ g ≡ f' ⋆ⱽ g'
  -- ⟨ f≡ ⟩⋆ⱽ⟨ g≡ ⟩ = cong₂ _⋆ⱽ_ f≡ g≡

  -- ⟨_⟩⋆ᴴ⟨_⟩ : ∀ {x y z} {f f' : Homᴴ[ x , y ]} {g g' : Homᴴ[ y , z ]} →
  --     {α α' : Homᴴ[ x , y ]} {β β' : Homᴴ[ y , z ]} →
  --     α ≡ α' → β ≡ β' → α ⋆ᴴ β ≡ α' ⋆ᴴ β'
  -- ⟨ α≡ ⟩⋆ᴴ⟨ β≡ ⟩ = cong₂ _⋆ᴴ_ α≡ β≡

-- open Bifunctor
-- -- TODO level polymorphise
-- module _ {ℓC ℓC' ℓS ℓR} {C D E : Category ℓC ℓC'}
--   where
--   seqRelator :
--     Relatoro* C ℓS D  →
--     Relatoro* D ℓR E  →
--     Relatoro* C _ E
--   seqRelator S R = ⊗-Bif ∘Flr (CurryBifunctor S , CurryBifunctor (Sym R))

-- open DoubleCategory
-- open PshHom
-- open Functor


-- -- module _
-- --   {ℓC ℓC' ℓCᴰ ℓCᴰ' ℓP}
-- --   {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (P : Presheaf C ℓP)
-- --   where

-- module _ {ℓC ℓC' ℓS} where
--   PROF : DoubleCategory _ _ _ _
--   PROF .ob = Category ℓC ℓC'
--   PROF .Homⱽ[_,_] = Functor
--   PROF .idⱽ = Id
--   PROF ._⋆ⱽ_ G F = F ∘F G
--   PROF .⋆ⱽIdL _ = F-lUnit
--   PROF .⋆ⱽIdR _ = F-rUnit
--   PROF .⋆ⱽAssoc _ _ _ = F-assoc
--   PROF .Homᴴ[_,_] C D = Relatoro* C (ℓ-max (ℓ-max ℓC ℓC') ℓS) D
--   PROF .idᴴ {x = C} = {!HomBif C!}
--   -- compF (LiftF {ℓ = ℓC'} {ℓ' = ℓ-max ℓC ℓS}) (HomBif C)
--   PROF ._⋆ᴴ_ S R = seqRelator S R
--   -- TODO show these are iso then use univalence
--   PROF .⋆ᴴIdL S = {!!}
--   PROF .⋆ᴴIdR S = {!!}
--   PROF .⋆ᴴAssoc = {!!}
--   PROF .isSetHomᴴ = {!!}
--   PROF .Sq S R F G = RelatorHom S (R ∘Flr ((F ^opF) , G))
--   PROF .idⱽSq = eqToPshHom _ Eq.refl Eq.refl
--   PROF .idᴴSq {v = F} = {!!}
--     -- mkRelatorHom (λ c d z → lift (F .Functor.F-hom (z .lower)))
--     --   (λ _ _ _ _ _ → cong lift (F .F-seq _ _))
--     --   (λ _ _ _ _ _ → cong lift (F .F-seq _ _))
--   PROF ._⋆ⱽSq_ {↑f = ↑f} {→f = →f} {↓f' = ↓f'} {→f' = →f'} α β =
--     {!!}
--     -- mkRelatorHom (λ c d z → β .N-ob _ (α .N-ob (c , d) z))
--     --   (λ c c' d f p →
--     --     cong (β .N-ob _) (cong (α .N-ob (c , d)) (funExt⁻ (↑f .Bif-L×-agree f) p ) ∙ α .N-hom _ _ _ _)
--     --     ∙ β .N-hom _ _ _ _
--     --     ∙ funExt⁻ (cong₂ (↓f' .Bif-hom×) refl (cong (→f' .F-hom) (→f .F-id) ∙ →f' .F-id)) _
--     --     ∙ (sym $ funExt⁻ (↓f' .Bif-L×-agree _) _))
--     --   {!!}
--   PROF .⋆ⱽIdLSq α = {!!}
--   PROF .⋆ⱽIdRSq = {!!}
--   PROF ._⋆ᴴSq_ = {!!}
--   PROF .⋆ᴴIdLSq = {!!}
--   PROF .⋆ᴴIdRSq = {!!}
--   PROF .⋆ⱽAssocSq = {!!}
--   PROF .⋆ᴴAssocSq = {!!}
--   PROF .interchange = {!!}

-- -- -- module _ {ℓC ℓC'} where
-- -- --   CAT : 2Category _ _ _
-- -- --   CAT .ob = GroupoidObjectsCategory ℓC ℓC'
-- -- --   CAT .Hom₁[_,_] C D = Functor (C .cat) (D .cat)
-- -- --   CAT .Hom₂[_,_] = NatTrans
-- -- --   CAT .id₁ = Id
-- -- --   CAT .id₂ = idTrans _
-- -- --   CAT ._⋆₁_ F G = G ∘F F
-- -- --   CAT ._⋆ⱽ_ = seqTrans
-- -- --   CAT ._⋆ᴴ_ α β = whiskerTrans β α
-- -- --   CAT .⋆₁IdL F = F-lUnit
-- -- --   CAT .⋆₁IdR F = F-rUnit
-- -- --   CAT .⋆₁Assoc _ _ _ = F-assoc
-- -- --   CAT .⋆ⱽIdL {y = D} α =
-- -- --     makeNatTransPath (funExt λ _ → D.⋆IdL _ )
-- -- --     where module D = GroupoidObjectsCategory D
-- -- --   CAT .⋆ⱽIdR {y = D} α =
-- -- --     makeNatTransPath (funExt λ _ → D.⋆IdR _ )
-- -- --     where module D = GroupoidObjectsCategory D
-- -- --   CAT .⋆ⱽAssoc {y = D} _ _ _ =
-- -- --     makeNatTransPath (funExt λ _ → D.⋆Assoc _ _ _ )
-- -- --     where module D = GroupoidObjectsCategory D
-- -- --   CAT .⋆ᴴIdL {y = D} {f = F} α =
-- -- --     makeNatTransPathP _ _ (funExt λ _ → cong₂ D._⋆_ (F .F-id) refl ∙ D.⋆IdL _)
-- -- --     where module D = GroupoidObjectsCategory D
-- -- --   CAT .⋆ᴴIdR {y = D} α =
-- -- --     makeNatTransPathP _ _ (funExt λ _ → D.⋆IdR _)
-- -- --     where module D = GroupoidObjectsCategory D
-- -- --   CAT .⋆ᴴAssoc {w = D} {f = F} {g = G} {h = H} _ _ _ =
-- -- --     makeNatTransPathP _ _
-- -- --       (funExt λ _ →
-- -- --         D.⟨ H .F-seq _ _ ⟩⋆⟨ refl ⟩
-- -- --         ∙ D.⋆Assoc _ _ _
-- -- --       )
-- -- --     where module D = GroupoidObjectsCategory D
-- -- --   CAT .interchange {z = D}{k = k} α β γ δ =
-- -- --     makeNatTransPath (funExt λ _ →
-- -- --       (sym $ D.⋆Assoc _ _ _)
-- -- --       ∙ D.⟨ D.⟨ k .F-seq _ _ ⟩⋆⟨ refl ⟩
-- -- --                 ∙ D.⋆Assoc _ _ _
-- -- --                 ∙ D.⟨ refl ⟩⋆⟨ N-hom γ (N-ob β _) ⟩
-- -- --                 ∙ (sym $ D.⋆Assoc _ _ _)
-- -- --           ⟩⋆⟨ refl ⟩
-- -- --       ∙ D.⋆Assoc _ _ _)
-- -- --     where module D = GroupoidObjectsCategory D
-- -- --   CAT .isGroupoidHom₁ {y = D} = isOfHLevelFunctor 1 D.groupoid-obs
-- -- --     where module D = GroupoidObjectsCategory D
-- -- --   CAT .isSetHom₂ = isSetNatTrans

-- -- -- module _ {ℓC ℓC'} (C : Category ℓC ℓC') where
-- -- --   private
-- -- --     module C = Category C

-- -- --   Cat→2Cat : 2Category _ _ _
-- -- --   Cat→2Cat .ob = C.ob
-- -- --   Cat→2Cat .Hom₁[_,_] = C.Hom[_,_]
-- -- --   Cat→2Cat .Hom₂[_,_] f g = f ≡ g
-- -- --   Cat→2Cat .id₁ = C.id
-- -- --   Cat→2Cat .id₂ = refl
-- -- --   Cat→2Cat ._⋆₁_ = C._⋆_
-- -- --   Cat→2Cat ._⋆ⱽ_ = _∙_
-- -- --   Cat→2Cat ._⋆ᴴ_ = C.⟨_⟩⋆⟨_⟩
-- -- --   Cat→2Cat .⋆₁IdL = C.⋆IdL
-- -- --   Cat→2Cat .⋆₁IdR = C.⋆IdR
-- -- --   Cat→2Cat .⋆₁Assoc = C.⋆Assoc
-- -- --   Cat→2Cat .⋆ⱽIdL _ = C.isSetHom _ _ _ _
-- -- --   Cat→2Cat .⋆ⱽIdR _ = C.isSetHom _ _ _ _
-- -- --   Cat→2Cat .⋆ⱽAssoc _ _ _ = C.isSetHom _ _ _ _
-- -- --   Cat→2Cat .⋆ᴴIdL _ = isProp→PathP (λ _ → C.isSetHom _ _) _ _
-- -- --   Cat→2Cat .⋆ᴴIdR _ = isProp→PathP (λ _ → C.isSetHom _ _) _ _
-- -- --   Cat→2Cat .⋆ᴴAssoc _ _ _ = isProp→PathP (λ _ → C.isSetHom _ _) _ _
-- -- --   Cat→2Cat .interchange  _ _ _ _ = C.isSetHom _ _ _ _
-- -- --   Cat→2Cat .isGroupoidHom₁ = isSet→isGroupoid C.isSetHom
-- -- --   Cat→2Cat .isSetHom₂ = isSet→isGroupoid C.isSetHom _ _

-- -- -- --   Cat→2CatEq : 2Category _ _ _
-- -- -- --   Cat→2CatEq .ob = C.ob
-- -- -- --   Cat→2CatEq .Hom₁[_,_] = C.Hom[_,_]
-- -- -- --   Cat→2CatEq .Hom₂[_,_] f g = f Eq.≡ g
-- -- -- --   Cat→2CatEq .id₁ = C.id
-- -- -- --   Cat→2CatEq .id₂ = Eq.refl
-- -- -- --   Cat→2CatEq ._⋆₁_ = C._⋆_
-- -- -- --   Cat→2CatEq ._⋆ⱽ_ = Eq._∙_
-- -- -- --   Cat→2CatEq ._⋆ᴴ_ Eq.refl Eq.refl = Eq.refl
-- -- -- --   Cat→2CatEq .⋆₁IdL = C.⋆IdL
-- -- -- --   Cat→2CatEq .⋆₁IdR = C.⋆IdR
-- -- -- --   Cat→2CatEq .⋆₁Assoc = C.⋆Assoc
-- -- -- --   Cat→2CatEq .⋆ⱽIdL _ = refl
-- -- -- --   Cat→2CatEq .⋆ⱽIdR Eq.refl = refl
-- -- -- --   Cat→2CatEq .⋆ⱽAssoc Eq.refl Eq.refl Eq.refl = refl
-- -- -- --   Cat→2CatEq .interchange Eq.refl Eq.refl Eq.refl Eq.refl = refl
-- -- -- --   Cat→2CatEq .isGroupoidHom₁ = isSet→isGroupoid C.isSetHom
-- -- -- --   Cat→2CatEq .isSetHom₂ = isSetRetract Eq.eqToPath Eq.pathToEq
-- -- -- --     Eq.pathToEq-eqToPath (isSet→isGroupoid C.isSetHom _ _)

-- -- -- module _ {ℓC ℓC' ℓC''} (C : 2Category ℓC ℓC' ℓC'') where
-- -- --   private
-- -- --     module C = 2Category C
-- -- --   _^op2 : 2Category ℓC ℓC' ℓC''
-- -- --   _^op2 .ob = C.ob
-- -- --   _^op2 .Hom₁[_,_] x y = C.Hom₁[ y , x ]
-- -- --   _^op2 .Hom₂[_,_] f g = C.Hom₂[ g , f ]
-- -- --   _^op2 .id₁ = C.id₁
-- -- --   _^op2 .id₂ = C.id₂
-- -- --   _^op2 ._⋆₁_ = λ f g → g C.⋆₁ f
-- -- --   _^op2 ._⋆ⱽ_ = λ z z₁ → z₁ C.⋆ⱽ z
-- -- --   _^op2 ._⋆ᴴ_ = λ z₁ z₂ → z₂ C.⋆ᴴ z₁
-- -- --   _^op2 .⋆₁IdL = C.⋆₁IdR
-- -- --   _^op2 .⋆₁IdR = C.⋆₁IdL
-- -- --   _^op2 .⋆₁Assoc _ _ _ = sym $ C.⋆₁Assoc _ _ _
-- -- --   _^op2 .⋆ⱽIdL = C.⋆ⱽIdR
-- -- --   _^op2 .⋆ⱽIdR = C.⋆ⱽIdL
-- -- --   _^op2 .⋆ⱽAssoc _ _ _ = sym $ C.⋆ⱽAssoc _ _ _
-- -- --   _^op2 .⋆ᴴIdL = C.⋆ᴴIdR
-- -- --   _^op2 .⋆ᴴIdR = C.⋆ᴴIdL
-- -- --   _^op2 .⋆ᴴAssoc _ _ _ = symP $ C.⋆ᴴAssoc _ _ _
-- -- --   _^op2 .interchange = λ α β γ δ → C.interchange δ γ β α
-- -- --   _^op2 .isGroupoidHom₁ = C.isGroupoidHom₁
-- -- --   _^op2 .isSetHom₂ = C.isSetHom₂
