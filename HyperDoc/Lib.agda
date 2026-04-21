open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to  ⊎rec ; map to ⊎map)
open import Cubical.Data.List renaming (map to lmap ; rec to lrec ; elim to lelim)
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Logic 
open import Cubical.Foundations.Powerset
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.HITs.PropositionalTruncation.Properties
open import Cubical.Relation.Binary.Preorder
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint 
open import Cubical.Categories.Category 
open import Cubical.Categories.Functor
open import Cubical.Foundations.Structure 
open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor

open Category
open Categoryᴰ
open Functor
open Functorᴰ

module HyperDoc.Lib where 


{-
-- this has to exist somewhere 
open import Cubical.Relation.Binary.Base


data RTC {ℓ : Level}{X : Type ℓ }(R : Rel X X ℓ): Rel X X ℓ where 
  base : {x y : X} → R x y → RTC R x y
  ref : {x : X} → RTC R x x 
  trans : {x y z : X} → RTC R x y → RTC R y z → RTC R x z

data RC {ℓ : Level}{X : Type ℓ }(R : Rel X X ℓ): Rel X X ℓ where 
  base : {x y : X} → R x y → RC R x y
  ref : {x : X} → RC R x x 
  -}

-- \<->
_↔_ : Type → Type → Type 
_↔_ X Y = (X → Y) × (Y → X)

_⊃⊂_ : {X : Type} → (P Q :  ℙ X) → Type
_⊃⊂_ P Q = (P ⊆ Q) × (Q ⊆ P)

levels : List Level → Level 
levels = foldr ℓ-max ℓ-zero

ℓsuc : List Level → List Level 
ℓsuc = lmap ℓ-suc

propBind : {ℓ ℓ' : Level} {A : Type ℓ}{B : Type ℓ'} → ∥ A ∥₁ → (A → ∥ B ∥₁) → ∥ B ∥₁ 
propBind M f = rec squash₁ f M

flatten : {A : Type} → ∥ ∥ A ∥₁ ∥₁ → ∥ A ∥₁ 
flatten {A} = rec squash₁ λ x → x

choice : {ℓ ℓ' : Level}{A : Type ℓ}{B : A → Type ℓ'} → 
  (safe : (a : A) → isProp (B a)) → 
  ((a : A) → ∥ ( B a) ∥₁) → 
  ∥ ((a : A) → B a) ∥₁ 
choice {A = A}{B} safe f = ∣ (λ a → rec (safe a) (λ z → z) (f a)) ∣₁

existsΣ : {ℓ ℓ' : Level}{A : Type ℓ}{B : A → Type ℓ'} → 
  (Σ[ a ∈ A ] ∥ ( B a) ∥₁) → 
  ∥ Σ[ a ∈ A ] B a ∥₁ 
existsΣ {A = A}{B} p = map (λ z → p .fst , z) (p .snd)

merge : {A B : Type} → 
  (∥ ∥ A ∥₁ ⊎ ∥ B ∥₁ ∥₁ ) → 
  ∥ A ⊎ B ∥₁  
merge {A}{B} prf = propBind prf (⊎rec (map _⊎_.inl)  (map _⊎_.inr))

propBind' : {ℓ ℓ' : Level} {A : Type ℓ}{B : Type ℓ'} → ⟨ ∥ A ∥ₚ ⟩ → (A → ⟨ ∥ B ∥ₚ ⟩ ) → ⟨ ∥ B ∥ₚ ⟩
propBind' M f = propBind M f

to^op^op : {ℓ ℓ' : Level}{C : Category ℓ ℓ'}  → Functor C (C ^op ^op) 
to^op^op .F-ob = λ z → z
to^op^op .F-hom = λ z → z
to^op^op .F-id = refl
to^op^op .F-seq _ _ = refl

from^op^op : {ℓ ℓ' : Level}{C : Category ℓ ℓ'} → Functor (C ^op ^op) C 
from^op^op .F-ob = λ z → z
from^op^op .F-hom = λ z → z
from^op^op .F-id = refl
from^op^op .F-seq _ _ = refl

from^opᴰ^opᴰ : {ℓ ℓ' ℓD ℓD' : Level}{C : Category ℓ ℓ'}{Cᴰ : Categoryᴰ C ℓD ℓD'}
  → Functorᴰ from^op^op (Cᴰ ^opᴰ ^opᴰ) Cᴰ 
from^opᴰ^opᴰ .F-obᴰ = λ z → z
from^opᴰ^opᴰ .F-homᴰ = λ z → z
from^opᴰ^opᴰ .F-idᴰ = refl
from^opᴰ^opᴰ .F-seqᴰ _ _ = refl

Cᴰ^op^op : {ℓ ℓ' ℓD ℓD' : Level}{C : Category ℓ ℓ'}
  → Categoryᴰ (C ^op ^op) ℓD ℓD'
  → Categoryᴰ C ℓD ℓD'
Cᴰ^op^op Cᴰ .ob[_] = Cᴰ .ob[_]
Cᴰ^op^op Cᴰ .Hom[_][_,_] = Cᴰ .Hom[_][_,_]
Cᴰ^op^op Cᴰ .idᴰ = Cᴰ .idᴰ
Cᴰ^op^op Cᴰ ._⋆ᴰ_ = Cᴰ ._⋆ᴰ_
Cᴰ^op^op Cᴰ .⋆IdLᴰ = Cᴰ .⋆IdLᴰ
Cᴰ^op^op Cᴰ .⋆IdRᴰ = Cᴰ .⋆IdRᴰ
Cᴰ^op^op Cᴰ .⋆Assocᴰ = Cᴰ .⋆Assocᴰ
Cᴰ^op^op Cᴰ .isSetHomᴰ = Cᴰ .isSetHomᴰ

module _ {ℓ ℓ' ℓ'' : Level}
    {B C D E : Category ℓ ℓ'}
    {F : Functor B C} {G : Functor C D} {H : Functor D E}
    where 
  open import Cubical.Categories.NaturalTransformation
  open NatTrans

  F-assocl : {F : Functor B C} {G : Functor C D} {H : Functor D E}
        →  NatTrans (H ∘F (G ∘F F)) ((H ∘F G) ∘F F)
  F-assocl .N-ob = λ x → E .id
  F-assocl .N-hom f = E .⋆IdR _ ∙ sym (E .⋆IdL _)

  F-assocr : {F : Functor B C} {G : Functor C D} {H : Functor D E}
        →  NatTrans ((H ∘F G) ∘F F) (H ∘F (G ∘F F)) 
  F-assocr .N-ob = λ x → E .id
  F-assocr .N-hom f = E .⋆IdR _ ∙ sym (E .⋆IdL _)

-- will need this again for operational stuff
module _ {ℓS : Level} where 
  data Gen {A B : hSet ℓS}(f : ⟨ A ⟩ → ⟨ B ⟩ → ⟨ B ⟩ )(P : ℙ ⟨ B ⟩) : ⟨ B ⟩ → Type ℓS where
    base  : ∀ (b) → b ∈ P → Gen f P b
    step  : ∀ (a : ⟨ A ⟩)(b : ⟨ B ⟩) → Gen {A}{B} f P b → Gen f P (f a b)


  Gen-rec :
    ∀ {A B : hSet ℓS}{ℓS' : Level} {X : Type ℓS'}{f : ⟨ A ⟩ → ⟨ B ⟩ → ⟨ B ⟩}{P : ℙ ⟨ B ⟩} →
    -- base case
    (baseC : ∀ (b) → b ∈ P → X) →
    -- step case
    (stepC : ∀ (a : ⟨ A ⟩)(b : ⟨ B ⟩) → X → X) →
    ∀ {b} → Gen {A}{B} f P b → X 
  Gen-rec baseC stepC (base b b∈P) = baseC b b∈P
  Gen-rec baseC stepC (step a b x∈Gen) = stepC a b (Gen-rec baseC stepC x∈Gen)

  Gen-elim :
    ∀ {A B : hSet ℓS}
      {f : ⟨ A ⟩ → ⟨ B ⟩ → ⟨ B ⟩}
      {P : ℙ ⟨ B ⟩}
      {ℓS' : Level} 
      (X : ∀ b → Gen{A}{B} f P b → Type ℓS') →

      -- base case
      (baseC :
        ∀ b (p : b ∈ P) →
        X b (base b p)) →

      -- step case
      (stepC :
        ∀ (a : ⟨ A ⟩)(b : ⟨ B ⟩)
          (g : Gen f P b) →
        X b g →
        X (f a b) (step a b g)) →

      ∀ b (g : Gen f P b) → X b g
  Gen-elim X baseC stepC b (base b' b'∈P ) = baseC b' b'∈P
  Gen-elim {f = f} X baseC stepC b (step a b' b'∈Gen) = stepC a b' b'∈Gen  (Gen-elim X baseC stepC b' b'∈Gen)


module AdjSyntax {ℓ ℓ' : Level} {X Y : Preorder ℓ ℓ'}{R : MonFun Y X} (adj : HasLeftAdj R) where 
  L : MonFun X Y 
  L = adj .fst 

  open MonFun

  open _⊣_ (adj .snd) 
  open Iso 
  private
    module 𝕏 = PreorderStr (X .snd)
    module 𝕐 = PreorderStr (Y .snd)
    module Xpre = IsPreorder (𝕏.isPreorder)
    module Ypre = IsPreorder (𝕐.isPreorder)

  LtoR : ∀ {x y} → L $ x 𝕐.≤ y → x 𝕏.≤ (R $ y)
  LtoR = fun adjIff

  RtoL : ∀ {x y} → x 𝕏.≤ (R $ y) → L $ x 𝕐.≤ y 
  RtoL = inv adjIff

  LMon : ∀ {x x'} →  x 𝕏.≤  x' → L $ x 𝕐.≤ (L $ x') 
  LMon = L .isMon 

  RMon : ∀ {y y'} →  y 𝕐.≤  y' → R $ y 𝕏.≤ (R $ y') 
  RMon = R .isMon 

  unit : ∀ {x} → x 𝕏.≤ (R $ (L $ x))
  unit {x} = LtoR (Ypre.is-refl (L $ x))

  counit : ∀ {y} → (L $ (R $ y)) 𝕐.≤ y
  counit {y} = RtoL (Xpre.is-refl (R $ y))

open import Cubical.Categories.Presheaf.Representable hiding (Representation)
module _ {ℓo}{ℓh}{ℓp} (C : Category ℓo ℓh) (P : Presheaf C ℓp) where
  -- Note this PshIso uses PshHom
  -- vs the one here
  -- Cubical.Categories.Presheaf.Representable
  -- uses NatIso with Lifts
  -- TODO fix?
  Representation : Type (ℓ-max (ℓ-max ℓo ℓh) ℓp)
  Representation =  Σ[ A ∈ C .ob ] PshIso (C [-, A ]) P

  reprToUniversalElement : Representation → UniversalElement C P 
  reprToUniversalElement (A , pISo) = representationToUniversalElement C P (A , PshIso→PshIsoLift  (C [-, A ]) P pISo)
