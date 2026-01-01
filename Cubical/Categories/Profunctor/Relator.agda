-- | A Relator contravariant in C and covariant in D is
-- | a bifunctor C ^op , D → Set.

-- | This is equivalent to a functor D → Psh(C), but some concepts are
-- | more naturally formulated in these terms.

-- | Furthermore, we use the Redundant definition of Bifunctors,
-- | whereas the category of presheaves as defined currently in the
-- | library only gives the "separate" functorial action. In practice,
-- | relators tend to only come with a separate action anyway (e.g.,
-- | Hom) but in principle a relator carries more information
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Profunctor.Relator where

open import Cubical.Reflection.RecordEquiv

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor as Bif
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Constructions.BinProduct as BP
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functors.More
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Data.Sigma

open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Instances.Functors.More

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓP ℓQ ℓS ℓR : Level

open Category
open Bifunctor

_o-[_]-*_ : (C : Category ℓC ℓC') → ∀ ℓS → (D : Category ℓD ℓD') → Type _
C o-[ ℓS ]-* D = Bifunctor (C ^op) D (SET ℓS)

_*-[_]-o_ : (C : Category ℓC ℓC') → ∀ ℓS → (D : Category ℓD ℓD') → Type _
C *-[ ℓS ]-o D = Bifunctor C (D ^op) (SET ℓS)

Relatoro* : (C : Category ℓC ℓC') → ∀ ℓS → (D : Category ℓD ℓD') → Type _
Relatoro* C ℓS D = C o-[ ℓS ]-* D

module RelatorNotation
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  (R : C o-[ ℓR ]-* D)
  where
  private
    module C = Category C
    module D = Category D
    variable
      x x' x'' x''' : C.ob
      y y' y'' y''' : D.ob
    module R = Bifunctor R
    -- ⋆IdLᶜᵖ
  Het[_,_] : (x : C.ob) (y : D.ob) → Type _
  Het[ x , y ] = ⟨ R.Bif-ob x y  ⟩

  _⋆ʳᶜ_ : (h : Het[ x , y ])(g : D [ y , y' ]) → Het[ x , y' ]
  h ⋆ʳᶜ g = R.Bif-homR _ g h
  _⋆ᶜʳ_ : (f : C [ x , x' ])(h : Het[ x' , y ]) → Het[ x , y ]
  f ⋆ᶜʳ h = R.Bif-homL f _ h

  opaque
    ⟨_⟩⋆ʳᶜ⟨_⟩ : {h h' : Het[ x , y ]}{g g' : D [ y , y' ]}
      → h ≡ h' → g ≡ g' → h ⋆ʳᶜ g ≡ h' ⋆ʳᶜ g'
    ⟨ h≡h' ⟩⋆ʳᶜ⟨ g≡g' ⟩ = cong₂ _⋆ʳᶜ_ h≡h' g≡g'

    ⟨_⟩⋆ᶜʳ⟨_⟩ : {f f' : C [ x' , x ]}{h h' : Het[ x , y ]}
      → f ≡ f' → h ≡ h' → f ⋆ᶜʳ h ≡ f' ⋆ᶜʳ h'
    ⟨ f≡f' ⟩⋆ᶜʳ⟨ h≡h' ⟩ = cong₂ _⋆ᶜʳ_ f≡f' h≡h'

    ⋆IdLᶜʳ : (h : Het[ x , y ])
      → C.id ⋆ᶜʳ h ≡ h
    ⋆IdLᶜʳ = funExt⁻ R.Bif-L-id

    ⋆IdRʳᶜ : (h : Het[ x , y ])
      → h ⋆ʳᶜ D.id ≡ h
    ⋆IdRʳᶜ = funExt⁻ R.Bif-R-id

    ⋆Assocʳᶜᶜ : (h : Het[ x , y ])(g : D [ y , y' ])(g' : D [ y' , y'' ])
      → ((h ⋆ʳᶜ g) ⋆ʳᶜ g') ≡ (h ⋆ʳᶜ (g D.⋆ g'))
    ⋆Assocʳᶜᶜ h g g' = sym $ funExt⁻ (R.Bif-R-seq g g') h

    ⋆Assocᶜᶜʳ : (f' : C [ x'' , x' ])(f : C [ x' , x ])(h : Het[ x , y ])
      → ((f' C.⋆ f) ⋆ᶜʳ h) ≡ (f' ⋆ᶜʳ (f ⋆ᶜʳ h))
    ⋆Assocᶜᶜʳ f' f h = funExt⁻ (R.Bif-L-seq f f') h

    ⋆Assocᶜʳᶜ : (f : C [ x , x' ])(h : Het[ x' , y ])(g : D [ y , y' ])
      → ((f ⋆ᶜʳ h) ⋆ʳᶜ g) ≡ (f ⋆ᶜʳ (h ⋆ʳᶜ g))
    ⋆Assocᶜʳᶜ f h g =
      funExt⁻ (R .Bif-LR-fuse f g) h
      ∙ (sym $ funExt⁻ (R .Bif-RL-fuse f g) h)
  open Bifunctor R public

  rappL : ∀ c → Presheaf (D ^op) ℓR
  rappL c = appL R c ∘F fromOpOp

module ProfunctorNotation {ℓC ℓC' ℓD ℓD' ℓR}
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  (R : Profunctor C D ℓR)
  = RelatorNotation (CurriedToBifunctorL R)

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  private
    module C = Category C
    module D = Category D
  -- TODO: this relies on definitional (C ×C D ^op) ^op ≡ (C ^op ×C D)
  Relator→Psh : (P : C o-[ ℓP ]-* D) → Presheaf (C ×C D ^op) ℓP
  Relator→Psh P = BifunctorToParFunctor P ∘F ((BP.Fst C (D ^op) ^opF) ,F recOp (BP.Snd C (D ^op)))

  RelatorHom : (P : C o-[ ℓP ]-* D) → (Q : C o-[ ℓQ ]-* D) → Type _
  RelatorHom P Q = PshHom (Relator→Psh P) (Relator→Psh Q)

  RelatorIso : (P : C o-[ ℓP ]-* D) → (Q : C o-[ ℓQ ]-* D) → Type _
  RelatorIso P Q = PshIso (Relator→Psh P) (Relator→Psh Q)

  ProfunctorHom ProfunctorIso : (P : Profunctor D C ℓP) (Q : Profunctor D C ℓQ) → Type _
  ProfunctorHom P Q = RelatorHom (CurriedToBifunctorL P) (CurriedToBifunctorL Q)
  ProfunctorIso P Q = RelatorIso (CurriedToBifunctorL P) (CurriedToBifunctorL Q)

  module _ {P : C o-[ ℓP ]-* D}{Q : C o-[ ℓQ ]-* D} where
    private
      module P = RelatorNotation P
      module Q = RelatorNotation Q
    mkRelatorHom : (N-ob : ∀ c d → P.Het[ c , d ] → Q.Het[ c , d ])
      → (N-homL : ∀ c c' d (f : C.Hom[ c , c' ])(p : P.Het[ c' , d ])
        → N-ob c d (f P.⋆ᶜʳ p) ≡ (f Q.⋆ᶜʳ N-ob c' d p))
      → (N-homR : ∀ c d d' (p : P.Het[ c , d ])(g : D.Hom[ d , d' ])
        → N-ob c d' (p P.⋆ʳᶜ g) ≡ (N-ob c d p Q.⋆ʳᶜ g))
      → RelatorHom P Q
    mkRelatorHom N-ob N-homL N-homR = pshhom (λ (c , d) → N-ob c d)
      λ (c , d) (c' , d') (f , g) p →
        cong (N-ob c d) (sym $ funExt⁻ (P.Bif-LR-fuse f g) p)
        ∙ (N-homR c d' d (f P.⋆ᶜʳ p) g
        ∙ Q.⟨ N-homL c c' d' f p ⟩⋆ʳᶜ⟨ refl ⟩)
        ∙ funExt⁻ (Q.Bif-LR-fuse f g) (N-ob c' d' p)

    open PshHom
    natL : ∀ (α : RelatorHom P Q) {c c' d} (f : C.Hom[ c , c' ])(p : P.Het[ c' , d ])
        → α .N-ob (c , d) (f P.⋆ᶜʳ p) ≡ (f Q.⋆ᶜʳ α .N-ob (c' , d) p)
    natL α {c} {c'} {d} f p =
      (cong (α .N-ob (c , d)) (funExt⁻ (P .Bif-L×-agree f) p)
      ∙ α .N-hom (c , d) (c' , d) (f , D.id) p)
      ∙ (sym $ (funExt⁻ (Q .Bif-L×-agree f) _))

    natR : ∀ (α : RelatorHom P Q) {c d d'} (p : P.Het[ c , d ])(g : D.Hom[ d , d' ])
      → α .N-ob (c , d') (p P.⋆ʳᶜ g) ≡ (α .N-ob (c , d) p Q.⋆ʳᶜ g)
    natR α {c}{d}{d'} p g =
      cong (α .N-ob (c , d')) (funExt⁻ (P .Bif-R×-agree g) p)
      ∙ α .N-hom (c , d') (c , d) (C.id , g) p
      ∙ (sym $ funExt⁻ (Q .Bif-R×-agree g) _)

    appL-Hom : RelatorHom P Q → ∀ c → PshHom (P.rappL c) (Q.rappL c)
    appL-Hom α c .N-ob d = α .N-ob (c , d)
    appL-Hom α c .N-hom _ _ f p = natR α p f

    -- is there a way to get this for free from appL-Hom?
    appR-Hom : RelatorHom P Q → ∀ d → PshHom (appR P d) (appR Q d)
    appR-Hom α d .N-ob c = α .N-ob (c , d)
    appR-Hom α d .N-hom _ _ = natL α
  module _ {P : C o-[ ℓP ]-* D}{Q : C o-[ ℓQ ]-* D} where
    private
      module P = RelatorNotation P
      module Q = RelatorNotation Q
    open PshHom
    open PshIso
    appL-Iso : RelatorIso P Q → ∀ c → PshIso (P.rappL c) (Q.rappL c)
    appL-Iso α c = pshiso (appL-Hom (α .trans) c)
      (λ d → (α .nIso (c , d) .fst) ,
        ( α .nIso (c , d) .snd .fst
        , α .nIso (c , d) .snd .snd))
    appR-Iso : RelatorIso P Q → ∀ c → PshIso (appR P c) (appR Q c)
    appR-Iso α d = pshiso (appR-Hom (α .trans) d)
      (λ c → α .nIso (c , d) .fst , α .nIso (c , d) .snd .fst , α .nIso (c , d) .snd .snd)

  module _ {P : Profunctor D C ℓP}{Q : Profunctor D C ℓQ} where
    app-ProfHom : ProfunctorHom P Q → ∀ x → PshHom (P ⟅ x ⟆) (Q ⟅ x ⟆)
    app-ProfHom α x = pshhom (λ c → α .PshHom.N-ob (c , x)) (λ c c' f p → natL α f p)

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {ℓR} where
  _[_,_]R : (R : C o-[ ℓR ]-* D) → C .ob → D .ob → Type ℓR
  R [ c , d ]R = ⟨ R ⟅ c , d ⟆b ⟩

  relSeqL' : ∀ (R : C o-[ ℓR ]-* D) {c' c d}
            (f : C [ c' , c ]) (r : ⟨ R ⟅ c , d ⟆b ⟩)
          → ⟨ R ⟅ c' , d ⟆b ⟩
  relSeqL' R f r = (R ⟪ f ⟫l) r

  infixr 15 relSeqL'
  syntax relSeqL' R f r = f ⋆l⟨ R ⟩ r

  relSeqLId : ∀ (R : C o-[ ℓR ]-* D) {c d}
            (r : ⟨ R ⟅ c , d ⟆b ⟩)
          → C .id ⋆l⟨ R ⟩ r ≡ r
  relSeqLId R = funExt⁻ (R .Bif-L-id)

  profAssocL : ∀ (R : C o-[ ℓR ]-* D) {c'' c' c d}
    (f' : C [ c'' , c' ])
    (f : C [ c' , c ])
    (r : R [ c , d ]R)
    → ((f' ⋆⟨ C ⟩ f) ⋆l⟨ R ⟩ r) ≡ f' ⋆l⟨ R ⟩ f ⋆l⟨ R ⟩ r
  profAssocL R f' f = funExt⁻ (R .Bif-L-seq _ _)

  relSeqR' : ∀ (R : C o-[ ℓR ]-* D) {c d d'}
            (r : ⟨ R ⟅ c , d ⟆b ⟩) (g : D [ d , d' ])
          → ⟨ R ⟅ c , d' ⟆b ⟩
  relSeqR' R r g = (R ⟪ g ⟫r) r

  infixl 15 relSeqR'
  syntax relSeqR' R r g = r ⋆r⟨ R ⟩ g

  relSeqRId : ∀ (R : C o-[ ℓR ]-* D) {c d}
            (r : ⟨ R ⟅ c , d ⟆b ⟩)
          → r ⋆r⟨ R ⟩ D .id ≡ r
  relSeqRId R = funExt⁻ (R .Bif-R-id)

  profAssocR : ∀ (R : C o-[ ℓR ]-* D) {c d d' d''}
    (r : R [ c , d ]R)
    (g : D [ d , d' ])
    (g' : D [ d' , d'' ])
    → (r ⋆r⟨ R ⟩ (g ⋆⟨ D ⟩ g')) ≡ r ⋆r⟨ R ⟩ g ⋆r⟨ R ⟩ g'
  profAssocR R r g g' = funExt⁻ (R .Bif-R-seq g g') r

  profAssocLR : ∀ (R : C o-[ ℓR ]-* D) {c' c d d'}
    → (f : C [ c' , c ]) (r : R [ c , d ]R) (g : D [ d , d' ])
    → (f ⋆l⟨ R ⟩ (r ⋆r⟨ R ⟩ g)) ≡ (f ⋆l⟨ R ⟩ r) ⋆r⟨ R ⟩ g
  profAssocLR R f r g = funExt⁻ (Bif-RL-commute R f g) r

  isSetHet : (R : C o-[ ℓR ]-* D) → ∀ c d → isSet (R [ c , d ]R)
  isSetHet R c d = (R ⟅ c , d ⟆b) .snd

module _ {C : Category ℓC ℓC'} {ℓS} {D : Category ℓD ℓD'} where
  Profunctor→Relatoro* : Profunctor C D ℓS → D o-[ ℓS ]-* C
  Profunctor→Relatoro* P = Bif.Sym (CurriedToBifunctor P)

  Profunctor→Relator*o : Profunctor C D ℓS → C *-[ ℓS ]-o D
  Profunctor→Relator*o = CurriedToBifunctor

  Profunctor→Relatoro*^op : Profunctor C D ℓS → (C ^op) o-[ ℓS ]-* (D ^op)
  Profunctor→Relatoro*^op P = CurriedToBifunctor P ∘Flr (fromOpOp , Id)

  Relator→Profunctor : D o-[ ℓS ]-* C → Profunctor C D ℓS
  Relator→Profunctor R = CurryBifunctor (Bif.Sym R)

module _ {C : Category ℓC ℓC'} (R : C o-[ ℓS ]-* C) where
  private
    module C = Category C
    module R = Bifunctor R
  -- Natural Element of a profunctor
  -- Example: A natural transformation F ⇒ G is
  -- a natural element of Hom[ F , G ]

  -- Note this is a "redundant" definition, it specifies an action on
  -- objects and an action on morphisms and asks that they agree up to
  -- Path
  record NatElt : Type (ℓ-max (ℓ-max ℓC ℓC') ℓS) where
    field
      N-ob  : (x : C.ob) → R [ x , x ]R
      -- It may be useful to include this
      N-hom× : {x y : C.ob}(f : C [ x , y ]) → R [ x , y ]R

      N-ob-hom×-agree : {x : C.ob} → N-hom× C.id ≡ N-ob x

      N-natL : {x y : C.ob}(f : C [ x , y ])
             → R.Bif-homL f y (N-ob y) ≡ N-hom× f

      N-natR : {x y : C.ob}(f : C [ x , y ])
             → N-hom× f ≡ R.Bif-homR x f (N-ob x)

    N-LR-agree : {x y : C.ob}(f : C [ x , y ])
               → R.Bif-homL f y (N-ob y) ≡ R.Bif-homR x f (N-ob x)
    N-LR-agree f = N-natL f ∙ N-natR f

    N-hom×-fuseL : {w x y : C.ob}(e : C [ w , x ])(f : C [ x , y ])
                 → R.Bif-homL e y (N-hom× f) ≡ N-hom× (e C.⋆ f)
    N-hom×-fuseL e f =
      cong (R.Bif-homL e _) (sym (N-natL f))
      ∙ sym (funExt⁻ (R.Bif-L-seq _ _) (N-ob _))
      ∙ N-natL _

    N-hom×-fuseR : {x y z : C.ob}(f : C [ x , y ])(g : C [ y , z ])
                 → R.Bif-homR x g (N-hom× f) ≡ N-hom× (f C.⋆ g)
    N-hom×-fuseR f g =
      cong (R.Bif-homR _ _) (N-natR f)
      ∙ sym (funExt⁻ (R.Bif-R-seq _ _) (N-ob _))
      ∙ sym (N-natR _)

  record NatEltUnary : Type (ℓ-max (ℓ-max ℓC ℓC') ℓS) where
    field
      N-ob : (x : C.ob) → R [ x , x ]R
      N-nat : ∀ {x y} (f : C [ x , y ])
            → (f ⋆l⟨ R ⟩ N-ob y) ≡ (N-ob x ⋆r⟨ R ⟩ f)

  open NatElt
  open NatEltUnary
  NatEltUnary→NatElt : NatEltUnary → NatElt
  NatEltUnary→NatElt neu .N-ob = neu .N-ob
  NatEltUnary→NatElt neu .N-hom× {x}{y} = λ f → f ⋆l⟨ R ⟩ neu .N-ob y
  NatEltUnary→NatElt neu .N-ob-hom×-agree = funExt⁻ R.Bif-L-id _
  NatEltUnary→NatElt neu .N-natL f = refl
  NatEltUnary→NatElt neu .N-natR f = neu .N-nat f

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
         {R : D o-[ ℓS ]-* D}
         (α : NatElt R) (F : Functor C D) where
  private
    module F = Functor F
    module α = NatElt α
  whisker : NatElt (R ∘Flr (F ^opF , F))
  whisker .NatElt.N-ob c = α.N-ob (F ⟅ c ⟆)
  whisker .NatElt.N-hom× f = α.N-hom× (F ⟪ f ⟫)
  whisker .NatElt.N-ob-hom×-agree =
    cong α.N-hom× F.F-id
    ∙ α.N-ob-hom×-agree
  whisker .NatElt.N-natL f = α.N-natL _
  whisker .NatElt.N-natR f = α.N-natR _
