module Cubical.Categories.Instances.SynId where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Functions.FunExtEquiv
private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓ : Level

module _ (C : Category ℓC ℓC') where
  private
    module C = Category C
  data Hom+Id : C.ob → C.ob → Type (ℓ-max ℓC ℓC') where
    synId : ∀ {x} → Hom+Id x x
    semHom : ∀ {x y} → (f : C [ x , y ]) → Hom+Id x y
    syn≡sem : ∀ {x} → synId {x = x} ≡ semHom C.id
    isSetHom+Id : ∀ {x y} → isSet (Hom+Id x y)

  ⋆Hom+Id-elim' : ∀ x {M : ∀ y (f : Hom+Id x y) → Type ℓ}
    (isSetM : ∀ y (f : Hom+Id x y) → isSet (M y f))
    (synIdCase : M x synId)
    (semHomCase : ∀ y (f : C [ x , y ]) → M y (semHom f))
    (syn≡semCase : PathP (λ i → M x (syn≡sem i)) synIdCase (semHomCase x C.id))
    → ∀ y (f : Hom+Id x y) → M y f
  ⋆Hom+Id-elim' x isSetM synIdCase semHomCase syn≡semCase y synId = synIdCase
  ⋆Hom+Id-elim' x isSetM synIdCase semHomCase syn≡semCase y (semHom f) = semHomCase y f
  ⋆Hom+Id-elim' x isSetM synIdCase semHomCase syn≡semCase y (syn≡sem i) = syn≡semCase i
  ⋆Hom+Id-elim' x isSetM synIdCase semHomCase syn≡semCase y (isSetHom+Id f f₁ x₁ y₁ i i₁) = {!!}

  ⋆Hom+Id-elimProp : ∀ x {M : ∀ y (f : Hom+Id x y) → Type ℓ}
    (isSetM : ∀ y (f : Hom+Id x y) → isProp (M y f))
    (synIdCase : M x synId)
    (semHomCase : ∀ y (f : C [ x , y ]) → M y (semHom f))
    → ∀ y (f : Hom+Id x y) → M y f
  ⋆Hom+Id-elimProp x isSetM synIdCase semHomCase = ⋆Hom+Id-elim' x (λ y f → isProp→isSet (isSetM y f)) synIdCase semHomCase
    (isProp→PathP (λ i → isSetM x (syn≡sem i)) synIdCase (semHomCase x C.id))

  ⋆Hom+Id : ∀ x y (f : Hom+Id x y) → ∀ z → (g : Hom+Id y z) → Hom+Id x z
  ⋆Hom+Id x = ⋆Hom+Id-elim' x (λ y f → isSetΠ (λ _ → isSet→ isSetHom+Id))
    (λ z g → g)
    (λ y f → ⋆Hom+Id-elim' y (λ z g → isSetHom+Id) (semHom f) (λ z g → semHom (f C.⋆ g))
      (λ i → semHom (C.⋆IdR f (~ i))))
    (funExt₂ (⋆Hom+Id-elimProp x (λ y f → isSetHom+Id f _)
      syn≡sem
      λ y f i → semHom (C.⋆IdL f (~ i))))

  ⋆Hom+IdR : ∀ x y (f : Hom+Id x y) → ⋆Hom+Id x y f y synId ≡ f
  ⋆Hom+IdR x = ⋆Hom+Id-elimProp x {!!} refl (λ y f → refl)
  
  ⋆Hom+IdAssoc : ∀ x y (f : Hom+Id x y) z (g : Hom+Id y z) w (h : Hom+Id z w) →
      ⋆Hom+Id x z (⋆Hom+Id x y f z g) w h ≡
      ⋆Hom+Id x y f w (⋆Hom+Id y z g w h)
  ⋆Hom+IdAssoc x = ⋆Hom+Id-elimProp x {!!}
    (λ z g w h → refl)
    (λ y f → ⋆Hom+Id-elimProp y {!!}
      (λ _ _ → refl)
      (λ z g → ⋆Hom+Id-elimProp z {!!}
      refl (λ w h → λ i → semHom (C.⋆Assoc f g h i))))

  Cat+SynId : Category ℓC (ℓ-max ℓC ℓC')
  Cat+SynId .Category.ob = C.ob
  Cat+SynId .Category.Hom[_,_] = Hom+Id
  Cat+SynId .Category.id = synId
  Cat+SynId .Category._⋆_ = λ f g → ⋆Hom+Id _ _ f _ g
  Cat+SynId .Category.⋆IdL f = refl
  Cat+SynId .Category.⋆IdR = ⋆Hom+IdR _ _
  Cat+SynId .Category.⋆Assoc f g h = ⋆Hom+IdAssoc _ _ f _ g _ h
  Cat+SynId .Category.isSetHom = isSetHom+Id

  Hom+Id→Hom : ∀ x y (f : Hom+Id x y) → C [ x , y ]
  Hom+Id→Hom x = ⋆Hom+Id-elim' x (λ _ _ → C.isSetHom) C.id (λ y f → f) refl

  Hom+Id→Hom-seq : ∀ x y (f : Hom+Id x y) z (g : Hom+Id y z)
    → Hom+Id→Hom x z (⋆Hom+Id _ _ f _ g) ≡ (Hom+Id→Hom _ _ f C.⋆ Hom+Id→Hom _ _ g)
  Hom+Id→Hom-seq x = ⋆Hom+Id-elimProp x {!!}
    (λ _ _ → sym $ C.⋆IdL _)
    λ y f → ⋆Hom+Id-elimProp y {!!}
    (sym $ C.⋆IdR _)
    (λ z g → refl)

  π : Functor Cat+SynId C
  π .Functor.F-ob = λ z → z
  π .Functor.F-hom = Hom+Id→Hom _ _
  π .Functor.F-id = refl
  π .Functor.F-seq f g = Hom+Id→Hom-seq _ _ f _ g

  module _ {D : Category ℓD ℓD'} (F : Functor C D) where
    private
      module D = Category D
    recF-hom : ∀ x y (f : Cat+SynId [ x , y ]) → D [ F ⟅ x ⟆ , F ⟅ y ⟆ ]
    recF-hom x = ⋆Hom+Id-elim' x (λ y f → D.isSetHom) D.id (λ y → F .Functor.F-hom) (sym $ F .Functor.F-id)

    rec : Functor Cat+SynId D
    rec .Functor.F-ob = F .Functor.F-ob
    rec .Functor.F-hom = recF-hom _ _
    rec .Functor.F-id = refl
    rec .Functor.F-seq = {!!}

Bifunctor : (C : Category ℓC ℓC')(D : Category ℓD ℓD') (E : Category ℓE ℓE') → Type _
Bifunctor C D = Functor (Cat+SynId C ×C Cat+SynId D)

-- Natural Transformation From F to G (C → D)
--
-- two functors and a natural transformation between them should be a functor C × I → D
--
-- (c , 0) → F c
-- (c , 1) → G c
-- (f , id0) -> F f
-- (f , line) -> α f
-- (f , id1) -> G f
record NatTrans {C : Category ℓC ℓC'}{D : Category ℓD ℓD'} (F G : Functor C D) : Type
  (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
  where
  private
    module C = Category C
    module D = Category D
  field
    N-mor : ∀ {x y} (f : C [ x , y ]) → D [ F ⟅ x ⟆ , G ⟅ y ⟆ ]
    N-natL : ∀ {x y z} (f : C [ x , y ]) (g : C [ y , z ]) → (F ⟪ f ⟫ D.⋆ N-mor g) ≡ N-mor (f C.⋆ g)
    N-natR : ∀ {x y z} (f : C [ x , y ]) (g : C [ y , z ]) → (N-mor f D.⋆ G ⟪ g ⟫) ≡ N-mor (f C.⋆ g)

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'} where
  private
    module C = Category C
    module D = Category D
  module _ {F : Functor C D} where
    idNT : NatTrans F F
    idNT .NatTrans.N-mor = F .Functor.F-hom
    idNT .NatTrans.N-natL = {!!}
    idNT .NatTrans.N-natR = {!!}
  module _ {F G H : Functor C D} where
    _⋆NT_ : NatTrans F G → NatTrans G H → NatTrans F H
    (α ⋆NT β) .NatTrans.N-mor = λ f → α .NatTrans.N-mor C.id D.⋆ β .NatTrans.N-mor f
    (α ⋆NT β) .NatTrans.N-natL = {!!}
    (α ⋆NT β) .NatTrans.N-natR = {!!}

module _ (C : Category ℓC ℓC')(D : Category ℓD ℓD') where
  private
    module C = Category C
    module D = Category D
  FUNCTOR : Category (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD') (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD')
  FUNCTOR .Category.ob = Functor C D
  FUNCTOR .Category.Hom[_,_] = NatTrans
  FUNCTOR .Category.id = idNT
  FUNCTOR .Category._⋆_ = _⋆NT_
  FUNCTOR .Category.⋆IdL = {!!}
  FUNCTOR .Category.⋆IdR = {!!}
  FUNCTOR .Category.⋆Assoc = {!!}
  FUNCTOR .Category.isSetHom = {!!}


module _ (C : Category ℓC ℓC')(D : Category ℓD ℓD') where
  RedundFUNCTOR : Category (ℓ-max (ℓ-max (ℓ-max ℓC (ℓ-max ℓC ℓC')) ℓD) ℓD') (ℓ-max (ℓ-max (ℓ-max ℓC (ℓ-max ℓC ℓC')) ℓD) ℓD')
  RedundFUNCTOR = FUNCTOR (Cat+SynId C) D

-- CurryBifunctor : 

-- Homomorphism of profunctors
RedundNatTrans : {C : Category ℓC ℓC'}{D : Category ℓD ℓD'} (F G : Functor C D) → Type _
RedundNatTrans {C = C}{D = D} F G = NatTrans (rec C F) (rec C G)
