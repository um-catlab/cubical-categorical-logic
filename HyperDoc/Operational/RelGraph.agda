{-# OPTIONS --type-in-type #-}
module  HyperDoc.Operational.RelGraph  where 

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Relation.Binary.Base hiding(Rel)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum 
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Foundations.Powerset
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.HITs.PropositionalTruncation renaming (rec to hrec)
open import Cubical.Functions.Logic hiding(inl ; inr)
open import Cubical.Categories.Constructions.BinProduct
open Category
open Functor
open NatTrans
import Cubical.Data.Equality as Eq
-- Pred Lifting

Pow : Functor (SET _) (SET _) 
Pow .F-ob (X , isSetX) = (ℙ X) , isSetℙ
Pow .F-hom {X}{Y} f P y = (∃[ x ∈ ⟨ X ⟩ ] (f x ≡ y) × (x ∈ P)) , squash₁
Pow .F-id {X} = funExt λ PX → funExt λ x → 
  ⇔toPath 
    (hrec (∈-isProp PX x) λ (x , x≡ , Px) → subst (λ h → h ∈ PX) x≡ Px) 
    λ Px → ∣ x , (refl , Px) ∣₁
Pow .F-seq = {!   !}

data Shape : Type where 
  var 𝟙 : Shape
  _⊗_ _⊕_ : Shape → Shape → Shape


Const : hSet _ → Functor (SET _) (SET _) 
Const X .F-ob _ = X
Const X .F-hom = λ z z₁ → z₁
Const X .F-id = refl
Const X .F-seq _ _ = refl

ToFunctor : Shape → Functor (SET _) (SET _) 
ToFunctor var = Id
ToFunctor 𝟙 = Const (Unit , isSetUnit)
ToFunctor (s ⊗ s') .F-ob X .fst = ToFunctor s .F-ob X .fst × ToFunctor s' .F-ob X .fst
ToFunctor (s ⊗ s') .F-ob X .snd = isSet× (ToFunctor s .F-ob X .snd) (ToFunctor s' .F-ob X .snd)
ToFunctor (s ⊗ s') .F-hom f (x , y) = (ToFunctor s .F-hom f x) , ToFunctor s' .F-hom f y
ToFunctor (s ⊗ s') .F-id i (x , y) = (ToFunctor s .F-id  i x) , (ToFunctor s' .F-id i y)
ToFunctor (s ⊗ s') .F-seq f g i (x , y)= (ToFunctor s .F-seq f g i x) , (ToFunctor s' .F-seq f g i y)
ToFunctor (s ⊕ s') .F-ob X .fst = ToFunctor s .F-ob X .fst ⊎ ToFunctor s' .F-ob X .fst
ToFunctor (s ⊕ s') .F-ob X .snd = isSet⊎ (ToFunctor s .F-ob X .snd) (ToFunctor s' .F-ob X .snd)
ToFunctor (s ⊕ s') .F-hom f (inl x) = inl (ToFunctor s .F-hom f x)
ToFunctor (s ⊕ s') .F-hom f (inr x) = inr (ToFunctor s' .F-hom f x)
ToFunctor (s ⊕ s') .F-id i (inl x) = inl (ToFunctor s .F-id i x)
ToFunctor (s ⊕ s') .F-id i (inr x) = inr (ToFunctor s' .F-id i x)
ToFunctor (s ⊕ s') .F-seq f g i (inl x) = inl (ToFunctor s .F-seq f g i x)
ToFunctor (s ⊕ s') .F-seq f g i (inr x) = inr (ToFunctor s' .F-seq f g i x)

dist : (s : Shape) → NatTrans (ToFunctor s ∘F Pow) (Pow ∘F ToFunctor s) 
dist var .N-ob = λ x z → z
dist var .N-hom f = refl
dist 𝟙 .N-ob X tt tt = ⊤
dist 𝟙 .N-hom f = {!   !}
  -- yes, separate out to help agda w66
  -- funExt λ {tt → funExt λ {tt → ⇔toPath {!   !} {!   !}}}
dist (s ⊗ s') .N-ob X (a , b)(sa , sb) = dist s .N-ob  X a sa ⊓ dist s' .N-ob X b sb
dist (s ⊗ s') .N-hom {X}{Y} f = funExt λ (P , Q) → funExt λ (y , y') → 
  ⇔toPath (λ {(fst₁ , snd₁) → ∣ {!   !} ∣₁}) 
  λ x → (hrec {!   !} {!   !} x) , {!   !}
dist (s ⊕ s') .N-ob X (inl a) (inl x) = N-ob (dist s) X a x
dist (s ⊕ s') .N-ob X (inl a) (inr x) = Cubical.Functions.Logic.⊥
dist (s ⊕ s') .N-ob X (inr b) (inl x) = Cubical.Functions.Logic.⊥
dist (s ⊕ s') .N-ob X (inr b) (inr x) = N-ob (dist s') X b x
dist (s ⊕ s') .N-hom f = {!   !}

{-}
PolyToSet : {X : Type} → Poly X → Type 
PolyToSet {X} var = X
PolyToSet 𝟙 = Unit
PolyToSet (p ⊗ p') = PolyToSet p × PolyToSet p'
PolyToSet (p ⊕ p') = PolyToSet p ⊎ PolyToSet p'

PolyToFunctor : Poly (hSet _) → Functor (SET _) (SET _) 
PolyToFunctor p .F-ob X = PolyToSet {⟨ X ⟩ } {!   !} , {!   !}
PolyToFunctor p .F-hom = {!   !}
PolyToFunctor p .F-id = {!   !}
PolyToFunctor p .F-seq = {!   !}
-}

-- Relational lifting of type operators

Rel' : {ℓ : Level} → hSet ℓ → hSet ℓ → Type (ℓ-suc ℓ) 
Rel' {ℓ} X Y = ⟨ X ⟩ → ⟨ Y ⟩ → hSet ℓ

Rel : (ℓ : Level) → Type (ℓ-suc ℓ) 
Rel ℓ = 
  Σ[ (A , A') ∈ hSet ℓ × hSet ℓ ] 
   Rel' A A'


Rel≡ :{ℓ : Level}(R R' : Rel ℓ) → R .fst ≡ R' .fst → {!   !}
Rel≡ = {!   !}


idRel : {ℓ : Level} → (A : hSet ℓ) → Rel ℓ 
idRel A .fst = A , A
idRel A .snd a a' .fst = a Eq.≡ a'
idRel A .snd a a' .snd = {!   !} 

_×R_ : {ℓ : Level} → Rel ℓ  → Rel ℓ  → Rel ℓ 
(((A , A') , R ) ×R ((B , B' ) , S)) .fst = 
  (⟨ A ⟩  × ⟨ B ⟩ , isSet× (A .snd) (B .snd)) , 
  (⟨ A' ⟩ × ⟨ B' ⟩ , isSet× (A' .snd) (B' .snd))
(((A , A') , R ) ×R ((B , B' ) , S)) .snd (a , b)(a' , b') = 
  ⟨ R a a' ⟩ × ⟨ S b b' ⟩ , isSet× (R a a' .snd) (S b b' .snd)

-- identity extension principle for ×RType ℓ , {!   !}
Id× : {ℓ : Level}{A B : hSet ℓ} → idRel A ×R idRel B ≡ idRel ((⟨ A ⟩ × ⟨ B ⟩) , (isSet× (A .snd) (B .snd)))
Id× {ℓ}{A}{B} = ΣPathP (refl , funExt λ p → funExt λ p'  → ΣPathP ({! !} , {!   !}))

_+R_ : {ℓ : Level} → Rel ℓ  → Rel ℓ  → Rel ℓ 
(((A , A') , R ) +R ((B , B' ) , S)) .fst = 
  ((⟨ A ⟩ ⊎ ⟨ B ⟩) , isSet⊎ (A .snd) (B .snd)) , 
  ((⟨ A' ⟩ ⊎ ⟨ B' ⟩) , isSet⊎ (A' .snd) (B' .snd))
(((A , A') , R ) +R ((B , B' ) , S)) .snd (inl a) (inl a') = R a a'
(((A , A') , R ) +R ((B , B' ) , S)).snd (inl a) (inr b') = ⊥* , (λ())
(((A , A') , R ) +R ((B , B' ) , S)) .snd (inr b) (inl a') = ⊥* , (λ())
(((A , A') , R ) +R ((B , B' ) , S)) .snd (inr b) (inr b') = S b b'

_→R_ : {ℓ : Level} → Rel ℓ  → Rel ℓ  → Rel ℓ 
(((A , A') , R) →R ((B , B') , S)) .fst = 
  ((⟨ A ⟩ → ⟨ B ⟩) , isSet→ (B .snd)) , 
  ((⟨ A' ⟩ → ⟨ B' ⟩) , isSet→ (B' .snd))
(((A , A') , R) →R ((B , B') , S)) .snd f f' .fst = 
  (a : ⟨ A ⟩)(a' : ⟨ A' ⟩ ) → ⟨ R a a' ⟩ → ⟨ S (f a) (f' a') ⟩
(((A , A') , R) →R ((B , B') , S)) .snd f f' .snd = 
  isSetΠ2 λ a a' → isSet→ (S (f a) (f' a') .snd)

ℙR : {ℓ : Level} → Rel ℓ → Rel (ℓ-suc ℓ) 
ℙR ((A , A') , R) .fst =  ((ℙ ⟨ A ⟩) , isSetℙ) , ((ℙ ⟨ A' ⟩) , isSetℙ)
ℙR ((A , A') , R) .snd u u' =  
  (Lift ((a : ⟨ A ⟩)(a' : ⟨ A' ⟩) → ⟨ R a a' ⟩  → (a ∈ u → a' ∈ u') × (a' ∈ u' → a ∈ u))), 
  {!   !}

1R : {ℓ : Level} → Rel ℓ
1R = idRel (Unit* , isSetUnit*)

-- Relation of Groups 
Group : {ℓ : Level} → Type (ℓ-suc ℓ)
Group {ℓ } = 
  Σ[ X ∈ hSet ℓ ] 
  Σ[ _⊗_ ∈ (⟨ X ⟩ → ⟨ X ⟩ → ⟨ X ⟩) ] 
  Σ[ inv ∈ (⟨ X ⟩ → ⟨ X ⟩)  ] 
  Σ[ e ∈ ⟨ X ⟩ ] 
  ((x : ⟨ X ⟩) → e ⊗ x ≡ x) × 
  ((x : ⟨ X ⟩) → x ⊗ e ≡ x) × 
  ((x : ⟨ X ⟩) → inv x ⊗ x ≡ e) × 
  ((x y z : ⟨ X ⟩) → (x ⊗ (y ⊗ z)) ≡ ((x ⊗ y) ⊗ z))


GroupRel : {ℓ : Level} → 
  (G G' : Group {ℓ})(R : (⟨ G .fst ⟩ → ⟨ G' .fst ⟩ → hSet ℓ) ) → Type ℓ 
GroupRel {ℓ} G G' R' = eRe × ⊗R⊗' × invRinv' where 
  R : Rel ℓ 
  R .fst = (G .fst) , (G' .fst)
  R .snd = R'

  e = G .snd  .snd .snd .fst
  e' = G' .snd  .snd .snd .fst

  eRe = ⟨ R .snd  e e' ⟩

  ⊗g = G .snd  .fst
  ⊗' = G' .snd  .fst

  ⊗R⊗' = ⟨ (R →R (R →R R)) .snd ⊗g ⊗' ⟩

  inv = G .snd .snd .fst 
  inv' = G' .snd .snd .fst 
  
  invRinv' =  ⟨ (R →R R) .snd inv inv' ⟩


-- a transition system!
NA : {ℓ : Level} → Type (ℓ-suc ℓ)
NA {ℓ} = Σ[ S ∈ hSet ℓ ] (⟨ S ⟩ → ℙ ⟨ S ⟩)

DA : {ℓ : Level} → Type (ℓ-suc ℓ) 
DA {ℓ} = Σ[ S ∈ hSet ℓ ] (⟨ S ⟩ → Unit* ⊎ ⟨ S ⟩)

rel : {ℓ : Level}{X Y : hSet ℓ} → (⟨ X ⟩ → ⟨ Y ⟩ → hSet ℓ) → Rel ℓ 
rel {_}{X} {Y} R .fst .fst = X
rel {_}{X} {Y} R .fst .snd = Y
rel {_}{X} {Y} R .snd = R

_r⟨_,_⟩ :  {ℓ : Level} → (R : Rel ℓ) → R .fst .fst .fst → R .fst .snd .fst → Type ℓ  
_r⟨_,_⟩ R a b = ⟨ R .snd a b ⟩

BisimDA' : {ℓ : Level} → ((S , f)(S' , g) : DA {ℓ}) → Rel' S S' → Type ℓ 
BisimDA' {ℓ} (S , f)(S' , g) R' = (R →R (1R +R R)) r⟨ f , g ⟩ where 
  R : Rel ℓ 
  R .fst .fst = S
  R .fst .snd = S'
  R .snd = R'

BisimDA : {ℓ : Level} → DA {ℓ} → DA {ℓ} → Type (ℓ-suc ℓ) 
BisimDA {ℓ} (S , f)(S' , g) = 
  Σ[ R ∈ (⟨ S ⟩ → ⟨ S' ⟩ → hSet ℓ) ] 
    BisimDA' (S , f) (S' , g) R


ex : {ℓ : Level} → ((S , f)(T , g) : DA {ℓ}) → (R : Rel' S T) →
    BisimDA' (S , f)(T , g) R →  
    ((s : ⟨ S ⟩)(t : ⟨ T ⟩) → ⟨ R s t ⟩ → 
      ((f s ≡ inl tt*) × (g t ≡ inl tt*)) 
      ⊎ 
      (Σ[ (s' , t') ∈ (⟨ S ⟩ × ⟨ T ⟩) ]  (f s ≡ inr s') × (g t ≡ inr t') × ⟨ R s' t' ⟩))
ex (S , f)(T , g)  R bisim s t sRt with (f s , g t)
... | inl x , inl x₁ = {! bisim  s t sRt  !}
... | inl x , inr x₁ = {!   !}
... | inr x , inl x₁ = {!   !}
... | inr x , inr x₁ = {!   !}


     




--  Σ[ R ∈ (⟨ S ⟩ → ⟨ S' ⟩ → hSet ℓ)  ] {!   !}

-- det transition system 
-- S -> 1 + S 

RGraph : (ℓ : Level) → Type (ℓ-suc ℓ) 
RGraph ℓ = 
  Σ[ S ∈ hSet ℓ ] 
  Σ[ R ∈ Rel' S S ] 
  ((s : ⟨ S ⟩) → ⟨ R s s ⟩)

Relator : {ℓ : Level} → RGraph ℓ → RGraph ℓ → Type ℓ 
Relator {ℓ} (|G| , R , idG) (|H| , R' , idH) = 
  Σ[ f ∈ (⟨ |G| ⟩ → ⟨ |H| ⟩) ] 
  Σ[ rel-f ∈ ({x y : ⟨ |G| ⟩ } → ⟨ R x y ⟩  → ⟨ R' (f x) (f y) ⟩) ] 
  ({ x : ⟨ |G| ⟩} → rel-f (idG x) ≡ idH (f x))

Param : {ℓ : Level}{G H : RGraph ℓ} → Relator G H → Relator G H → Type {! ℓ-zero !} 
Param {ℓ}{|G| , R , idG} {|H| , R' , idH} (f , rel-f , idf) (g , rel-g , idg) =
   Σ[ α ∈ ((x : ⟨ |G| ⟩ ) → {! f x → ?  !}) ] {!   !}

RG : {ℓ : Level} → Category (ℓ-suc ℓ) ℓ 
RG {ℓ} .ob = RGraph ℓ
RG .Hom[_,_] = Relator
RG .id .fst x = x
RG .id .snd .fst xRy = xRy
RG .id .snd .snd = refl
(RG ⋆ r) s .fst = λ z₁ → s .fst (r .fst z₁)
(RG ⋆ r) s .snd .fst = λ z₁ → s .snd .fst (r .snd .fst z₁)
(RG ⋆ r) s .snd .snd = {!   !}
RG .⋆IdL r = ΣPathP (refl , ΣPathP (refl , {!   !}))
RG .⋆IdR r = ΣPathP (refl , ΣPathP (refl , {!   !}))
RG .⋆Assoc r s t = ΣPathP (refl , ΣPathP (refl , {!   !}))
RG .isSetHom = {!   !}

-- RG has binary products given pointwise


_×RG_ : {ℓ : Level} → RGraph ℓ  → RGraph ℓ  → RGraph ℓ 
(G ×RG H) .fst = ⟨ G .fst ⟩ × ⟨ H .fst ⟩ , isSet× (G .fst .snd) (H .fst .snd)
(G ×RG H) .snd .fst (g , h)(g' , h') = (⟨ G .snd .fst g g' ⟩ × ⟨ H .snd .fst h h' ⟩) , isSet× (G .snd .fst g g' .snd)  (H .snd .fst h h' .snd)
(G ×RG H) .snd .snd (g , h)=  G .snd .snd g , H .snd .snd h


-- the Category Set can be demoted to reflexive graph
set : (ℓ : Level) → RGraph (ℓ-suc ℓ) 
set ℓ .fst = (hSet ℓ) , {!   !}
set ℓ .snd .fst X Y = (Rel' X Y) , isSetΠ2 λ x y → {!   !}
set ℓ .snd .snd X x x' = (x Eq.≡ x') , {!   !} 

-- we have the relators 
{- 
_×R_, _+R_, _→R_, and ℙR
from above are all relators on set
-}
_×Rset_ : {ℓ : Level} → Relator (set ℓ ×RG set ℓ) (set ℓ)
_×Rset_ .fst (X , Y)= (⟨ X ⟩ × ⟨ Y ⟩) , (isSet× (X .snd) (Y .snd))
.snd ×Rset .fst = {!   !} -- _×R_
.snd ×Rset .snd = {!   !}


open import Cubical.Categories.Limits.BinProduct.More
-- Cat with × to RGraph
module _ {ℓ : Level}(C : Category ℓ ℓ )(bp :  BinProducts C) where
  open BinProductsNotation bp renaming(_×_ to _×bp_)
  RC : RGraph ℓ 
  RC .fst = (ob C) , {!   !}
  RC .snd .fst c c' = {!   !} -- subobjects of c ×bp c'
    -- ℙ {! c ×bp c'  !} , isSetℙ
  RC .snd .snd c = {!   !} -- c → c ×bp c , the diagonal

open import Cubical.Categories.Functor
open Functor

record RGCat : Type {! ℓ-zero !} where 
  field 
    𝓖v : Category _ _ 
    𝓖e : Category _ _
    ∂₀ : Functor 𝓖e 𝓖v 
    ∂₁ : Functor 𝓖e 𝓖v 
    𝓘 : Functor 𝓖v 𝓖e 
    lft : (A : ob 𝓖v) → (∂₀ ∘F 𝓘) .F-ob A ≡ A
    rgt : (A : ob 𝓖v) → (∂₁ ∘F 𝓘) .F-ob A ≡ A
{-}
RGraph : (ℓ : Level) → Type (ℓ-suc ℓ) 
RGraph ℓ = 
  Σ[ S ∈ hSet ℓ ] 
  Σ[ R ∈ (⟨ S ⟩ → ⟨ S ⟩ → hSet ℓ) ] 
  ((s : ⟨ S ⟩) → ⟨ R s s ⟩)


_×R_ : {ℓ : Level} → RGraph ℓ  → RGraph ℓ  → RGraph ℓ 
(G ×R H) fst = ⟨ G .fst ⟩ × ⟨ H .fst ⟩ , isSet× (G .fst .snd) (H .fst .snd)
(G ×R H) .snd .fst (g , h)(g' , h') = (⟨ G .snd .fst g g' ⟩ × ⟨ H .snd .fst h h' ⟩) , isSet× (G .snd .fst g g' .snd)  (H .snd .fst h h' .snd)
(G ×R H) .snd .snd (g , h)=  G .snd .snd g , H .snd .snd h

_+R_ : {ℓ : Level} → RGraph ℓ  → RGraph ℓ  → RGraph ℓ 
(G +R H) .fst = (⟨ G .fst ⟩ ⊎ ⟨ H .fst ⟩) , isSet⊎ (G .fst .snd) (H .fst .snd)
(G +R H) .snd .fst (inl g) (inl g') = G .snd .fst g g'
(G +R H) .snd .fst (inl g) (inr h) = ⊥* , λ()
(G +R H) .snd .fst (inr h) (inl g) = ⊥* , λ()
(G +R H) .snd .fst (inr h) (inr h') = H .snd .fst h h'
(G +R H) .snd .snd (inl g) = G .snd .snd g
(G +R H) .snd .snd (inr h) = H .snd .snd h

_→R_ :  {ℓ : Level} → RGraph ℓ  → RGraph ℓ  → RGraph ℓ 
(G →R H) .fst = (⟨ G .fst ⟩  → ⟨ H .fst ⟩) , isSet→ (H .fst .snd) 
(G →R H) .snd .fst f f' = 
   ((g g' : ⟨ G .fst ⟩ ) → ⟨ G .snd .fst g g' ⟩ → ⟨ H .snd .fst (f g)(f' g') ⟩ ), 
   isSetΠ2 λ x y → isSet→ (H .snd .fst (f x) (f' y) .snd) 
(G →R H) .snd .snd f g g' gRg' = {!  gRg'!}


-}