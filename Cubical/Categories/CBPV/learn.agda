module Cubical.Categories.CBPV.learn where  


open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets 
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Functions.Logic

open import Cubical.Categories.Functor

open Category


module trivial where  
  open import Cubical.Categories.WithFamilies.Simple.Base
  open import Cubical.Data.Unit

  T : Category ℓ-zero ℓ-zero 
  T .ob = Unit
  T .Hom[_,_] tt tt = Unit
  T .id = tt
  T ._⋆_ = λ f g → tt
  T .⋆IdL tt = refl
  T .⋆IdR tt = refl
  T .⋆Assoc tt tt tt = refl
  T .isSetHom = isSetUnit

  data VTy : Type where 
   -- one : VTy

  el : VTy → hSet ℓ-zero 
  el A = {!   !}
  -- one = Unit , isSetUnit

  open import Cubical.Categories.Presheaf.Constructions.BinProduct.LocalRepresentability
  open import Cubical.Categories.Presheaf.Representable
  open import Cubical.Categories.NaturalTransformation
  triv : SCwF _ _ _ _
  triv .fst = T
  triv .snd .fst = VTy
  triv .snd .snd .fst A .Functor.F-ob tt = el A
  triv .snd .snd .fst A .Functor.F-hom tt x = x
  triv .snd .snd .fst A .Functor.F-id = refl
  triv .snd .snd .fst A .Functor.F-seq f g = refl
  triv .snd .snd .snd .fst = {!   !}
  triv .snd .snd .snd .snd A tt = 
    representationToUniversalElement 
      T 
      (Functor.F-ob (LRProf (triv .snd .snd .fst A)) tt)  
      (tt , (record { trans = natTrans (λ {tt (lift tt) → lift (tt , {!   !})}) {!   !} ; 
        nIso = λ { tt → isiso ((λ _ → tt*)) {!    !} {!   !}} }))




--open Categoryᴰ
-- cartesian morphism 
-- https://ncatlab.org/nlab/show/Grothendieck+fibration 

-- see also https://1lab.dev/Cat.Displayed.Cartesian.html#1751
module Foo
  {ℓ ℓ' ℓD ℓD' : Level}
  (C : Category ℓ ℓ')
  (Cᴰ : Categoryᴰ C ℓD ℓD') 
  where 

  open Categoryᴰ Cᴰ

  record isCartesian
    {X Y : ob C}
    {xᵈ : ob[ X ] }
    {yᵈ : ob[ Y ]}
    {f : C [ X , Y ]}
    (f̂ : Cᴰ [ f ][ xᵈ , yᵈ ]) : Type (ℓ-max ℓD (ℓ-max ℓ' (ℓ-max ℓ ℓD'))) where   

    field 
      -- existence
      clift : 
        {Z : ob C}
        {zᵈ : ob[ Z ]}
        {g : C [ Z , X ]}
        (ĥ : Cᴰ [ g ⋆⟨ C ⟩ f ][ zᵈ , yᵈ ])
        → Cᴰ [ g ][ zᵈ , xᵈ ]  
      -- commutes upstairs
      comm :         
        {Z : ob C}
        {zᵈ : ob[ Z ]}
        {g : C [ Z , X ]}
        {ĥ : Cᴰ [ g ⋆⟨ C ⟩ f ][ zᵈ , yᵈ ]} 
        → (clift ĥ ⋆ᴰ f̂) ≡[ refl ] ĥ
      -- uniqueness

  record CartesianLift {X Y : ob C}(f : C [ X , Y ])(yᵈ : ob[ Y ]): Type (ℓ-max ℓD (ℓ-max ℓ' (ℓ-max ℓ ℓD'))) where 
    field 
      {xᵈ} : ob[ X ]
      f̂ : Cᴰ [ f ][ xᵈ , yᵈ ]
      isCart : isCartesian f̂ 
                
  CartesianFibration : Type (ℓ-max ℓD (ℓ-max ℓ' (ℓ-max ℓ ℓD')))
  CartesianFibration = {X Y : ob C} (f : C [ X , Y ])(yᵈ : ob[ Y ]) → CartesianLift f yᵈ


module example (ℓ : Level) where  
  open Categoryᴰ

  Pred : Categoryᴰ (SET ℓ) (ℓ-suc ℓ) ℓ 
  Pred. ob[_] X = ⟨ X ⟩ → hProp ℓ
  Pred .Hom[_][_,_] f P Q = ⟨ ∀[ x ] (P x ⇒ Q (f x)) ⟩
  Pred .idᴰ = λ x z → z
  Pred ._⋆ᴰ_ {f = f} f^d g^d x p = g^d (f x) (f^d x p)
  Pred .⋆IdLᴰ _ = refl
  Pred .⋆IdRᴰ _ = refl
  Pred .⋆Assocᴰ _ _ _ = refl
  Pred .isSetHomᴰ {f = f} {x^d}{y^d} = 
    isProp→isSet ((∀[ x ] (x^d x ⇒ y^d (f x))) .snd)


  open Foo (SET ℓ) Pred

  open CartesianLift
  open isCartesian

  ex : CartesianFibration 
  ex f yᵈ .xᵈ = λ x → yᵈ (f x) -- reindex the predicate using F
  ex f yᵈ .f̂ = λ x x' → x'
  ex f yᵈ .isCart .clift = λ ĥ → ĥ
  ex f yᵈ .isCart .comm = refl
  


