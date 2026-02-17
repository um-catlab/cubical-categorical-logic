module Cubical.Categories.CBPV.Simple where 
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Data.Sigma
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Data.Graph.Base hiding (Node ; Edge)

open Category
open Functor
open Graph


module _ 
  {ℓ ℓ' : Level}
  (G : Graph ℓ ℓ') where 

  data _⊢_ : G .Node → G .Node → Type (ℓ-max ℓ ℓ') where  
    var : {X : G .Node} → X ⊢ X

    app : {X Y Z : G .Node} → 
      G .Edge X Y → 
      Z ⊢ X → 
      Z ⊢ Y

  sub : {X Y Z : G .Node} → X ⊢ Y → Y ⊢ Z → X ⊢ Z 
  sub m var = m
  sub m (app x n) = app x (sub m n)

  FreeCat : Category {!   !} {!   !} 
  FreeCat .ob = G .Node
  FreeCat .Hom[_,_] = _⊢_
  FreeCat .id = var
  FreeCat ._⋆_ = sub
  FreeCat .⋆IdL = {!   !}
  FreeCat .⋆IdR _ = refl
  FreeCat .⋆Assoc = {!   !}
  FreeCat .isSetHom = {!   !}

module simple 
  {ℓV ℓV' ℓC ℓC' ℓS : Level } 
  (V : Graph ℓV ℓV')
  (C : Graph ℓC ℓC')
  (O : V .Node → C .Node → Type ℓS) where 

  𝓥 : Category ℓV (ℓ-max ℓV ℓV') 
  𝓥 = FreeCat V

  𝓒 : Category ℓC (ℓ-max ℓC ℓC') 
  𝓒 = FreeCat C

  data _~>_ : ob 𝓥 → ob 𝓒 → Type (ℓ-max ℓV (ℓ-max ℓV' (ℓ-max ℓC (ℓ-max ℓC' ℓS)))) where 
    gen : {A : ob 𝓥}{B : ob 𝓒} → 
      O A B → 
      A ~> B

    genv : {A A' : ob 𝓥}{B : ob 𝓒} → 
      V .Edge A A' →  
      A' ~> B → 
      A ~> B

    genc : {A : ob 𝓥}{B B' : ob 𝓒} → 
      C .Edge B B' → 
      A ~> B → 
      A ~> B' 

  -- S[M[V/x]] ≡ S[M][V/x]
  subv : {A A' : ob 𝓥}{B : ob 𝓒} → 𝓥 [ A' , A ] → A ~> B → A' ~> B 
  subv var o = o
  subv (app x v) o = subv v (genv x o)

  subc : {A : ob 𝓥}{B B' : ob 𝓒} → 𝓒 [ B , B' ] → A ~> B → A ~> B'  
  subc var o = o
  subc (app x m) o = genc x (subc m o)

  𝓞 : Functor ((𝓥 ^op) ×C 𝓒) (SET (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓV ℓV') ℓC) ℓC') ℓS)) 
  𝓞 .F-ob (A , B) = (A ~> B) , {!   !}
  𝓞 .F-hom (v , m) o = subc m (subv v o)
  𝓞 .F-id = refl
  𝓞 .F-seq (V , M)(W , N) = {!   !}
      

    

  
