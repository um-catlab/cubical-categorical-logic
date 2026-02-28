
module HyperDoc.Operational.Free where 

open import Cubical.Data.List 
open import Cubical.Data.Graph.Base 
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category 
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Sets

open import HyperDoc.Lib
open import HyperDoc.CBPVModel

open Model
open Category
open Functor

record Raw (ℓV ℓV' ℓC ℓC' ℓS : Level) : Type (levels (ℓsuc (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ []))) where 
  field 
    VG : Graph ℓV ℓV' 
    CG : Graph ℓC ℓC' 
    OF : VG .Node → CG .Node → Type ℓS



module Syntax
  {ℓV ℓV' ℓC ℓC' ℓS : Level }
  (R : Raw ℓV ℓV' ℓC ℓC' ℓS) where

  ℓm = (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ []))
  open Raw R 

  mutual 
    data VTy : Type (levels (ℓV ∷ ℓC ∷ [])) where 
      inV : VG .Node → VTy
      _+_ : VTy → VTy → VTy
      one : VTy 
      U : CTy → VTy 

    data CTy : Type (levels (ℓV ∷ ℓC ∷ [])) where
      inC : CG .Node →  CTy
      _&_ : CTy → CTy → CTy 
      F : VTy → CTy    

  data _⊢v_ : (A A' : VTy) → Type  ℓm
  data _⊢c_ : (A : VTy)(B : CTy) → Type  ℓm
  data _⊢k_ : (B B' : CTy) → Type  ℓm 
  
  data _⊢v_   where
    -- category 
    varv : {A : VTy} → A ⊢v A
    appv : {X : VTy}{A A' : VG .Node}→ 
      VG .Edge A A' →
      X ⊢v inV A → 
      --------
      X ⊢v inV A' 


  data _⊢c_ where     
    appo : ∀ {A A' B}
      → OF A' B
      →  A ⊢v inV A' 
      → A ⊢c inC B

    appc : ∀{A B B'} →
      CG .Edge B B' →
      A ⊢c inC B →
      A ⊢c inC B'

  data _⊢k_ where 
    -- category 
    hole : {B : CTy} → B ⊢k B
    appk : {X : CTy}{B B' : CG .Node} →
      CG .Edge B B' →
      X ⊢k inC B  →
      --------
      X ⊢k inC B'

    _,,_ : ∀{B B' B''} → B ⊢k B' → B ⊢k B'' → B ⊢k (B' & B'')
    π₁ : ∀{B B' B''} → B ⊢k (B' & B'') → B ⊢k B'
    π₂ : ∀{B B' B''} → B ⊢k (B' & B'') → B ⊢k B''


  mutual
    subv : {A A' A'' : VTy} → A ⊢v A' → A' ⊢v A'' → A ⊢v A'' 
    subv v varv = v
    subv v (appv x w) = appv x (subv v w)

    kcomp : {B B' B'' : CTy} → B ⊢k B' → B' ⊢k B'' → B ⊢k B'' 
    kcomp s hole = s
    kcomp s (appk x s') = appk x (kcomp s s')
    kcomp s (s' ,, s'') = kcomp s s' ,, kcomp s s''
    kcomp s (π₁ s') = π₁ (kcomp s s')
    kcomp s (π₂ s') = π₂ (kcomp s s')


    plug : {A : VTy}{B B' : CTy} → B ⊢k B' → A ⊢c B → A ⊢c B'
    plug hole m = m
    plug (appk x s) m = appc x (plug s m)
    plug (s ,, s') m = {! plug s m  !} where 
      _  = {! plug s m  !}
      _ = {! plug s' m  !}
    plug (π₁ s) m = {!  π₁ s !}
    plug (π₂ s) m = {!   !}
      -- plug (kcomp s (π₁ {! hole  !})) m

    subc : {A A' : VTy}{B : CTy} → A' ⊢v A → A ⊢c B → A' ⊢c B 
    subc v (appo x w) = appo x (subv v w)
    subc v (appc x m) = appc x (subc v m)


  subvIdL : ∀{A A'} (f : A ⊢v A') → subv varv f ≡ f
  subvIdL varv = refl
  subvIdL (appv x v) = cong₂ appv refl (subvIdL v)

  subVAssoc : ∀ {A₁ A₂ A₃ A₄} → 
    (f : A₁ ⊢v A₂) (g : A₂ ⊢v A₃) (h : A₃ ⊢v A₄) →
    subv (subv f g) h ≡ subv f (subv g h)
  subVAssoc f g varv = refl
  subVAssoc f g (appv x h) = cong₂ appv refl (subVAssoc f g h)

  kcompIdL : ∀{B B'} (f : B ⊢k B') → kcomp hole f ≡ f
  kcompIdL hole = refl
  kcompIdL (appk x s) = {!   !}
  kcompIdL (s ,, s₁) = {!   !}
  kcompIdL (π₁ s') = {!   !}
  kcompIdL (π₂ s') = {!   !}


  Free : Model  (ℓ-max ℓV ℓC) ℓm (ℓ-max ℓV ℓC) ℓm ℓm
  Free .V .ob = VTy
  Free .V .Hom[_,_] = _⊢v_
  Free .V .id = varv
  Free .V ._⋆_ = subv
  Free .V .⋆IdL = subvIdL
  Free .V .⋆IdR _ = refl
  Free .V .⋆Assoc = subVAssoc
  Free .V .isSetHom = {!   !}

  Free .C .ob = CTy
  Free .C .Hom[_,_] = _⊢k_
  Free .C .id = hole
  Free .C ._⋆_ = kcomp
  Free .C .⋆IdL = kcompIdL
  Free .C .⋆IdR _ =  refl
  Free .C .⋆Assoc = {!   !}
  Free .C .isSetHom = {!   !}

  Free .O .F-ob (A , B) = A ⊢c B , {!   !}
  Free .O .F-hom (v , s) m = plug s (subc v m)
  Free .O .F-id = {!   !}
  Free .O .F-seq = {!   !}


    -- type structure 
  {-  bind : ∀ {A B} → F A ⊢k B 
    _,,_ : ∀{B B' B''} → B ⊢k B' → B ⊢k B'' → B ⊢k (B' & B'')
    π₁ : ∀{B B'} → (B & B') ⊢k B
    π₂ : ∀{B B'} → (B & B') ⊢k B' -}


  --  isSet⊢k : ∀{B B'} → isSet (B ⊢k B')
{-
  data _⊢v_  : (A A' : VTy) → Type  ℓm  where
    -- category 
    varv : {A : VTy} → A ⊢v A
    appv : {X : VTy}{A A' : VG .Node}→ --{Ae Ae' : VTy} →
      VG .Edge A A' →
   --   {p : inV A Eq.≡ Ae}{q : inV A' Eq.≡ Ae'} → 
      X ⊢v inV A → -- Ae →
      --------
      X ⊢v inV A' -- Ae'
  test : ∀ {A A'} → A ⊢v A' → A ⊢v A'
  test varv = {!   !}
  test (appv x v) = {!   !}
-}

 
{-
  mutual
    subv : {A A' A'' : VTy} → A ⊢v A' → A' ⊢v A'' → A ⊢v A'' 
    subv v varv = v
    subv v (appv x w) = appv x (subv v w)
    subv v tt = tt
    subv v (thunk x) = thunk (subc v x)

    plug : {B B' B'' : CTy} → B ⊢k B' → B' ⊢k B'' → B ⊢k B'' 
    plug m varc = m
    plug m (appc x n) = appc x (plug m n)
    plug m (ret x) = {! ret ? !}
    plug m (n ,, n₁) = plug m n ,, plug m n₁
    plug m (π₁ n) = π₁ (plug m n)
    plug m (π₂ n) = π₂ (plug m n)

    subk : {A : VTy}{B B' : CTy} → B ⊢k B' → A ⊢c B → A ⊢c B' -- A ~ B → 𝓒 [ B , B' ] → A ~> B'
    subk varc m = m
    subk (appc x s) m = appc x (subk s m)
    subk (ret x) m = {!   !}
    subk (s ,, s₁) m = {! bind  !}
    subk (π₁ s) m = bind (π₁ (ret (subk s m)))
    subk (π₂ s) m = bind (π₂ (ret (subk s m)))

    subc : {A A' : VTy}{B : CTy} → A' ⊢v A → A ⊢c B → A' ⊢c B 
    subc v (appo x x₁) = appo x (subv v x₁)
    subc v (appc x m) = appc x (subc v m)
    subc v (bind x) = bind {!   !}
    subc v (force x) = force (subv v x)
    subc v (case m m₁) = {! case ? ?   !}
    subc v (σ₁ m) = {!   !}
    subc v (σ₂ m) = {!   !} 

-}

{-  subv : {A A' : VTy}{B : CTy} → A' ⊢v A → A ⊢c B → A' ⊢c B 
  subv v (appo o w) = appo o (appv {!   !}  {!   !})
  subv v (appc x m) = {!   !}
  subv v (bind x) = {!   !}
  subv v (force x) = {!   !}
  subv v (case m m₁) = {!   !}
  subv v (σ₁ m) = {!   !}
  subv v (σ₂ m) = {!   !}
  subv v (isSet⊢c m m₁ x y i i₁) = {!   !}
-}

{-


-- M[V/x]
subv : {A A' : ob 𝓥}{B : ob 𝓒} → 𝓥 [ A' , A ] → A ~> B → A' ~> B
-- f(V')[V/x] = f(V'[V/x])
subv V (appo f V') = appo f (V 𝓥.⋆ V')
-- ϕ(M)[V/x] = ϕ(M[V/x])
subv V (appc ϕ M) = appc ϕ (subv V M)

-- S[M]
subc : {A : ob 𝓥}{B B' : ob 𝓒} → A ~> B → 𝓒 [ B , B' ] → A ~> B'
-- ∙[M] = M
subc M var = M
-- ϕ(S)[M] = ϕ(S[M])
subc M (app ϕ S) = appc ϕ (subc M S)
-}