{-# OPTIONS -W noUnsupportedIndexedMatch #-}
module Cubical.Categories.CBPV.lr where 

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.TotalCategory.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Sets
open import Cubical.Functions.Logic

open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Displayed
open import Cubical.Categories.WithFamilies.Simple.Instances.Sets 
  renaming(SET to SETScwf)
open Functor
open Category
open Functorᴰ
open Categoryᴰ
open import Cubical.Categories.WithFamilies.Simple.Functor
open import Cubical.Categories.NaturalTransformation hiding (_⇒_)
open import Cubical.Categories.CBPV.SmallStep renaming (F to Sem)
open import Cubical.Categories.CBPV.Instances.DefinedSubstitution

private  
  variable
    ℓC ℓC' ℓT ℓT' ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level
    ℓD ℓD' ℓS ℓS' : Level



module _
  ((_ , Ty , Tm , _ , _) : SCwF ℓC ℓC' ℓT ℓT')
  where 
  _ = PshProd
  hasProd : Type _ 
  hasProd = ∀ (A B : Ty) → Σ[ A×B ∈ Ty ] NatIso (Tm A×B) (Tm A ×Psh Tm B)

SCwF× : (ℓC ℓC' ℓT ℓT' : Level) → Type _
SCwF× ℓC ℓC' ℓT ℓT' = Σ[ S ∈ SCwF ℓC ℓC' ℓT ℓT' ] (hasProd S)

module _
  {(S , S×) : SCwF× ℓC ℓC' ℓS ℓS'}
  {(T , T×) : SCwF× ℓD ℓD' ℓT ℓT'}
  (F : PreFunctor S T)
  where 

  Tyₛ = S .snd .fst 
  Tyₜ = T .snd .fst 

  Tmₛ = S .snd .snd .fst 
  Tmₜ = T .snd .snd .fst 

  Fty = F .snd .fst

  _×t_ : (A B : Tyₜ) → Tyₜ 
  _×t_ A B = T× A B .fst

  _×s_ : (A B : Tyₛ) → Tyₛ 
  _×s_ A B = S× A B .fst

  pres× : Type _ 
  pres× = ∀ (A B : Tyₛ ) → 
    NatIso (Tmₜ (Fty (A ×s B))) (Tmₜ (Fty A ×t Fty B))

Functor× : (S : SCwF× ℓC ℓC' ℓS ℓS') → (T : SCwF× ℓD ℓD' ℓT ℓT') → Type _ 
Functor× S T = Σ[ F ∈ PreFunctor (S .fst) (T .fst) ] 
  (pres×{_}{_}{_}{_} {_}{_}{_}{_}{S}{T} F)

-- doesn't work for CBPV without complex values
scwf× : SCwF× _ _ _ _ 
scwf× = scwf , λ A B → (prod A B) , 
  record { trans = natTrans (λ Γ p → {!   !} , {!   !}) {!   !} ; nIso = {!   !} }

-- again doesn't work for CBPV without complex values
ex : Functor× scwf× (SETScwf ℓ-zero , λ A B → ((⟨ A ⟩ × ⟨ B ⟩) , {!   !}) , {!   !}) 
ex = Sem , λ A B → 
  record { 
    trans = 
      natTrans 
        (λ X v → λ x → {!  v x !} , {!   !}) 
        {!   !} ; 
    nIso = {!   !} }
  
module fam {ℓ ℓ' : Level} where 

  setD = SETᴰ ℓ ℓ'

  -- Democratic displayed SCwF using CCCᴰ structure of SETᴰ
  Fam : SCwFᴰ (SETScwf ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ') (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  Fam .fst = setD
  Fam .snd .fst = λ X → fst X → ob (SET _) 
    --setD .ob[_]
  Fam .snd .snd .fst Â = setD [-][-, Â ]
  Fam .snd .snd .snd = {! setD .ob[_]  !}

  Pred : Categoryᴰ (SET ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  Pred. ob[_] X = ⟨ X ⟩ → hProp ℓ'
  Pred .Hom[_][_,_] f P Q = ⟨ ∀[ x ] (P x ⇒ Q (f x)) ⟩
  Pred .idᴰ = λ x z → z
  Pred ._⋆ᴰ_ {f = f} f^d g^d x p = g^d (f x) (f^d x p)
  Pred .⋆IdLᴰ _ = refl
  Pred .⋆IdRᴰ _ = refl
  Pred .⋆Assocᴰ _ _ _ = refl
  Pred .isSetHomᴰ {f = f} {x^d}{y^d} = 
    isProp→isSet ((∀[ x ] (x^d x ⇒ y^d (f x))) .snd)

  open import Cubical.Categories.Displayed.BinProduct
  _ = _×ᴰ_
  open import Cubical.Categories.Displayed.Limits.CartesianD 
  _ = CartesianCategoryᴰ

  PredSCwF : SCwFᴰ (SETScwf ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ') (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  PredSCwF .fst = Pred
  PredSCwF .snd .fst X = ⟨ X ⟩ → hProp ℓ'
  PredSCwF .snd .snd .fst Q = Pred [-][-, Q ]
  PredSCwF .snd .snd .snd = {!   !}


module total 
  ((C , Ty , Tm , term , comp ) : SCwF ℓC ℓC' ℓT ℓT')
  ((Cᴰ , Tyᴰ , Tmᴰ , termᴰ , comprehensionᴰ) : SCwFᴰ (C , Ty , Tm , term , comp ) ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ')where 

  tm : Σ[ A ∈ Ty ] Tyᴰ A → Presheaf (∫C Cᴰ) (ℓ-max ℓT' ℓTᴰ')
  tm (A , Â) .F-ob (Γ , Γ̂ )= (Σ[ m ∈ ⟨ Tm A .F-ob Γ ⟩ ] ⟨ Tmᴰ Â .F-obᴰ Γ̂  m ⟩) , {!   !}
  tm (A , Â) .F-hom (f , f̂ )(m , m̂)= (Tm A .F-hom f m) , (Tmᴰ Â .F-homᴰ f̂ m m̂)
  tm (A , Â) .F-id = funExt λ (_ , _ ) → 
    ΣPathP ((funExt⁻ (Tm A .F-id) _) , {! (Tmᴰ  Â .F-idᴰ)   !} )
  tm (A , Â) .F-seq (f , f̂ )(g , ĝ ) = funExt λ (_ , _) → 
    ΣPathP (((funExt⁻ (Tm A .F-seq _ _ ) _)) , {!   !})

  tot : SCwF (ℓ-max ℓC ℓCᴰ) (ℓ-max ℓC' ℓCᴰ') (ℓ-max ℓT ℓTᴰ) (ℓ-max ℓT' ℓTᴰ') 
  tot .fst = ∫C Cᴰ
  tot .snd .fst = Σ[ A ∈ Ty ] Tyᴰ A
  tot .snd .snd .fst = tm
  tot .snd .snd .snd = {!   !}


open fam 
open total 

FamSCwF : SCwF (ℓ-suc ℓ-zero)( ℓ-zero) (ℓ-suc ℓ-zero) ℓ-zero 
FamSCwF = tot (SETScwf ℓ-zero) PredSCwF -- also works for Fam

hasProdFam : hasProd FamSCwF 
hasProdFam (A , P) (B , Q) = goal where 

  Ty = FamSCwF .snd .fst
  Tm = FamSCwF .snd .snd .fst

  A×B : Ty 
  A×B = ((⟨ A ⟩ × ⟨ B ⟩) , (isSet× (A .snd) (B .snd))), λ (a , b) → P a ⊓ Q b

  goal : Σ Ty λ A×B → NatIso (Tm A×B) (Tm (A , P) ×Psh Tm (B , Q))
  goal = A×B , (
    record { 
      trans = 
        natTrans 
          -- X : Set , R : X → Prop
          -- v : X → A×B 
          -- p : ∀(x : X) → R(x) ⇒ P(v x .fst) ⊓ Q (v x .snd) 
          -- goal : 
          --  (Σ(f : X → A) ((x : X) → R x → P(f x))) × 
          --  (Σ(f : X → B) ((x : X) → R x → Q(f x)))
          (λ (X , R)(v , p) → 
            ((λ x → v x .fst) , (λ x rx → p x rx .fst)) , 
            (λ x → v x .snd) , (λ x rx → p x rx .snd)) 
          λ (f , f̂) → refl ; 
      nIso = λ (X , R) → 
        isiso 
          (λ ((v , p), (w , q)) → (λ x → v x , w x) , (λ x rab → (p x rab) , (q x rab) )) 
          refl 
          refl})
 --- (((⟨ A ⟩ × ⟨ B ⟩) , (isSet× (A .snd) (B .snd))) , {!   !}) , {!   !}

FamSCwF× : SCwF× (ℓ-suc ℓ-zero)( ℓ-zero) (ℓ-suc ℓ-zero) ℓ-zero  
FamSCwF× = FamSCwF , hasProdFam

open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Instances.Sets.Properties
Pred× : BinProductsᴰ Pred BinProductsSET 
Pred× = λ (P , Q) → 
  record { 
    vertexᴰ = λ (x , y) → P x ⊓ Q y ; 
    elementᴰ = (λ (x , y)(Px , Qx) → Px) , (λ (x , y)(Px , Qx) → Qx) ; 
    universalᴰ = {!   !} }

-- open import Cubical.Categories.CBPV.Instances.Free
open import Cubical.Data.List.Dependent
open import Cubical.Data.List hiding (elim; [_])

open import Cubical.Categories.WithFamilies.Simple.Instances.Free.Base
  renaming (ren to ren'; wkRen to wkRen' ; idRen to idRen' ; Var to Var' ; 
  Var' to none)
open import Cubical.Data.Unit
-- by initiality ..?
over : PreFunctor (SETScwf ℓ-zero) FamSCwF
over .fst .F-ob (X , XisSet) = ((X , XisSet)) , λ x → {! setD .ob[_]   !} , {!   !}
over .fst .F-hom = {! FamSCwF .snd .snd .fst  !}
over .fst .F-id = {!   !}
over .fst .F-seq = {!   !}
over .snd .fst = {!   !}
over .snd .snd = {!   !}

mutual
  𝓥[_] : (A : VTy)(v : · ⊢v A) → Type ℓ-zero 
  𝓥[_] one v = Unit
  𝓥[_] (prod A A') (pair v w) = 𝓥[ A ] v × 𝓥[ A' ] w
  𝓥[_] (U B) v = 𝓒[ B ] (force v)

  𝓒[_] : (B : CTy)(m : · ⊢c B) → Type ℓ-zero
  𝓒[_] (fun A B) m = ∀ (v : · ⊢v A) → 𝓥[ A ] v → 𝓒[ B ] (app m v)
  𝓒[_] (F A) m = Σ[ v ∈ · ⊢v A ] (m ≡ ret v) × 𝓥[ A ] v 


𝓖[_] : (Γ : Ctx)(γ : Sub[ · , Γ ]) → Type ℓ-zero 
𝓖[ [] ] [] = Unit
𝓖[ (A ∷ Γ) ] (v ∷ γ) = 𝓥[ A ] v × 𝓖[ Γ ] γ 



mutual 
  FLV : {Γ : Ctx}{A : VTy} → 
    (v : Γ ⊢v A) → ∀ (γ* : Sub[ · , Γ ]) → 𝓖[ Γ ] γ*  → 𝓥[ A ] (subv γ* v) 
  FLV (var vz) (y ∷ γ*) (Â , G) = Â
  FLV (var (vs x)) (y ∷ γ*) (B̂  , G) = FLV (var x) γ* G
  FLV u γ* G = tt
  FLV (pair v w) γ* G = (FLV v γ* G) , (FLV w γ* G)
  FLV (thunk m) γ* G = {! FLC m γ* G  !}
  -- have 𝓒[ B ] (subc γ* m)
  -- need 𝓒[ B ] (force (thunk (subc γ* m)))
  -- so need to establish antireduction if using operational
  -- or use beta laws 


  FLC : {Γ : Ctx}{B : CTy} → 
    (m : Γ ⊢c B) → ∀ (γ* : Sub[ · , Γ ]) → 𝓖[ Γ ] γ*  → 𝓒[ B ] (subc γ* m) 
  FLC (ret v) γ* G = subv γ* v , refl , (FLV v γ*  G)
  FLC (force x) γ* G = {!   !}
  FLC (lam m) γ* G = λ v Â → {!   !}
  FLC (app m x) γ* G = {!   !}
  FLC (rec× x m) γ* G = {!   !}
  FLC (bind m m₁) γ* G = {!   !}

ctxMap : {Δ Γ : Ctx}{γ : Sub[ Δ , Γ ]}{δ : Sub[ · , Δ ]} → 
  𝓖[ Δ ] δ → 𝓖[ Γ ] (δ ⋆Sub γ) 
ctxMap {Δ} {[]} {[]} {δ*} G = tt
ctxMap {Δ} {A ∷ Γ} {v ∷ γ} {δ*} G = (FLV v δ* G) , ctxMap G

{-}
ctxMap {Δ} {[]} {[]} {δ*} G = tt
ctxMap {[]} {x ∷ Γ} {y ∷ γ} {[]} tt = FLV y [] tt , ctxMap tt
ctxMap {x₁ ∷ Δ} {x ∷ Γ} {y ∷ γ} {y₁ ∷ δ*} (fst₁ , snd₁) = FLV y (y₁ ∷ δ*) (fst₁ , snd₁) , ctxMap (fst₁ , snd₁)
-- ctxMap {A ∷ Δ} {Γ} {[]} {v ∷ δ*} (Â , Ĝ) = tt
-- ctxMap {A ∷ Δ} {Γ} {y ∷ γ} {v ∷ δ*} (Â , Ĝ) = {!   !} , {!   !}
-}

-- derive without initiality
CtxF : Functor SubCat (FamSCwF .fst) 
CtxF .F-ob Γ = Fctx .F-ob Γ , λ γ* → (𝓖[ Γ ] γ*) , {!   !}
CtxF .F-hom {Δ}{Γ} γ = Fctx .F-hom γ , λ δ → ctxMap
CtxF .F-id {Γ} = ΣPathP ((Fctx .F-id) , (funExt λ γ* → funExt λ Gγ* → {!   !}))
  -- (ctxMap Gγ*) = Gγ* when normal γ is identity
CtxF .F-seq γ δ = ΣPathP ((Fctx .F-seq _ _) , {!   !})

LR : PreFunctor scwf FamSCwF 
LR .fst = CtxF
LR .snd .fst A = (Fvty A) , (λ v → 𝓥[ A ] v , {!   !}) 
  -- isSet (𝓥[A]v)
  -- could even be a hProp!
LR .snd .snd .PshHom.N-ob Γ v = (λ γ* → subv γ* v) , (FLV v)
LR .snd .snd .PshHom.N-hom Δ Γ γ v =
  ΣPathP 
    (Fvtm .PshHom.N-hom Δ Γ γ v , 
    (funExt (λ δ* → funExt λ Gδ* → {!   !})))
-- FLV (subv γ v) δ* Gδ*) = (FLV v (δ* ⋆Sub γ) (ctxMap Gδ*)
-- we can move the substitution in the Fundamental lemma from the term
-- to the closing substitution and semantic substitution



LR× : Functor× scwf× FamSCwF× 
LR× = LR , λ A B → 
  record { 
    trans = 
      natTrans 
        (λ(Γ^* , Γ̂ )(v , v̂) → (λ γ → {!  v !}) , {!   !}) 
        {!   !} ; 
    nIso = {!   !} }


{-
LR .fst .F-ob Γ = Fctx .F-ob Γ , λ γ → 𝓖[ Γ ] γ  , {!   !}
LR .fst .F-hom {Δ}{Γ} γ = Fctx .F-hom γ , λ δ → ctxMap
LR .fst .F-id {Γ}= ΣPathP ((funExt (SubCat .⋆IdR)) , funExt λ γ* → funExt λ Gγ* → {!   !})
  -- (ctxMap Gγ*) = Gγ* when normal γ is identity
LR .fst .F-seq = {!   !}
LR .snd .fst A = (Fvty A) , (λ v → (𝓥[ A ] v) , {!   !})
LR .snd .snd .PshHom.N-ob Γ v = (λ γ* → subv γ* v) , (FLV v)
LR .snd .snd .PshHom.N-hom Δ Γ γ v =
  ΣPathP 
    ((funExt (λ γ* → {!   !})) , 
    (funExt (λ δ* → funExt λ Gδ* → {!   !})))
-}
-- first goal
-- subv γ* (subv γ v) ≡ subv (γ* ⋆Sub γ) v
-- second goal 
-- FLV (subv γ v) δ* Gδ*) = (FLV v (δ* ⋆Sub γ) (ctxMap Gδ*)
-- we can move the substitution in the Fundamental lemma from the term
-- to the closing substitution and semantic substitution

{-
LR .snd .snd .PshHom.N-ob Γ (var x) = (λ γ* → subv γ* (var x)) , {!   !}
LR .snd .snd .PshHom.N-ob Γ u = (λ γ* → subv γ* u) , λ γ γ̂  → tt
LR .snd .snd .PshHom.N-ob Γ (pair v w) = (λ γ* → subv γ* (pair v w)) , λ γ γ̂  → {!   !} , {!   !}
LR .snd .snd .PshHom.N-ob Γ (thunk m) = (λ γ* → subv γ* (thunk m)) , {!   !}
LR .snd .snd .PshHom.N-hom = {!   !}
-}
{-}.PshHom.N-ob Γ v = (Fvtm .PshHom.N-ob Γ v) , (λ γ* → {!  v !})
LR .snd .snd .PshHom.N-hom = {!   !}
-}

proj : PreFunctor FamSCwF (SETScwf ℓ-zero)
proj .fst .F-ob (X , X̂) = X
proj .fst .F-hom (f , f̂) = f
proj .fst .F-id = refl
proj .fst .F-seq f g = refl
proj .snd .fst (X , X̂) = X
proj .snd .snd .PshHom.N-ob (X , X̂)(m , _) = m
proj .snd .snd .PshHom.N-hom _ _ _ _ = refl

