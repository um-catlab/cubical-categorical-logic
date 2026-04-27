module HyperDoc.Operational.Graph where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.FullSubcategory 
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Instances.Sets

open Category
open Categoryᴰ
open Functor

{- 
  could have used these.. but they are not using hLevels
  open import Cubical.Relation.Binary.Base
  open import Cubical.Data.Graph
  open import Cubical.Data.Graph.Displayed
-}

Graph : (ℓ ℓ' : Level) → Type _
Graph ℓ ℓ' = Σ[ S ∈ hSet ℓ ] (⟨ S ⟩ → ⟨ S ⟩ → hSet ℓ') 

RGraph : (ℓ ℓ' : Level) → Type _
RGraph  ℓ ℓ' = Σ[ G ∈ Graph ℓ ℓ' ] ((n : ⟨ G .fst ⟩) → ⟨ G .snd n n ⟩)


isGraphHom : {ℓ ℓ' : Level}{G H : Graph ℓ ℓ'} → (⟨ G .fst ⟩ → ⟨ H .fst ⟩) → Type _ 
isGraphHom {G = N , E} {N' , E'} f = {n n' : ⟨ N ⟩} → ⟨ E n n' ⟩ → ⟨ E' (f n) (f n') ⟩

GraphHom : {ℓ ℓ' : Level}→ (G H : Graph ℓ ℓ') → Type _ 
GraphHom (N , E) (N' , E') = 
  Σ[ f ∈ (⟨ N ⟩ → ⟨ N' ⟩) ] 
    isGraphHom {G = N , E} {N' , E'} f

{- 
    Fv : G.Car → H.Car
    Fe : {x y : G.Car} → x G.R y → Fv x H.R Fv y
    -- this is the identity extension principle! 
    Fid : {x : G.Car} → Fe (G.Rid {x}) ≡ H.Rid{Fv x}
-}
Relator : {ℓ ℓ' : Level}→ (G H : RGraph ℓ ℓ') → Type _ 
Relator G H = Σ[ h ∈ GraphHom (G .fst) (H .fst) ] ({n : ⟨ G .fst .fst ⟩} → h .snd (G .snd n) ≡ H .snd (h .fst  n))

Relator≡ :{ℓ ℓ' : Level}{G H : RGraph ℓ ℓ'}(f g : Relator G H) → f .fst ≡ g .fst → f ≡ g 
Relator≡ {G = G}{H} f g  prf = Σ≡Prop (λ x → isPropImplicitΠ λ n → H .fst .snd _ _ .snd _ _) prf

GRAPH : (ℓ ℓ' : Level) → Category (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-max ℓ ℓ') 
GRAPH ℓ ℓ' .ob = Graph ℓ ℓ'
GRAPH ℓ ℓ' .Hom[_,_] = GraphHom
GRAPH ℓ ℓ' .id = (λ z → z) , (λ {n} {n'} z → z)
GRAPH ℓ ℓ' ._⋆_ = λ f g →
    (λ z₁ → g .fst (f .fst z₁)) , (λ {n} {n'} z₁ → g .snd (f .snd z₁))
GRAPH ℓ ℓ' .⋆IdL _ = refl
GRAPH ℓ ℓ' .⋆IdR _ = refl
GRAPH ℓ ℓ' .⋆Assoc _ _ _ = refl
GRAPH ℓ ℓ' .isSetHom {G}{H}= 
  isSetΣ (isSet→ (H .fst .snd)) 
    λ f → isSetImplicitΠ2 λ n n' → isSet→ (H .snd (f n) (f n') .snd)

idRelator : {ℓ ℓ' : Level}{G : RGraph ℓ ℓ'} → Relator G G 
idRelator {G = G} .fst .fst n = n
idRelator {G = G} .fst .snd e = e
idRelator {G = G} .snd = refl

seqRelator : {ℓ ℓ' : Level}{G H J : RGraph ℓ ℓ'} → Relator G H → Relator H J → Relator G J 
seqRelator f g .fst .fst n = g .fst .fst (f .fst .fst n)
seqRelator f g .fst .snd e = g .fst .snd (f .fst .snd e)
seqRelator {G = G}{H}{J} f g .snd {n} = goal where 

  have : f .fst .snd (G .snd n) ≡ H .snd (f .fst .fst n)
  have = f .snd {n}

  have' : g .fst .snd (H .snd (f .fst .fst n)) ≡ J .snd (g .fst .fst (f .fst .fst n)) 
  have' = g .snd {f .fst .fst n}
  
  goal : g .fst .snd (f .fst .snd (G .snd n)) ≡ J .snd (g .fst .fst (f .fst .fst n))
  goal = cong (λ h → g .fst .snd h ) have ∙ have'

RGRAPH : (ℓ ℓ' : Level) → Category (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-max ℓ ℓ') 
RGRAPH ℓ ℓ' .ob = RGraph ℓ ℓ'
RGRAPH ℓ ℓ' .Hom[_,_] = Relator
RGRAPH ℓ ℓ' .id {G} = idRelator {G = G} 
RGRAPH ℓ ℓ' ._⋆_ {G}{H}{J} f g = seqRelator {G = G}{H}{J} f g
RGRAPH ℓ ℓ' .⋆IdL {G}{H} f = Σ≡Prop (λ x → isPropImplicitΠ λ n → H .fst .snd _ _ .snd _ _)  refl
RGRAPH ℓ ℓ' .⋆IdR {G}{H} f = Σ≡Prop (λ x → isPropImplicitΠ λ n → H .fst .snd _ _ .snd _ _)  refl
RGRAPH ℓ ℓ' .⋆Assoc {G}{H}{J}{K} f g h = Σ≡Prop (λ x → isPropImplicitΠ λ n → K .fst .snd _ _ .snd _ _)  refl
RGRAPH ℓ ℓ' .isSetHom {G}{H} = isSetΣ (isSetΣ (isSet→ (H .fst .fst .snd)) λ f → isSetImplicitΠ2 λ n n' → isSet→  (H .fst .snd (f n) (f n') .snd)) 
  λ _ → isSetImplicitΠ λ _ → isProp→isSet (H .fst .snd _ _ .snd _ _)

FORGET : Functor (GRAPH _ _) (SET _) 
FORGET .F-ob = fst
FORGET .F-hom = fst
FORGET .F-id = refl
FORGET .F-seq _ _ = refl

open import Cubical.Data.Empty 

FREE : Functor (SET _ ) (GRAPH _ _)
FREE .F-ob X = X , (λ x ×' → ⊥ , λ())
FREE .F-hom f = f , λ bot → bot
FREE .F-id = refl
FREE .F-seq _ _ = refl
{-
  we can define Functors 
    GRAPH → RGRAPH 
      where RGRAPH is the category of reflexive graphs 
      by taking the reflexive closure
    GRAPH → CAT 
      by taking the reflexive transitive closure
    GRAPH → PREORDER 
      by taking the reflexive transitive closure
        of a graph with prop edges
-}

module _ {ℓ ℓ' : Level}(G : ob (GRAPH ℓ ℓ')) where 

  N = G .fst 
  E = G .snd 
  
  -- For notes on this implementation of RTC, see 
  -- Shulman - Categorical logic from a categorical point of view
  data _⊢_ : ⟨ N ⟩ → ⟨ N ⟩ → Type (ℓ-max ℓ ℓ') where  
    ref : {n : ⟨ N ⟩} → n ⊢ n

    tran : {X Y Z : ⟨ N ⟩} →
      ⟨ E X Y ⟩ →
      Z ⊢ X →
      Z ⊢ Y

  sub : {X Y Z :  ⟨ N ⟩} → X ⊢ Y → Y ⊢ Z → X ⊢ Z
  sub m ref = m
  sub m (tran x n) = tran x (sub m n)

  sub-idl : {X Y :  ⟨ N ⟩} →(f : X ⊢ Y) → sub ref f ≡ f
  sub-idl ref = refl
  sub-idl (tran x f) = cong₂ tran refl (sub-idl f)

  sub-assoc : {X Y Z W :  ⟨ N ⟩}(f : X ⊢ Y) (g : Y ⊢ Z) (h : Z ⊢ W) →
    sub (sub f g) h ≡ sub f (sub g h)
  sub-assoc f g ref = refl
  sub-assoc f g (tran x h) = cong₂ tran refl (sub-assoc f g h)

  -- could prove this
  -- module _ (isSet⊢ : (n n' : ⟨ N ⟩) → isSet (n ⊢ n') ) where 

  RTCGraph : ob (GRAPH ℓ (ℓ-max ℓ ℓ'))
  RTCGraph .fst = N
  RTCGraph .snd n n' = (n ⊢ n') , {!   !}



  FreeCat : Category ℓ (ℓ-max ℓ ℓ')
  FreeCat .ob = ⟨ N ⟩
  FreeCat .Hom[_,_] = _⊢_
  FreeCat .id = ref
  FreeCat ._⋆_ = sub
  FreeCat .⋆IdL = sub-idl
  FreeCat .⋆IdR _ = refl
  FreeCat .⋆Assoc = sub-assoc
  FreeCat .isSetHom = {!   !}

RTCGraphHom : {G H : ob (GRAPH _ _)} → (GRAPH _ _ ) [ G , H ] → (GRAPH _ _)[ RTCGraph G , RTCGraph H ] 
RTCGraphHom {G} {H} f .fst e = f .fst e
RTCGraphHom {G} {H} f .snd {n}{n'} = go where 
  go : {n n' : ⟨ G .fst ⟩} → (G ⊢ n) n'  → (H ⊢ f .fst n) (f .fst n') 
  go ref = ref
  go (tran x e) = tran (f .snd x) (go e)

open import Cubical.Categories.Instances.Preorders.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Relation.Binary.Preorder renaming (Preorder to Preorder')
open MonFun renaming (f to fun)
open PreorderStr
open  IsPreorder

graphToPre : Graph _ _ → ob (PREORDER _ _) 
graphToPre G .fst .fst = G .fst .fst
graphToPre G .fst .snd ._≤_ = _⊢_ G
graphToPre G .fst .snd .isPreorder .is-prop-valued = {!   !}
graphToPre G .fst .snd .isPreorder .is-refl _ = ref
graphToPre G .fst .snd .isPreorder .is-trans _ _ _ = sub G
graphToPre G .snd = G .fst .snd

graphToPreHom : {G H : Graph _ _ } → (GRAPH _ _ )[ G , H ] → (PREORDER _ _ )[ graphToPre G , graphToPre H ] 
graphToPreHom {G} {H} h .fun = h .fst
graphToPreHom {G} {H} h .isMon ref = ref
graphToPreHom {G} {H} h .isMon {n}{n'} = go where 
  go : {n n' : ⟨ G .fst ⟩} → (G ⊢ n) n'  → (H ⊢ h .fst n) (h .fst n') 
  go ref = ref
  go (tran x e) = tran (h .snd x) (go e)

RTCGraphF : Functor (GRAPH _ _) (PREORDER _ _) 
RTCGraphF .F-ob = graphToPre
RTCGraphF .F-hom = graphToPreHom
RTCGraphF .F-id = eqMon _ _  refl
RTCGraphF .F-seq _ _ = eqMon _ _ refl

{-
RTCGraphF' : Functor (GRAPH _ _) (GRAPH _ _) 
RTCGraphF' .F-ob = RTCGraph
RTCGraphF' .F-hom = RTCGraphHom 
RTCGraphF' .F-id = ΣPathP (refl , implicitFunExt (implicitFunExt (funExt {!   !}))) 
RTCGraphF' .F-seq = {!   !}
-}

pGRAPH : (ℓ ℓ' : Level) → Category (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-max ℓ ℓ') 
pGRAPH ℓ ℓ' = FullSubcategory (GRAPH ℓ ℓ') 
  λ {(N , E) → (n n' : ⟨ N ⟩ ) → isProp ⟨ E n n' ⟩}



pGraphHom≡ : {ℓ ℓ' : Level}{G H : ob (pGRAPH ℓ ℓ')}{f g : (pGRAPH ℓ ℓ') [ G , H ]} 
  → f .fst ≡ g .fst → f ≡ g 
pGraphHom≡ {H = H} prf = 
  Σ≡Prop (λ f → isPropImplicitΠ2 λ n n' → isProp→ (H .snd (f n) (f n'))) prf

Graphᴰ : {ℓ ℓ' : Level}(ℓᴰ ℓᴰ' : Level) → Graph ℓ ℓ' → Type _ 
Graphᴰ ℓᴰ ℓᴰ' (N , E) = 
  Σ[ Nᴰ ∈ (⟨ N ⟩ → hSet ℓᴰ) ] 
  ({n n' : ⟨ N ⟩ } → ⟨ E  n n' ⟩ → ⟨ Nᴰ n ⟩ → ⟨ Nᴰ n' ⟩ →  hSet ℓᴰ')

GraphHomᴰ : {ℓ ℓ' ℓᴰ ℓᴰ' : Level}{G H : Graph ℓ ℓ'} → 
  GraphHom G H → Graphᴰ ℓᴰ ℓᴰ' G → Graphᴰ ℓᴰ ℓᴰ' H → Type _ 
GraphHomᴰ {G = G}{H} f Gᴰ Hᴰ =
  Σ[ fᴰ ∈ ((n : ⟨ G .fst ⟩) → ⟨ Gᴰ .fst n ⟩ → ⟨ Hᴰ .fst (f .fst n) ⟩) ] 
  ({n n' : ⟨ G .fst ⟩}{e : ⟨ G .snd n n' ⟩}
  (nᴰ : ⟨ Gᴰ .fst  n ⟩ )(n'ᴰ : ⟨ Gᴰ .fst n' ⟩ ) → 
  ⟨ Gᴰ .snd e nᴰ n'ᴰ ⟩  → ⟨ Hᴰ .snd (f .snd e) (fᴰ n nᴰ) (fᴰ n' n'ᴰ) ⟩)

GRAPHᴰ : (ℓ ℓ' ℓᴰ ℓᴰ' : Level) → 
  Categoryᴰ (GRAPH ℓ ℓ' ) 
    (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓᴰ)) (ℓ-suc ℓᴰ')) 
    (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓᴰ) ℓᴰ') 
ob[ GRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' ] = Graphᴰ ℓᴰ ℓᴰ'
GRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' .Hom[_][_,_] {G} {H} = GraphHomᴰ {G = G}{H}
GRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' .idᴰ .fst n nᴰ = nᴰ
GRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' .idᴰ .snd nᴰ nᴰ' eᴰ = eᴰ
GRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' ._⋆ᴰ_ {G}{H}{K}{f}{g}{Gᴰ}{Hᴰ}{Kᴰ} fᴰ gᴰ .fst n nᴰ = 
    gᴰ .fst (f .fst n) (fᴰ .fst n nᴰ)
GRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' ._⋆ᴰ_ {G}{H}{K}{f}{g}{Gᴰ}{Hᴰ}{Kᴰ} fᴰ gᴰ .snd nᴰ nᴰ' eᴰ = 
    gᴰ .snd (fᴰ .fst _ nᴰ) (fᴰ .fst _ nᴰ') (fᴰ .snd nᴰ nᴰ' eᴰ)
GRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' .⋆IdLᴰ _ = refl
GRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' .⋆IdRᴰ  _ = refl
GRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' .⋆Assocᴰ _ _ _ = refl
GRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' .isSetHomᴰ {G}{H}{f}{Gᴰ}{Hᴰ} = 
  isSetΣ (isSetΠ (λ n → isSet→ (Hᴰ .fst (f .fst n) .snd))) 
  λ fᴰ → isSetImplicitΠ3 λ n n' e → isSetΠ2 λ nᴰ nᴰ' → isSet→ 
  (Hᴰ .snd (f .snd e) (fᴰ n nᴰ) (fᴰ n' nᴰ') .snd)

open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Sets 
open Functorᴰ

FORGETᴰ : Functorᴰ FORGET (GRAPHᴰ _ _ _ _ ) (SETᴰ _ _ )
FORGETᴰ .F-obᴰ = fst
FORGETᴰ .F-homᴰ = fst
FORGETᴰ .F-idᴰ = refl
FORGETᴰ .F-seqᴰ _ _ = refl

pGRAPHᴰ : (ℓ ℓ' ℓᴰ ℓᴰ' : Level) → 
  Categoryᴰ (pGRAPH ℓ ℓ' ) 
    (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓᴰ)) (ℓ-suc ℓᴰ')) 
    (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓᴰ) ℓᴰ') 
ob[ pGRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' ] G = 
  Σ[ Gᴰ ∈ GRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' .ob[_] (G .fst) ] 
  ({n n' : ⟨ G .fst .fst ⟩}{e : ⟨ G .fst .snd n n' ⟩}{nᴰ : ⟨ Gᴰ .fst n ⟩ }{n'ᴰ : ⟨ Gᴰ .fst n' ⟩ }  → 
  isProp ⟨ Gᴰ .snd e nᴰ n'ᴰ ⟩)
pGRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' .Hom[_][_,_] {G}{H} f (Gᴰ , _) (Hᴰ , _)= GRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' .Hom[_][_,_] {G .fst}{H .fst} f Gᴰ Hᴰ
pGRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' .idᴰ {G}{Gᴰ , _}= GRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' .idᴰ {G .fst}{Gᴰ}
pGRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' ._⋆ᴰ_ {G}{H}{K}{f}{g}{Gᴰ , _}{Hᴰ , _}{Kᴰ , _} = GRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' ._⋆ᴰ_ {G  .fst}{H .fst}{K .fst }{f}{g}{Gᴰ}{Hᴰ}{Kᴰ}
pGRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' .⋆IdLᴰ {G}{H}{f}{Gᴰ , _}{Hᴰ , _}= GRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' .⋆IdLᴰ{G .fst}{H .fst}{f}{Gᴰ}{Hᴰ}
pGRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' .⋆IdRᴰ {G}{H}{f}{Gᴰ , _}{Hᴰ , _}= GRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' .⋆IdRᴰ{G .fst}{H .fst}{f}{Gᴰ}{Hᴰ}
pGRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' .⋆Assocᴰ {G}{H}{K}{L}{f}{g}{h}{Gᴰ , _}{Hᴰ , _}{Kᴰ , _}{Lᴰ , _}= 
  GRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' .⋆Assocᴰ {G .fst}{H .fst}{K .fst}{L .fst}{f}{g}{h}{Gᴰ}{Hᴰ}{Kᴰ}{Lᴰ}
pGRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ' .isSetHomᴰ {G}{H}{f}{Gᴰ , _}{Hᴰ , _} = GRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ'  .isSetHomᴰ {G .fst}{H .fst}{f}{Gᴰ}{Hᴰ}

pGraphHomᴰ≡ : {ℓ ℓ' ℓᴰ ℓᴰ' : Level}{G H : ob (pGRAPH ℓ ℓ')}{f : (pGRAPH ℓ ℓ')[ G , H ]}
  {Gᴰ : (pGRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ') .ob[_] G}{Hᴰ : (pGRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ') .ob[_] H}
  {fᴰ gᴰ : (pGRAPHᴰ ℓ ℓ' ℓᴰ ℓᴰ') .Hom[_][_,_]  {G}{H}f Gᴰ Hᴰ}
   → fᴰ .fst ≡ gᴰ .fst  → fᴰ ≡ gᴰ 
pGraphHomᴰ≡ {G = G}{H}{f}{Gᴰ}{Hᴰ}{fᴰ}{gᴰ} prf = 
  ΣPathP (prf , toPathP (implicitFunExt (implicitFunExt (implicitFunExt 
  (funExt λ x → funExt λ y → funExt λ z → Hᴰ .snd
    (transport
     (λ i →
        {n n' : ⟨ G .fst .fst ⟩} {e : ⟨ G .fst .snd n n' ⟩}
        (nᴰ : ⟨ Gᴰ .fst .fst n ⟩) (n'ᴰ : ⟨ Gᴰ .fst .fst n' ⟩) →
        ⟨ Gᴰ .fst .snd e nᴰ n'ᴰ ⟩ →
        ⟨ Hᴰ .fst .snd (f .snd e) (prf i n nᴰ) (prf i n' n'ᴰ) ⟩)
     (fᴰ .snd) x y z)
    (gᴰ .snd x y z))))))


∫Graphᴰ : {ℓ ℓ' ℓᴰ ℓᴰ' : Level} → (G : Graph ℓ ℓ') → (Gᴰ : Graphᴰ ℓᴰ ℓᴰ' G) → Graph (ℓ-max ℓ ℓᴰ) (ℓ-max ℓ' ℓᴰ')
∫Graphᴰ G Gᴰ .fst = (Σ ⟨ G .fst ⟩ λ n → ⟨ Gᴰ .fst n ⟩) , isSetΣ (G .fst .snd) λ x → Gᴰ .fst x .snd
∫Graphᴰ G Gᴰ .snd (n , nᴰ)(n' , n'ᴰ)= 
  Σ ⟨ G .snd n n' ⟩  (λ e → ⟨ Gᴰ .snd e nᴰ n'ᴰ ⟩) , 
  isSetΣ (G .snd n n' .snd) λ x → Gᴰ .snd x nᴰ n'ᴰ .snd

∫GraphHomᴰ : {ℓ ℓ' ℓᴰ ℓᴰ' : Level}{G H : Graph ℓ ℓ'}{Gᴰ : Graphᴰ ℓᴰ ℓᴰ' G}{Hᴰ : Graphᴰ ℓᴰ ℓᴰ' H}
  (f : GraphHom G H)(fᴰ : GraphHomᴰ {G = G}{H} f Gᴰ Hᴰ) → GraphHom (∫Graphᴰ G Gᴰ) (∫Graphᴰ H Hᴰ)
∫GraphHomᴰ f fᴰ .fst (n , nᴰ) = f .fst n , fᴰ .fst n nᴰ
∫GraphHomᴰ {G = G}{H}{Gᴰ}{Hᴰ} f fᴰ .snd {n , nᴰ}{n' , nᴰ'}(e , eᴰ)= f .snd e , fᴰ .snd nᴰ nᴰ' eᴰ