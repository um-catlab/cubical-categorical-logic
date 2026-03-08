module HyperDoc.AsDisplayed where 

open import Cubical.Data.Sigma
open import Cubical.Data.Unit 
open import Cubical.Relation.Binary.Preorder
open import Agda.Builtin.Cubical.Equiv

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure 
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Category 
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf.Representable 

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.BinProduct 
open import Cubical.Categories.Displayed.Instances.Sets

open import Cubical.Categories.Displayed.Fibration
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Limits.BinProduct.Base
open import Cubical.Categories.Displayed.Limits.BinProduct.Properties
open import Cubical.Categories.NaturalTransformation

open import HyperDoc.Syntax
open import HyperDoc.CBPVLogic
open import HyperDoc.CBPVModel
open import HyperDoc.Lib
open import HyperDoc.Connectives.Connectives

open Category
open Categoryᴰ
open Functorᴰ
open Functor
open Iso
open MonFun
open UniversalElement
open NatTrans
open PreorderStr
open MonFun renaming (f to fun)

-- demonstrating that our proof irrelevant model 
-- lines up with the proof relevant version
module convert 
  {ℓ ℓ' ℓP ℓP' : Level}{C : Category ℓ ℓ'}
  (F : Functor (C ^op) (POSET ℓP ℓP')) where 

  open HDSyntax F  

  Cᴰ : Categoryᴰ C ℓP ℓP' 
  ob[ Cᴰ ] = F∣_∣
  Cᴰ .Hom[_][_,_] {x}{y} f Fx Fy = x ◂ Fx ≤ f* f Fy
  Cᴰ .idᴰ = eqTo≤  (sym f*id)
  Cᴰ ._⋆ᴰ_ {f = f} {g} = seq* f g
  Cᴰ .⋆IdLᴰ fᴰ = toPathP (isProp≤ _ fᴰ)
  Cᴰ .⋆IdRᴰ fᴰ = toPathP (isProp≤ _ fᴰ)
  Cᴰ .⋆Assocᴰ _ _ _ = toPathP (isProp≤ _ _)
  Cᴰ .isSetHomᴰ = isProp→isSet isProp≤ 


module Modelᴰ 
  {ℓV ℓV' ℓC ℓC' ℓP ℓP' : Level}
  (M : Model ℓV ℓV' ℓC ℓC' (ℓ-max ℓP ℓP') )
  (L : Logic {ℓP = ℓP} {ℓP'} M) where 

  open Model M 
  open Logic L
  
  Vᴰ : Categoryᴰ V ℓP ℓP' 
  Vᴰ = convert.Cᴰ VH

  Cᴰ : Categoryᴰ C ℓP ℓP' 
  Cᴰ = convert.Cᴰ CH
  
  module VL = HDSyntax VH 
  module CL = HDSyntax CH 

  Oᴰ :  Functorᴰ O ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) (SETᴰ (ℓ-max ℓP ℓP') ℓP'  )
  Oᴰ .F-obᴰ {(A , B)}(P , Q) o = (A VL.◂ P ≤ (Sq .N-ob (A , B) o .fun Q) ), isProp→isSet VL.isProp≤ 
  Oᴰ .F-homᴰ {(A , B)}{(A' , B')}{(f , g)}{(P , Q)}{(P' , Q')}(P'≤f*P , Q≤g*Q' ) o  P≤o*Q = 
    VL.seq  P'≤f*P (
    VL.seq (VL.mon* f P≤o*Q) (
    VL.seq (VL.mon* f (pull o .isMon  Q≤g*Q')) (
    VL.eqTo≤ (sym (cong(λ h → h .fun Q') (funExt⁻ (Sq .N-hom (f , g)) o))))))
  Oᴰ .F-idᴰ = toPathP (funExt λ _ → funExt λ _ → VL.isProp≤ _ _)
  Oᴰ .F-seqᴰ _ _ = toPathP (funExt λ _ → funExt λ _ → VL.isProp≤ _ _)

  open import Cubical.Categories.Displayed.Bifunctor
  open import Cubical.Categories.Bifunctor

  OᴰBif : Bifunctorᴰ (ParFunctorToBifunctor O) (Vᴰ ^opᴰ) Cᴰ (SETᴰ (ℓ-max ℓP ℓP') ℓP')
  OᴰBif = ParFunctorᴰToBifunctorᴰ Oᴰ



{-}
  module Coproducts (cprod : HasO+ M) where 
    open import Cubical.Categories.Presheaf.Morphism.Alt
    open import Cubical.Categories.Displayed.Presheaf.Morphism
    open import Cubical.Categories.Displayed.Constructions.BinProduct.More
    open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Base
    open import Cubical.Foundations.Equiv.Dependent
    open isIsoOver
    open PshIso
    open PshHom

    _+_ : ob V → ob V → ob V 
    _+_ A A' = cprod A A' .fst

    σ₁ : ∀{A A' B} → (M : O[ A + A' , B ]) → O[ A , B ]
    σ₁ {A}{A'}{B} M = cprod A A' .snd .trans .N-ob B M .fst

    σ₂ : ∀{A A' B} → (M : O[ A + A' , B ]) → O[ A' , B ]
    σ₂ {A}{A'}{B} M = cprod A A' .snd .trans .N-ob B M .snd

    case : ∀{A A' B} → O[ A , B ] → O[ A' , B ] → O[ A + A' , B ]
    case {A}{A'}{B} M N = cprod A A' .snd .nIso B .fst (M , N)

    Oᴰ[_,-] : {A : ob V}(aᴰ : ob[ Vᴰ ] A) → Functorᴰ O[ A ,-] Cᴰ (SETᴰ (ℓ-max ℓP ℓP') ℓP') 
    Oᴰ[_,-] aᴰ = Oᴰ ∘Fᴰ rinjᴰ _ _ aᴰ

    hasCompᴰ : Type _ 
    hasCompᴰ = ∀(A A' : ob V)(aᴰ : ob[ Vᴰ ] A)(aᴰ' : ob[ Vᴰ ] A') → 
      Σ[ a+a' ∈ ob[ Vᴰ ] (A + A') ] 
        PshIsoᴰ (cprod A A' .snd) (Oᴰ[ a+a' ,-] ∘Fᴰ from^opᴰ^opᴰ) ((Oᴰ[ aᴰ ,-] ∘Fᴰ from^opᴰ^opᴰ) ×ᴰPsh (Oᴰ[ aᴰ' ,-] ∘Fᴰ from^opᴰ^opᴰ)) 


    module _
      (_⋁_ : ∀{A A'} → ob[ Vᴰ ] A →  ob[ Vᴰ ] A' → ob[ Vᴰ ] (A + A'))
      (σ₁ᴰ : ∀{A A' B aᴰ aᴰ' bᴰ} → (M : O[ A + A' , B  ]) → 
        (A + A') VL.◂ aᴰ ⋁ aᴰ' ≤ (pull M $ bᴰ)  → 
        A VL.◂ aᴰ ≤ (pull (σ₁ M) $ bᴰ))
      (σ₂ᴰ : ∀{A A' B aᴰ aᴰ' bᴰ} → (M : O[ A + A' , B  ]) → 
        (A + A') VL.◂ aᴰ ⋁ aᴰ' ≤ (pull M $ bᴰ)  → 
        A' VL.◂ aᴰ' ≤ (pull (σ₂ M) $ bᴰ))
      (caseᴰ : ∀{A A' B aᴰ aᴰ' bᴰ} → (M : O[ A  , B  ]) → (N : O[ A' , B  ])
         → A  VL.◂ aᴰ ≤  (pull M $ bᴰ) 
        → A' VL.◂  aᴰ' ≤  (pull N $ bᴰ) 
        → (A + A') VL.◂ aᴰ ⋁ aᴰ' ≤  (pull (case M N) $ bᴰ) ) where 


      poke : hasCompᴰ
      poke A A' aᴰ aᴰ' .fst = aᴰ ⋁ aᴰ'
      poke A A' aᴰ aᴰ' .snd .fst .PshHomᴰ.N-obᴰ {B}{bᴰ} {A+A'⊢B} A+A'≤B = σ₁ᴰ A+A'⊢B A+A'≤B , σ₂ᴰ A+A'⊢B A+A'≤B
      poke A A' aᴰ aᴰ' .snd .fst .PshHomᴰ.N-homᴰ = toPathP (ΣPathP ((VL.isProp≤  _ _) , (VL.isProp≤  _ _))) 
      poke A A' aᴰ aᴰ' .snd .snd .inv (M , N) (p1 , p2) = caseᴰ M N p1 p2
      poke A A' aᴰ aᴰ' .snd .snd .rightInv _ _  = toPathP (ΣPathP (VL.isProp≤  _ _ , VL.isProp≤  _ _))
      poke A A' aᴰ aᴰ' .snd .snd .leftInv _ _  = toPathP (VL.isProp≤  _ _)
        --  (Oᴰ[-,  b&b' ] ) (Oᴰ[-, bᴰ ] ×ᴰPsh Oᴰ[-, bᴰ' ])

    {-
      HasO+ : Type (ℓ-max (ℓ-max (ℓ-max ℓV ℓC) ℓC') ℓS) 
  HasO+  = (A A' : ob V) → Σ[ A+A' ∈ ob V ] PshIso (O[ A+A' ,-] ∘F from^op^op) ((O[ A ,-] ∘F from^op^op) ×Psh (O[ A' ,-] ∘F from^op^op))
    -}
  -}

  module _ 
    (⊤ : L⊤.Has⊤ VH)
    (V⊤ : HasV⊤  M) where

    open L⊤.HA 
    open L⊤.HAHom

    Vterm : Terminal' V
    Vterm .vertex = V⊤ .fst
    Vterm .element = tt
    Vterm .universal A .equiv-proof tt .fst = {!   !} , {!   !}
    Vterm .universal A .equiv-proof tt .snd = {!   !}

    Vᴰtermⱽ : Terminalsⱽ Vᴰ
    Vᴰtermⱽ c .UniversalElementⱽ.vertexⱽ = top (⊤ .fst c)
    Vᴰtermⱽ c .UniversalElementⱽ.elementⱽ = tt
    Vᴰtermⱽ c .UniversalElementⱽ.universalⱽ {y = c'}{f = f} .fst tt = VL.seq (top-top (⊤ .fst c')) (VL.eqTo≤ (sym (f-top (⊤ .snd f) )))
    Vᴰtermⱽ c .UniversalElementⱽ.universalⱽ .snd .fst tt = refl
    Vᴰtermⱽ c .UniversalElementⱽ.universalⱽ .snd .snd a = VL.isProp≤ _ a

    open import Cubical.Foundations.Equiv.Dependent
    Vᴰtermᴰ : Terminalᴰ Vᴰ Vterm 
    Vᴰtermᴰ .UniversalElementᴰ.vertexᴰ = top (⊤ .fst (Vterm .vertex))
    Vᴰtermᴰ .UniversalElementᴰ.elementᴰ = tt
    Vᴰtermᴰ .UniversalElementᴰ.universalᴰ .isIsoOver.inv = {!   !}
    Vᴰtermᴰ .UniversalElementᴰ.universalᴰ .isIsoOver.rightInv = {!   !}
    Vᴰtermᴰ .UniversalElementᴰ.universalᴰ .isIsoOver.leftInv = {!   !}
      -- Terminalⱽ→Terminalᴰ Vᴰ (Vᴰtermⱽ (TerminalNotation.𝟙 Vterm))

    Cᴰbpⱽ : BinProductsⱽ Cᴰ 
    Cᴰbpⱽ x (P , Q) .UniversalElementⱽ.vertexⱽ = P
    Cᴰbpⱽ x (P , Q) .UniversalElementⱽ.elementⱽ = {!   !} , {!   !}
    Cᴰbpⱽ x (P , Q) .UniversalElementⱽ.universalⱽ = {!   !}
{-}

  open import Cubical.Categories.Displayed.Constructions.BinProduct.More
  --O[-,_] : (c : ob C) → Functor (V ^op) (SET ℓS)
  --O[-,_] c = O ∘F linj _ _ c
  Oᴰ[-,_] : {B : ob C}(bᴰ : ob[ Cᴰ ] B) → Functorᴰ O[-, B ] (Vᴰ ^opᴰ) (SETᴰ ℓV ℓV)
  Oᴰ[-,_] bᴰ = Oᴰ ∘Fᴰ linjᴰ _ _ bᴰ
  -- testing 
  --open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
  open import Cubical.Categories.Displayed.Presheaf.Morphism
  open import Cubical.Categories.Presheaf.Morphism.Alt
  open import Cubical.Categories.Presheaf.Base
  open import Cubical.Categories.Presheaf.Constructions.BinProduct.Base hiding(π₁ ; π₂)
  open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Base


  -- computation products in base 
  hasComp : Type _ 
  hasComp = ∀(B B' : ob C) → Σ[ B&B' ∈ ob C ] PshIso O[-, B&B' ] (O[-, B ] ×Psh O[-, B' ])

  hasCompᴰ : hasComp → Type _ 
  hasCompᴰ prod = ∀(B B' : ob C)(bᴰ : ob[ Cᴰ ] B)(bᴰ' : ob[ Cᴰ ] B') → 
    Σ[ b&b' ∈ ob[ Cᴰ ] (prod B  B' .fst) ] 
      PshIsoᴰ (prod B B' .snd) (Oᴰ[-,  b&b' ] ) (Oᴰ[-, bᴰ ] ×ᴰPsh Oᴰ[-, bᴰ' ])
    
  -- so what do we need in the hyperdoctrine to satisfy this ^ 

  module _ 
    (prod : hasComp)
    (and : L∧.Has∧ CH ) where
    open PshIso
    open PshHom
    open import Cubical.Foundations.Equiv.Dependent
    open isIsoOver

    _&_ : ob C → ob C → ob C
    _&_ B B' = prod B B' .fst

    cπ₁ : ∀{A B B'} → (M : O[ A , B & B' ]) → O[ A , B ]
    cπ₁ {A}{B}{B'} M = prod B B' .snd .trans .N-ob A M .fst

    cπ₂ : ∀{A B B'} → (M : O[ A , B & B' ]) → O[ A , B' ]
    cπ₂ {A}{B}{B'} M = prod B B' .snd .trans .N-ob A M .snd

    kπ₁ : ∀{B B'} → C [ B & B' , B ] 
    kπ₁ = {!   !}

    〈_,_〉 : ∀{A B B'} → O[ A , B ] → O[ A , B' ] → O[ A , B & B' ]
    〈_,_〉 {A}{B}{B'} M N = prod B B' .snd .nIso A .fst (M , N)

    -- the vertical product
    --_⋀_ : ∀{B} → ob[ Cᴰ ] B → ob[ Cᴰ ] B → ob[ Cᴰ ] B
    --_⋀_ {B} P Q = and .fst B .L∧.HA._∧_ P Q

    -- we don't have binary products in C
    -- so we can't make displayed products in Cᴰ


    module _ 
      (_⋀_ : ∀{B B'} → ob[ Cᴰ ] B →  ob[ Cᴰ ] B' → ob[ Cᴰ ] (B & B'))
      (to : ∀{A B B' aᴰ bᴰ bᴰ'} → (M : O[ A , B & B' ]) → 
        A VL.◂ aᴰ ≤ pull  M .fun (bᴰ ⋀ bᴰ') → (A VL.◂ aᴰ ≤  pull (cπ₁ M) .fun bᴰ) × (A VL.◂ aᴰ ≤ pull (cπ₂  M) .fun bᴰ'))
      (fro : ∀{A B B' aᴰ bᴰ bᴰ'} → (M : O[ A , B ])(N : O[ A , B' ]) → (A VL.◂ aᴰ ≤ pull M .fun bᴰ) × (A VL.◂ aᴰ ≤ pull N .fun bᴰ') 
        → A VL.◂ aᴰ ≤ pull 〈 M , N 〉 .fun (bᴰ ⋀ bᴰ')) where 


      disp : hasCompᴰ prod 
      disp B B' bᴰ bᴰ' .fst = (bᴰ ⋀ bᴰ')
      disp B B' bᴰ bᴰ' .snd .fst .PshHomᴰ.N-obᴰ {A}{aᴰ} {A⊢B&B'} A≤B&B' = to A⊢B&B' A≤B&B'
      disp B B' bᴰ bᴰ' .snd .fst .PshHomᴰ.N-homᴰ = toPathP (ΣPathP ((VL.isProp≤  _ _) , (VL.isProp≤  _ _)))
      disp B B' bᴰ bᴰ' .snd .snd .inv (M , N ) (p1 , p2) = fro M N (p1 , p2)
      disp B B' bᴰ bᴰ' .snd .snd .rightInv b q = toPathP (ΣPathP (VL.isProp≤  _ _ , VL.isProp≤  _ _))
      disp B B' bᴰ bᴰ' .snd .snd .leftInv a p = toPathP (VL.isProp≤  _ _)
      -- (bᴰ ⋀ bᴰ') , {! d !} , {!   !}

    _ = {!   !}

-}

{-}
  module Modelᴰstruct
    ((V⊤  , UTy , FTy ) : TypeStructure  M)
    (⊤ : L⊤.Has⊤ VH) where 

    open L⊤.HA 
    open L⊤.HAHom

    open TypeSyntax (M , V⊤  , UTy , FTy ) renaming(⊤ to ⊤ty ; tt to tterm)


    Vterm : Terminal' V
    Vterm .vertex = ⊤ty
    Vterm .element = tt
    Vterm .universal A .equiv-proof tt = {!   !}

    open import  Cubical.Categories.Limits.Terminal.More
    open TerminalNotation Vterm
    -- _ = {! !t !}

    --  Cubical.Categories.Limits.Terminal.More

    Vᴰtermⱽ : Terminalsⱽ Vᴰ
    Vᴰtermⱽ c .UniversalElementⱽ.vertexⱽ = top (⊤ .fst c)
    Vᴰtermⱽ c .UniversalElementⱽ.elementⱽ = tt
    Vᴰtermⱽ c .UniversalElementⱽ.universalⱽ {y = c'}{f = f} .fst tt = VL.seq (top-top (⊤ .fst c')) (VL.eqTo≤ (sym (f-top (⊤ .snd f) )))
    Vᴰtermⱽ c .UniversalElementⱽ.universalⱽ .snd .fst tt = refl
    Vᴰtermⱽ c .UniversalElementⱽ.universalⱽ .snd .snd a = VL.isProp≤ _ a

    Vᴰtermᴰ : Terminalᴰ Vᴰ Vterm 
    Vᴰtermᴰ = Terminalⱽ→Terminalᴰ Vᴰ (Vᴰtermⱽ (TerminalNotation.𝟙 Vterm))



  {-}
  Vᴰtermⱽ : Terminalsⱽ Vᴰ
  Vᴰtermⱽ c .UniversalElementⱽ.vertexⱽ = top (⊤ .fst c)
  Vᴰtermⱽ c .UniversalElementⱽ.elementⱽ = tt
  Vᴰtermⱽ c .UniversalElementⱽ.universalⱽ {y = c'}{f = f} .fst tt = LV.seq (top-top (⊤ .fst c')) (LV.eqTo≤ (sym (f-top (⊤ .snd f) )))
  Vᴰtermⱽ c .UniversalElementⱽ.universalⱽ .snd .fst tt = refl
  Vᴰtermⱽ c .UniversalElementⱽ.universalⱽ .snd .snd a = LV.isProp≤ _ a
  -}

  -}

  
{-

module _ 
  {ℓV ℓV' ℓC ℓC' ℓS ℓP ℓP' ℓR : Level}
  {(M , V⊤  , UTy , FTy , C×) : ModelWithTypeStructure ℓV ℓV' ℓC ℓC' ℓS}
  (L : Logic M ) 
  ((⊤ , ∧) : WithConnectives L)where 

  open TypeSyntax (M , V⊤  , UTy , FTy , C×) renaming(⊤ to ⊤ty ; tt to tterm)

  open Model M 
  open Logic L
  --open L⊤.HA 
  -- open L∧.HA renaming (_∧_ to and)
  open L⊤.HA 
  open L∧.HA renaming (_∧_ to and)
  module LV = HDSyntax VH
  module LC = HDSyntax CH
  open L⊤.HAHom
  open L∧.HAHom

  Vterm : Terminal' V
  Vterm .vertex = ⊤ty
  Vterm .element = tt
  Vterm .universal A .equiv-proof tt = {!   !}

  Cbp : BinProducts C 
  Cbp (a , b) .vertex = a & b
  Cbp (a , b) .element = (π₁ (C .id)) , π₂ (C .id)
  Cbp (a , b) .universal A .equiv-proof (f , g) = ({!   !} , {!   !}) , (λ y   → {!   !})


  Vᴰ : Categoryᴰ V ℓV ℓV 
  Vᴰ = convert.Cᴰ VH

  Cᴰ : Categoryᴰ C ℓV ℓV 
  Cᴰ = convert.Cᴰ CH

  VHisFibration : isFibration Vᴰ 
  VHisFibration cᴰ p .UniversalElementⱽ.vertexⱽ = VH .F-hom p .f cᴰ
  VHisFibration cᴰ p .UniversalElementⱽ.elementⱽ = LV.eqTo≤ (cong (λ h → VH .F-hom h .f cᴰ) (sym (V .⋆IdL p)))
  VHisFibration cᴰ p .UniversalElementⱽ.universalⱽ .fst prf = LV.seq prf (LV.eqTo≤ (cong (λ h → h .f cᴰ) (VH .F-seq _ _)))
  VHisFibration cᴰ p .UniversalElementⱽ.universalⱽ .snd .fst _ = LV.isProp≤ _ _
  VHisFibration cᴰ p .UniversalElementⱽ.universalⱽ .snd .snd _ = LV.isProp≤ _ _

  CHisFibration : isFibration Cᴰ 
  CHisFibration cᴰ p .UniversalElementⱽ.vertexⱽ = CH .F-hom p .f cᴰ
  CHisFibration cᴰ p .UniversalElementⱽ.elementⱽ = LC.eqTo≤ (cong (λ h → CH .F-hom h .f cᴰ) (sym (C .⋆IdL p)))
  CHisFibration cᴰ p .UniversalElementⱽ.universalⱽ .fst prf = LC.seq prf (LC.eqTo≤ (cong (λ h → h .f cᴰ) (CH .F-seq _ _)))
  CHisFibration cᴰ p .UniversalElementⱽ.universalⱽ .snd .fst _ = LC.isProp≤ _ _
  CHisFibration cᴰ p .UniversalElementⱽ.universalⱽ .snd .snd _ = LC.isProp≤ _ _

  Vᴰtermⱽ : Terminalsⱽ Vᴰ
  Vᴰtermⱽ c .UniversalElementⱽ.vertexⱽ = top (⊤ .fst c)
  Vᴰtermⱽ c .UniversalElementⱽ.elementⱽ = tt
  Vᴰtermⱽ c .UniversalElementⱽ.universalⱽ {y = c'}{f = f} .fst tt = LV.seq (top-top (⊤ .fst c')) (LV.eqTo≤ (sym (f-top (⊤ .snd f) )))
  Vᴰtermⱽ c .UniversalElementⱽ.universalⱽ .snd .fst tt = refl
  Vᴰtermⱽ c .UniversalElementⱽ.universalⱽ .snd .snd a = LV.isProp≤ _ a

  Vᴰtermᴰ : Terminalᴰ Vᴰ Vterm 
  Vᴰtermᴰ = Terminalⱽ→Terminalᴰ Vᴰ (Vᴰtermⱽ (TerminalNotation.𝟙 Vterm))

  Cᴰbpⱽ : BinProductsⱽ Cᴰ 
  Cᴰbpⱽ x (P , Q) .UniversalElementⱽ.vertexⱽ = and (∧ .fst x) P Q
  Cᴰbpⱽ x (P , Q) .UniversalElementⱽ.elementⱽ = (LC.f*id' (and-elim1 (∧ .fst x) LC.id⊢)) , LC.f*id' (and-elim2 (∧ .fst x) LC.id⊢)
  Cᴰbpⱽ x (P , Q) .UniversalElementⱽ.universalⱽ {y = y}{f = f} .fst (R≤f*P , R≤f*Q)= LC.seq (and-intro (∧ .fst y)  R≤f*P R≤f*Q) (LC.eqTo≤  (sym (f-and (∧ .snd f) _ _)))
  Cᴰbpⱽ x (P , Q) .UniversalElementⱽ.universalⱽ .snd .fst (prf , prf') = ΣPathP ((LC.isProp≤ _ _) , LC.isProp≤ _ _)
  Cᴰbpⱽ x (P , Q) .UniversalElementⱽ.universalⱽ .snd .snd _ = LC.isProp≤ _ _

  Cᴰbpᴰ : BinProductsᴰ Cᴰ Cbp
  Cᴰbpᴰ = BinProductsⱽ→BinProductsᴰ _ CHisFibration Cᴰbpⱽ Cbp

  module SETᴰ = Fibers (SETᴰ ℓS ℓV)

--  open ORelFunctor ORel

{-
-- Recommendation: implement PROPᴰ and then implement this as a composition of a ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) to PROPᴰ and a vertical functor PROPᴰ to SETᴰ
Oᴰ : Functorᴰ O ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) (SETᴰ ℓS ℓV)
Oᴰ .F-obᴰ (P , Q) o = ⟨ Rel P Q o ⟩ , isProp→isSet (Rel P Q o .snd)
Oᴰ .F-homᴰ {(v , c)}{(v' , c')}{(f , g)}{(P , Q)}{(P' , Q')}(v'P'≤f*P' , c'Q'≤g*Q) o =
  RelMono v'P'≤f*P' c'Q'≤g*Q
Oᴰ .F-idᴰ {(v , c)}{(P , Q)} =
  -- agda can't fill in these implicits because there is no canonical choice
  SETᴰ.rectifyOut {a = O ⟅ (v , c) ⟆ }{b = O ⟅ (v , c) ⟆ }
    {aᴰ = λ o → ⟨ Rel P Q o ⟩ , isProp→isSet (Rel P Q o .snd)}
    {bᴰ = λ o → ⟨ Rel P Q o ⟩ , isProp→isSet (Rel P Q o .snd)}
    (ΣPathP (O .F-id , toPathP (funExt λ o → funExt λ r → Rel P Q o .snd _ r)))
Oᴰ .F-seqᴰ {(v , c)}{(v' , c')}{(v'' , c'')}{(f , g)}{(f' , g')}{(P , Q)}{(P' , Q')}{(P'' , Q'')} fᴰ gᴰ =
  SETᴰ.rectifyOut {a = O ⟅ (v , c) ⟆}{b = O ⟅ (v'' , c'') ⟆}{aᴰ = λ o → ⟨ Rel P Q o ⟩ , isProp→isSet (Rel P Q o .snd)}{bᴰ = λ o → ⟨ Rel P'' Q'' o ⟩ , isProp→isSet (Rel P'' Q'' o .snd)}
    
    (ΣPathP (O .F-seq _ _ , toPathP (funExt λ o → funExt λ r → Rel P'' Q'' (O .F-hom (f' , g') (O .F-hom (f , g) o)) .snd _ _ )))
-}
-}