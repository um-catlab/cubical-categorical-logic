{-# OPTIONS --type-in-type #-}
module HyperDoc.Examples.Beep where 

open import Cubical.Data.List hiding (elim)
open import Cubical.Data.Sigma 
open import Cubical.Data.Unit hiding (terminal)
open import Cubical.Data.Empty hiding (elim)

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Graph.Base 
open import Cubical.Categories.Category 
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Base

open import HyperDoc.Models.Free1UF 
open import HyperDoc.Models.ManualWriter hiding (F)
open import HyperDoc.Effects.ManualWriter
open import HyperDoc.CBPVModel
open import HyperDoc.Lib
open import HyperDoc.Section
open import HyperDoc.Syntax
open import HyperDoc.CBPVLogic
open import HyperDoc.AsDisplayed


open Initiality
open FreeModel
open PshHom
open Functor
open Writer (Unit* , isSetUnit*)
open Categoryᴰ

-- No, need a quiver/graph that is aware of the existing type structure
Sig : Raw _ _ _ _ _ 
Sig .Raw.VG .Node = ⊥
Sig .Raw.VG .Edge ()
Sig .Raw.CG .Node = ⊥
Sig .Raw.CG .Edge ()
Sig .Raw.OF ()

open Syntax Sig 
open ModelInterpretation 
open ModelMorphism 

N = CBPVWrite {M = Unit* , isSetUnit*}

interp : ModelInterpretation Sig N
interp .interpV ._$g_  ()
interp .interpV ._<$g>_ {()} 
interp .interpC ._$g_ ()
interp .interpC ._<$g>_ {()}
interp .interpO ()


clCTm : (B : CTy) → Type _ 
clCTm B = (O Sig) .F-ob (one , B) .fst

m : ModelMorphism _ _ _ _ _ _ _ _ _ _  (M Sig) N
m .FV = (V Sig) [ one ,-]
m .FC .F-ob B = FreeWriterAlg (clCTm B) , {!   !}
m .FC .F-hom {B}{B'} S = ext (FreeWriterAlg (clCTm B')) λ M → Writer.ret (plug S M)
m .FC .F-id {B} = 
  extExt {X = one ⊢c B}{B = FreeWriterAlg (clCTm B)  , {!   !}}(funExt λ M → cong Writer.ret plugId) 
  ∙ sym extUP 

  -- WriterHom≡  {!   !} (sym (extUP (FreeWriterAlg (clCTm B)) (|ext| (FreeWriterAlg (clCTm B))
  --  (λ M₁ → ret (plug (Model.C (M Sig) .Category.id) M₁)))) ∙ {!  funE !})
m .FC .F-seq f g = {!   !}
m .FO .N-ob (A , B) M V = Writer.ret (subC V M)
m .FO .N-hom (A , B)(A' , B') (V , S) M = funExt λ W → cong Writer.ret (subDist ∙ plugSub)

L : Logic N
L = CBPVLogic {M = Unit* , isSetUnit*} 

open Logic L


module LV = HDSyntax VH
module LC = HDSyntax CH

_ = {! Vᴰ N L !}

lvty : (A : VTy) → one ⊢v A → hProp _
lvty A (subV V₁ V₂) = Vᴰ N L ._⋆ᴰ_  {!   !} {!   !} {!   !} {!   !} {!   !}
lvty A var = {!   !}
lvty A (subVIdl V₁ i) = {!   !}
lvty A (subVIdr V₁ i) = {!   !}
lvty A (subVAssoc V₁ V₂ V₃ i) = {!   !}
lvty A tt = {!   !}
lvty A (oneη i) = {!   !}
lvty A (thunk x) = {!   !}
lvty A (Uη i) = {!   !}
lvty A (isSet⊢v V₁ V₂ x y i i₁) = {!   !}

lcty : (B : CTy) → {!   !} 
lcty = {!   !}

elim : MSection {M = M Sig}{N} m CBPVLogic 
elim .fst .Section.F-obᴰ = lvty
elim .fst .Section.F-homᴰ = {!   !}
elim .fst .Section.F-idᴰ = toPathP (LV.isProp≤ {!   !} {!   !})
elim .fst .Section.F-seqᴰ = {!   !}
elim .snd .fst .Section.F-obᴰ = {!   !}
elim .snd .fst .Section.F-homᴰ = {!   !}
elim .snd .fst .Section.F-idᴰ = {!   !}
elim .snd .fst .Section.F-seqᴰ = {!   !}
elim .snd .snd = {!   !}

{-}
m : ModelMorphism _ _ _ _ _ _ _ _ _ _  (M Sig) N
m = M-rec {R = Sig}{N , has⊤ {M = Unit* , isSetUnit*} , hasUTy {M = Unit* , isSetUnit*} , hasFTy {M = Unit* , isSetUnit*}} 
  interp 
  λ _ → Writer.c* tt* (Writer.ret tt*)

ex : one ⊢c F one 
ex = plug (bind beep) (plug (bind beep) ret)

_ : m .FO .N-ob _ ex tt* ≡ Writer.c* tt* (Writer.c* tt* (Writer.ret tt*))
_ = refl

-}
