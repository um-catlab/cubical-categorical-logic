{-# OPTIONS --type-in-type #-}
module HyperDoc.Examples.Beep where 

open import Cubical.Data.List 
open import Cubical.Data.Sigma 
open import Cubical.Data.Unit hiding (terminal)
open import Cubical.Data.Empty

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Graph.Base 
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Constructions.BinProduct

open import HyperDoc.Models.Free1UF 
open import HyperDoc.Models.ManualWriter hiding (F)
open import HyperDoc.Effects.ManualWriter
open import HyperDoc.CBPVModel
open import HyperDoc.Lib

open Initiality
open FreeModel
open PshHom
open Functor
open Writer (Unit* , isSetUnit*)

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

m : ModelMorphism _ _ _ _ _ _ _ _ _ _  (M Sig) N
m = M-rec {R = Sig}{N , has⊤ {M = Unit* , isSetUnit*} , hasUTy {M = Unit* , isSetUnit*} , hasFTy {M = Unit* , isSetUnit*}} 
  interp 
  λ _ → Writer.c* tt* (Writer.ret tt*)

ex : one ⊢c F one 
ex = plug (bind beep) (plug (bind beep) Syntax.ret)

_ : m .FO .N-ob _ ex tt* ≡ Writer.c* tt* (Writer.c* tt* (Writer.ret tt*))
_ = refl
