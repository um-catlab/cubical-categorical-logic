-- A subobject of `c` in a category `D` is a monomorphism into `c`.
--
-- We build the category of subobjects of `c` compositionally as a displayed
-- category over `D`: it is the `StructureOver` whose structure on an object
-- `a` is a mono `a → c`, and whose (propositional) hom-constraint on a map
-- `f : a → a'` is that the triangle commutes.  `SubobjectCat` is its total
-- category.  Sieves instantiate this at `(PSh C , よc)`.
module Cubical.Categories.Subobject.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Morphism
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.StructureOver.Base
open import Cubical.Categories.Instances.TotalCategory

open Category

private
  variable
    ℓ ℓ' : Level

module _ (D : Category ℓ ℓ') (c : D .ob) where
  private module D = Category D

  -- structure on `a`: a mono into c ;  constraint on `f`: the triangle commutes
  SubobjectStr : StructureOver D (ℓ-max ℓ ℓ') ℓ'
  SubobjectStr .StructureOver.ob[_] a = Σ[ m ∈ D [ a , c ] ] isMonic D m
  SubobjectStr .StructureOver.Hom[_][_,_] f m m' = (f D.⋆ m' .fst) ≡ m .fst
  SubobjectStr .StructureOver.idᴰ {p = m} = D.⋆IdL (m .fst)
  SubobjectStr .StructureOver._⋆ᴰ_ {f = f} {g = g} {zᴰ = m''} p q =
    D.⋆Assoc f g (m'' .fst) ∙ cong (f D.⋆_) q ∙ p
  SubobjectStr .StructureOver.isPropHomᴰ = D.isSetHom _ _

  Subobjectᴰ : Categoryᴰ D (ℓ-max ℓ ℓ') ℓ'
  Subobjectᴰ = StructureOver→Catᴰ SubobjectStr

  -- subobjects of c, with refinement morphisms (commuting triangles)
  SubobjectCat : Category (ℓ-max ℓ ℓ') ℓ'
  SubobjectCat = ∫C Subobjectᴰ

  -- a subobject of c = a mono into c
  Subobject : Type (ℓ-max ℓ ℓ')
  Subobject = SubobjectCat .ob

  module _ (S : Subobject) where
    sub-dom : D .ob
    sub-dom = S .fst

    sub-incl : D [ sub-dom , c ]
    sub-incl = S .snd .fst

    sub-isMonic : isMonic D sub-incl
    sub-isMonic = S .snd .snd
