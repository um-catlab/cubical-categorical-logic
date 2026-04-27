module HyperDoc.Operational.Cat where 

open import Cubical.Data.Sigma 
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category 

open import Cubical.Categories.Functor

open Category


GrpCat :  {ℓ ℓ' : Level} → Category (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-max ℓ ℓ') 
GrpCat .ob = hGroupoid {!   !}
GrpCat .Hom[_,_] = {!   !}
GrpCat .id = {!   !}
GrpCat ._⋆_ = {!   !}
GrpCat .⋆IdL = {!   !}
GrpCat .⋆IdR = {!   !}
GrpCat .⋆Assoc = {!   !}
GrpCat .isSetHom = {!   !}

CAT : {ℓ ℓ' : Level} → Category (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-max ℓ ℓ') 
CAT {ℓ}{ℓ'} .ob = Σ[ C ∈ Category ℓ ℓ' ] isSet (C .ob)
CAT .Hom[_,_] (C , _)(D , _) = Functor C D 
CAT .id = Id
CAT ._⋆_ F G = G ∘F F
CAT .⋆IdL _ = F-lUnit
CAT .⋆IdR _ = F-rUnit
CAT .⋆Assoc _ _ _ = F-assoc
CAT .isSetHom {C , obCSet}{D , obDSet} = isSetFunctor obDSet

hmm : ob CAT 
hmm .fst .ob = hSet _
hmm .fst .Hom[_,_] = {!   !}
hmm .fst .id = {!   !}
hmm .fst ._⋆_ = {!   !}
hmm .fst .⋆IdL = {!   !}
hmm .fst .⋆IdR = {!   !}
hmm .fst .⋆Assoc = {!   !}
hmm .fst .isSetHom = {!   !}
hmm .snd = {!   !}
Logic : Category _ _ → Type {!   !}
Logic C = Functor (C ^op) CAT

