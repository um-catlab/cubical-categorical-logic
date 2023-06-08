-- The graph of a profunctor
module Cubical.Categories.Constructions.Graph where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Foundations.Prelude hiding (Square)
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Profunctor.General

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS : Level

open Category hiding (_∘_)
open Functor

-- Examples:
module Graph {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
             (P : C o-[ ℓS ]-* D) where
  Element : Type _
  Element = Σ[ c ∈ C .ob ] Σ[ d ∈ D .ob ] (P ⟅ c , d ⟆) .fst

  Square : Element → Element → Type _
  Square (c , d , p) (c' , d' , p') =
    -- more convenient bc the rhs is a prop
    Σ[ (f , g) ∈ C [ c , c' ] × D [ d , d' ] ]
    P .F-hom ((C .id) , g) p ≡ P .F-hom (f , D .id) p'

  Graph : Category _ _
  Graph .ob = Element
  Graph .Hom[_,_] = Square
  Graph .id = (C .id , D .id) , refl
  Graph ._⋆_ {x = p}{y = p'}{z = p''} ((f , g) , comm) ((f' , g') , comm') =
    -- Time to implement a profunctor solver I guess lol
    (f ⋆⟨ C ⟩ f' , g ⋆⟨ D ⟩ g') ,
    (P .F-hom (C .id , g ⋆⟨ D ⟩ g') (p .snd .snd)
      ≡[ i ]⟨ P .F-hom (C .⋆IdR (C .id) (~ i) , g ⋆⟨ D ⟩ g') (p .snd .snd) ⟩
     P .F-hom (C .id ⋆⟨ C ⟩ C .id , g ⋆⟨ D ⟩ g') (p .snd .snd)
      ≡[ i ]⟨ P .F-seq (C .id , g) (C .id , g') i (p .snd .snd) ⟩
     P .F-hom (C .id , g') (P .F-hom (C .id , g) (p .snd .snd))
      ≡[ i ]⟨ P .F-hom (C .id , g') (comm i) ⟩
     P .F-hom (C .id , g') (P .F-hom (f , D .id) (p' .snd .snd))
      ≡[ i ]⟨ P .F-seq (f , D .id) (C .id , g') (~ i) (p' .snd .snd) ⟩
     P .F-hom (C .id ⋆⟨ C ⟩ f , D .id ⋆⟨ D ⟩ g') (p' .snd .snd)
      ≡[ i ]⟨ P .F-hom (C .⋆IdL f i , D .⋆IdL g' i) (p' .snd .snd) ⟩
     P .F-hom (f , g') (p' .snd .snd)
      ≡[ i ]⟨ P .F-hom (C .⋆IdR f (~ i) , D .⋆IdR g' (~ i)) (p' .snd .snd) ⟩
     P .F-hom (f ⋆⟨ C ⟩ C .id , g' ⋆⟨ D ⟩ D .id) (p' .snd .snd)
       ≡[ i ]⟨ P .F-seq (C .id , g') (f , D .id) i (p' .snd .snd) ⟩
     P .F-hom (f , D .id) (P .F-hom (C .id , g') (p' .snd .snd))
      ≡[ i ]⟨ P .F-hom (f , D .id) (comm' i) ⟩
     P .F-hom (f , D .id) (P .F-hom (f' , (D .id)) (p'' .snd .snd))
      ≡[ i ]⟨ P .F-seq (f' , (D .id)) (f , (D .id)) (~ i) (p'' .snd .snd) ⟩
     P .F-hom (f ⋆⟨ C ⟩ f' , D .id ⋆⟨ D ⟩ D .id) (p'' .snd .snd)
      ≡[ i ]⟨ P .F-hom (f ⋆⟨ C ⟩ f' , D .⋆IdR (D .id) i) (p'' .snd .snd) ⟩
     P .F-hom (f ⋆⟨ C ⟩ f' , D .id) (p'' .snd .snd)
     ∎)
  Graph .⋆IdL ((f , g), comm) =
    Σ≡Prop (λ x → P .F-ob _ .snd _ _) (≡-× (C .⋆IdL f) (D .⋆IdL g))
  Graph .⋆IdR ((f , g), comm) =
    Σ≡Prop (λ x → P .F-ob _ .snd _ _) (≡-× (C .⋆IdR f) (D .⋆IdR g))
  Graph .⋆Assoc ((f , g) , comm) ((f' , g') , comm') ((f'' , g'') , comm'') =
    Σ≡Prop (λ x → P .F-ob _ .snd _ _)
           (≡-× (C .⋆Assoc f f' f'') (D .⋆Assoc g g' g''))
  Graph .isSetHom =
    isSetΣ (isSet× (C .isSetHom) (D .isSetHom)) λ x →
      isProp→isSet (P .F-ob _ .snd _ _)

  -- TODO: isUnivalent if C, D are
