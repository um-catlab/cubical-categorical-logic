{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Double.Instances.Span.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.TotalCategory.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Pullback.Alt
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.BinProduct

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Graph.Presheaf

open Categoryᴰ

module SpanDefs {ℓC ℓC'}
  (C : Category ℓC ℓC')
  (pbs : Pullbacks C)
  where
  private
    module C = Category C

  open PullbackNotation public

  module _ (l r : C.ob) where
    SpanPsh : Presheaf C _
    SpanPsh = (C [-, l ]) ×Psh (C [-, r ])

    SpanPshElt : Categoryᴰ C _ _
    SpanPshElt = Element SpanPsh

    SpanCat : Category _ _
    SpanCat = ∫C SpanPshElt

    Span : Type _
    Span = SpanCat .Category.ob

  module _ {x y z w : C.ob}
    ((xy , f , g) : Span x y) ((zw , u , v) : Span z w)
    (x→z : C [ x , z ]) (y→w : C [ y , w ]) where
    SpanSquare : Type _
    SpanSquare = Σ[ xy→zw ∈ C [ xy , zw ] ]
      (f C.⋆ x→z ≡ xy→zw C.⋆ u) × (g C.⋆ y→w ≡ xy→zw C.⋆ v)

  module _ {x y z w : C.ob}
    {s : Span x y} {t : Span z w}
    {x→z : I → C [ x , z ]} {y→w : I → C [ y , w ]}
    {sq : SpanSquare s t (x→z i0) (y→w i0)}
    {sq' : SpanSquare s t (x→z i1) (y→w i1)}
    where
    makeSpanSquarePathP :
      sq .fst ≡ sq' .fst →
      PathP (λ i → SpanSquare s t (x→z i) (y→w i)) sq sq'
    makeSpanSquarePathP =
      ΣPathPProp (λ _ → isProp× (C.isSetHom _ _) (C.isSetHom _ _))

  idSpan : ∀ {x} → Span x x
  idSpan = _ , C.id , C.id

  abstract
    seqⱽSq-path : ∀ {o₁ o₂ o₃ o₄ o₅ o₆ : C.ob}
      {a : C [ o₁ , o₂ ]} {v : C [ o₂ , o₃ ]}
      {h : C [ o₁ , o₄ ]} {d : C [ o₄ , o₃ ]}
      {v' : C [ o₃ , o₅ ]} {h' : C [ o₄ , o₆ ]} {c : C [ o₆ , o₅ ]}
      → a C.⋆ v ≡ h C.⋆ d
      → d C.⋆ v' ≡ h' C.⋆ c
      → a C.⋆ (v C.⋆ v') ≡ (h C.⋆ h') C.⋆ c
    seqⱽSq-path p q =
      sym (C.⋆Assoc _ _ _) ∙ C.⟨ p ⟩⋆⟨ refl ⟩ ∙ C.⋆Assoc _ _ _
        ∙ C.⟨ refl ⟩⋆⟨ q ⟩ ∙ sym (C.⋆Assoc _ _ _)

    idⱽSq-path : ∀ {o₁ o₂ : C.ob} {f : C [ o₁ , o₂ ]}
      → f C.⋆ C.id ≡ C.id C.⋆ f
    idⱽSq-path = C.⋆IdR _ ∙ sym (C.⋆IdL _)

    seqᴴSq-path : ∀ {o₁ o₂ o₃ o₄ o₅ o₆ : C.ob}
      {π : C [ o₁ , o₂ ]} {a : C [ o₂ , o₃ ]} {v : C [ o₃ , o₄ ]}
      {h : C [ o₂ , o₅ ]} {b : C [ o₅ , o₄ ]}
      {med : C [ o₁ , o₆ ]} {π' : C [ o₆ , o₅ ]}
      → a C.⋆ v ≡ h C.⋆ b
      → med C.⋆ π' ≡ π C.⋆ h
      → (π C.⋆ a) C.⋆ v ≡ med C.⋆ (π' C.⋆ b)
    seqᴴSq-path p β =
      C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ p ⟩ ∙ sym (C.⋆Assoc _ _ _)
        ∙ C.⟨ sym β ⟩⋆⟨ refl ⟩ ∙ C.⋆Assoc _ _ _

    seqᴴSq-med-path : ∀ {o₁ o₂ o₃ o₄ o₅ o₆ o₇ : C.ob}
      {π₁ : C [ o₁ , o₂ ]} {a : C [ o₂ , o₃ ]}
      {π₂ : C [ o₁ , o₄ ]} {b : C [ o₄ , o₃ ]}
      {h₁ : C [ o₂ , o₅ ]} {c : C [ o₅ , o₆ ]}
      {h₂ : C [ o₄ , o₇ ]} {d : C [ o₇ , o₆ ]}
      {u : C [ o₃ , o₆ ]}
      → π₁ C.⋆ a ≡ π₂ C.⋆ b
      → a C.⋆ u ≡ h₁ C.⋆ c
      → b C.⋆ u ≡ h₂ C.⋆ d
      → (π₁ C.⋆ h₁) C.⋆ c ≡ (π₂ C.⋆ h₂) C.⋆ d
    seqᴴSq-med-path comm p q =
      C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ sym p ⟩ ∙ sym (C.⋆Assoc _ _ _)
        ∙ C.⟨ comm ⟩⋆⟨ refl ⟩ ∙ C.⋆Assoc _ _ _
        ∙ C.⟨ refl ⟩⋆⟨ q ⟩ ∙ sym (C.⋆Assoc _ _ _)

  idⱽSq : ∀ {x y} {s : Span x y} → SpanSquare s s C.id C.id
  idⱽSq = C.id , idⱽSq-path , idⱽSq-path

  seqSpan : ∀ {x y z} → Span x y → Span y z → Span x z
  seqSpan (xy , f , g) (yz , u , v) =
    pb.vert , (pb.pbπ₁ C.⋆ f) , (pb.pbπ₂ C.⋆ v)
    where module pb = PullbackNotation (pbs g u)

  seqⱽSq : ∀ {x y z w a b}
    {s : Span x y} {t : Span z w} {r : Span a b}
    {v₁ : C [ x , z ]} {u₁ : C [ y , w ]}
    {v₂ : C [ z , a ]} {u₂ : C [ w , b ]}
    → SpanSquare s t v₁ u₁ → SpanSquare t r v₂ u₂
    → SpanSquare s r (v₁ C.⋆ v₂) (u₁ C.⋆ u₂)
  seqⱽSq sq sq' =
    sq .fst C.⋆ sq' .fst ,
    seqⱽSq-path (sq .snd .fst) (sq' .snd .fst) ,
    seqⱽSq-path (sq .snd .snd) (sq' .snd .snd)

  seqᴴSq : ∀ {x₁ x₂ x₃ y₁ y₂ y₃}
    {↑f : Span x₁ x₂} {↓f : Span y₁ y₂}
    {↑f' : Span x₂ x₃} {↓f' : Span y₂ y₃}
    {v : C [ x₁ , y₁ ]} {u : C [ x₂ , y₂ ]} {w : C [ x₃ , y₃ ]}
    → SpanSquare ↑f ↓f v u → SpanSquare ↑f' ↓f' u w
    → SpanSquare (seqSpan ↑f ↑f') (seqSpan ↓f ↓f') v w
  seqᴴSq {↑f = ↑f} {↓f = ↓f} {↑f' = ↑f'} {↓f' = ↓f'} sq sq' =
    med ,
    seqᴴSq-path (sq .snd .fst) pb↓.pbβ₁ ,
    seqᴴSq-path (sq' .snd .snd) pb↓.pbβ₂
    where
    module pb↓ = PullbackNotation (pbs (↓f .snd .snd) (↓f' .snd .fst))
    module pb↑ = PullbackNotation (pbs (↑f .snd .snd) (↑f' .snd .fst))
    abstract
      med-comm : (pb↑.pbπ₁ C.⋆ sq .fst) C.⋆ (↓f .snd .snd)
        ≡ (pb↑.pbπ₂ C.⋆ sq' .fst) C.⋆ (↓f' .snd .fst)
      med-comm = seqᴴSq-med-path pb↑.pbCommutes
        (sq .snd .snd) (sq' .snd .fst)
    med = pb↓.pbIntro (pb↑.pbπ₁ C.⋆ sq .fst) (pb↑.pbπ₂ C.⋆ sq' .fst)
      med-comm
