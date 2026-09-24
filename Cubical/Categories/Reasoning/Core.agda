{-
  A partial port of `Categories.Morphism.Reasoning.Core` from
  agda-categories to Cubical.

  Convention: Cubical uses the diagrammatic composition `_⋆_`, so
  `f ⋆ g` reads "first f, then g". A hypothesis `a ⋆ b ≡ c` says
  "the composite a-then-b equals c". The suffixes ˡ / ʳ record where
  the rewrite lands relative to the *existing* morphism `f`:

    pullʳ : (f ⋆ a) ⋆ b ≡ f ⋆ c      -- a⋆b sits to the right of f
    pullˡ : a ⋆ (b ⋆ f) ≡ c ⋆ f      -- a⋆b sits to the left of f

  The convention mirrors agda-categories despite the switch from `_∘_`
  to `_⋆_`: in both the label describes which side (syntactically) of `f`
  the rewrite applies to.
-}
module Cubical.Categories.Reasoning.Core where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category

private variable
  ℓC ℓC' : Level

module Reasoning (C : Category ℓC ℓC') where
  open Category C


  -- use  a ⋆ b ≡ c  as a left-to-right rewrite.
  module Pulls {x y z : ob}
               {a : Hom[ x , y ]} {b : Hom[ y , z ]} {c : Hom[ x , z ]}
               (ab≡c : a ⋆ b ≡ c) where

    pullʳ : ∀ {w} {f : Hom[ w , x ]} → (f ⋆ a) ⋆ b ≡ f ⋆ c
    pullʳ {f = f} = ⋆Assoc f a b ∙ cong (f ⋆_) ab≡c

    pullˡ : ∀ {w} {f : Hom[ z , w ]} → a ⋆ (b ⋆ f) ≡ c ⋆ f
    pullˡ {f = f} = sym (⋆Assoc a b f) ∙ cong (_⋆ f) ab≡c

  open Pulls public

  -- use  c ≡ a ⋆ b  as a left-to-right rewrite.
  module Pushes {x y z : ob}
                {a : Hom[ x , y ]} {b : Hom[ y , z ]} {c : Hom[ x , z ]}
                (c≡ab : c ≡ a ⋆ b) where

    pushʳ : ∀ {w} {f : Hom[ w , x ]} → f ⋆ c ≡ (f ⋆ a) ⋆ b
    pushʳ {f = f} = cong (f ⋆_) c≡ab ∙ sym (⋆Assoc f a b)

    pushˡ : ∀ {w} {f : Hom[ z , w ]} → c ⋆ f ≡ a ⋆ (b ⋆ f)
    pushˡ {f = f} = cong (_⋆ f) c≡ab ∙ ⋆Assoc a b f

  open Pushes public


  -- introduce or eliminate an equal-to-identity arrow.
  module IntroElim {x : ob} {a : Hom[ x , x ]} (a≡id : a ≡ id) where

    elimʳ : ∀ {w} {f : Hom[ w , x ]} → f ⋆ a ≡ f
    elimʳ {f = f} = cong (f ⋆_) a≡id ∙ ⋆IdR f

    elimˡ : ∀ {w} {f : Hom[ x , w ]} → a ⋆ f ≡ f
    elimˡ {f = f} = cong (_⋆ f) a≡id ∙ ⋆IdL f

    introʳ : ∀ {w} {f : Hom[ w , x ]} → f ≡ f ⋆ a
    introʳ = sym elimʳ

    introˡ : ∀ {w} {f : Hom[ x , w ]} → f ≡ a ⋆ f
    introˡ = sym elimˡ

  open IntroElim public

  {-
  Commuting squares and their whiskerings.

  CommutingSquare {a b c d} f g f' g' =
    a -f–→ b
    |      |
    g      f'
    ↓      ↓
    c -g'→ d
  -}
  CommutingSquare : ∀ {a b c d}
    → Hom[ a , b ] → Hom[ a , c ] → Hom[ b , d ] → Hom[ c , d ]
    → Type _
  CommutingSquare f g f' g' = f ⋆ f' ≡ g ⋆ g'

  module Extends {a b c d}
    {f : Hom[ a , b ]} {g : Hom[ a , c ]}
    {f' : Hom[ b , d ]} {g' : Hom[ c , d ]}
    (s : CommutingSquare f g f' g') where

    {-
        a -f–→ b
        |      |
        g      f'
        ↓      ↓
        c -g'→ d -x→ y
    -}
    extendʳ : ∀ {y} {x : Hom[ d , y ]}
            → CommutingSquare f g (f' ⋆ x) (g' ⋆ x)
    extendʳ {x = x} =
      sym (⋆Assoc f f' x) ∙ cong (_⋆ x) s ∙ ⋆Assoc g g' x

    {-
      y -x→  a -f–→ b
             |      |
             g      f'
             ↓      ↓
             c -g'→ d
    -}
    extendˡ : ∀ {y} {x : Hom[ y , a ]}
            → CommutingSquare (x ⋆ f) (x ⋆ g) f' g'
    extendˡ {x = x} =
      ⋆Assoc x f f' ∙ cong (x ⋆_) s ∙ sym (⋆Assoc x g g')

  open Extends public

  {-
   Glue two stacked commuting squares (composition in the arrow category).
      A₁ - top → B₁
      |          |
      l₁         r₁        sq-top : top ⋆ r₁ ≡ l₁ ⋆ mid
      ↓          ↓
      A₂ - mid → B₂
      |          |
      l₂         r₂        sq-bot : mid ⋆ r₂ ≡ l₂ ⋆ bot
      ↓          ↓
      A₃ - bot → B₃
   Outer rectangle: top ⋆ (r₁ ⋆ r₂) ≡ (l₁ ⋆ l₂) ⋆ bot.
  -}
  glue : ∀ {A₁ A₂ A₃ B₁ B₂ B₃}
    {top : Hom[ A₁ , B₁ ]} {mid : Hom[ A₂ , B₂ ]} {bot : Hom[ A₃ , B₃ ]}
    {l₁  : Hom[ A₁ , A₂ ]} {r₁  : Hom[ B₁ , B₂ ]}
    {l₂  : Hom[ A₂ , A₃ ]} {r₂  : Hom[ B₂ , B₃ ]}
    → CommutingSquare top l₁ r₁ mid
    → CommutingSquare mid l₂ r₂ bot
    → CommutingSquare top (l₁ ⋆ l₂) (r₁ ⋆ r₂) bot
  glue sq-top sq-bot =
    extendʳ sq-top ∙ cong (_ ⋆_) sq-bot ∙ sym (⋆Assoc _ _ _)

  {-
   Glue a commuting triangle onto the right side of a square, extending
   the right/bottom edges.
      a -f-→ b
      |      │ ╲
      g      f'  t   tri : f' ⋆ x ≡ t   (t is the diagonal b → e)
      ↓      ↓    ↘
      c -g'→ d -x→ e
   Result: f ⋆ t ≡ g ⋆ (g' ⋆ x)  — the new square with right edge t and
   bottom edge g' ⋆ x.
  -}
  glueTriR : ∀ {a b c d e}
    {f : Hom[ a , b ]} {g : Hom[ a , c ]}
    {f' : Hom[ b , d ]} {g' : Hom[ c , d ]}
    {t : Hom[ b , e ]} {x : Hom[ d , e ]}
    → CommutingSquare f g f' g'
    → f' ⋆ x ≡ t
    → CommutingSquare f g t (g' ⋆ x)
  glueTriR {f = f} sq tri = cong (f ⋆_) (sym tri) ∙ extendʳ sq

  {-
   Glue a triangle onto the left side of a square,
   extending the top/left edges.
      e -x→ a -f-→ b
       ╲    │      │
         t  g      f'    tri : x ⋆ g ≡ t   (t is the diagonal e → c)
          ↘ ↓      ↓
            c -g'→ d
   Result: (x ⋆ f) ⋆ f' ≡ t ⋆ g'  — new square with top x⋆f and left t.
  -}
  glueTriL : ∀ {a b c d e}
    {f : Hom[ a , b ]} {g : Hom[ a , c ]}
    {f' : Hom[ b , d ]} {g' : Hom[ c , d ]}
    {t : Hom[ e , c ]} {x : Hom[ e , a ]}
    → CommutingSquare f g f' g'
    → x ⋆ g ≡ t
    → CommutingSquare (x ⋆ f) t f' g'
  glueTriL {g' = g'} sq tri = extendˡ sq ∙ cong (_⋆ g') tri
