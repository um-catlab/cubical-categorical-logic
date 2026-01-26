{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open PshHom
open PshIso
open UniversalElement

module _ {C : Category ℓC ℓC'}(P : Presheaf C ℓP)(Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module P = PresheafNotation P
  CartesianLiftPsh : ∀ {x} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (p : P.p[ x ])
    → Type _
  CartesianLiftPsh {x = x} Pᴰ p = Representableⱽ Cᴰ x (reindPshᴰNatTrans (yoRec P p) Pᴰ)

  isFibrationPshᴰ : Presheafᴰ P Cᴰ ℓPᴰ → Type _
  isFibrationPshᴰ Pᴰ = ∀ x (p : P.p[ x ]) → CartesianLiftPsh Pᴰ p

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  CartesianLift : ∀ {x y} (f : C [ x , y ]) (yᴰ : Cᴰ.ob[ y ])
    → Type _
  CartesianLift f yᴰ = CartesianLiftPsh (C [-, _ ]) Cᴰ (Cᴰ [-][-, yᴰ ]) f

  -- TODO: more general RepresentableⱽNotation

  module CartesianLiftNotation {x y} {f : C [ x , y ]} {yᴰ : Cᴰ.ob[ y ]} (f*yᴰ : CartesianLift f yᴰ) where
    introᴰ : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{g} → Cᴰ [ g C.⋆ f ][ Γᴰ , yᴰ ] → Cᴰ [ g ][ Γᴰ , f*yᴰ .fst ]
    introᴰ = f*yᴰ .snd .nIso (_ , _ , _) .fst

    _⋆πⱽ : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{g}
        → Cᴰ [ g ][ Γᴰ , f*yᴰ .fst ]
        → Cᴰ [ g C.⋆ f ][ Γᴰ , yᴰ ]
    gᴰ ⋆πⱽ = f*yᴰ .snd .trans .N-ob (_ , _ , _) gᴰ

    πⱽ : Cᴰ [ C.id C.⋆ f ][ f*yᴰ .fst , yᴰ ]
    πⱽ = Cᴰ.idᴰ ⋆πⱽ

    opaque
      congP-introᴰ :
        ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{g g'}
          → {gfᴰ : Cᴰ [ g C.⋆ f ][ Γᴰ , yᴰ ]}
          → {g'fᴰ : Cᴰ [ g' C.⋆ f ][ Γᴰ , yᴰ ]}
          → {g≡g' : g ≡ g'}
          → (gfᴰ≡g'fᴰ : gfᴰ Cᴰ.≡[ C.⟨ g≡g' ⟩⋆⟨ refl ⟩ ] g'fᴰ)
          → introᴰ gfᴰ Cᴰ.≡[ g≡g' ] introᴰ g'fᴰ
      congP-introᴰ {g≡g' = g≡g'} gfᴰ≡g'fᴰ i = f*yᴰ .snd .nIso (_ , _ , g≡g' i) .fst (gfᴰ≡g'fᴰ i)

      cong-introᴰ :
        ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{g g'}
          → {gfᴰ : Cᴰ [ g C.⋆ f ][ Γᴰ , yᴰ ]}
          → {g'fᴰ : Cᴰ [ g' C.⋆ f ][ Γᴰ , yᴰ ]}
          → (g≡g' : g ≡ g')
          → (gfᴰ≡g'fᴰ :
            Path Cᴰ.Hom[ _ , _ ]
              ((g C.⋆ f) , gfᴰ)
              ((g' C.⋆ f) , g'fᴰ))
          → Path Cᴰ.Hom[ _ , _ ]
              (g , introᴰ gfᴰ)
              (g' , introᴰ g'fᴰ)
      cong-introᴰ g≡g' gfᴰ≡g'fᴰ =
        ΣPathP (g≡g' , (congP-introᴰ (Cᴰ.rectify $ Cᴰ.≡out gfᴰ≡g'fᴰ)))

      ⟨_⟩⋆πⱽ : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{g g'}
        → {gᴰ : Cᴰ [ g ][ Γᴰ , f*yᴰ .fst ]}
        → {gᴰ' : Cᴰ [ g' ][ Γᴰ , f*yᴰ .fst ]}
        → Path Cᴰ.Hom[ _ , _ ]
            (_ , gᴰ)
            (_ , gᴰ')
        → Path Cᴰ.Hom[ _ , _ ]
            (_ , gᴰ ⋆πⱽ)
            (_ , gᴰ' ⋆πⱽ)
      ⟨_⟩⋆πⱽ {Γ} {Γᴰ} {g} {g'} {gᴰ} {gᴰ'} gᴰ≡gᴰ' i .fst = gᴰ≡gᴰ' i .fst C.⋆ f
      ⟨_⟩⋆πⱽ {Γ} {Γᴰ} {g} {g'} {gᴰ} {gᴰ'} gᴰ≡gᴰ' i .snd =
        f*yᴰ .snd .trans .N-ob (Γ , Γᴰ , gᴰ≡gᴰ' i .fst) (gᴰ≡gᴰ' i .snd)

      ⋆πⱽ-natural : ∀ {Δ Γ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γᴰ : Cᴰ.ob[ Γ ]}{γ g}
        {γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ]}
        {gᴰ : Cᴰ [ g ][ Γᴰ , f*yᴰ .fst ]}
        → Path Cᴰ.Hom[ _ , _ ]
            (_ , (γᴰ Cᴰ.⋆ᴰ gᴰ) ⋆πⱽ)
            (_ , γᴰ Cᴰ.⋆ᴰ (gᴰ ⋆πⱽ))
      ⋆πⱽ-natural {Δ} {Γ} {Δᴰ} {Γᴰ} {γ} {g} {γᴰ} {gᴰ} =
        ⟨ Cᴰ.reind-filler _ ⟩⋆πⱽ
        ∙ (Cᴰ.≡in $ f*yᴰ .snd .trans .N-hom (Δ , (Δᴰ , (γ C.⋆ g))) (Γ , (Γᴰ , g)) (γ , (γᴰ , wrap refl)) gᴰ)
        ∙ (sym $ Cᴰ.reind-filler _)


      ⋆πⱽ≡⋆ᴰπⱽ : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{g}
        → (gᴰ : Cᴰ [ g ][ Γᴰ , f*yᴰ .fst ])
        → Path Cᴰ.Hom[ _ , _ ] (_ , gᴰ ⋆πⱽ) (_ , gᴰ Cᴰ.⋆ᴰ πⱽ)
      ⋆πⱽ≡⋆ᴰπⱽ gᴰ = ⟨ sym $ Cᴰ.⋆IdR _ ⟩⋆πⱽ ∙ ⋆πⱽ-natural

      βᴰ : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{g} → (gfᴰ : Cᴰ [ g C.⋆ f ][ Γᴰ , yᴰ ])
        → Path Cᴰ.Hom[ _ , _ ]
            (_ , introᴰ gfᴰ ⋆πⱽ)
            (_ , gfᴰ)
      βᴰ gfᴰ = Cᴰ.≡in $ f*yᴰ .snd .nIso (_ , _ , _) .snd .fst gfᴰ

      βᴰ' : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{g} → (gfᴰ : Cᴰ [ g C.⋆ f ][ Γᴰ , yᴰ ])
        → Path Cᴰ.Hom[ _ , _ ]
            (_ , introᴰ gfᴰ Cᴰ.⋆ᴰ πⱽ)
            (_ , gfᴰ)
      βᴰ' gfᴰ = sym (⋆πⱽ≡⋆ᴰπⱽ _) ∙ βᴰ gfᴰ

      ηᴰ : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{g}
        → (gᴰ : Cᴰ [ g ][ Γᴰ , f*yᴰ .fst ])
        → Path Cᴰ.Hom[ _ , _ ]
            (_ , gᴰ)
            (_ , introᴰ (gᴰ ⋆πⱽ))
      ηᴰ gᴰ = Cᴰ.≡in $ sym $ f*yᴰ .snd .nIso (_ , _ , _) .snd .snd gᴰ

      extensionalityᴰ : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{g g'}
        → {gᴰ : Cᴰ [ g ][ Γᴰ , f*yᴰ .fst ]}
        → {g'ᴰ : Cᴰ [ g' ][ Γᴰ , f*yᴰ .fst ]}
        → (g≡g' : g ≡ g')
        → Path Cᴰ.Hom[ _ , _ ]
            (g C.⋆ f , gᴰ ⋆πⱽ)
            (g' C.⋆ f , g'ᴰ ⋆πⱽ)
        → Path Cᴰ.Hom[ _ , _ ]
            (g  , gᴰ)
            (g' , g'ᴰ)
      extensionalityᴰ g≡g' gᴰπⱽ≡g'ᴰπⱽ = ηᴰ _ ∙ cong-introᴰ g≡g' gᴰπⱽ≡g'ᴰπⱽ ∙ (sym $ ηᴰ _)

      extensionalityᴰin : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{g g'}
        → {gᴰ : Cᴰ [ g ][ Γᴰ , f*yᴰ .fst ]}
        → {g'ᴰ : Cᴰ [ g' ][ Γᴰ , f*yᴰ .fst ]}
        → (g≡g' : g ≡ g')
        → Path Cᴰ.Hom[ _ , _ ]
            (g C.⋆ f , gᴰ ⋆πⱽ)
            (g' C.⋆ f , g'ᴰ ⋆πⱽ)
        → gᴰ Cᴰ.≡[ g≡g' ] g'ᴰ
      extensionalityᴰin g≡g' gᴰπⱽ≡g'ᴰπⱽ = Cᴰ.rectify $ Cᴰ.≡out $ extensionalityᴰ g≡g' gᴰπⱽ≡g'ᴰπⱽ

      introᴰ≡ : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{g}
        → {gfᴰ : Cᴰ [ g C.⋆ f ][ Γᴰ , yᴰ ]}
        → {gᴰ : Cᴰ [ g ][ Γᴰ , f*yᴰ .fst ]}
        → Path Cᴰ.Hom[ _ , _ ]
            (g C.⋆ f , gfᴰ)
            (g C.⋆ f , gᴰ ⋆πⱽ)
        → Path Cᴰ.Hom[ _ , _ ]
            (g , introᴰ gfᴰ)
            (g , gᴰ)
      introᴰ≡ gfᴰ≡gᴰπ = cong-introᴰ refl gfᴰ≡gᴰπ ∙ sym (ηᴰ _)

      introᴰ≡' : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{g g'}
        → {gfᴰ : Cᴰ [ g C.⋆ f ][ Γᴰ , yᴰ ]}
        → {gᴰ : Cᴰ [ g' ][ Γᴰ , f*yᴰ .fst ]}
        → g ≡ g'
        → Path Cᴰ.Hom[ _ , _ ]
            (g C.⋆ f , gfᴰ)
            (g' C.⋆ f , gᴰ ⋆πⱽ)
        → Path Cᴰ.Hom[ _ , _ ]
            (g , introᴰ gfᴰ)
            (g' , gᴰ)
      introᴰ≡' g≡g' gfᴰ≡gᴰπⱽ =
        introᴰ≡ (gfᴰ≡gᴰπⱽ ∙ ⟨ Cᴰ.reind-filler _ ⟩⋆πⱽ)
        ∙ (sym $ Cᴰ.reind-filler (wrap $ sym g≡g'))
  CartesianLiftable : ∀ {y} (yᴰ : Cᴰ.ob[ y ])
    → Type _
  CartesianLiftable {y} yᴰ = ∀ {x} (f : C [ x , y ]) → CartesianLift f yᴰ

  Quadrable : ∀ {x y} (f : C [ x , y ]) → Type _
  Quadrable f = ∀ yᴰ → CartesianLift f yᴰ

  module QuadrableNotation {x y}{f : C [ x , y ]}(f-Quad : Quadrable f){yᴰ : Cᴰ.ob[ y ]} = CartesianLiftNotation {f = f}{yᴰ} (f-Quad yᴰ)

  isFibration : Type _
  isFibration = ∀ {x} (xᴰ : Cᴰ.ob[ x ]) → isFibrationPshᴰ (C [-, x ]) Cᴰ (Cᴰ [-][-, xᴰ ])


  -- Given a commuting square like this in C
  --    f
  -- w --> x
  -- | g   | h
  -- \/    \/
  -- y --> z
  --    k
  --
  -- we can fill this horn and get a commuting square in C over the above
  --
  --      sq-filler kᴰ
  -- g*yᴰ -----------> h*zᴰ
  -- | π                | π
  -- \/                 \/
  -- yᴰ   -----------> zᴰ
  --          kᴰ
  module _ {w x y z}{f : C [ w , x ]}{g : C [ w , y ]}{h : C [ x , z ]}{k : C [ y , z ]}
    {yᴰ : Cᴰ.ob[ y ]}
    {zᴰ : Cᴰ.ob[ z ]}
    (g*yᴰ : CartesianLift g yᴰ)
    (h*zᴰ : CartesianLift h zᴰ)
    (kᴰ : Cᴰ [ k ][ yᴰ , zᴰ ])
    where
    private
      module g*yᴰ = CartesianLiftNotation g*yᴰ
      module h*zᴰ = CartesianLiftNotation h*zᴰ
    -- the gen one is the most flexible, use it for theorems
    cartLift-sq-filler-gen : (commutes : (C.id C.⋆ g) C.⋆ k ≡ f C.⋆ h) → Cᴰ [ f ][ g*yᴰ .fst , h*zᴰ .fst ]
    cartLift-sq-filler-gen commutes =
      h*zᴰ.introᴰ (Cᴰ.reind (wrap commutes) (g*yᴰ.πⱽ Cᴰ.⋆ᴰ kᴰ))

    -- this one is the most convenient to use bc the extra id isn't there.
    cartLift-sq-filler : (commutes : g C.⋆ k ≡ f C.⋆ h) → Cᴰ [ f ][ g*yᴰ .fst , h*zᴰ .fst ]
    cartLift-sq-filler commutes = cartLift-sq-filler-gen (C.⟨ C.⋆IdL g ⟩⋆⟨ refl ⟩ ∙ commutes)

  module _ {w x y z}{f f' : C [ w , x ]}{g : C [ w , y ]}{h : C [ x , z ]}{k k' : C [ y , z ]}
    {yᴰ : Cᴰ.ob[ y ]}
    {zᴰ : Cᴰ.ob[ z ]}
    (g*yᴰ : CartesianLift g yᴰ)
    (h*zᴰ : CartesianLift h zᴰ)
    (kᴰ : Cᴰ [ k ][ yᴰ , zᴰ ])
    (k'ᴰ : Cᴰ [ k' ][ yᴰ , zᴰ ])
    (commutes : g C.⋆ k ≡ f C.⋆ h)
    (commutes' : g C.⋆ k' ≡ f' C.⋆ h)
    (f≡f' : f ≡ f')
    (kᴰ≡k'ᴰ : kᴰ Cᴰ.∫≡ k'ᴰ)
    where
    private
      module g*yᴰ = CartesianLiftNotation g*yᴰ
      module h*zᴰ = CartesianLiftNotation h*zᴰ
    opaque
      cartLift-sq-filler-cong :
        cartLift-sq-filler g*yᴰ h*zᴰ kᴰ commutes
        Cᴰ.∫≡ cartLift-sq-filler g*yᴰ h*zᴰ k'ᴰ commutes'
      cartLift-sq-filler-cong = h*zᴰ.cong-introᴰ f≡f' $ Cᴰ.cong-reind _ _ Cᴰ.⟨⟩⋆⟨ kᴰ≡k'ᴰ ⟩

  --    f
  -- w --> x
  -- | g   | h
  -- \/    \/
  -- y === y
  --    id
  module _ {x y}{g : C [ x , y ]}
    {yᴰ : Cᴰ.ob[ y ]}
    (g*yᴰ : CartesianLift g yᴰ)
    where
    private
      module g*yᴰ = CartesianLiftNotation g*yᴰ
    opaque
      cartLift-sq-id :
        {id' : C [ x , x ]}
        {commutes : (C.id C.⋆ g) C.⋆ C.id ≡ id' C.⋆ g}
        (id'≡id : id' ≡ C.id)
        → Path Cᴰ.Hom[ _ , _ ]
            (_ , cartLift-sq-filler-gen g*yᴰ g*yᴰ Cᴰ.idᴰ commutes)
            (_ , Cᴰ.idᴰ)
      cartLift-sq-id id'≡id = g*yᴰ.introᴰ≡' id'≡id
        (sym (Cᴰ.reind-filler _) ∙ Cᴰ.⋆IdR _)

  module _ {w x y}{f : C [ w , x ]}{g : C [ w , y ]}{h : C [ x , y ]}
    {yᴰ : Cᴰ.ob[ y ]}
    (g*yᴰ : CartesianLift g yᴰ)
    (h*yᴰ : CartesianLift h yᴰ)
    where
    private
      module g*yᴰ = CartesianLiftNotation g*yᴰ
      module h*yᴰ = CartesianLiftNotation h*yᴰ
    cartLift-tri-filler-gen : (commutes : C.id C.⋆ g ≡ f C.⋆ h) → Cᴰ [ f ][ g*yᴰ .fst , h*yᴰ .fst ]
    cartLift-tri-filler-gen commutes =
      h*yᴰ.introᴰ (Cᴰ.reind (wrap commutes) g*yᴰ.πⱽ)

    cartLift-tri-filler : (commutes : g ≡ f C.⋆ h) → Cᴰ [ f ][ g*yᴰ .fst , h*yᴰ .fst ]
    cartLift-tri-filler commutes = cartLift-tri-filler-gen (C.⋆IdL g ∙ commutes)

    opaque
      -- this is written to infer the rhs from the lhs
      cartLift-tri-filler≡sq-filler :
        ∀ {tri : C.id C.⋆ g ≡ f C.⋆ h}
        → Path Cᴰ.Hom[ _ , _ ]
            (f , cartLift-tri-filler-gen tri)
            (f , cartLift-sq-filler-gen g*yᴰ h*yᴰ Cᴰ.idᴰ (C.⋆IdR _ ∙ tri))
      cartLift-tri-filler≡sq-filler =
        h*yᴰ.cong-introᴰ refl $
          sym (Cᴰ.reind-filler _)
          ∙ sym (Cᴰ.⋆IdR (_ , g*yᴰ.πⱽ))
          ∙ Cᴰ.reind-filler _

  --    f     f'
  -- w --> x --> x'
  -- | g   | h   | h'
  -- \/    \/    \/
  -- y --> z --> z'
  --    k     k'
  module _ {w x y z x' z'}
    {f : C [ w , x ]}{g : C [ w , y ]}{h : C [ x , z ]}{k : C [ y , z ]}
    {f' : C [ x , x' ]}{h' : C [ x' , z' ]}{k' : C [ z , z' ]}
    {yᴰ : Cᴰ.ob[ y ]}
    {zᴰ : Cᴰ.ob[ z ]}
    {z'ᴰ : Cᴰ.ob[ z' ]}
    (g*yᴰ : CartesianLift g yᴰ)
    (h*zᴰ : CartesianLift h zᴰ)
    (h'*z'ᴰ : CartesianLift h' z'ᴰ)
    (kᴰ : Cᴰ [ k ][ yᴰ , zᴰ ])
    (k'ᴰ : Cᴰ [ k' ][ zᴰ , z'ᴰ ])
    where
    private
      module g*yᴰ = CartesianLiftNotation g*yᴰ
      module h*zᴰ = CartesianLiftNotation h*zᴰ
      module h'*z'ᴰ = CartesianLiftNotation h'*z'ᴰ
    opaque
      cartLift-sq-seq :
        {ff'~ : C [ w , x' ]}
        {comm1 : (C.id C.⋆ g) C.⋆ k ≡ f C.⋆ h}
        {comm2 : (C.id C.⋆ h) C.⋆ k' ≡ f' C.⋆ h'}
        {comm3 : (C.id C.⋆ g) C.⋆ k C.⋆ k' ≡ ff'~ C.⋆ h'}
        → ff'~ ≡ (f C.⋆ f')
        → Path Cᴰ.Hom[ _ , _ ]
            (ff'~ , cartLift-sq-filler-gen g*yᴰ h'*z'ᴰ (kᴰ Cᴰ.⋆ᴰ k'ᴰ) comm3)
            ((f C.⋆ f') , cartLift-sq-filler-gen g*yᴰ h*zᴰ kᴰ comm1 Cᴰ.⋆ᴰ cartLift-sq-filler-gen h*zᴰ h'*z'ᴰ k'ᴰ comm2)
      cartLift-sq-seq ff'~≡ff' = h'*z'ᴰ.introᴰ≡' ff'~≡ff'
        (sym (Cᴰ.reind-filler _) ∙ (sym $
          h'*z'ᴰ.⋆πⱽ-natural
          ∙ Cᴰ.⟨ refl ⟩⋆⟨ h'*z'ᴰ.βᴰ _ ∙ (sym $ Cᴰ.reind-filler _) ⟩
          ∙ sym (Cᴰ.⋆Assoc _ _ _)
          ∙ Cᴰ.⟨
              h*zᴰ.βᴰ' _ ∙ sym (Cᴰ.reind-filler _)
               ⟩⋆⟨⟩
          ∙ Cᴰ.⋆Assoc _ _ _))

      comm1+comm2→comm3 :
        (comm1 : (C.id C.⋆ g) C.⋆ k ≡ f C.⋆ h)
        (comm2 : (C.id C.⋆ h) C.⋆ k' ≡ f' C.⋆ h')
        → (C.id C.⋆ g) C.⋆ k C.⋆ k' ≡ (f C.⋆ f') C.⋆ h'
      comm1+comm2→comm3 comm1 comm2 =
        sym (C.⋆Assoc _ k k')
        ∙ C.⟨ comm1 ⟩⋆⟨ refl ⟩
        ∙ C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ C.⟨ sym $ C.⋆IdL h ⟩⋆⟨ refl ⟩ ∙ comm2 ⟩ ∙ sym (C.⋆Assoc _ _ _)

      -- same as the previous but the rhs is inferred from the lhs
      cartLift-sq-collapse :
        {comm1 : (C.id C.⋆ g) C.⋆ k ≡ f C.⋆ h}
        {comm2 : (C.id C.⋆ h) C.⋆ k' ≡ f' C.⋆ h'}
        → Path Cᴰ.Hom[ _ , _ ]
            ((f C.⋆ f') , cartLift-sq-filler-gen g*yᴰ h*zᴰ kᴰ comm1 Cᴰ.⋆ᴰ cartLift-sq-filler-gen h*zᴰ h'*z'ᴰ k'ᴰ comm2)
            ((f C.⋆ f') , cartLift-sq-filler-gen g*yᴰ h'*z'ᴰ (kᴰ Cᴰ.⋆ᴰ k'ᴰ) (comm1+comm2→comm3 comm1 comm2))
      cartLift-sq-collapse = sym $ cartLift-sq-seq refl


  module FibrationNotation (cartLifts : isFibration) where
    module AllN {x y}{f : C [ x , y ]}{yᴰ : Cᴰ.ob[ y ]}
      = CartesianLiftNotation {f = f}{yᴰ} (cartLifts yᴰ x f)
    open AllN public
    _*_ : ∀ {x y}(f : C [ x , y ])(yᴰ : Cᴰ.ob[ y ]) → Cᴰ.ob[ x ]
    f * yᴰ = cartLifts yᴰ _ f .fst

    module _ {w x y z}{f : C [ w , x ]}{g : C [ w , y ]}{h : C [ x , z ]}{k : C [ y , z ]}
      {yᴰ : Cᴰ.ob[ y ]}
      {zᴰ : Cᴰ.ob[ z ]}
      (kᴰ : Cᴰ [ k ][ yᴰ , zᴰ ])
      where
      -- -- the gen one is the most flexible, use it for theorems
      sq-filler-gen : (commutes : (C.id C.⋆ g) C.⋆ k ≡ f C.⋆ h)
        → Cᴰ [ f ][ g * yᴰ , h * zᴰ ]
      sq-filler-gen = cartLift-sq-filler-gen (cartLifts yᴰ w g) (cartLifts zᴰ x h) kᴰ

      sq-filler : (commutes : g C.⋆ k ≡ f C.⋆ h) → Cᴰ [ f ][ g * yᴰ , h * zᴰ ]
      sq-filler = cartLift-sq-filler (cartLifts yᴰ w g) (cartLifts zᴰ x h) kᴰ
    module _ {w x y z}{f f' : C [ w , x ]}{g : C [ w , y ]}{h : C [ x , z ]}{k k' : C [ y , z ]}
      {yᴰ : Cᴰ.ob[ y ]}
      {zᴰ : Cᴰ.ob[ z ]}
      (kᴰ : Cᴰ [ k ][ yᴰ , zᴰ ])
      (k'ᴰ : Cᴰ [ k' ][ yᴰ , zᴰ ])
      (commutes : g C.⋆ k ≡ f C.⋆ h)
      (commutes' : g C.⋆ k' ≡ f' C.⋆ h)
      (f≡f' : f ≡ f')
      (kᴰ≡k'ᴰ : kᴰ Cᴰ.∫≡ k'ᴰ)
      where
      opaque
        sq-filler-cong : sq-filler kᴰ commutes Cᴰ.∫≡ sq-filler k'ᴰ commutes'
        sq-filler-cong = cartLift-sq-filler-cong (cartLifts yᴰ w g) (cartLifts zᴰ x h) kᴰ k'ᴰ commutes commutes' f≡f' kᴰ≡k'ᴰ

    module _ {x y}{g : C [ x , y ]}
      {yᴰ : Cᴰ.ob[ y ]}
      where
      opaque
        sq-id :
          {id' : C [ x , x ]}
          {commutes : (C.id C.⋆ g) C.⋆ C.id ≡ id' C.⋆ g}
          (id'≡id : id' ≡ C.id)
          → Path Cᴰ.Hom[ _ , _ ]
              (_ , sq-filler-gen (Cᴰ.idᴰ {p = yᴰ}) commutes)
              (_ , Cᴰ.idᴰ)
        sq-id = cartLift-sq-id (cartLifts yᴰ x g)

    module _ {w x y}{f : C [ w , x ]}{g : C [ w , y ]}{h : C [ x , y ]}
      {yᴰ : Cᴰ.ob[ y ]}
      where
      tri-filler-gen : (commutes : C.id C.⋆ g ≡ f C.⋆ h) → Cᴰ [ f ][ g * yᴰ , h * yᴰ ]
      tri-filler-gen = cartLift-tri-filler-gen (cartLifts yᴰ w g) (cartLifts yᴰ x h)

      tri-filler : (commutes : g ≡ f C.⋆ h) → Cᴰ [ f ][ g * yᴰ , h * yᴰ ]
      tri-filler = cartLift-tri-filler (cartLifts yᴰ w g) (cartLifts yᴰ x h)

      opaque
        tri-filler≡sq-filler :
          ∀ {tri : C.id C.⋆ g ≡ f C.⋆ h}
          → Path Cᴰ.Hom[ _ , _ ]
              (f , tri-filler-gen tri)
              (f , sq-filler-gen Cᴰ.idᴰ (C.⋆IdR (C.id C.⋆ g) ∙ tri))
        tri-filler≡sq-filler = cartLift-tri-filler≡sq-filler (cartLifts yᴰ w g) (cartLifts yᴰ x h)

    module _ {w x y z x' z'}
      {f : C [ w , x ]}{g : C [ w , y ]}{h : C [ x , z ]}{k : C [ y , z ]}
      {f' : C [ x , x' ]}{h' : C [ x' , z' ]}{k' : C [ z , z' ]}
      {yᴰ : Cᴰ.ob[ y ]}
      {zᴰ : Cᴰ.ob[ z ]}
      {z'ᴰ : Cᴰ.ob[ z' ]}
      (kᴰ : Cᴰ [ k ][ yᴰ , zᴰ ])
      (k'ᴰ : Cᴰ [ k' ][ zᴰ , z'ᴰ ])
      where
      sq-seq : ∀
        {ff'~}
        {comm1 : (C.id C.⋆ g) C.⋆ k ≡ f C.⋆ h}
        {comm2 : (C.id C.⋆ h) C.⋆ k' ≡ f' C.⋆ h'}
        {comm3 : (C.id C.⋆ g) C.⋆ k C.⋆ k' ≡ ff'~ C.⋆ h'}
        → ff'~ ≡ (f C.⋆ f')
        → Path Cᴰ.Hom[ _ , _ ]
            (ff'~ , sq-filler-gen (kᴰ Cᴰ.⋆ᴰ k'ᴰ) comm3)
            ((f C.⋆ f') , sq-filler-gen kᴰ comm1 Cᴰ.⋆ᴰ sq-filler-gen k'ᴰ comm2)
      sq-seq = cartLift-sq-seq (cartLifts yᴰ w g) (cartLifts zᴰ x h) (cartLifts z'ᴰ x' h') kᴰ k'ᴰ

      sq-collapse :
        {comm1 : (C.id C.⋆ g) C.⋆ k ≡ f C.⋆ h}
        {comm2 : (C.id C.⋆ h) C.⋆ k' ≡ f' C.⋆ h'}
        → Path Cᴰ.Hom[ _ , _ ]
            ((f C.⋆ f') , sq-filler-gen kᴰ comm1 Cᴰ.⋆ᴰ sq-filler-gen k'ᴰ comm2)
            ((f C.⋆ f') , sq-filler-gen (kᴰ Cᴰ.⋆ᴰ k'ᴰ) _)
      sq-collapse =
        cartLift-sq-collapse (cartLifts yᴰ w g) (cartLifts zᴰ x h) (cartLifts z'ᴰ x' h') kᴰ k'ᴰ
