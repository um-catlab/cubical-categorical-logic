{-# OPTIONS  --allow-unsolved-metas #-}
-- Following 1Lab
-- https://1lab.dev/Cat.Monoidal.Instances.Day.html
module Cubical.Categories.Constructions.Day.Base where 
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.HLevels
    open import Cubical.Data.Sigma

    open import Cubical.Categories.Presheaf
    open import Cubical.Categories.Category
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Bifunctor.Base
    open import Cubical.Categories.Monoidal.Base 
    open import Cubical.Categories.Instances.Sets

    private
        variable
            ℓC ℓC' ℓS  : Level

    -- for SET
    -- strict or regular? StrictMonCategory
    module _ {MC : StrictMonCategory ℓC ℓC'}(F G : Presheaf (MC .StrictMonCategory.C) (ℓ-max ℓC ℓC')) where
        open StrictMonCategory MC 
        open Category C renaming (ob to obᶜ ; _⋆_ to _⋆ᶜ_ ; id to idᶜ ; ⋆IdL to ⋆IdLᶜ ; ⋆IdR to ⋆IdRᶜ ;  isSetHom to isSetHomC )
        
        open Category (SET (ℓ-max ℓC ℓC')) renaming (ob to obˢ ; _⋆_ to _⋆ˢ_ ; id to idˢ ; ⋆IdR to ⋆IdRˢ ; ⋆IdL to ⋆IdLˢ)
        open Functor
        open Bifunctor
        
        open import Cubical.Categories.Constructions.BinProduct
        
        diagram : obᶜ → Bifunctor ((C ×C C) ^op) (C ×C C) (SET (ℓ-max ℓC ℓC')) 
        diagram c .Bif-ob (c₁⁻ , c₂⁻) (c₁⁺ , c₂⁺) = 
            ((((C)[ c , c₁⁺ ⊗ c₂⁺ ]) × fst ( F ⟅ c₁⁻ ⟆ )) × fst ( G ⟅ c₂⁻ ⟆ )) , 
            isSet× (isSet× isSetHomC (snd ( F ⟅ c₁⁻ ⟆ ))) (snd ( G ⟅ c₂⁻ ⟆ ))
        diagram c .Bif-homL (f₁ , f₂) _ = map-× (map-× (λ x → x) (F ⟪ f₁ ⟫)) (G ⟪ f₂ ⟫)
        diagram c .Bif-homR _ (f₁ , f₂) = map-× (map-× (λ m → m ⋆⟨ C ⟩ (f₁ ⊗ₕ f₂)) λ x → x ) λ x → x
        diagram c .Bif-idL = 
            funExt λ {((_ , Fc), Gc) → ≡-× (≡-× refl (funExt⁻ (F .F-id) Fc)) ((funExt⁻ (G .F-id) Gc))}
        diagram c .Bif-idR = 
            funExt λ {((f , _), _) → ≡-× (≡-×  {!  !} refl )refl }
        diagram c .Bif-seqL {d = (d₁ , d₂)} (f₁ , f₂) (g₁ , g₂) = 
            funExt λ{((c→d₁d₂ , Fc₁fst) , Gc₁snd) → ≡-× (≡-× refl (funExt⁻ (F-seq F f₁ g₁) Fc₁fst)) ((funExt⁻ (F-seq G f₂ g₂) Gc₁snd))}
        diagram c .Bif-seqR {d = (d₁ , d₂)} (f₁ , f₂) (g₁ , g₂) = 
            funExt λ{((c→d₁d₂ , Fc₁fst) , Gc₁snd) → ≡-× (≡-× {!   !} refl) refl}
        diagram c .Bif-assoc (f₁ , f₂) (g₁ , g₂) = refl

        open import Cubical.Categories.Constructions.Coend.Base

        Day : (c : obᶜ) → Coend (diagram c)
        Day c = Set-Coend (diagram c) 

        open import Cubical.HITs.SetCoequalizer.Base
        open Coend
        open Cowedge
        open Functor

        day : {z x y : obᶜ} → ((C)[ z , (x ⊗ y) ]) → ( fst ( F ⟅ x ⟆ ))→  ( fst ( G ⟅ y ⟆ )) → fst( Day z .cowedge .nadir) 
        day {x = x}{y} f Fx Gy = inc ((x , y) , (f , Fx) , Gy)

        day-ap : {i a b : obᶜ} {h h' : (C)[ i , (a ⊗ b) ]} {x x' : fst ( F ⟅ a ⟆) } {y y' :  fst (G ⟅ b ⟆) }
            → h ≡ h' → x ≡ x' → y ≡ y' → day h x y ≡ day h' x' y'
        day-ap {a = a} {b} p q r i =  inc ((a , b) , (p i , q i) , r i) 

        day-apₘ : ∀ {i a b} {h h' : (C)[ i , (a ⊗ b)]} {x y} → h ≡ h' → day h x y ≡ day h' x y
        day-apₘ p = day-ap p refl refl

        Day-cowedge : ∀ {x} {y} → (C)[ y ,  x ] → Cowedge (diagram x)
        Day-cowedge {_} {y} _ .nadir = Day y .cowedge .nadir
        Day-cowedge f .ψ (a , b) ((g , Fa) , Gb) = day (f ⋆ᶜ g) Fa Gb
        Day-cowedge f .extranatural (f₁ , f₂) = {!   !}

        factor' : ∀ {i} (W : Cowedge (diagram i)) → fst(Day i . cowedge .nadir) → fst (W .nadir)
        factor' W = Day _ .factor W 
    
        _⊗ᴰ_ : Presheaf (MC .StrictMonCategory.C) (ℓ-max ℓC ℓC')
        _⊗ᴰ_ .F-ob x = Day x .cowedge .nadir
        _⊗ᴰ_ .F-hom {y}{x} f = factor' (Day-cowedge f)
        _⊗ᴰ_ .F-id = funExt λ{x → {!  !} }
        _⊗ᴰ_ .F-seq f g = funExt λ nad → {!   !} 

    module _ (MC : StrictMonCategory ℓC ℓC') where 
        open StrictMonCategory MC 
        open Category C renaming (ob to obᶜ ; _⋆_ to _⋆ᶜ_ ; id to idᶜ ; ⋆IdL to ⋆IdLᶜ ; ⋆IdR to ⋆IdRᶜ ;  isSetHom to isSetHomC )
    
        open import Cubical.Categories.Constructions.BinProduct
        open Functor

        PshC = PresheafCategory C (ℓ-max ℓC ℓC')

        Day-Functor : Functor (PshC ×C PshC) PshC 
        Day-Functor .F-ob (F , G)= _⊗ᴰ_ {MC = MC} F G
        Day-Functor .F-hom {(x₁ , x₂)}{(y₁ , y₂)}(f₁ , f₂) = {!   !}
        Day-Functor .F-id = {!   !}
        Day-Functor .F-seq = {!   !}

        open MonoidalStr
        PshMon : MonoidalStr PshC 
        PshMon .tenstr = record { ─⊗─ = Day-Functor ; unit = {!   !} }
        PshMon .α = {!   !}
        PshMon .η = {!   !}
        PshMon .ρ = {!   !}
        PshMon .pentagon = {!   !}
        PshMon .triangle = {!   !}

        Day-Monoidal : MonoidalCategory (ℓ-suc (ℓ-max ℓC ℓC')) (ℓ-max ℓC ℓC')
        Day-Monoidal = record { C = PshC ; monstr = PshMon }