-- | Should probably rename this to "products"
module UMP where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Instances.Sets
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.FinSet
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism

open Category
open Functor
open NatTrans
open UnivElt
open isUniversal

private
  variable
    ℓc ℓc' ℓd ℓd' ℓp ℓj : Level

⊤ᴾ : ∀ {ℓo ℓt} (C : Category ℓo ℓt) → Presheaf C ℓ-zero
⊤ᴾ C .F-ob Γ = Unit , isSetUnit
⊤ᴾ C .F-hom = λ x₁ x₂ → tt
⊤ᴾ C .F-id = refl
⊤ᴾ C .F-seq = λ f g → refl

push-⊤ᴾ : {C : Category ℓc ℓc'} {D : Category ℓd ℓd'} (F : Functor C D) →
          PshHom F (⊤ᴾ C) (⊤ᴾ D)
push-⊤ᴾ F .N-ob _ _ = lift tt
push-⊤ᴾ F .N-hom f = funExt (λ _ → refl)

preserves-⊤ : {C : Category ℓc ℓc'} {D : Category ℓd ℓd'} (F : Functor C D) →
              Type (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓd) ℓd')
preserves-⊤ {C = C}{D} F =
  preserves-representability F (⊤ᴾ C) (⊤ᴾ D) (push-⊤ᴾ F)

×ᴾ : ∀ {ℓo ℓt ℓS} (C : Category ℓo ℓt) → (P Q : Presheaf C ℓS) → Presheaf C ℓS
×ᴾ C P Q .F-ob  = λ a → ((fst (P ⟅ a ⟆)) × (fst (Q ⟅ a ⟆))) ,
                         isSet× (snd (P ⟅ a ⟆ )) (snd (Q ⟅ a ⟆))
×ᴾ C P Q .F-hom f (ϕ₁ , ϕ₂) = C [ ϕ₁ ∘ᴾ⟨ P ⟩ f ] , C [ ϕ₂ ∘ᴾ⟨ Q ⟩ f ]
×ᴾ C P Q .F-id  = funExt λ ϕ i → (∘ᴾId C P (fst ϕ) i) , ((∘ᴾId C Q (snd ϕ) i))
×ᴾ C P Q .F-seq f g = funExt (λ ϕ i → (∘ᴾAssoc C P (fst ϕ) f g i) ,
                                      ((∘ᴾAssoc C Q (snd ϕ) f g i) ))

-- TODO: should be easier using limit formulation
push-×ᴾ : {C : Category ℓc ℓc'} {D : Category ℓd ℓd'}
          (F : Functor C D) (a b : C .ob)
        → PshHom F (×ᴾ C (C [-, a ]) (C [-, b ]))
                   (×ᴾ D (D [-, F ⟅ a ⟆ ]) (D [-, F ⟅ b ⟆ ]))
push-×ᴾ F a b .N-ob c (lift (f₁ , f₂)) = lift ((F .F-hom f₁) , (F .F-hom f₂))
push-×ᴾ {C = C}{D} F a b .N-hom f = funExt λ (lift (f₁ , f₂)) →
  λ i → lift ((F .F-seq f f₁ i) , ((F .F-seq f f₂ i)))

preserves-× : {C : Category ℓc ℓc'} {D : Category ℓd ℓd'}
              (F : Functor C D) → Type _
preserves-× {C = C}{D} F = (a b : C .ob) →
  preserves-representability F (×ᴾ C (C [-, a ]) (C [-, b ]))
                               (×ᴾ D (D [-, F ⟅ a ⟆ ]) (D [-, F ⟅ b ⟆ ]))
                               (push-×ᴾ F a b)


Πᴾ : ∀ {ℓo ℓt ℓS} (C : Category ℓo ℓt)
              → (J : Type ℓp)
              → (J → Presheaf C ℓS)
              → Presheaf C (ℓ-max ℓS ℓp)
Πᴾ C J Ps .F-ob Γ =
  ((j : J) → fst (Ps j ⟅ Γ ⟆) ) , isSetΠ (λ j → snd (Ps j ⟅ Γ ⟆))
Πᴾ C J Ps .F-hom = λ γ ϕs j → C [ ϕs j ∘ᴾ⟨ Ps j ⟩ γ ]
Πᴾ C J Ps .F-id = funExt (λ ϕs i j → ∘ᴾId C (Ps j) (ϕs j) i)
Πᴾ C J Ps .F-seq δ γ = λ i ϕs j → ∘ᴾAssoc C (Ps j) (ϕs j) δ γ i

push-Πᴾ : {C : Category ℓc ℓc'} {D : Category ℓd ℓd'} (F : Functor C D)
        → (Vars : Type ℓ-zero) (obs : Vars → C .ob)
        → PshHom F (Πᴾ C Vars λ x → C [-, obs x ] )
                   ((Πᴾ D Vars λ x → D [-, F ⟅ obs x ⟆ ] ))
push-Πᴾ F Vars obs .N-ob c fs = lift (λ x → F ⟪ fs .lower x ⟫)
push-Πᴾ F Vars obs .N-hom f =
  funExt (λ fs i → lift (λ x → F .F-seq f (fs .lower x) i))

-- Proof that any object is its own unary product
unaryProd : ∀ {ℓo ℓt} (C : Category ℓo ℓt)(Γ : C .ob) →
  isUniversal C (Πᴾ C Unit (λ tt → C [-, Γ ])) (Γ , λ tt → id C)
unaryProd C Γ .coinduction = λ z → z tt
unaryProd C Γ .commutes ϕ = funExt (λ x → C .⋆IdR (ϕ tt))
unaryProd C Γ .is-uniq ϕ f comm =
  f ≡⟨ sym (C .⋆IdR f) ⟩ f ⋆⟨ C ⟩ C .id  ≡[ i ]⟨ comm i tt ⟩ ϕ tt ∎

product : ∀ {ℓo ℓt ℓJ} (C : Category ℓo ℓt) (J : Type ℓJ) →
          (D : J → C .ob) → Type _
product C J D = UnivElt C (Πᴾ C J λ j → C [-, D j ])

product-cone : ∀ {ℓo ℓt ℓJ} (C : Category ℓo ℓt) (J : Type ℓJ) →
              (D : J → C .ob) → (Π : C .ob) → ((j : J) → C [ Π , D j ]) → Type _
product-cone C J D Π π = isUniversal C (Πᴾ C J (λ j → C [-, D j ])) (Π , π)

-- Some notation would greatly improve this...
nestProd : ∀ {ℓo ℓt ℓJ ℓK} (C : Category ℓo ℓt)
         (J : Type ℓJ) (K : J → Type ℓK)
         (D : (j : J) → K j → C .ob)
         → (K-prods : ∀ j → product C (K j) (D j))
         → (JK-prod : product C (Σ J K) (λ (j , k) → D j k))
         → product-cone C J (λ j → K-prods j .vertex)
                        (JK-prod .vertex)
                        λ j → K-prods j .universal .coinduction
                          λ k → JK-prod .element (j , k)
nestProd C J K D K-prods JK-prod .coinduction =
  λ M⟨j⟩ → JK-prod .universal .coinduction (λ (j , k) →
    K-prods j .element k ∘⟨ C ⟩ M⟨j⟩ j)
nestProd C J K D K-prods JK-prod .commutes M⟨j⟩ = funExt (λ j →
  K-prods j .universal .coinduction (λ k → JK-prod .element (j , k))
    ∘⟨ C ⟩ JK-prod .universal .coinduction
      (λ (j , k) → K-prods j .element k ∘⟨ C ⟩ M⟨j⟩ j)
  ≡⟨ coinduction-natural (K-prods j .universal)
     ((λ k → JK-prod .element (j , k))) _ ⟩
  K-prods j .universal .coinduction (λ k →
    JK-prod .element (j , k) ∘⟨ C ⟩ JK-prod .universal .coinduction
      (λ (j , k) → K-prods j .element k ∘⟨ C ⟩ M⟨j⟩ j))

  ≡[ i ]⟨ K-prods j .universal .coinduction (λ k → JK-prod .universal .commutes
          (λ (j , k) → K-prods j .element k ∘⟨ C ⟩ M⟨j⟩ j) i (j , k)) ⟩
  K-prods j .universal .coinduction (λ k → K-prods j .element k ∘⟨ C ⟩ M⟨j⟩ j)
  ≡⟨ sym (η-expansion (K-prods j .universal) (M⟨j⟩ j)) ⟩
  M⟨j⟩ j ∎)
nestProd C J K D K-prods JK-prod .is-uniq M⟨j⟩ f f-comm =
  JK-prod .universal .is-uniq
    ((λ (j , k) → K-prods j .element k ∘⟨ C ⟩ M⟨j⟩ j)) f
  (funExt (λ (j , k) →
    -- need to show π (j , k) ∘ f ≡ π k ∘ M⟨j⟩ j
    JK-prod .element (j , k) ∘⟨ C ⟩ f
      ≡[ i ]⟨ K-prods j .universal .commutes
              (λ k' → JK-prod .element (j , k')) (~ i) k ∘⟨ C ⟩ f ⟩
    (K-prods j .element k ∘⟨ C ⟩ (K-prods j .universal .coinduction
      λ k' → JK-prod .element (j , k'))) ∘⟨ C ⟩ f
      ≡⟨ sym (C .⋆Assoc _ _ _) ⟩
    K-prods j .element k ∘⟨ C ⟩ ((K-prods j .universal .coinduction
      λ k' → JK-prod .element (j , k')) ∘⟨ C ⟩ f)
      ≡[ i ]⟨ K-prods j .element k ∘⟨ C ⟩ f-comm i j ⟩
    K-prods j .element k ∘⟨ C ⟩ M⟨j⟩ j
    ∎))

record CartesianCategory ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    cat : Category ℓ ℓ'
    finite-products : ∀ (J : FinSet ℓ-zero) →
                      (obs : J .fst → cat .ob) → product cat (J .fst) obs

  module _ (J : FinSet ℓ-zero) (obs : J .fst → cat .ob) where
    prod-ob : cat .ob
    prod-ob = finite-products J obs .vertex

    π : (j : J .fst) → cat [ prod-ob , obs j ]
    π j = finite-products J obs .element j

    prod-I : ∀ {Γ} (fs : ∀ (j : J .fst) →
             cat [ Γ , obs j ]) → cat [ Γ , prod-ob ]
    prod-I fs = finite-products J obs .universal .coinduction fs

    π∘prod-I : ∀ {Γ} (fs : ∀ (j : J .fst) → cat [ Γ , obs j ]) (j : J .fst)
             → π j ∘⟨ cat ⟩ prod-I fs ≡ fs j
    π∘prod-I fs j i = finite-products J obs .universal .commutes fs i j

    prod-I⟨π⟩ : prod-I π ≡ cat .id
    prod-I⟨π⟩ =
      prod-I π
        ≡[ i ]⟨ prod-I (λ j → cat .⋆IdL (π j) (~ i)) ⟩
      prod-I (λ j → π j ∘⟨ cat ⟩ cat .id)
        ≡[ i ]⟨ η-expansion (finite-products _ _ .universal) (cat .id) (~ i) ⟩
      cat .id ∎

  null-prod-ob : cat .ob
  null-prod-ob = prod-ob (⊥ , isFinSetFin) λ ()

  prod₀-I : ∀ {Γ} → cat [ Γ , null-prod-ob ]
  prod₀-I = prod-I _ (λ ()) λ ()

  module _ (Γ₁ Γ₂ : cat .ob) where
    bin-prod-ob : cat .ob
    bin-prod-ob = prod-ob (Bool , isFinSetBool) (if_then Γ₁ else Γ₂)

    π₁ : cat [ bin-prod-ob , Γ₁ ]
    π₁ = π _ _ true
    π₂ : cat [ bin-prod-ob , Γ₂ ]
    π₂ = π _ _ false

    BoolElim : ∀ {ℓ}{A : Bool → Type ℓ} →
               (A true) → (A false) → (b : Bool) → A b
    BoolElim t f false = f
    BoolElim t f true = t

    prod₂-I : ∀ {Γ} → cat [ Γ , Γ₁ ] → cat [ Γ , Γ₂ ] → cat [ Γ , bin-prod-ob ]
    prod₂-I γ₁ γ₂ = prod-I _ (λ z → if z then Γ₁ else Γ₂) (BoolElim γ₁ γ₂)

    private
      prod₂-lem : BoolElim π₁ π₂ ≡
                  π (_ , isFinSetBool) (λ z → if z then Γ₁ else Γ₂)
      prod₂-lem i false = π₂
      prod₂-lem i true = π₁

    prod₂-I⟨π⟩ : prod₂-I π₁ π₂ ≡ cat .id
    prod₂-I⟨π⟩ =
      prod₂-I π₁ π₂
        ≡[ i ]⟨ prod-I (_ , isFinSetBool) _ (prod₂-lem i) ⟩
      prod-I
        ((_ , isFinSetBool))
        (if_then Γ₁ else Γ₂)
        (π (_ , isFinSetBool) (if_then Γ₁ else Γ₂))
          ≡⟨ prod-I⟨π⟩ (_ , isFinSetBool) (if_then Γ₁ else Γ₂) ⟩
      cat .id ∎

open CartesianCategory

record CartesianFunctor
  (C : CartesianCategory ℓc ℓc')
  (D : CartesianCategory ℓd ℓd') :
    Type ((ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓd) (ℓ-max ℓd' (ℓ-suc ℓ-zero)))) where
  field
    func : Functor (C .cat) (D .cat)
    preserves-fin-products : ∀ (J : FinSet ℓ-zero) (obs : J .fst → C .cat .ob)
      → preserves-representation func
        (Πᴾ (C .cat) (J .fst) λ j → C .cat [-, obs j ])
        (Πᴾ (D .cat) (J .fst) λ j → D .cat [-, func ⟅ obs j ⟆ ])
                                 (push-Πᴾ func (J .fst) obs)
                                 (C .finite-products J obs)
