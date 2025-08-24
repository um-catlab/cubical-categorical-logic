-- A redundant version of the functor category

-- What is a morphism of functors:
-- F ⇒ G : Functor C D
-- Either a natural family of α a : F a ⇒ G a
-- Or a profunctor homomorphism C → D(F,G) C [ c , c' ] → D [ F c , G c' ]
-- Or how about D(F c , F c') → D(G c , G c')

-- C → Func,Nat D E
-- gives us "one-sided" actions, for every c a functor from D to E
-- that commutes with C-morphisms
-- and vice-versa

-- C → Func,ProfHom D E
-- gives us


module Cubical.Categories.Instances.Functors.Redundant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Data.Sigma

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓ ℓ' : Level

open Category
open Functor
open NatTrans

RedundantStr : {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
               {F G : Functor C D}
               (α : NatTrans F G)
             → Type _
RedundantStr {C = C}{D = D}{F = F}{G = G} α =
  Σ[ ϕ ∈ (∀ {a a'} → C [ a , a' ] → D [ F ⟅ a ⟆ , G ⟅ a' ⟆ ]) ]
  (∀ {a a'}(f : C [ a , a' ]) → ϕ f ≡ α ⟦ a ⟧ ⋆⟨ D ⟩ G ⟪ f ⟫)

RedundNatTrans : {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
                 (F G : Functor C D)
               → Type _
RedundNatTrans F G = Σ[ α ∈ NatTrans F G ] RedundantStr α

isContrRedundantStr : {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
               {F G : Functor C D}
               (α : NatTrans F G)
             → isContr (RedundantStr α)
isContrRedundantStr {C = C} {D = D} {F = F} {G = G} α .fst .fst f =
  α ⟦ _ ⟧ ⋆⟨ D ⟩ G ⟪ f ⟫
isContrRedundantStr {C = C} {D = D} {F = F} {G = G} α .fst .snd f = refl
isContrRedundantStr {C = C} {D = D} {F = F} {G = G} α .snd (ϕ , p) =
  Σ≡Prop (λ x → isPropImplicitΠ2 λ _ _ → isPropΠ (λ _ → D .isSetHom _ _))
  (implicitFunExt λ {x} → implicitFunExt λ {y} → funExt λ f →
    sym (p f))

RedundNatTrans≡  : {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
                   {F G : Functor C D}
                 → {α β : RedundNatTrans F G}
                 → (α .fst .N-ob ≡ β .fst .N-ob)
                 → α ≡ β
RedundNatTrans≡ p = Σ≡Prop (λ α → isContr→isProp (isContrRedundantStr α))
  (makeNatTransPath p)

module _ (C : Category ℓC ℓC')(D : Category ℓD ℓD') where
  FUNCTOR : Category _ _
  FUNCTOR .ob = Functor C D
  FUNCTOR .Hom[_,_] F G = RedundNatTrans F G
  FUNCTOR .id {x = F} .fst = idTrans F
  FUNCTOR .id {x = F} .snd .fst = F .F-hom
  FUNCTOR .id {x = F} .snd .snd f = sym (D .⋆IdL _)
  FUNCTOR ._⋆_ (α , ϕ) (β , ψ) .fst = β ∘ᵛ α
  FUNCTOR ._⋆_ {x = F}{y = G}{z = H} (α , ϕ) (β , ψ) .snd .fst f =
    ϕ .fst f ⋆⟨ D ⟩ β ⟦ _ ⟧
  FUNCTOR ._⋆_ (α , ϕ) (β , _) .snd .snd f =
    cong₂ (seq' D) (ϕ .snd f) refl
    ∙ D .⋆Assoc _ _ _
    ∙ cong₂ (seq' D) refl (β .N-hom f)
    ∙ sym (D .⋆Assoc _ _ _)
  FUNCTOR .⋆IdL (α , ϕ) = RedundNatTrans≡ (funExt (λ a → D .⋆IdL _))
  FUNCTOR .⋆IdR (α , _) = RedundNatTrans≡ (funExt (λ a → D .⋆IdR _))
  FUNCTOR .⋆Assoc f g h = RedundNatTrans≡ (funExt (λ a → D .⋆Assoc _ _ _))
  FUNCTOR .isSetHom =
    isSetΣ isSetNatTrans
           (λ α → isProp→isSet (isContr→isProp (isContrRedundantStr α)))

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'} {E : Category ℓE ℓE'} where
  Sym : Functor C (FUNCTOR D E) → Functor D (FUNCTOR C E)
  Sym F .F-ob d .F-ob c = F ⟅ c ⟆ ⟅ d ⟆
  Sym F .F-ob d .F-hom f = (F ⟪ f ⟫) .fst ⟦ d ⟧
  Sym F .F-ob d .F-id = λ i → F .F-id i .fst ⟦ d ⟧
  Sym F .F-ob d .F-seq f f' = λ i → F .F-seq f f' i .fst ⟦ d ⟧
  Sym F .F-hom g .fst .N-ob c = F ⟅ c ⟆ ⟪ g ⟫
  Sym F .F-hom g .fst .N-hom f = sym ((F ⟪ f ⟫) .fst .N-hom g)
  Sym F .F-hom g .snd .fst f = (F ⟪ f ⟫) .snd .fst g
  Sym F .F-hom g .snd .snd f = (F ⟪ f ⟫) .snd .snd g
    ∙ (λ i → (F ⟪ f ⟫) .fst .N-hom g (~ i))
  Sym F .F-id = RedundNatTrans≡ (funExt (λ c → (F ⟅ c ⟆) .F-id ))
  Sym F .F-seq g g' = RedundNatTrans≡ (funExt λ c → (F ⟅ c ⟆) .F-seq g g')


-- (C × D) × E → F
-- ≅ (C × D) → (E → F)
-- ≡ C → (D → (E → F))
-- ≡ C → (D × E → F)
-- ≡ C × (D × E) → F

