
{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Exponentials where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Instances.Sets

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Fibration.Base
import Cubical.Categories.Displayed.Reasoning
open import Cubical.Categories.Displayed.Instances.Sets.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    C : Category ℓC ℓC'

open Category
open UniversalElement
open Functorᴰ
open CartesianOver
open UniversalElementᴰ

module ReasoningDom (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  open Categoryᴰ Cᴰ
  _≡dom[_]_ : {x y : C .ob}{f : C [ x , y ]}
    {xᴰ xᴰ' : ob[ x ]}{yᴰ : ob[ y ]} →
    Hom[ f ][ xᴰ , yᴰ ] → xᴰ ≡ xᴰ' → Hom[ f ][ xᴰ' , yᴰ ] → Type _
  _≡dom[_]_ {f = f} {yᴰ = yᴰ} fᴰ p fᴰ' = PathP (λ i → Hom[ f ][ p i , yᴰ ]) fᴰ fᴰ'
  _≡₂[_,_]_ : {x y : C .ob}{f g : C [ x , y ]}
      {xᴰ xᴰ' : ob[ x ]}{yᴰ : ob[ y ]} →
    Hom[ f ][ xᴰ , yᴰ ] → f ≡ g → xᴰ ≡ xᴰ' → Hom[ g ][ xᴰ' , yᴰ ] → Type _
  _≡₂[_,_]_ {yᴰ = yᴰ} fᴰ p q gᴰ = PathP (λ i → Hom[ p i ][ q i , yᴰ ]) fᴰ gᴰ
  module _ where
    private
      variable
        x y : C .ob
        e f g : C [ x , y ]
        xᴰ : ob[ x ]
        xᴰ' : ob[ x ]
        yᴰ : ob[ y ]
    reind-dom : xᴰ ≡ xᴰ' → Hom[ f ][ xᴰ , yᴰ ] → Hom[ f ][ xᴰ' , yᴰ ]
    reind-dom = subst Hom[ _ ][_, _ ]
    reind-dom-filler : (p : xᴰ ≡ xᴰ') (fᴰ : Hom[ f  ][ xᴰ , yᴰ  ]) →
      fᴰ ≡dom[ p ] (reind-dom p fᴰ)
    reind-dom-filler = subst-filler Hom[ _ ][_, _ ]
    reind-dom-filler-sym : (p : xᴰ ≡ xᴰ') (fᴰ' : Hom[ f ][ xᴰ' , yᴰ ]) →
      reind-dom (sym p) fᴰ' ≡dom[ p ] fᴰ'
    reind-dom-filler-sym p fᴰ' = symP (reind-dom-filler (sym p) fᴰ')

    reind₂ : f ≡ g → xᴰ ≡ xᴰ' → Hom[ f ][ xᴰ , yᴰ ] → Hom[ g  ][ xᴰ' , yᴰ ]
    reind₂ = subst2 Hom[_][_, _ ]
    reind₂-filler : (p : f ≡ g)(q : xᴰ ≡ xᴰ')(fᴰ : Hom[ f ][ xᴰ , yᴰ ]) → fᴰ ≡₂[ p , q ] reind₂ p q fᴰ
    reind₂-filler = subst2-filler Hom[_][_, _ ]
    ≡₂[]-rectify : {p p' : f ≡ g}{q : xᴰ ≡ xᴰ'}
      {fᴰ : Hom[ f ][ xᴰ , yᴰ ]}
      {gᴰ : Hom[ g ][ xᴰ' , yᴰ ]} →
      fᴰ ≡₂[ p , q ] gᴰ → fᴰ ≡₂[ p' , q ] gᴰ
    ≡₂[]-rectify {q = q} {fᴰ = fᴰ} {gᴰ = gᴰ} = subst (fᴰ ≡₂[_, q ] gᴰ) (C .isSetHom _ _ _ _)

    --module _ {ℓ : Level}
    --  {A : Type ℓ}{B : A → Type ℓ}{C : (a : A) → B a → Type ℓ}
    --  {a a' a'' : A}
    --  {b : B a}{b' : B a'}{b'' : B a''}
    --  (f : (a : A) → (b : B a) → C a b)
    --  (p : a ≡ a')(q : a' ≡ a'')
    --  (r : PathP (λ i → B (p i)) b b')(s : PathP (λ i → B (q i)) b' b'')
    --  where
    --  generic :
    --    cong₂ (λ x y → f x y) (p ∙ q) {!compPathP r s!}
    --    ≡
    --    {!!}
    --  generic = {!!}
  module _ {x y : C .ob}
    {e f g : C [ x , y ]}
    {o : e ≡ f}{p : f ≡ g}
    {xᴰ : ob[ x ]}{xᴰ' : ob[ x ]}{yᴰ : ob[ y ]}
    {q : xᴰ ≡ xᴰ'}
    {fᴰ' : Hom[ e ][ xᴰ , yᴰ ]}{fᴰ : Hom[ f ][ xᴰ , yᴰ ]}{gᴰ : Hom[ g ][ xᴰ' , yᴰ ]}
    where
    _◁ᴰ_ : fᴰ' ≡[ o ] fᴰ → fᴰ ≡₂[ p , q ] gᴰ → fᴰ' ≡₂[ o ∙ p , q ] gᴰ
    l ◁ᴰ r = subst (λ x → PathP (λ i → x i) fᴰ' gᴰ) (sym filler) (compPathP l r)
      where
      -- TODO: I don't get why this works, I just copied congFunct and tried
      helper :
        cong₂ (λ x y → Hom[ x ][ y , yᴰ ]) (o ∙ p) (refl ∙ q)
        ≡ cong₂ (λ x y → Hom[ x ][ y , yᴰ ]) o refl ∙ cong₂ (λ x y → Hom[ x ][ y , yᴰ ]) p q
      helper j i = hcomp (λ k → (λ { (i = i0) → Hom[ e ][ xᴰ , yᴰ ]
                                   ; (i = i1) → cong₂ (λ x y → Hom[ x ][ y , yᴰ ]) p q k
                                   ; (j = i0) → cong₂ (λ x y → Hom[ x  ][ y , yᴰ  ]) (compPath-filler o p k) (compPath-filler refl q k) i
                                   }))
                                   (cong₂ (λ x y → Hom[ x ][ y , yᴰ ]) o {u = xᴰ} refl i)
      reduced-filler :
        cong₂ (Hom[_][_, yᴰ ]) (o ∙ p) q
        ≡
        congS (Hom[_][ xᴰ , yᴰ ]) o ∙ cong₂ (Hom[_][_, yᴰ  ]) p q
      reduced-filler = (congS (cong₂ Hom[_][_, yᴰ ] _) (lUnit _)) ∙ helper
      filler :
        _≡_ {A = Hom[ e ][ xᴰ , yᴰ ] ≡ Hom[ g ][ xᴰ' , yᴰ ]}
        (λ i → Hom[ (o ∙ p) i ][ q i , yᴰ ])
        (λ i → ((λ z → Hom[ o z ][ xᴰ , yᴰ ]) ∙ (λ z → Hom[ p z ][ q z , yᴰ ])) i)
      filler = reduced-filler
  --≡₂[]-contract : {!!}
  --≡₂[]-contract = {!!}
  --reind₂ : →
--module _ (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  open Cubical.Categories.Displayed.Reasoning Cᴰ
  private
    module Cᴰ = Categoryᴰ Cᴰ
  -- TODO: this is already in the library, I just don't want to find it right now
  module _ (c : C .ob) where
    idue : UniversalElement C (C [-, c ])
    idue .vertex = c
    idue .element = C .id
    idue .universal c' .equiv-proof f = uniqueExists
      f (C .⋆IdR _) (λ _ → C .isSetHom _ _) (λ _ p → sym p ∙ C .⋆IdR _)
  -- the universal property of `c'ᴰ ∧ f* cᴰ`,
  -- the vertical binary product of c'ᴰ and the pullback of cᴰ' along f
  module heterogeneous-pair {c' c}
    (f : C [ c' , c ])(c'ᴰ : Cᴰ.ob[ c' ])(cᴰ : Cᴰ.ob[ c ]) where
    spec : Presheafᴰ Cᴰ (C [-, c' ]) _
    spec .F-obᴰ {x = c''} c''ᴰ g =
      Cᴰ.Hom[ g ][ c''ᴰ , c'ᴰ ] × Cᴰ.Hom[ g ⋆⟨ C ⟩ f ][ c''ᴰ , cᴰ ] ,
      isSet× Cᴰ.isSetHomᴰ Cᴰ.isSetHomᴰ
    spec .F-homᴰ {x = c''} {y = c'''} {f = h}
      {xᴰ = c''ᴰ} {yᴰ = c'''ᴰ} hᴰ g (l , r) =
      hᴰ Cᴰ.⋆ᴰ l , reind (sym (C .⋆Assoc _ _ _)) (hᴰ Cᴰ.⋆ᴰ r)
    spec .F-idᴰ {x = c''} {xᴰ = c''ᴰ} = funExt (λ g → funExt (λ (l , r) →
      ΣPathP
        (Cᴰ.⋆IdLᴰ l ,
        ≡[]-rectify (reind-filler-sym _ _ [ _ ]∙[ _ ] Cᴰ.⋆IdLᴰ _))))
    spec .F-seqᴰ {x = c''''} {y = c'''} {z = c''} {f = h} {g = i}
      {xᴰ = c''''ᴰ} {yᴰ = c'''ᴰ} {zᴰ = c''ᴰ} hᴰ iᴰ =
      funExt (λ g → funExt (λ (l , r) → ΣPathP
        (Cᴰ.⋆Assocᴰ _ _ _ ,
        ≡[]-rectify (reind-filler-sym _ _ [ _ ]∙[ _ ]
          Cᴰ.⋆Assocᴰ _ _ _ [ _ ]∙[ _ ]
          ≡[]⋆ refl (sym (C .⋆Assoc _ _ _)) refl (reind-filler _ _) [ _ ]∙[ _ ]
          reind-filler _ _))))
    ue : Type _
    ue = UniversalElementᴰ Cᴰ spec (idue c')
    module HetPairNotation (hp : ue) where
      vert : Cᴰ.ob[ c' ]
      vert = hp .vertexᴰ
      π₁₂ : Cᴰ.Hom[ C .id ][ vert , c'ᴰ ] × Cᴰ.Hom[ C .id ⋆⟨ C ⟩ f ][ vert , cᴰ ]
      π₁₂ = hp .elementᴰ
      π₁ = π₁₂ .fst
      π₂ = π₁₂ .snd
      module _ {x : C .ob}{xᴰ : Cᴰ.ob[ x ]}{g : C [ x , c' ]} where
        _p,_ : Cᴰ.Hom[ g ⋆⟨ C ⟩ C .id ][ xᴰ , c'ᴰ ] →
          Cᴰ.Hom[ g ⋆⟨ C ⟩ C .id ⋆⟨ C ⟩ f ][ xᴰ , cᴰ ] →
          Cᴰ.Hom[ g ][ xᴰ , vert ]
        gᴰ p, g⋆fᴰ = invIsEq (hp .universalᴰ) (gᴰ , g⋆fᴰ)
        β : (gᴰ : Cᴰ.Hom[ g ⋆⟨ C ⟩ C .id ][ xᴰ , c'ᴰ ]) →
          (g⋆fᴰ : Cᴰ.Hom[ g ⋆⟨ C ⟩ C .id ⋆⟨ C ⟩ f ][ xᴰ , cᴰ ]) →
          (gᴰ p, g⋆fᴰ Cᴰ.⋆ᴰ π₁ , reind (sym (C .⋆Assoc _ _ _)) (gᴰ p, g⋆fᴰ Cᴰ.⋆ᴰ π₂)) ≡ (gᴰ , g⋆fᴰ)
        β gᴰ g⋆fᴰ = secIsEq (hp .universalᴰ) (gᴰ , g⋆fᴰ)
        η : (gᴰ : Cᴰ.Hom[ g ][ xᴰ , hp .vertexᴰ ]) →
          ((gᴰ Cᴰ.⋆ᴰ π₁) p, reind (sym (C .⋆Assoc _ _ _)) (gᴰ Cᴰ.⋆ᴰ π₂)) ≡ gᴰ
        η gᴰ = retIsEq (hp .universalᴰ) gᴰ
  AllHetPairs : Type _
  AllHetPairs = ∀{c' c}
    (f : C [ c' , c ])(c'ᴰ : Cᴰ.ob[ c' ])(cᴰ : Cᴰ.ob[ c ]) →
    heterogeneous-pair.ue f c'ᴰ cᴰ
  module _
    (isFib : AllCartesianOvers Cᴰ) {- for typechecking performance -}
    (vps : VerticalBinProducts Cᴰ)
    where
    module  _ {c' c}
      (f : C [ c' , c ])(c'ᴰ : Cᴰ.ob[ c' ])(cᴰ : Cᴰ.ob[ c ])
      where
      private
        module het-pair = heterogeneous-pair f c'ᴰ cᴰ
        module ∧ = VerticalBinProductsAtNotation (vps (c'ᴰ , isFib cᴰ f .f*cᴰ'))
      impl : het-pair.ue
      impl .vertexᴰ = ∧.vert
      impl .elementᴰ = ∧.π₁ , (∧.π₂ Cᴰ.⋆ᴰ isFib cᴰ f .π)
      impl .universalᴰ {f = g} .equiv-proof (l , r) = uniqueExists
        ∧.⟨ l , r* ⟩
        (ΣPathP (
          congS fst (∧.β l r*) ,
          ≡[]-rectify (reind-filler-sym _ _ [ _  ]∙[ _ ]
            symP (Cᴰ.⋆Assocᴰ _ _ _) [ _ ]∙[ _ ]
            ≡[]⋆ refl refl (congS snd (∧.β l r*)) refl [ _ ]∙[ _ ]
            r*-comm)))
        (λ _ → isSet× Cᴰ.isSetHomᴰ Cᴰ.isSetHomᴰ _ _)
        λ gᴰ' p → ≡[]-rectify
          (cong₂ (λ x y → ∧.⟨ x , y ⟩)
            (sym (congS fst p))
            (congS (λ x → isFib cᴰ f .isCartesian _ _ x .fst .fst)
              (sym (congS snd p)) ∙
              congS fst (isFib cᴰ f .isCartesian _ _ _ .snd (_ , ≡[]-rectify (Cᴰ.⋆Assocᴰ _ _ _ [ _ ]∙[ _ ] reind-filler _ _)))))
          ∙ ∧.η gᴰ'
        where
        r* : Cᴰ.Hom[ g  ⋆⟨ C ⟩ C .id ][ _ , isFib cᴰ f .f*cᴰ' ]
        r* = isFib cᴰ f .isCartesian _ _ r .fst .fst
        r*-comm : r* Cᴰ.⋆ᴰ isFib cᴰ f .π ≡ r
        r*-comm = isFib cᴰ f .isCartesian _ _ r .fst .snd

module _ (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (ahp : ReasoningDom.AllHetPairs Cᴰ)
  where
  open Cubical.Categories.Displayed.Reasoning Cᴰ
  open ReasoningDom Cᴰ
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
  module _ {c : C .ob}
    (cᴰ cᴰ' : Cᴰ.ob[ c ]) where
    VerticalExponentialsAtSpec : Presheafᴰ Cᴰ (C [-, c ]) _
    VerticalExponentialsAtSpec .F-obᴰ xᴰ f = Cᴰ.Hom[ f ][ foo.vert , cᴰ' ] , Cᴰ.isSetHomᴰ
      where
      module foo = heterogeneous-pair.HetPairNotation Cᴰ f xᴰ cᴰ (ahp _ _ _)
    VerticalExponentialsAtSpec .F-homᴰ {f = g} {xᴰ = xᴰ} {yᴰ = yᴰ} gᴰ f fᴰ =
      (reind (C .⋆IdL _ ∙ sym (C .⋆IdR _)) (bar.π₁ Cᴰ.⋆ᴰ gᴰ)
      foo.p,
      reind (sym (C .⋆Assoc _ _ _) ∙ congS (C._⋆ f) (C .⋆IdL _ ∙ sym (C .⋆IdR _))) bar.π₂)
      Cᴰ.⋆ᴰ fᴰ
      where
      module foo = heterogeneous-pair.HetPairNotation Cᴰ f xᴰ cᴰ (ahp _ _ _)
      module bar = heterogeneous-pair.HetPairNotation Cᴰ (g ⋆⟨ C ⟩ f) yᴰ cᴰ (ahp _ _ _)
    VerticalExponentialsAtSpec .F-idᴰ {xᴰ = xᴰ} = funExt (λ f → funExt (λ fᴰ → ≡₂[]-rectify (goal f fᴰ)))
      where
      module _ f fᴰ where
        module foo = heterogeneous-pair.HetPairNotation Cᴰ f xᴰ cᴰ (ahp _ _ _)
        module bar = heterogeneous-pair.HetPairNotation Cᴰ (C .id ⋆⟨ C ⟩ f) xᴰ cᴰ (ahp _ _ _)
        hm : C .id ⋆⟨ C ⟩ C .id ≡ C .id ⋆⟨ C ⟩ C .id
        hm = C .⋆IdL (C .id) ∙ sym (C .⋆IdR (C .id))
        goal :
          ((reind hm (bar.π₁ Cᴰ.⋆ᴰ Cᴰ.idᴰ)
          foo.p,
          reind (sym (C .⋆Assoc _ _ _) ∙ congS (C._⋆ f) hm) bar.π₂)
          Cᴰ.⋆ᴰ fᴰ)
          ≡₂[ _ , congS (λ x → ahp x xᴰ cᴰ .vertexᴰ) (C .⋆IdL f) ]
          fᴰ
        goal = {!!}
    VerticalExponentialsAtSpec .F-seqᴰ = {!!}
    VerticalExponentialsAt : Type _
    VerticalExponentialsAt = UniversalElementᴰ Cᴰ VerticalExponentialsAtSpec {!!} --(idue c)
