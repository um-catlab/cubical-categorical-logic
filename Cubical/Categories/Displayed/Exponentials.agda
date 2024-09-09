
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

module Reasoning₂ (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  open Categoryᴰ Cᴰ
  _≡₂[_,_]_ : {x y : C .ob}{f g : C [ x , y ]}
      {xᴰ xᴰ' : ob[ x ]}{yᴰ : ob[ y ]} →
    Hom[ f ][ xᴰ , yᴰ ] → f ≡ g → xᴰ ≡ xᴰ' → Hom[ g ][ xᴰ' , yᴰ ] → Type _
  _≡₂[_,_]_ {yᴰ = yᴰ} fᴰ p q gᴰ = PathP (λ i → Hom[ p i ][ q i , yᴰ ]) fᴰ gᴰ

  module _ where
    private
      module C = Category C
      variable
        x y : C .ob
        e f g : C [ x , y ]
        xᴰ xᴰ' : ob[ x ]
        yᴰ : ob[ y ]

    reind₂ : f ≡ g → xᴰ ≡ xᴰ' → Hom[ f ][ xᴰ , yᴰ ] → Hom[ g  ][ xᴰ' , yᴰ ]
    reind₂ = subst2 Hom[_][_, _ ]
    reind₂-filler : (p : f ≡ g)(q : xᴰ ≡ xᴰ')(fᴰ : Hom[ f ][ xᴰ , yᴰ ]) →
      fᴰ ≡₂[ p , q ] reind₂ p q fᴰ
    reind₂-filler = subst2-filler Hom[_][_, _ ]
    reind₂-filler-sym : (p : f ≡ g)(q : xᴰ ≡ xᴰ')(fᴰ : Hom[ f ][ xᴰ , yᴰ ]) →
      reind₂ p q fᴰ ≡₂[ sym p , sym q ] fᴰ
    reind₂-filler-sym p q fᴰ = symP (reind₂-filler p q fᴰ)
    -- copied from reind-contract
    reind₂-contract :
      {z : C .ob}
      {h : C [ y , z ]}
      (p : f ≡ g)
      (q : xᴰ ≡ xᴰ')
      {zᴰ : ob[ z ]}
      {fᴰ : Hom[ f ][ xᴰ , yᴰ ]}
      {hᴰ : Hom[ h ][ yᴰ , zᴰ ]} →
      reind₂ (congS (C._⋆ h) p) q (fᴰ ⋆ᴰ hᴰ) ≡ (reind₂ p q fᴰ) ⋆ᴰ hᴰ
    reind₂-contract p q {hᴰ = hᴰ} = fromPathP (congP (λ _ → _⋆ᴰ hᴰ) (transport-filler _ _))
    ≡₂[]-rectify : {p p' : f ≡ g}{q : xᴰ ≡ xᴰ'}
      {fᴰ : Hom[ f ][ xᴰ , yᴰ ]}
      {gᴰ : Hom[ g ][ xᴰ' , yᴰ ]} →
      fᴰ ≡₂[ p , q ] gᴰ → fᴰ ≡₂[ p' , q ] gᴰ
    ≡₂[]-rectify {q = q} {fᴰ = fᴰ} {gᴰ = gᴰ} = subst (fᴰ ≡₂[_, q ] gᴰ) (C .isSetHom _ _ _ _)
  module _ where
    private
      module R = Cubical.Categories.Displayed.Reasoning Cᴰ
    reind₂-contract' :
      {x y : C .ob}
      {f f' g g' : C [ x , y ]}
      {p : f ≡ g}
      {p' : f ≡ f'}
      {p'' : g ≡ g'}
      {xᴰ xᴰ' : ob[ x ]}
      {yᴰ : ob[ y ]}
      {q : xᴰ ≡ xᴰ'}
      {fᴰ : Hom[ f ][ xᴰ , yᴰ ]}
      {gᴰ : Hom[ g ][ xᴰ , yᴰ ]} →
      fᴰ ≡[ p ] gᴰ →
      reind₂ p' q fᴰ ≡[ (sym p') ∙ p ∙ p'' ] reind₂ p'' q gᴰ
    reind₂-contract' {p = p} {p' = p'} {p'' = p''} {yᴰ = yᴰ} {q = q} eq = congP₂
      (λ _ a b → reind₂ {yᴰ = yᴰ} a q b)
      (isSet→SquareP (λ _ _ → C .isSetHom) _ _ _ ((sym p') ∙ p ∙ p''))
      eq

  module _ {x y : C .ob}
    {e f g : C [ x , y ]}
    {o : e ≡ f}{p : f ≡ g}
    {xᴰ : ob[ x ]}{xᴰ' : ob[ x ]}{yᴰ : ob[ y ]}
    {q : xᴰ ≡ xᴰ'}
    {fᴰ' : Hom[ e ][ xᴰ , yᴰ ]}{fᴰ : Hom[ f ][ xᴰ , yᴰ ]}{gᴰ : Hom[ g ][ xᴰ' , yᴰ ]}
    where
    _◁₂_ : fᴰ' ≡[ o ] fᴰ → fᴰ ≡₂[ p , q ] gᴰ → fᴰ' ≡₂[ o ∙ p , q ] gᴰ
    l ◁₂ r = subst (λ x → PathP (λ i → x i) fᴰ' gᴰ) (sym filler) (compPathP l r)
      where
      -- TODO: I don't get why this works, I just copied congFunct and tried some things
      helper :
        cong₂ Hom[_][_, yᴰ ] (o ∙ p) (refl ∙ q)
        ≡ cong₂ Hom[_][_, yᴰ ] o refl ∙ cong₂ Hom[_][_, yᴰ ] p q
      helper j i = hcomp (λ k → (λ { (i = i0) → Hom[ e ][ xᴰ , yᴰ ]
                                   ; (i = i1) → cong₂ Hom[_][_, yᴰ ] p q k
                                   ; (j = i0) → cong₂ Hom[_][_, yᴰ ] (compPath-filler o p k) (compPath-filler refl q k) i
                                   }))
                                   (cong₂ Hom[_][_, yᴰ ] o {u = xᴰ} refl i)
      -- I'm not sure why we can't just replace filler with reduced-filler, but
      -- it doesn't type check if I do
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

module _ (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
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
  (ahp : AllHetPairs Cᴰ)
  where
  open Cubical.Categories.Displayed.Reasoning Cᴰ
  open Reasoning₂ Cᴰ
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
        vert≡ : bar.vert ≡ foo.vert
        vert≡ = congS (λ x → ahp x _ _ .vertexᴰ) (C .⋆IdL _)
        hm : C .id ⋆⟨ C ⟩ C .id ≡ C .id ⋆⟨ C ⟩ C .id
        hm = C .⋆IdL (C .id) ∙ sym (C .⋆IdR (C .id))
        one : reind hm (bar.π₁ Cᴰ.⋆ᴰ Cᴰ.idᴰ) ≡ Cᴰ.idᴰ Cᴰ.⋆ᴰ bar.π₁
        one = ≡[]-rectify
          (reind-filler-sym _ _ [ _ ]∙[ _ ]
          Cᴰ.⋆IdRᴰ _ [ _ ]∙[ _ ] symP (Cᴰ.⋆IdLᴰ _))
        simpl : reind (sym (C .⋆Assoc _ _ _) ∙ congS (C._⋆ f) hm) bar.π₂
          ≡
          reind (sym (C .⋆Assoc _ _ _)) bar.π₂
        simpl = reind-rectify
        two : reind (sym (C .⋆Assoc _ _ _)) bar.π₂
          Cᴰ.≡[ C.⋆Assoc _ _ _ ∙ congS (C .id C.⋆_) (sym (C .⋆IdL _)) ]
          Cᴰ.idᴰ Cᴰ.⋆ᴰ bar.π₂
        two = ≡[]-rectify
          (reind-filler-sym _ _ [ _ ]∙[ _ ] symP (Cᴰ.⋆IdLᴰ _))
        lemma :
          {! ((reind hm (bar.π₁ Cᴰ.⋆ᴰ Cᴰ.idᴰ)
          foo.p,
          reind (sym (C .⋆Assoc _ _ _) ∙ congS (C._⋆ f) hm) bar.π₂)
          Cᴰ.⋆ᴰ fᴰ) !}
        lemma = {!!}
        test-η :
          (Cᴰ.idᴰ Cᴰ.⋆ᴰ bar.π₁)
          bar.p,
          reind (sym (C .⋆Assoc _ _ _)) (Cᴰ.idᴰ Cᴰ.⋆ᴰ bar.π₂)
          ≡
          Cᴰ.idᴰ
        test-η = bar.η _
        test-η' : {!!}
        test-η' = {!test-η!}
        goal :
          ((reind hm (bar.π₁ Cᴰ.⋆ᴰ Cᴰ.idᴰ)
          foo.p,
          reind (sym (C .⋆Assoc _ _ _) ∙ congS (C._⋆ f) hm) bar.π₂)
          Cᴰ.⋆ᴰ fᴰ)
          ≡₂[ _ , congS (λ x → ahp x xᴰ cᴰ .vertexᴰ) (C .⋆IdL f) ]
          fᴰ
        --goal = (congP (λ _ → Cᴰ._⋆ᴰ fᴰ) {!!} [ _ ]∙[ _ ]
        --  {! symP (reind₂-contract refl (sym vert≡) {fᴰ = Cᴰ.idᴰ} {hᴰ = fᴰ}) !} [ _ ]∙[ _ ]
        --  reind₂-contract' (Cᴰ.⋆IdLᴰ _))
        --  ◁₂ reind₂-filler-sym (sym (C .⋆IdL _)) (sym vert≡) fᴰ
        goal = ((congP (λ _ a → Cᴰ._⋆ᴰ_ {f = C .id} a fᴰ) {!!}) [ _ ]∙[ _ ]
            symP (reind₂-contract refl (sym vert≡) {fᴰ = Cᴰ.idᴰ} {hᴰ = fᴰ}) [ _ ]∙[ _ ]
            reind₂-contract' (Cᴰ.⋆IdLᴰ _))
          ◁₂ reind₂-filler-sym (sym (C .⋆IdL _)) (sym vert≡) fᴰ
        --goal = (cong₂ (λ x y → (x foo.p, y) Cᴰ.⋆ᴰ fᴰ) one simpl [ _ ]∙[ _ ]
        --  {!!} [ _ ]∙[ _ ] --≡[]-rectify (congP (λ _ x → (_ foo.p, x) Cᴰ.⋆ᴰ fᴰ) (≡[]-rectify {!two!})) [ _ ]∙[ _ ]
        --  {!congP (λ _ a → a Cᴰ.⋆ᴰ fᴰ) (foo.η Cᴰ.idᴰ)!} [ _  ]∙[ _  ] Cᴰ.⋆IdLᴰ {!fᴰ!})
        --  ◁₂ {!!}
    VerticalExponentialsAtSpec .F-seqᴰ = {!!}
    VerticalExponentialsAt : Type _
    VerticalExponentialsAt = UniversalElementᴰ Cᴰ VerticalExponentialsAtSpec (idue Cᴰ c) --(idue c)
