{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category

module Cubical.Categories.Enriched.Enrichment.Instances.Presheaf.StrictHom.Product
  {ℓ ℓ' : Level} (A : Category ℓ ℓ') (ℓS : Level) where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.StrictHom.CartesianClosed
open import Cubical.Categories.Presheaf.Constructions.BinProduct using (_×Psh_)
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Enriched.Enrichment.Base
import Cubical.Categories.Enriched.Enrichment.Functor.Base as FE

open PshHomStrict
open PshMon A ℓS using (𝓟Mon ; 𝓟 ; 𝟙)
open Enrichment

private
  variable
    ℓC ℓC' ℓD ℓD' ℓW ℓW' : Level

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (ℰC : Enrichment C 𝓟Mon) (ℰD : Enrichment D 𝓟Mon) where
  private
    module ℰC = Enrichment ℰC
    module ℰD = Enrichment ℰD

    pt : ∀ {P Q : Category.ob 𝓟} {f g : 𝓟 [ P , Q ]} → f ≡ g → ∀ c x → f .N-ob c x ≡ g .N-ob c x
    pt p c x i = p i .N-ob c x

  _×ᴱ_ : Enrichment (C ×C D) 𝓟Mon
  _×ᴱ_ .VE[_,_] (a , b) (a' , b') = ℰC.VE[ a , a' ] ×Psh ℰD.VE[ b , b' ]
  _×ᴱ_ .id = ×PshIntroStrict ℰC.id ℰD.id
  _×ᴱ_ .seq _ _ _ .N-ob c ((f , g) , (f' , g')) =
    ℰC.seq _ _ _ .N-ob c (f , f') , ℰD.seq _ _ _ .N-ob c (g , g')
  _×ᴱ_ .seq _ _ _ .N-hom c c' k ((f , g) , (f' , g')) ((h , j) , (h' , j')) e = ΣPathP
    ( ℰC.seq _ _ _ .N-hom c c' k (f , f') (h , h') (λ i → e i .fst .fst , e i .snd .fst)
    , ℰD.seq _ _ _ .N-hom c c' k (g , g') (j , j') (λ i → e i .fst .snd , e i .snd .snd))
  _×ᴱ_ .⇄-agree .Iso.fun (f , g) = ×PshIntroStrict ℰC.⌜ f ⌝ ℰD.⌜ g ⌝
  _×ᴱ_ .⇄-agree .Iso.inv h =
    ℰC.⌞ h ⋆PshHomStrict π₁ _ _ ⌟ , ℰD.⌞ h ⋆PshHomStrict π₂ _ _ ⌟
  _×ᴱ_ .⇄-agree .Iso.sec h = makePshHomStrictPath (funExt λ c → funExt λ x → ΣPathP
    ( pt (ℰC.⇄-agree← (h ⋆PshHomStrict π₁ _ _)) c x
    , pt (ℰD.⇄-agree← (h ⋆PshHomStrict π₂ _ _)) c x))
  _×ᴱ_ .⇄-agree .Iso.ret (f , g) = ΣPathP
    ( cong ℰC.⌞_⌟ (makePshHomStrictPath refl) ∙ ℰC.⇄-agree→ f
    , cong ℰD.⌞_⌟ (makePshHomStrictPath refl) ∙ ℰD.⇄-agree→ g)
  _×ᴱ_ .⋆IdL (a , b) (a' , b') = makePshHomStrictPath (funExt λ c → funExt λ (t , (f , g)) →
    ΣPathP (pt (ℰC.⋆IdL a a') c (t , f) , pt (ℰD.⋆IdL b b') c (t , g)))
  _×ᴱ_ .⋆IdR (a , b) (a' , b') = makePshHomStrictPath (funExt λ c → funExt λ ((f , g) , t) →
    ΣPathP (pt (ℰC.⋆IdR a a') c (f , t) , pt (ℰD.⋆IdR b b') c (g , t)))
  _×ᴱ_ .⋆Assoc (a , b) (a' , b') (a'' , b'') (a''' , b''') =
    makePshHomStrictPath (funExt λ c → funExt λ ((f , g) , ((f' , g') , (f'' , g''))) →
      ΣPathP ( pt (ℰC.⋆Assoc a a' a'' a''') c (f , (f' , f''))
             , pt (ℰD.⋆Assoc b b' b'' b''') c (g , (g' , g''))))
  _×ᴱ_ .⌜id⌝ = cong₂ ×PshIntroStrict ℰC.⌜id⌝ ℰD.⌜id⌝
  _×ᴱ_ .⌜⋆⌝ (f , g) (f' , g') = makePshHomStrictPath (funExt λ c → funExt λ t →
    ΣPathP (pt (ℰC.⌜⋆⌝ f f') c t , pt (ℰD.⌜⋆⌝ g g') c t))

module _ {W : Category ℓW ℓW'} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {ℰW : Enrichment W 𝓟Mon} {ℰC : Enrichment C 𝓟Mon} {ℰD : Enrichment D 𝓟Mon}
  {f : Category.ob W → Category.ob C} {g : Category.ob W → Category.ob D}
  (F : FE.EnrichmentFor 𝓟Mon ℰW ℰC f) (G : FE.EnrichmentFor 𝓟Mon ℰW ℰD g) where
  private
    module F = FE.EnrichmentFor F
    module G = FE.EnrichmentFor G
    pt : ∀ {P Q : Category.ob 𝓟} {α β : 𝓟 [ P , Q ]} → α ≡ β → ∀ c x → α .N-ob c x ≡ β .N-ob c x
    pt p c x i = p i .N-ob c x

  _,EnrFor_ : FE.EnrichmentFor 𝓟Mon ℰW (ℰC ×ᴱ ℰD) (λ x → f x , g x)
  _,EnrFor_ .FE.EnrichmentFor.f[_,_] x y = ×PshIntroStrict F.f[ x , y ] G.f[ x , y ]
  _,EnrFor_ .FE.EnrichmentFor.fid = makePshHomStrictPath (funExt λ c → funExt λ t →
    ΣPathP (pt F.fid c t , pt G.fid c t))
  _,EnrFor_ .FE.EnrichmentFor.f-seq = makePshHomStrictPath (funExt λ c → funExt λ x →
    ΣPathP (pt F.f-seq c x , pt G.f-seq c x))

module _ {C : Category ℓC ℓC'} (ℰC : Enrichment C 𝓟Mon) where
  IdEnr : FE.Enrichment 𝓟Mon ℰC ℰC Id
  IdEnr .FE.Enrichment.F[_,_] x y = idPshHomStrict
  IdEnr .FE.Enrichment.F-id = makePshHomStrictPath refl
  IdEnr .FE.Enrichment.F-seq = makePshHomStrictPath refl
  IdEnr .FE.Enrichment.agree f = makePshHomStrictPath refl

module _ {W : Category ℓW ℓW'} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {ℰW : Enrichment W 𝓟Mon} {ℰC : Enrichment C 𝓟Mon} {ℰD : Enrichment D 𝓟Mon}
  {F : Functor W C} {G : Functor W D}
  (F̃ : FE.Enrichment 𝓟Mon ℰW ℰC F) (G̃ : FE.Enrichment 𝓟Mon ℰW ℰD G) where
  private
    pt : ∀ {P Q : Category.ob 𝓟} {α β : 𝓟 [ P , Q ]} → α ≡ β → ∀ c x → α .N-ob c x ≡ β .N-ob c x
    pt p c x i = p i .N-ob c x

  _,Enr_ : FE.Enrichment 𝓟Mon ℰW (ℰC ×ᴱ ℰD) (F ,F G)
  _,Enr_ .FE.Enrichment.F[_,_] x y = ×PshIntroStrict (F̃ .FE.Enrichment.F[_,_] x y) (G̃ .FE.Enrichment.F[_,_] x y)
  _,Enr_ .FE.Enrichment.F-id = makePshHomStrictPath (funExt λ c → funExt λ t →
    ΣPathP (pt (F̃ .FE.Enrichment.F-id) c t , pt (G̃ .FE.Enrichment.F-id) c t))
  _,Enr_ .FE.Enrichment.F-seq = makePshHomStrictPath (funExt λ c → funExt λ x →
    ΣPathP (pt (F̃ .FE.Enrichment.F-seq) c x , pt (G̃ .FE.Enrichment.F-seq) c x))
  _,Enr_ .FE.Enrichment.agree f = makePshHomStrictPath (funExt λ c → funExt λ t →
    ΣPathP (pt (F̃ .FE.Enrichment.agree f) c t , pt (G̃ .FE.Enrichment.agree f) c t))
