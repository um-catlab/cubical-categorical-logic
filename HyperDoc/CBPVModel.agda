module HyperDoc.CBPVModel where 

open import Cubical.Data.Sigma

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure 

open import Cubical.Categories.Category 
open import Cubical.Categories.Constructions.BinProduct 
open import Cubical.Categories.Functor
open import Cubical.Categories.FunctorComprehension.Base 
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Constructions.BinProduct hiding (π₁ ; π₂)
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Profunctor.General

open import HyperDoc.Lib
open import Cubical.Data.List using (_∷_ ; [])

open Category
open Functor
open NatTrans

record Model (ℓV ℓV' ℓC ℓC' ℓS : Level) : Type (levels (ℓsuc (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ []))) where 
  field 
    V : Category ℓV ℓV' 
    C : Category ℓC ℓC' 
    O : Functor ((V ^op) ×C C) (SET ℓS) 

  O[_,-] : (v : ob V) → Functor C (SET ℓS)
  O[_,-] v = O ∘F rinj _ _ v

  O[-,_] : (c : ob C) → Functor (V ^op) (SET ℓS)
  O[-,_] c = O ∘F linj _ _ c

  O[_,_] : ob V → ob C → Type ℓS
  O[_,_] v c = ⟨ O .F-ob (v , c)⟩

  -- really need to find those bifunctor/profunctor combinators
  -- these are all used to constuct the recursor/eliminator for the free model

  lcomp : ∀{v v' c} → V [ v , v' ] → O[ v' , c ] → O[ v , c ] 
  lcomp f o = O .F-hom (f , (C .id)) o

  rcomp : ∀{v c c'} → C [ c , c' ] → O[ v , c ] → O[ v , c' ] 
  rcomp g o = O .F-hom ((V .id) , g) o

  lrcomp : ∀{v v' c c'} → V [ v' , v ] → C [ c , c' ] → O[ v , c ] → O[ v' , c' ] 
  lrcomp V S M = O .F-hom (V , S) M

  lcompId : ∀{v c}{M : O[ v , c ]} → lcomp (V .id) M ≡ M
  lcompId {v}{c}{M} = funExt⁻ (O .F-id) M

  rcompId : ∀{v c}{M : O[ v , c ]} → rcomp (C .id) M ≡ M
  rcompId {v}{c}{M} = funExt⁻ (O .F-id) M

  rcompSeq : ∀ {v c c' c''}{S : C [ c , c' ]}{S' : C [ c' , c'' ]}{M : O[ v , c ]} → 
    rcomp  S' (rcomp S M) ≡ rcomp (S ⋆⟨ C ⟩ S') M
  rcompSeq {S = S}{S'}{M} =  funExt⁻ (sym (O .F-seq (V .id , S) (V .id , S'))) M ∙ cong₂ (O .F-hom) (cong₂ _,_ (V .⋆IdL _) refl) refl

  lcompSeq : ∀ {v v' v'' c }{W : V [ v , v' ]}{Y : V [ v' , v'' ]}{M : O[ v'' , c ]} → 
    lcomp  W (lcomp Y M) ≡ lcomp (W ⋆⟨ V ⟩ Y) M
  lcompSeq {W = W}{Y}{M}= funExt⁻ (sym (O .F-seq (Y , C .id) (W , C .id))) M ∙ cong₂ (O .F-hom) (cong₂ _,_ refl (C .⋆IdL _)) refl

  lrSeq : ∀ {A A' B B'}{W : V [ A , A' ]}{M : O[ A' , B ]}{S : C [ B , B' ]} → 
    lcomp W (rcomp S M) ≡ rcomp S (lcomp W M)
  lrSeq {W = W}{M}{S} = 
    funExt⁻ (sym (O .F-seq _ _)) M  
    ∙ cong₂ (O .F-hom ) (cong₂ _,_ (V .⋆IdR _ ∙ sym (V .⋆IdL _)) (C .⋆IdR _ ∙ sym (C .⋆IdL _))) refl 
    ∙ funExt⁻ (O .F-seq _ _ ) M



    

module _
  {ℓV ℓV' ℓC ℓC' ℓS : Level}
  (M : Model ℓV ℓV' ℓC ℓC' ℓS ) where 

  open Model M
  open import Cubical.Categories.Bifunctor

  HasV⊤ : Type  (ℓ-max ℓV ℓV')
  HasV⊤ = Representation V (Unit*Psh {ℓ'' = ℓV'})

  HasV+ : Type (ℓ-max (ℓ-max (ℓ-max ℓV ℓC) ℓC') ℓS) 
  HasV+  = (A A' : ob V) → Σ[ A+A' ∈ ob V ] PshIso (O[ A+A' ,-] ∘F from^op^op) ((O[ A ,-] ∘F from^op^op) ×Psh (O[ A' ,-] ∘F from^op^op))

  HasUTy : Type (ℓ-max (ℓ-max (ℓ-max ℓV ℓV') ℓC) ℓS)
  HasUTy = (B : ob C) → Representation V O[-, B ]
  

  --  idk where the bifunctor combinators are 
  UProf : Profunctor C V ℓS
  UProf .F-ob B = O[-, B ]
  UProf .F-hom f .N-ob = λ x₁ → O .F-hom (V .id , f)
  UProf .F-hom f .N-hom g = 
    sym (O .F-seq _ _ ) ∙ 
    cong (λ h → O .F-hom h) (ΣPathP ((V .⋆IdL g ∙ sym (V .⋆IdR g)) , C .⋆IdL f 
    ∙ sym (C .⋆IdR f))) ∙ O .F-seq _ _
  UProf .F-id = makeNatTransPath (funExt λ v → O .F-id)
  UProf .F-seq f g = 
    makeNatTransPath (
      funExt λ v → 
        cong (λ h → O .F-hom (h , (C ⋆ f) g)) (sym (V .⋆IdL (V .id))) 
        ∙ O .F-seq (V .id , f) (V .id , g))
  
  UProf' : Profunctor C V ℓS
  UProf' = CurryBifunctorL (ParFunctorToBifunctor O)
  -- ^^ here they are

  Ucomp :  HasUTy → Functor C V 
  Ucomp uty = FunctorComprehension UProf λ B → reprToUniversalElement V (F-ob UProf B) (uty B)

  HasFTy : Type (ℓ-max (ℓ-max (ℓ-max ℓV ℓC) ℓC') ℓS)
  HasFTy = (A : ob V) → Representation (C ^op) (O[ A ,-] ∘F from^op^op)
  
  FProf : Profunctor (V ^op) (C ^op) ℓS
  FProf .F-ob A = O[ A ,-] ∘F from^op^op
  FProf .F-hom f .N-ob = λ x₁ → O .F-hom (f , C .id)
  FProf .F-hom f .N-hom g = 
    sym (O .F-seq _ _ ) 
    ∙  cong (λ h → O .F-hom h) (ΣPathP ( V .⋆IdR f ∙ sym (V .⋆IdL f) , C .⋆IdR g ∙ sym (C .⋆IdL g) )) 
    ∙ O .F-seq _ _
  FProf .F-id = makeNatTransPath (funExt λ c → O .F-id)
  FProf .F-seq f g = 
    makeNatTransPath 
      (funExt λ c → 
        cong (λ h → O .F-hom ((V ⋆ g) f , h)) (sym (C .⋆IdL (C .id))) ∙ 
        O .F-seq (f , C .id) (g , C .id))

  Fcomp : HasFTy → Functor V C
  Fcomp fty = from^op^op ∘F ((FunctorComprehension FProf λ A → reprToUniversalElement (C ^op) (F-ob FProf A) (fty A)) ^opF) ∘F to^op^op

  HasC× : Type (ℓ-max ℓC ℓC')
  HasC× = (B B' : ob C) → Representation C ((C [-, B ]) ×Psh (C [-, B' ]))

  HasO× : Type _ 
  HasO× = ∀(B B' : ob C) → Σ[ B&B' ∈ ob C ] PshIso O[-, B&B' ] (O[-, B ] ×Psh O[-, B' ])

{-}
  open import Cubical.Categories.Limits.BinProduct.More
  open import Cubical.Categories.Presheaf.Base
  open import Cubical.Categories.Bifunctor

  O' : Functor C (PresheafCategory V _) 
  O' = CurryBifunctorL (ParFunctorToBifunctor O)-}

  TypeStructure : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓV ℓV') ℓC) ℓC') ℓS) 
  TypeStructure = HasV⊤ × HasUTy × HasFTy 


ModelWithTypeStructure : (ℓV ℓV' ℓC ℓC' ℓS : Level) → Type (levels (ℓsuc (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ [])))
ModelWithTypeStructure ℓV ℓV' ℓC ℓC' ℓS  = Σ[ M ∈ Model ℓV ℓV' ℓC ℓC' ℓS  ] TypeStructure M


record ModelMorphism (ℓVS ℓV'S ℓCS ℓC'S ℓSS ℓVT ℓV'T ℓCT ℓC'T ℓST : Level)
  (M : Model ℓVS ℓV'S ℓCS ℓC'S ℓSS)
  (N : Model ℓVT ℓV'T ℓCT ℓC'T ℓST) : Type  (levels (ℓsuc (ℓVS ∷ ℓV'S ∷ ℓCS ∷ ℓC'S ∷ ℓSS ∷ ℓVT ∷ ℓV'T ∷ ℓCT ∷ ℓC'T ∷ ℓST ∷ []))) where
  private 
    module M = Model M 
    module N = Model N
  field 
    FV : Functor M.V N.V 
    FC : Functor M.C N.C 
    -- use PshHom
    FO : PshHom (M.O ∘F from^op^op) (N.O ∘F ((FV ^opF) ×F FC) ∘F from^op^op)


idModelMorphism : {ℓV ℓV' ℓC ℓC' ℓS : Level}(M : Model ℓV ℓV' ℓC ℓC' ℓS) → 
  ModelMorphism _ _ _ _ _ _ _ _ _ _ M M 
idModelMorphism M .ModelMorphism.FV = Id
idModelMorphism M .ModelMorphism.FC = Id
idModelMorphism M .ModelMorphism.FO .PshHom.N-ob = λ c z → z
idModelMorphism M .ModelMorphism.FO .PshHom.N-hom _ _ _ _ = refl

module TypeSyntax 
  {ℓV ℓV' ℓC ℓC' ℓS : Level}
  ((M , V⊤  , UTy , FTy ) : ModelWithTypeStructure ℓV ℓV' ℓC ℓC' ℓS) where 
  
  open Model M
  open PshIso
  open PshHom

  ⊤ : ob V 
  ⊤ = V⊤ .fst 

  tt : {A : ob V} → V [ A , ⊤ ] 
  tt {A} = V⊤ .snd .nIso A .fst _

  ⊤η : {A : ob V}{t :  V [ A , ⊤ ]}  → tt ≡ t
  ⊤η {A} {t} = V⊤ .snd .nIso A .snd .snd t

{-}
  _+_ : ob V → ob V → ob V 
  _+_ A A' = V+ A A' .fst
-}


  U : ob C → ob V 
  U = Ucomp M UTy .F-ob

  thunk : {A : ob V}{B : ob C} → O[ A , B ] → V [ A , U B ] 
  thunk {A}{B} = UTy B .snd .nIso A .fst 

  force : {B : ob C} → O[ U B , B ]
  force {B} = UTy B .snd .trans .N-ob (U B) (V .id)

  force' : {A : ob V}{B : ob C} → V [ A , U B ]  → O[ A , B ]
  force' {A}{B} V = UTy B .snd .trans .N-ob A V

  Uη' : {A : ob V}{B : ob C}{V : V [ A , U B ]} → thunk (force' V) ≡ V
  Uη' {A}{B}{V} = UTy B .snd .nIso A .snd .snd V

  forceSub : {A : ob V}{B : ob C} → (V : V [ A , U B ]) →  
    lcomp V force ≡ force' V
  forceSub {A}{B} V = 
    sym (UTy B .snd .trans  .N-hom _ _ V (M .Model.V .id)) ∙ cong force' ((M .Model.V .⋆IdR _))

  Uη : {A : ob V}{B : ob C}{V : V [ A , U B ]} →  thunk (lcomp V force) ≡ V 
  Uη {A}{B}{V} = cong thunk (forceSub V) ∙ Uη'

  Uβ' : ∀ {A B}{M : O[ A , B ]} → force' (thunk M) ≡ M
  Uβ' {A}{B}{M} = UTy B .snd .nIso A .snd .fst M

  Uβ : ∀{A B}{M : O[ A , B ]} → lcomp (thunk M) force ≡ M
  Uβ {A}{B}{M} = forceSub (thunk M) ∙ Uβ'
{-
i = i0 ⊢ M.lcomp (Syn.thunk (cterm M)) Syn.force
i = i1 ⊢ cterm M
-}

  F : ob V → ob C
  F = Fcomp M FTy .F-ob


  bind : {A : ob V}{B : ob C} →
        O[ A , B ] → C [ F A , B ]
  bind {A}{B} = FTy A .snd .nIso B .fst

  ret : {A : ob V} → 
    O[ A , F A ]
  ret {A} = FTy  A .snd .trans .N-ob (F A) (C .id) 

  ret' : ∀ {A B} → C [ F A , B ] → O[ A , B ]
  ret' {A}{B} S = FTy A .snd .trans .N-ob B S

  {-
  
      Fβ : ∀{A B}{M : A ⊢c B} → M ≡ plug (bind' M) ret
      force : ∀{B} → U B ⊢c B
      Uβ : ∀ {A B} → {M : A ⊢c B} → subC (thunk M) force ≡ M
  -}
  --  UTy B .snd .trans .N-ob A
{-}
  bind : {A : ob V} {B : ob C} →
       C [ F A , B ] → O[ A , B ]
  bind {A} {B} M = FTy A .snd .trans .N-ob B  M
    -- FTy A .snd .nIso B .snd .fst

  Fη : {A : ob V}{B : ob C}{M : C [ F A , B ]} → ret (bind M) ≡ M
  Fη {A}{B}{M}= FTy  A .snd .nIso B .snd .snd  M

  Fβ : {A : ob V}{B : ob C}{M : O[ A , B ]} → bind (ret M) ≡ M 
  Fβ {A}{B}{M} = FTy  A .snd .nIso B .snd .fst  M
  -}

{-

  coprod : HasV+ M 
  coprod  A A' .fst = A + A'
  coprod A A' .snd .trans .N-ob B p = (σ₁ p) , (σ₂ p)
  coprod A A' .snd .trans .N-hom B B' S p = ΣPathP ({!   !} , {!   !})
  coprod A A' .snd .nIso B .fst (M , N) = case M N
  coprod A A' .snd .nIso B .snd .fst (M , N) = ΣPathP (+β₁ , +β₂)
  coprod A A' .snd .nIso B .snd .snd p = +η
  
  σ₁ : {A A' : ob V}{B : ob C} →
     O[ A + A' , B ] → O[ A , B ]
  σ₁ {A} {A'} {B} x = V+ A A' .snd .trans .N-ob B x .fst


  σ₂ : {A A' : ob V}{B : ob C} →
     O[ A + A' , B ] → O[ A' , B ]
  σ₂ {A} {A'} {B} x = V+ A A' .snd .trans .N-ob B x .snd

  case+ :
    {A A' : ob V}{B : ob C} →
    O[ A , B ] →
    O[ A' , B ] →
    O[ A + A' , B ]
  case+ {A} {A'} {B} x y = V+ A A' .snd .nIso B .fst (x , y)

  +η : {A A' : ob V}{B : ob C} →
     {M : O[ A + A' , B ]} → case+ (σ₁ M) (σ₂ M) ≡ M
  +η {A}{A'}{B}{M} = V+ A A' .snd .nIso B .snd .snd M

  +β₁ : {A A' : ob V}{B : ob C} →
      {M :  O[ A , B ]} → 
      {N : O[ A' , B ]} → σ₁ (case+ M N) ≡ M
  +β₁ {A}{A'}{B}{M}{N}  = cong fst (V+ A A' .snd .nIso B .snd .fst (M , N))

  +β₂ : {A A' : ob V}{B : ob C} →
      {M :  O[ A , B ]} → 
      {N : O[ A' , B ]} → σ₂ (case+ M N) ≡ N
  +β₂ {A}{A'}{B}{M}{N}  = cong snd (V+ A A' .snd .nIso B .snd .fst (M , N))
    -- V+ A A' .snd .nIso B .s
-}

{-}
  _&_ : ob C → ob C → ob C
  B & B' = C× B B' .fst
  
  ⟨_,,_⟩ :
    {A B B' : ob C} →
    C [ A , B ] →
    C [ A , B' ] →
    C [ A , B & B' ]
  ⟨ f ,, g ⟩ = C× _ _ .snd .nIso _ .fst (f , g)


  π₁ : {B B' B'' : ob C} → 
    C [ B , B' & B'' ] → 
    C [ B , B' ] 
  π₁ {B}{B'}{B''} M = C× B' B'' .snd .trans .N-ob  B M .fst

  π₂ : {B B' B'' : ob C} → 
    C [ B , B' & B'' ] → 
    C [ B , B'' ] 
  π₂ {B}{B'}{B''} M = C× B' B'' .snd .trans .N-ob  B M .snd

  &β₁ : {B B' B'' : ob C} → 
    {M : C [ B , B' ]} → 
    {N : C [ B , B'' ]} → 
    π₁ (⟨ M ,, N ⟩) ≡ M
  &β₁ {B}{B'}{B''}{M}{N} = cong fst (C× B' B'' .snd .nIso B .snd .fst (M , N))


  &β₂ : {B B' B'' : ob C} → 
    {M : C [ B , B' ]} → 
    {N : C [ B , B'' ]} → 
    π₂ (⟨ M ,, N ⟩) ≡ N
  &β₂ {B}{B'}{B''}{M}{N} = cong snd (C× B' B'' .snd .nIso B .snd .fst (M , N))


  &η : {B B' B'' : ob C} → 
    {M : C [ B , B' & B'' ]} →
    ⟨ π₁ M ,, π₂ M ⟩ ≡ M
  &η {B}{B'}{B''}{M} = C× B' B'' .snd .nIso B .snd .snd M

-}
