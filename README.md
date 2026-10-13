# Logical Relations on Display — Agda artifact

The Cubical Agda development accompanying *Logical Relations on
Display* (Steven Schaefer, Johnson He, Max S. New, POPL 2027).

It is a snapshot of
[um-catlab/cubical-categorical-logic](https://github.com/um-catlab/cubical-categorical-logic)
restricted to the modules the paper uses.

## Project Layout

The code is split into two Agda libraries:

- `safe/` — checked with `--safe`. `safe/Cubical/` extends
  [agda/cubical](https://github.com/agda/cubical) and reuses its
  `Cubical.*` namespace. `safe/Gluing/` contains the applications.
- `unsafe/` — the synthetic step-indexed development of §5.4, which
  needs `--guarded --rewriting`.

Definitions marked *(agda/cubical)* come from the upstream library at
the pinned commit.

### Universal elements

Every universal property in the library is stated as a universal
element of a presheaf: an object together with an element of the
presheaf at that object such that the induced map out of the
representable is an isomorphism.

| Notion | Agda | Location |
|---|---|---|
| Universal element | `UniversalElement` | [`Cubical/Categories/Presheaf/Representable.agda`](https://github.com/agda/cubical/blob/92166033326aa59800a580b428125f3c654b5e45/Cubical/Categories/Presheaf/Representable.agda#L84) *(agda/cubical)* |
| `yoRec`, conversions to and from representations, notation | | [`safe/Cubical/Categories/Presheaf/Representable/More.agda`](safe/Cubical/Categories/Presheaf/Representable/More.agda) |
| Terminal and initial objects | `Terminal'`, `Initial'` | [`safe/Cubical/Categories/Limits/Terminal/More.agda`](safe/Cubical/Categories/Limits/Terminal/More.agda#L36) |
| Binary products and coproducts | `BinProduct`, `BinCoProduct` | [`safe/Cubical/Categories/Limits/BinProduct/More.agda`](safe/Cubical/Categories/Limits/BinProduct/More.agda#L56) |
| Exponentials | `Exponential` | [`safe/Cubical/Categories/Exponentials/Small.agda`](safe/Cubical/Categories/Exponentials/Small.agda#L34) |
| Cartesian category | `CartesianCategory` | [`safe/Cubical/Categories/Limits/Cartesian/Base.agda`](safe/Cubical/Categories/Limits/Cartesian/Base.agda#L18) |
| Cartesian closed category | `CartesianClosedCategory` | [`safe/Cubical/Categories/Limits/CartesianClosed/Base.agda`](safe/Cubical/Categories/Limits/CartesianClosed/Base.agda#L11) |
| Bicartesian closed category | `BiCartesianClosedCategory` | [`safe/Cubical/Categories/Limits/BiCartesianClosed/Base.agda`](safe/Cubical/Categories/Limits/BiCartesianClosed/Base.agda#L19) |
| Displayed and vertical universal elements | `UniversalElementᴰ`, `Representableⱽ`, `UniversalElementⱽ'` | [`safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Representable.agda`](safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Representable.agda) |
| Displayed and vertical (bi)cartesian closed structure | | [`safe/Cubical/Categories/Displayed/Limits`](safe/Cubical/Categories/Displayed/Limits) |

### Presheaves and their morphisms

`Presheaf C ℓ` is a functor `C ^op → SET ℓ`
([`Cubical/Categories/Presheaf/Base.agda`](https://github.com/agda/cubical/blob/92166033326aa59800a580b428125f3c654b5e45/Cubical/Categories/Presheaf/Base.agda#L17) *(agda/cubical)*).
There are four notions of morphism of presheaves:

| Agda | Location | Description |
|---|---|---|
| `NatTrans` | *(agda/cubical)* | Natural transformations between functors, so both presheaves live at the same universe level. |
| `PshHom` | [`safe/Cubical/Categories/Presheaf/Morphism/Alt.agda`](safe/Cubical/Categories/Presheaf/Morphism/Alt.agda#L87) | The same data as a `NatTrans`, between presheaves at *different* levels. |
| `PshHomStrict` | [`safe/Cubical/Categories/Presheaf/StrictHom/Base.agda`](safe/Cubical/Categories/Presheaf/StrictHom/Base.agda#L82) | Naturality takes the composite as an extra argument (`f ⋆ p' ≡ p → f ⋆ N-ob c' p' ≡ N-ob c p`), so the category laws for `PRESHEAF` hold by `refl`. Isomorphic to `PshHom` (`PshHom≅PshHomStrict`); see §6. |
| `PshHomEq` | [`safe/Cubical/Categories/Presheaf/Morphism/Alt.agda`](safe/Cubical/Categories/Presheaf/Morphism/Alt.agda#L103) | The same shape, with naturality in the inductive equality `Eq`. |

### Displayed presheaves

Let `Cᴰ` be a displayed category over `C` and `P` a presheaf on `C`.
A displayed presheaf on `Cᴰ` over `P` is defined in
[`safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Base.agda`](safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Base.agda#L203) as an ordinary
presheaf on the category `Cᴰ / P`. A vertical presheaf
`Presheafⱽ x Cᴰ` is a displayed presheaf over the representable
`C [-, x ]`.

*Uncurried* in the module names refers to this definition. The
alternative, *curried* definition is a displayed functor
`Functorᴰ P (Cᴰ ^opᴰ) (SETᴰ _ _)`, in
[`safe/Cubical/Categories/Displayed/Presheaf/Base.agda`](safe/Cubical/Categories/Displayed/Presheaf/Base.agda#L38).
The two definitions are equivalent. Older parts of the library use
the curried one; most of the development uses the uncurried one.

### `Eq`-based universal properties

[`safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Eq`](safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Eq)
is a second copy of the displayed-presheaf framework in which the
equation `f ⋆ p ≡ q` in `Cᴰ / P` uses the inductive equality type `Eq`
instead of the cubical `Path` type. Transport along `Eq`'s `refl`
reduces, whereas transport along a `Path` `refl` is a stuck term, and
these stuck terms made some proofs too slow to type-check (§6). The
universal properties of the concrete displayed categories are
therefore proved in the `Eq` version:

- `SETᴰ` — [`safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Eq/Sets.agda`](safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Eq/Sets.agda), assembled in
  [`safe/Cubical/Categories/Displayed/Instances/Sets/Properties.agda`](safe/Cubical/Categories/Displayed/Instances/Sets/Properties.agda#L204).
- `PRESHEAFᴰ` — [`safe/Cubical/Categories/Displayed/Instances/Presheaf/Eq`](safe/Cubical/Categories/Displayed/Instances/Presheaf/Eq).

[`safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Eq/Conversion`](safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Eq/Conversion)
converts them to the `Path`-based framework, which the rest of the
library uses.

### The gluing library

Each file in `safe/Gluing/` proves a metatheorem about a free
category in the same way: build a displayed category over the syntax
that expresses the property (usually by reindexing `SETᴰ` or
`PRESHEAFᴰ` along a functor out of the syntax), get its displayed
structure from vertical structure, interpret the generators, and apply
the eliminator to obtain a section. The theorem is read off from the
section.

- Canonicity glues along the global-sections functor `Hom[ ⊤ , - ]`
  into `SETᴰ` (`BiCartesianClosedCategory/BoolNatCanonicity`, and the
  smaller fragments in `Category/`,
  `CartesianCategory/`, `CartesianClosedCategory/`, `Lambda/`).
- Representation independence (added in revisions after discussion with Shepherd; not in original submission) uses binary logical relations, a section
  over a pair of interpretations (`BiCartesianClosedCategory/BinaryLogicalRelation.agda`,
  `IdentityExtension.agda`, `FlipperParametricity.agda`,
  `StackParametricity.agda`).
- Conservativity reindexes `PRESHEAFᴰ` along the nerve
  (`*/Conservativity/`).
- Our analytic proof of step-indexed canonicity uses `ω`-indexed sets
  (`Category/GuardedFixedPoint.agda`); the synthetic version is in
  `unsafe/Guarded/Gluing/Canonicity.agda`.

## By Section

### §2 Programming Languages as Free Categories

| Paper | Agda | Location |
|---|---|---|
| The free λ-calculus | | [`safe/Cubical/Categories/Instances/Free/Lambda`](safe/Cubical/Categories/Instances/Free/Lambda) |
| Canonicity for the λ-calculus | | [`safe/Gluing/Lambda/BoolNatCanonicity`](safe/Gluing/Lambda/BoolNatCanonicity) |
| Definition 2.3 | `Categoryᴰ` | [`Cubical/Categories/Displayed/Base.agda`](https://github.com/agda/cubical/blob/92166033326aa59800a580b428125f3c654b5e45/Cubical/Categories/Displayed/Base.agda#L20) *(agda/cubical)* |
| Definition 2.4 | `SETᴰ` | [`safe/Cubical/Categories/Displayed/Instances/Sets/Base.agda`](safe/Cubical/Categories/Displayed/Instances/Sets/Base.agda#L31) |
| Definition 2.5 | `GlobalSection` | [`Cubical/Categories/Displayed/Section/Base.agda`](https://github.com/agda/cubical/blob/92166033326aa59800a580b428125f3c654b5e45/Cubical/Categories/Displayed/Section/Base.agda#L152) *(agda/cubical)* |
| Theorem 2.7 | `elimBiCartesianClosed` | [`safe/Cubical/Categories/Instances/Free/BiCartesianClosedCategory/Forded.agda`](safe/Cubical/Categories/Instances/Free/BiCartesianClosedCategory/Forded.agda#L258) |
| Theorem 2.8 | `canonicity-bool`, `canonicity-nat` | [`safe/Gluing/BiCartesianClosedCategory/BoolNatCanonicity/Forded.agda`](safe/Gluing/BiCartesianClosedCategory/BoolNatCanonicity/Forded.agda#L124-L128) |

### §3 Logical Relations via Displayed Category Theory

| Paper | Agda | Location |
|---|---|---|
| Definition 3.1 | `∫C` | [`Cubical/Categories/Instances/TotalCategory/Base.agda`](https://github.com/agda/cubical/blob/92166033326aa59800a580b428125f3c654b5e45/Cubical/Categories/Instances/TotalCategory/Base.agda#L29) *(agda/cubical)* |
| Definition 3.2 | `reindex` | [`Cubical/Categories/Displayed/Instances/Reindex/Base.agda`](https://github.com/agda/cubical/blob/92166033326aa59800a580b428125f3c654b5e45/Cubical/Categories/Displayed/Instances/Reindex/Base.agda#L90) *(agda/cubical)* |
| Definition 3.5 | `Element` | [`safe/Cubical/Categories/Displayed/Instances/Graph/Presheaf.agda`](safe/Cubical/Categories/Displayed/Instances/Graph/Presheaf.agda#L61) |
| Definition 3.6 | `_/_` | [`safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Base.agda`](safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Base.agda#L95) |
| Definition 3.7 | `Presheafᴰ` | [`safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Base.agda`](safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Base.agda#L203) |
| Definition 3.8 | `_[-][-,_]` | [`safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Representable.agda`](safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Representable.agda#L64) |
| Definition 3.9 | `reindPshᴰNatTrans` | [`safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Base.agda`](safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Base.agda#L314) |
| Definition 3.10 | `PshHomᴰ` | [`safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Base.agda`](safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Base.agda#L466) |
| Definition 3.12 | `UniversalElementᴰ` | [`safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Representable.agda`](safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Representable.agda#L168) |
| Definition 3.13 | `Presheafⱽ` | [`safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Base.agda`](safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Base.agda#L212) |
| Definition 3.14 | `UniversalElementⱽ'` | [`safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Representable.agda`](safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Representable.agda#L141) |
| Definition 3.16 | `Terminalsⱽ` | [`safe/Cubical/Categories/Displayed/Presheaf/Uncurried/UniversalProperties.agda`](safe/Cubical/Categories/Displayed/Presheaf/Uncurried/UniversalProperties.agda#L63) |
| Definition 3.17 | `BinProductⱽ` | [`safe/Cubical/Categories/Displayed/Presheaf/Uncurried/UniversalProperties.agda`](safe/Cubical/Categories/Displayed/Presheaf/Uncurried/UniversalProperties.agda#L81) |
| Definition 3.18 | `BinProductsⱽ` | [`safe/Cubical/Categories/Displayed/Presheaf/Uncurried/UniversalProperties.agda`](safe/Cubical/Categories/Displayed/Presheaf/Uncurried/UniversalProperties.agda#L87) |
| Theorem 3.20 | `isFibrationSETᴰ` | [`safe/Cubical/Categories/Displayed/Instances/Sets/Properties.agda`](safe/Cubical/Categories/Displayed/Instances/Sets/Properties.agda#L93) |
| Definition 3.21 | `Exponentialsⱽ` | [`safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Constructions/Exponential.agda`](safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Constructions/Exponential.agda#L379) |
| Definition 3.22 | `UniversalQuantifiers` | [`safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Constructions/UniversalQuantifier.agda`](safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Constructions/UniversalQuantifier.agda#L189) |
| Definition 3.23 | `CartesianClosedCategoryⱽ` | [`safe/Cubical/Categories/Displayed/Limits/CartesianClosedV.agda`](safe/Cubical/Categories/Displayed/Limits/CartesianClosedV.agda#L38) |
| Theorem 3.24 | `EqSETᴰCCCⱽ` | [`safe/Cubical/Categories/Displayed/Instances/Sets/Properties.agda`](safe/Cubical/Categories/Displayed/Instances/Sets/Properties.agda#L204) |
| Theorem 3.26 | `CartesianCategoryⱽ→CartesianCategoryᴰ` | [`safe/Cubical/Categories/Displayed/Limits/CartesianV'.agda`](safe/Cubical/Categories/Displayed/Limits/CartesianV'.agda#L53) |
| Theorem 3.27 | `CartesianClosedCategoryⱽ→CartesianClosedCategoryᴰ` | [`safe/Cubical/Categories/Displayed/Limits/CartesianClosedV.agda`](safe/Cubical/Categories/Displayed/Limits/CartesianClosedV.agda#L66) |
| Corollary 3.28 | `EqSETᴰBCCCⱽ` | [`safe/Cubical/Categories/Displayed/Instances/Sets/Properties.agda`](safe/Cubical/Categories/Displayed/Instances/Sets/Properties.agda#L209) |

### §4 Concrete Semantic Domains

| Paper | Agda | Location |
|---|---|---|
| Definition 4.1 | `Fam` | [`safe/Cubical/Categories/Displayed/Instances/Family/Base.agda`](safe/Cubical/Categories/Displayed/Instances/Family/Base.agda#L20) |
| Definition 4.2 | `PRESHEAFᴰ` | [`safe/Cubical/Categories/Displayed/Instances/Presheaf/Eq/Base.agda`](safe/Cubical/Categories/Displayed/Instances/Presheaf/Eq/Base.agda#L273) |
| Theorem 4.3 | `CCCⱽPSHᴰ` | [`safe/Cubical/Categories/Displayed/Instances/Presheaf/Eq/CartesianClosed.agda`](safe/Cubical/Categories/Displayed/Instances/Presheaf/Eq/CartesianClosed.agda#L155) |
| Theorem 4.4 | `P⇒Large-UMP` | [`safe/Cubical/Categories/Presheaf/StrictHom/RightAdjoint.agda`](safe/Cubical/Categories/Presheaf/StrictHom/RightAdjoint.agda#L107) |
| Definition 4.6 | `Iso` | [`safe/Cubical/Categories/Displayed/Instances/Arrow/Base.agda`](safe/Cubical/Categories/Displayed/Instances/Arrow/Base.agda#L61) |
| Definition 4.7 | `IsoFiber` | [`safe/Cubical/Categories/Displayed/Instances/IsoFiber/Base.agda`](safe/Cubical/Categories/Displayed/Instances/IsoFiber/Base.agda#L43) |
| Theorem 4.8 | `IsoFiberReflection` | [`safe/Cubical/Categories/Displayed/Instances/IsoFiber/Base.agda`](safe/Cubical/Categories/Displayed/Instances/IsoFiber/Base.agda#L47) |
| Definition 4.9 | `IsoComma` | [`safe/Cubical/Categories/Displayed/Instances/Arrow/Monoidal.agda`](safe/Cubical/Categories/Displayed/Instances/Arrow/Monoidal.agda#L86) |
| Theorem 4.10 | `IsoReflection` | [`safe/Cubical/Categories/Displayed/Instances/Arrow/Base.agda`](safe/Cubical/Categories/Displayed/Instances/Arrow/Base.agda#L85) |

### §5 Applications

| Paper | Agda | Location |
|---|---|---|
| Theorem 5.1 (added in revisions after discussion with Shepherd; not in original submission) | `identityExtension` | [`safe/Gluing/BiCartesianClosedCategory/IdentityExtension.agda`](safe/Gluing/BiCartesianClosedCategory/IdentityExtension.agda#L85) |
| Theorem 5.2 (added in revisions after discussion with Shepherd; not in original submission) | `flipper-representation-independence` | [`safe/Gluing/BiCartesianClosedCategory/FlipperParametricity.agda`](safe/Gluing/BiCartesianClosedCategory/FlipperParametricity.agda#L149) |
| Stack representation independence (§5.1) (added in revisions after discussion with Shepherd; not in original submission) | `stack-representation-independence` | [`safe/Gluing/BiCartesianClosedCategory/StackParametricity.agda`](safe/Gluing/BiCartesianClosedCategory/StackParametricity.agda#L181) |
| Theorem 5.3 | `⊆-FullyFaithful` | [`safe/Gluing/CartesianClosedCategory/Conservativity/OverCartesianCategories/Forded.agda`](safe/Gluing/CartesianClosedCategory/Conservativity/OverCartesianCategories/Forded.agda#L238) |
| Lemma 5.5 | `hasPropHomsIsoRetract` | [`safe/Cubical/Categories/HLevels.agda`](safe/Cubical/Categories/HLevels.agda#L52) |
| Theorem 5.6 | `coherence` | [`safe/Cubical/Categories/Instances/Free/Monoidal/Coherence.agda`](safe/Cubical/Categories/Instances/Free/Monoidal/Coherence.agda#L29) |
| Theorem 5.7 | `GuardedCanonicity` | [`safe/Gluing/Category/GuardedFixedPoint.agda`](safe/Gluing/Category/GuardedFixedPoint.agda#L257) |
| Synthetic step-indexed canonicity (§5.4) | `GuardedCanonicity` | [`unsafe/Guarded/Gluing/Canonicity.agda`](unsafe/Guarded/Gluing/Canonicity.agda#L210) |

### §6 Implementation in Intensional Type Theory

| Paper | Agda | Location |
|---|---|---|
| Frobenius reciprocity (§6.5) | `FrobeniusReciprocity` | [`safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Constructions.agda`](safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Constructions.agda#L338) |
| Beck–Chevalley (§6.5) | `BeckChevalley` | [`safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Constructions.agda`](safe/Cubical/Categories/Displayed/Presheaf/Uncurried/Constructions.agda#L410) |

### §7 Related and Future Work

| Paper | Agda | Location |
|---|---|---|
| Conservativity of the free cartesian category over the free category | `⊆-FullyFaithful` | [`safe/Gluing/CartesianCategory/Conservativity/OverCategories/Forded.agda`](safe/Gluing/CartesianCategory/Conservativity/OverCategories/Forded.agda#L140) |
| Conservativity of the free cartesian closed category over the free category | `⊆-FullyFaithful` | [`safe/Gluing/CartesianClosedCategory/Conservativity/OverCategories/Forded.agda`](safe/Gluing/CartesianClosedCategory/Conservativity/OverCategories/Forded.agda#L160) |

## Other applications

Examples in `safe/Gluing/` that the paper does not discuss:

| Result | Location |
|---|---|
| Canonicity for the free category | [`safe/Gluing/Category/BoolNatCanonicity.agda`](safe/Gluing/Category/BoolNatCanonicity.agda) |
| Canonicity for the free cartesian category | [`safe/Gluing/CartesianCategory`](safe/Gluing/CartesianCategory) |
| Canonicity for the free cartesian closed category | [`safe/Gluing/CartesianClosedCategory/BoolNatCanonicity`](safe/Gluing/CartesianClosedCategory/BoolNatCanonicity) |
| Normal forms for the free category | [`safe/Gluing/Category.agda`](safe/Gluing/Category.agda) |

## Building

All dependencies are pinned:

- Agda at commit
  [`295c60c`](https://github.com/agda/agda/commit/295c60c79cd49e880b9f07add98462f1b82d26f2)
  of the development branch (it reports version 2.9.0, which is not a
  Hackage release), built with GHC 9.10.3.
- agda/cubical at commit
  [`92166033`](https://github.com/agda/cubical/commit/92166033326aa59800a580b428125f3c654b5e45).

The Nix flake pins both in `flake.lock`. Once Agda is installed, type-checking
the whole development, including the parts of agda/cubical it uses,
takes about 5 minutes on an M1 Pro MacBook and needs about 3 GB of
memory.

### With Nix

From the root of this repository, run

   ```sh
   nix build
   ```

This type-checks `safe/` and then `unsafe/`. The first run also
builds the pinned Agda from source, because that commit is not in
the public Nix binary cache; this can take 30–60 minutes.

For interactive use, `nix develop` opens a shell with the pinned
`agda` and agda/cubical already registered. In that shell,
`make check` type-checks both libraries.

### Without Nix

1. Install GHC 9.10.3 and cabal, for example with
   [GHCup](https://www.haskell.org/ghcup/):

   ```sh
   ghcup install ghc 9.10.3
   ghcup set ghc 9.10.3
   ghcup install cabal
   ```

2. Build and install Agda from the pinned commit:

   ```sh
   git clone https://github.com/agda/agda.git
   cd agda
   git checkout 295c60c79cd49e880b9f07add98462f1b82d26f2
   cabal update
   cabal install --overwrite-policy=always
   agda --version    # Agda version 2.9.0
   ```

   This compiles Agda and its Haskell dependencies, which can take 30–60
   minutes.

3. Download agda/cubical at the pinned commit:

   ```sh
   git clone https://github.com/agda/cubical.git
   cd cubical
   git checkout 92166033326aa59800a580b428125f3c654b5e45
   ```

4. Register agda/cubical with Agda by adding the absolute path of its
   library file to `~/.agda/libraries` (create the file if needed):

   ```sh
   mkdir -p ~/.agda
   echo "$PWD/cubical.agda-lib" >> ~/.agda/libraries
   ```

   To avoid changing your global Agda configuration, write the
   `libraries` file into a fresh directory instead and point the
   `AGDA_DIR` environment variable at it:

   ```sh
   mkdir -p ~/agda-artifact
   echo "$PWD/cubical.agda-lib" > ~/agda-artifact/libraries
   export AGDA_DIR=~/agda-artifact
   ```

   The two libraries in this repository do not need to be registered.
   `safe/` depends only on agda/cubical, and `unsafe/` includes `safe/`
   in its `.agda-lib` file.

5. From the root of this repository, run

   ```sh
   make check
   ```

   which runs `agda --build-library` in `safe/` and then in `unsafe/`.

### Checking individual files

Agda finds a library's `.agda-lib` file by searching upward from the
current directory, so run it from inside either `safe/` or `unsafe/`.

```sh
cd safe
agda Gluing/BiCartesianClosedCategory/BoolNatCanonicity/Forded.agda
cd ../unsafe
agda Guarded/Gluing/Canonicity.agda
```
