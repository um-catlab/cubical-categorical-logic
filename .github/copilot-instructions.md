# Cubical Categorical Logic — Agent Guidelines

## Project Overview

Cubical Agda library formalizing categorical logic for programming language semantics. Extends [agda/cubical](https://github.com/agda/cubical). Four top-level modules: `Cubical/`, `Gluing/`, `Multicategory/`, `Syntax/`.

## Build and Test

```sh
make test          # Full CI check: whitespace + Everything files + type-check
make check         # Generate Everything files, then agda TestEverything.agda
make fix-whitespace # Auto-fix trailing whitespace
make clean         # Remove .agdai and Everything.agda files
```

To type-check a single file: `agda --no-main <file.agda>`

To query normalized goal types for holes: `./scripts/agda-goals.sh <file.agda>`

Performance profiling: `./agda-perf.sh <file.agda>`

## Agda Flags

Set in [cubical-categorical-logic.agda-lib](cubical-categorical-logic.agda-lib):
`--cubical --postfix-projections --guardedness -WnoUnsupportedIndexedMatch`

## Code Style

- **80-column line limit** — enforced by `check-line-lengths.sh`
- **No trailing whitespace** — enforced by `fix-whitespace`
- **File header**: every `.agda` file starts with a `{- ... -}` block comment describing its contents
- **Module path = file path**: `module Cubical.Categories.Bifunctor where` lives at `Cubical/Categories/Bifunctor.agda`

## Agda Conventions

- **Postfix projections**: `C .ob`, `f .ω+Hom.fFin`, not `ob C`
- **`no-eta-equality`** on record declarations (performance)
- **Universe polymorphism**: declare level variables in `private variable` blocks:
  ```agda
  private variable ℓ ℓ' ℓ'' : Level
  ```
- **Record Iso via reflection**: use `defineRecordIsoΣ` from `Cubical.Reflection.RecordEquiv.More` to derive `Iso MyRecord MyRecordΣ`
- **Equality combinators**: define `makeXPath` helpers using `isoFunInjective` + `ΣPathPProp` for records with prop fields
- **`open` pattern**: `open Category`, `open Functor` etc. to bring record fields into scope; use `module C = Category C` for local aliases

## Naming Conventions

- Unicode throughout: `⋆` (composition), `ᴰ` (displayed), `πᵢ`, `Xω`, subscript numerals
- Displayed categories: suffix `ᴰ` — `Categoryᴰ`, `idᴰ`, `_⋆ᴰ_`, `Hom[_][_,_]`
- Mixfix operators: `Hom[_,_]`, `ob[_]`, `F-ob`, `F-hom`, `F-id`, `F-seq`
- Identity/composition: `id`, `_⋆_` (diagrammatic order, `f ⋆ g` = "f then g")

## Working with Goals

For complex categorical constructions (adjunctions, universal elements, presheaf operations), **always normalize goal types** rather than trying to manually unfold definitions. Unnormalized goals often have many layers of abstraction (`RightAdjointProf`, `precomposeF`, `YO`, etc.) that obscure the concrete type. Use `./scripts/agda-goals.sh <file.agda>` or Agda's `C-c C-,` (in Emacs/VS Code) with normalization to see what the goal actually computes to.

## Cubical Library Dependency

This project depends on the [agda/cubical](https://github.com/agda/cubical) library. The exact pinned commit is in `.github/workflows/main.yml` under the `CUBICAL_COMMIT` env var. When you need to look up cubical library API (e.g., field names, function signatures), read the source at that commit rather than guessing.

## Cubical Library API Notes

These are common sources of agent errors:
- `Iso` fields: `.fun`, `.inv`, `.sec` (section), `.ret` (retract) — NOT `rightInv`/`leftInv`
- `Category` fields: `.ob`, `.Hom[_,_]`, `.id`, `._⋆_`, `.⋆IdL`, `.⋆IdR`, `.⋆Assoc`, `.isSetHom`
- `isEmbedding→Inj` needs explicit `{f = ...}` when `f` can't be inferred
- `isProp→PathP` is the key tool for filling in propositional fields in dependent paths

## Import Grouping

1. `Cubical.Foundations.*` (Prelude, HLevels, Isomorphism, Equiv, Function, Structure)
2. `Cubical.Functions.*` (Embedding, etc.)
3. `Cubical.Data.*` (Nat, Sigma, Unit, etc.)
4. `Cubical.Reflection.*`
5. `Cubical.Categories.*` (from cubical library)
6. Project-local imports

## Architecture

- `Cubical/Categories/` — core categorical infrastructure: categories, functors, natural transformations, adjunctions, displayed categories, presheaves, monoidal categories
- `Cubical/Categories/Displayed/` — displayed (fibered) categories, the central organizational pattern
- `Gluing/` — gluing constructions for logical relations and conservativity proofs
- `Syntax/` — syntax of type theories (e.g., untyped lambda calculus)
- `Multicategory/` — planar multicategories
- `Everything.agda` files are **auto-generated** by `Everythings.hs` — never edit manually

## Protected Files

Do not modify files in `scripts/` without explicit user approval. These are stable utility scripts.
