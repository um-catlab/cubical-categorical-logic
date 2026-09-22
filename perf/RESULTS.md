# Performance results

What this branch is, what it cost to get here, and how to re-measure it.

All figures are **GHC bytes allocated**, read from the RTS's own `-s` report on a
from-scratch `agda --build-library`. Allocation is deterministic to eight
significant figures within a worktree and immune to machine load, which is why
differences of a few hundred MB are reported as real. Wall time is given
alongside but is not a result: on the reference machine it varied by up to 17%
between a quiet and a contended run of identical source.

Reference machine: 12 cores, 31 GiB, `-j1 +RTS -N1 -A1G -H4G -M24G -RTS`,
one shared pre-built cubical, every build serialised under an exclusive lock.
Pins: `agda/cubical` @ 92166033, `1lab/agda-cubical` @ 383f7e46.

## The headline

    tool     tree                 alloc GB   wall s   maxrss MiB   modules
    agda     baseline (82334ffb)     847.8    301.5         5190       469
    agda     this work               547.4    189.4         4608       476
    mikan    baseline                330.8    130.9         4892       469
    mikan    this work               266.1     98.3         4318       476

    agda   1.55x allocation, 1.59x wall, -11% peak memory
    mikan  1.24x allocation, 1.33x wall

Tool to tool on the baseline: 2.56x allocation. On this work: 2.06x.
Corner to corner -- agda on the baseline against mikan on this work -- 3.19x.

## Read the agda figure carefully

This branch proves strictly more than the baseline: it carries the displayed-sets
exponentials and quantifiers, two path-based canonicity clients, and three
Eq-free displayed-presheaf modules. Those cost allocation.

    baseline                                847.8 GB
    performance work only                   514.9        1.65x
    + the new mathematics                   547.4        1.55x

**1.65x is the like-for-like speedup.** The new constructions give back 32.5 GB
of it. Both figures are honest; they answer different questions, and neither
should be quoted alone.

## Where the saving came from

Twelve edits, each measured by reverting it from the finished tree and rebuilding
the whole library, so every figure is that edit's cost in the context it ships in.

    technique                                     GB saved   GB/100 lines
    rectifyOut fusion (333 sites)                   146.21           27.8
    Presented root-cause fix                         82.53          168.4
    LocallySmall notation trimming                   50.75           33.2
    argument pinning                                 21.49           18.1
    copatterns -> record expression                  10.01           18.2
    ∫-form sharing                                    ~9.5            1.4
    root-cause split (Pullback/Alt)                   7.40           41.1
    --lossy-unification (one pragma)                  4.99          499.0
    notation trimming (second pass)                   3.46           15.7
    shared elaboration                                1.71            1.0
    UniversalQuantifiers as a record                  1.07            5.6
    named projections                                 0.03            0.4

Individual contributions sum to within 0.14%-2.2% of the measured endpoint gap,
depending on the group, so these defects are file-local and do not overlap.

Two readings dominate. **The biggest lever is also the least clever**: rewriting
`rectify (≡out X)` to `rectifyOut X` at 333 sites, justified by the observation
that `rectify`'s implicit can only ever be `fst (PathPΣ X)`, so `X` was being
stored twice. Nothing about it needed a diagnosis. And **what pays is stopping a
type from being re-elaborated** -- a pragma, an opaque split, a trimmed notation
telescope, a named implicit. What does not pay is stopping a term from being
written twice.

## What is deliberately not here

The reind-normal-form framework. It was built, applied four separate ways, and
measured at **~0 GB library-wide** every time: 1,487 lines of churn for −0.31 GB.
It produced one genuine 6.0x win on a single quantifier proof and made 437 lines
of previously-abandoned mathematics affordable, but as a library-wide performance
technique it does not pay. `perf/06-RESULTS.md` §11 on the `perf/harness` branch
carries the full account, including the three obstructions that stop it
generalising.

Excluding it costs this branch those 437 lines of quantifier mathematics, which
only exist because the technique made them affordable. That is a deliberate
trade, not an oversight.

## Re-measuring

The harness lives on `perf/harness`:

    perf/bin/perf-stack     per-edit stack, agda only
    perf/bin/sweep-2x2      agda vs mikan
    perf/RUNNING-ELSEWHERE.md   prerequisites and flags

    git checkout perf/harness
    CUBICAL_DIR=~/cubical perf/bin/perf-stack -d      # dry run
    CUBICAL_DIR=~/cubical perf/bin/perf-stack         # ~70 minutes

The baseline is pinned as `perf/00-baseline` (82334ffb) rather than tracking
`main`: a branch that drifts changes the baseline and every ratio with it.
