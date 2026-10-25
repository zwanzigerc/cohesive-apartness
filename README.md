# Tight apartness relations in cohesive type theory

Answers, with Agda formalizations, to two open problems listed
under "In cohesive homotopy type theory" on the nLab page
[open problems in homotopy type theory](https://ncatlab.org/nlab/show/open+problems+in+homotopy+type+theory).

**Author and AI disclosure.** The Agda code, the prose and the mathematical
arguments in this repository are by Claude Opus 5.5, an AI model made by
Anthropic, prompted by Colin Zwanziger in a conversation on 24 and 25 October
2026.

**Acknowledgement.** We thank GPT-6 Astra for reviewing the formalization.

## The problems

The problems were posed on the nLab by the prolific contributor Anonymouse.

1. Suppose a discrete cohesive type A comes with a tight apartness relation.
   Then, assuming crisp excluded middle and axiom C1, is the tight apartness
   relation on A a crisp relation?
2. Suppose a cohesive type A comes with a tight apartness relation. Then,
   assuming crisp excluded middle and axiom C1, is the tight apartness
   relation on ♭A in the cohesive mode decidable?

## Answers

Neither statement follows from crisp excluded middle and axiom C1, and
neither is refuted by them: over crisp excluded middle, each is equivalent to
excluded middle in the cohesive mode. Both are false in real cohesion.

- **Reading.** We formulate both principles for crisp types A, with an
  arbitrary, not necessarily crisp, tight apartness. A relation is *crisp* if
  it is pointwise equivalent to one coming from ♭(A → A → Prop). The
  apartness on ♭A is the restriction along the counit ♭A → A.
- **Excluded middle implies both statements**, using
  `EM-gives-tight-apartness-is-≠` from TypeTopology's
  [`Apartness.Properties`](https://martinescardo.github.io/TypeTopology/Apartness.Properties.html).
- **Each statement implies double negation elimination.** This uses Andrew
  Swan's construction, as generalized by Tom de Jong
  ([Mathstodon thread](https://mathstodon.xyz/@de_Jong_Tom/113930642479158387)):
  for a proposition P, x ♯ y := P ∧ (x ≠ y) is an apartness on a type with
  decidable equality, and it is tight when ¬¬P.
- **Axiom C1.** We take Shulman's formulation
  ([arXiv:1509.07584](https://arxiv.org/abs/1509.07584), §8.2: a family of
  pointed generators) as authoritative. The problems link to the nLab page
  [axiom of punctual cohesion](https://ncatlab.org/nlab/show/axiom+of+punctual+cohesion),
  which uses a single pointed generator; we call a repaired reading of it
  *singly generated punctual cohesion*, and it is equivalent to Shulman's
  Axiom C1 with one generator.
  - Under Shulman's Axiom C1, and assuming propositional extensionality,
    each statement holds if and only if every generator is 0-connected.
  - Under singly generated punctual cohesion with generator (I, p), each
    statement holds if and only if I is 0-connected. For a set I this means
    that every point of I is p, and then propositional extensionality isn't
    needed.
- **Refutations.** Both statements fail as soon as some type with two
  distinct points has only constant maps to Bool (for the first statement,
  assuming crisp excluded middle and that Bool is ♭-discrete). This needs no
  form of axiom C1. In particular, Shulman's Axiom C2 refutes both, as in
  real cohesion, whose generator ℝ has 0 ≠ 1.
- **Not formalized.** Both statements hold in the degenerate model in which
  ♭ is the identity, the only generator is a singleton and excluded middle
  holds. This, and the existence of models of real cohesion with crisp
  excluded middle, are model-theoretic remarks that we don't formalize.

## Files

- `typetopology/source/gist/CohesiveApartness/`: the main formalization,
  written in TypeTopology's style (`index.lagda`, `Flat.lagda`,
  `TightApartness.lagda`), with `--safe --without-K --cohesion`. That Bool is
  ♭-discrete (Shulman, Theorems 6.19 and 6.21) is a hypothesis, because its
  proof needs crisp induction (`--flat-split`), which isn't available with
  `--safe --without-K`.
- `typetopology/cohesive-apartness.patch`: the same folder, as a patch
  against TypeTopology.
- `standalone/CohesiveApartness.agda`: an earlier, self-contained version
  (single generator only). It uses
  `--without-K --cohesion --flat-split` and postulates propositional
  truncation.

This is not a contribution to TypeTopology: TypeTopology's `AI-Policy.md`
says that AI generated Agda code or prose won't be considered. Also,
TypeTopology's library sets `--no-cohesion`, and `--cohesion` is infective,
so TypeTopology's index files couldn't import these modules without
changes.

## Checking

The workflow in `.github/workflows/check.yml` type-checks both versions
with Agda 2.8.0. To check by hand:

```sh
# TypeTopology version
git clone https://github.com/martinescardo/TypeTopology.git
cd TypeTopology
git checkout 52ed2eb58d72a6bab0dd70480fa73e2291b08219
cp -r ../cohesive-apartness/typetopology/source/gist/CohesiveApartness source/gist/
agda source/gist/CohesiveApartness/index.lagda

# Standalone version (also checks with Agda 2.6.3)
cd ../cohesive-apartness/standalone
agda CohesiveApartness.agda
```
