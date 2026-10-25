Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.CohesiveApartness.index.

Crisp case analysis on 𝟚, and the main theorems without hypotheses
on 𝟚.

Several results of gist.CohesiveApartness.TightApartness assume that
𝟚 is ♭-discrete. This is a theorem of Shulman's spatial type theory
[1, Theorems 6.19 and 6.21], whose proof uses the crisp induction
principles of [1, §5]. In Agda, crisp induction on 𝟚 is case analysis
on a crisp variable of type 𝟚, which needs the flag --flat-split, and
Agda's --safe mode doesn't allow --flat-split together with
--without-K. So the other modules of this folder, which are --safe,
take the fact as a hypothesis, and we prove it here. This is the only
module of this folder that uses --flat-split. Because --flat-split is
infective and this module isn't --safe, gist.CohesiveApartness.index
doesn't import it, and it has to be checked separately.

We then restate the main theorems of
gist.CohesiveApartness.TightApartness without the hypothesis. Over
crisp excluded middle, the first statement is equivalent to excluded
middle. Under axiom C1, each statement is equivalent to every
generator being 0-connected. Under singly generated punctual cohesion
with a second point, as in Shulman's Axiom C2, both statements are
false.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584

\begin{code}

{-# OPTIONS --without-K --cohesion --flat-split #-}

module gist.CohesiveApartness.FlatSplit where

open import MLTT.Spartan
open import UF.ClassicalLogic
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

\end{code}

The section s of the counit is defined by case analysis on an
arbitrary element of 𝟚. That s is a retraction of the counit is
proved by case analysis on a crisp element of 𝟚, and this is where
--flat-split is used.

\begin{code}

𝟚-is-♭-discrete : is-♭-discrete 𝟚
𝟚-is-♭-discrete = qinvs-are-equivs ♭-counit (s , η , ε)
 where
  s : 𝟚 → ♭ 𝟚
  s ₀ = ₀ ^♭
  s ₁ = ₁ ^♭

  crisp-η : (@♭ b : 𝟚) → s b ＝ b ^♭
  crisp-η ₀ = refl
  crisp-η ₁ = refl

  η : s ∘ ♭-counit ∼ id
  η (b ^♭) = crisp-η b

  ε : ♭-counit ∘ s ∼ id
  ε ₀ = refl
  ε ₁ = refl

\end{code}

The main theorems of gist.CohesiveApartness.TightApartness without the
hypothesis that 𝟚 is ♭-discrete.

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (pt : propositional-truncations-exist)
       where

 open import gist.CohesiveApartness.TightApartness fe pt
 open PropositionalTruncation pt

 tight-apartnesses-on-♭-discrete-types-are-crisp-iff-EM′
  : {@♭ 𝓥 : Universe}
  → Crisp-EM 𝓥
  → Tight-Apartnesses-On-♭-Discrete-Types-Are-Crisp 𝓤₀ 𝓥 ↔ EM 𝓥
 tight-apartnesses-on-♭-discrete-types-are-crisp-iff-EM′ cem =
  tight-apartnesses-on-♭-discrete-types-are-crisp-iff-EM cem 𝟚-is-♭-discrete

 module _ {@♭ 𝓦 : Universe}
          {𝓥 : Universe}
          {J : 𝓥 ̇ }
          (R : J → 𝓦 ̇ )
          (c1 : Axiom-C1 R)
        where

  open Axiom-C1 c1

  tight-apartnesses-on-♭-discrete-types-are-crisp-iff-generators-are-connected′
   : propext 𝓦
   → Crisp-EM 𝓦
   → Tight-Apartnesses-On-♭-Discrete-Types-Are-Crisp 𝓤₀ 𝓦
   ↔ ((j : J) (x : R j) → ∥ x ＝ base-point j ∥)
  tight-apartnesses-on-♭-discrete-types-are-crisp-iff-generators-are-connected′ =
   tight-apartnesses-on-♭-discrete-types-are-crisp-iff-generators-are-connected
    R c1 𝟚-is-♭-discrete

  induced-apartnesses-on-♭-are-decidable-iff-generators-are-connected′
   : propext 𝓦
   → Crisp-EM 𝓦
   → Induced-Apartnesses-On-♭-Are-Decidable 𝓤₀ 𝓦
   ↔ ((j : J) (x : R j) → ∥ x ＝ base-point j ∥)
  induced-apartnesses-on-♭-are-decidable-iff-generators-are-connected′ =
   induced-apartnesses-on-♭-are-decidable-iff-generators-are-connected
    R c1 𝟚-is-♭-discrete

 module _ {@♭ 𝓥 : Universe}
          (I : 𝓥 ̇ )
          (p : I)
          (sgpc : Singly-Generated-Punctual-Cohesion I p)
          (q : I)
          (q-is-not-p : q ≠ p)
        where

  not-all-tight-apartnesses-on-♭-discrete-types-are-crisp′
   : Crisp-EM 𝓥
   → ¬ Tight-Apartnesses-On-♭-Discrete-Types-Are-Crisp 𝓤₀ 𝓥
  not-all-tight-apartnesses-on-♭-discrete-types-are-crisp′ =
   not-all-tight-apartnesses-on-♭-discrete-types-are-crisp
    I p sgpc 𝟚-is-♭-discrete q q-is-not-p

  not-all-induced-apartnesses-on-♭-are-decidable′
   : ¬ Induced-Apartnesses-On-♭-Are-Decidable 𝓤₀ 𝓥
  not-all-induced-apartnesses-on-♭-are-decidable′ =
   not-all-induced-apartnesses-on-♭-are-decidable
    I p sgpc 𝟚-is-♭-discrete q q-is-not-p

\end{code}
