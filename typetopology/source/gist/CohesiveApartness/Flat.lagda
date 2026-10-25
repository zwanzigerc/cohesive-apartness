Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.CohesiveApartness.index.

The flat modality ♭ of spatial type theory [1], as provided by Agda's
--cohesion flag, together with the few notions about it that we need
in gist.CohesiveApartness.TightApartness: discrete types, crisp
excluded middle, null types, Shulman's Axioms C0 and C1 [1, §8], and
the single-generator variant of Axiom C1 used on the nLab [2], which
we call singly generated punctual cohesion.

A variable annotated with @♭ is crisp. In Shulman's notation [1] a
crisp variable x of type A is written x :: A. Only crisp variables
are available when we build an element of ♭ A, and a crisp variable
may be used in any position where an ordinary one may be used.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584

[2] nLab. Axiom of punctual cohesion.
    https://ncatlab.org/nlab/show/axiom+of+punctual+cohesion

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

module gist.CohesiveApartness.Flat where

open import MLTT.Spartan
open import UF.Base
open import UF.ClassicalLogic
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.FunExt
open import UF.Retracts
open import UF.Sets
open import UF.SubtypeClassifier
open import UF.Subsingletons

\end{code}

The flat modality and its counit.

\begin{code}

data ♭ {@♭ 𝓤 : Universe} (@♭ A : 𝓤 ̇ ) : 𝓤 ̇ where
 _^♭ : (@♭ a : A) → ♭ A

♭-counit : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } → ♭ A → A
♭-counit (a ^♭) = a

\end{code}

Pattern matching on an element x of ♭ A, which need not be crisp, as
a ^♭ gives a crisp element a of A. This is ♭-induction into an
arbitrary, possibly non-crisp, family of types, which is how ♭ is
eliminated in [1].

We never do case analysis on crisp elements of inductive types (Agda's
--flat-split), because --flat-split is not available together with
--safe and --without-K.

A crisp type is discrete if the counit is an equivalence [1]. We say
"♭-discrete", because in TypeTopology "discrete" means "has decidable
equality". The two notions are related below.

\begin{code}

is-♭-discrete : {@♭ 𝓤 : Universe} (@♭ A : 𝓤 ̇ ) → 𝓤 ̇
is-♭-discrete A = is-equiv (♭-counit {_} {A})

\end{code}

Excluded middle for crisp propositions [1, Axiom LEM]. Notice that both
the proposition and the witness of its propositionality are crisp.

\begin{code}

Crisp-EM : (@♭ 𝓤 : Universe) → 𝓤 ⁺ ̇
Crisp-EM 𝓤 = (@♭ P : 𝓤 ̇ ) → @♭ is-prop P → P + ¬ P

\end{code}

Under crisp excluded middle, every ♭-discrete crisp set is discrete in
the sense of TypeTopology. For crisp u and v, the proposition u ＝ v
is crisp, and hence decided by crisp excluded middle. An arbitrary
element of a ♭-discrete type is of the form ♭-counit (u ^♭) for a
crisp u. Compare [1, Lemma 8.15], which, assuming also axiom C1,
characterizes the discrete sets as the sets with decidable equality.

\begin{code}

♭-discrete-sets-are-discrete
 : {@♭ 𝓤 : Universe}
 → Crisp-EM 𝓤
 → (@♭ A : 𝓤 ̇ )
 → @♭ is-set A
 → is-♭-discrete A
 → is-discrete A
♭-discrete-sets-are-discrete cem A A-is-set ((s , ε-s) , _) x y = γ
 where
  I : (x' y' : ♭ A) → is-decidable (♭-counit x' ＝ ♭-counit y')
  I (u ^♭) (v ^♭) = cem (u ＝ v) A-is-set

  γ : is-decidable (x ＝ y)
  γ = transport₂ (λ a b → is-decidable (a ＝ b)) (ε-s x) (ε-s y)
       (I (s x) (s y))

\end{code}

If the type Ω 𝓤 of propositions is ♭-discrete, or merely if the
counit ♭ (Ω 𝓤) → Ω 𝓤 has a section, then crisp excluded middle gives
excluded middle, because then every proposition is (equal to) a crisp
one.

\begin{code}

Ω-is-♭-discrete-gives-EM
 : {@♭ 𝓤 : Universe}
 → Crisp-EM 𝓤
 → has-section (♭-counit {_} {Ω 𝓤})
 → EM 𝓤
Ω-is-♭-discrete-gives-EM {𝓤} cem (s , ε-s) P P-is-prop =
 γ (s (P , P-is-prop)) (ε-s (P , P-is-prop))
 where
  γ : (q : ♭ (Ω 𝓤)) → ♭-counit q ＝ (P , P-is-prop) → P + ¬ P
  γ (Q ^♭) e = transport (λ - → (- holds) + ¬ (- holds)) e
                (cem (Q holds) (holds-is-prop Q))

\end{code}

Null types. A type A is null with respect to a type B if the map
A → (B → A) that sends a to the constant function with value a is an
equivalence. If B is pointed by b, this amounts to every map f : B → A
satisfying f x ＝ f b for all x [1, Lemma 8.7].

\begin{code}

is-null : {𝓥 𝓦 : Universe} → 𝓥 ̇ → 𝓦 ̇ → 𝓥 ⊔ 𝓦 ̇
is-null B A = is-equiv (λ (a : A) (_ : B) → a)

null-iff-maps-are-constant
 : {𝓥 𝓦 : Universe}
 → funext 𝓥 𝓦
 → (B : 𝓥 ̇ ) (b : B) (A : 𝓦 ̇ )
 → is-null B A ↔ ((f : B → A) (x : B) → f x ＝ f b)
null-iff-maps-are-constant fe B b A = I , II
 where
  I : is-null B A → (f : B → A) (x : B) → f x ＝ f b
  I ((s , ε) , _) f x = happly (ε f) x ⁻¹ ∙ happly (ε f) b

  II : ((f : B → A) (x : B) → f x ＝ f b) → is-null B A
  II h = ((λ f → f b) , (λ f → dfunext fe (λ x → h f x ⁻¹))) ,
         ((λ f → f b) , (λ a → refl))

\end{code}

Shulman's axioms of cohesion [1, §8] are formulated in terms of a
family of generators. Axiom C0 asks for a family R of types such that
a crisp type is discrete if and only if it is null with respect to
every R j. Shulman asks the family to be crisp; we don't, because we
never need this, so our results apply in particular to crisp families.
(Shulman writes I for the index type, which we call J.)

\begin{code}

Axiom-C0 : {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } → (J → 𝓦 ̇ ) → 𝓤ω
Axiom-C0 {𝓥} {𝓦} {J} R =
   {@♭ 𝓣 : Universe} (@♭ A : 𝓣 ̇ )
 → is-♭-discrete A ↔ ((j : J) → is-null (R j) A)

\end{code}

Axiom C1 [1, §8.2] adds that every generator is pointed. We take this,
Shulman's formulation, as the definition of axiom C1. Shulman's Axiom
C2 [1, §9] further asks for a generator which is a set with two
distinct points; we use it in the form of hypotheses where needed.

\begin{code}

record Axiom-C1 {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ ) : 𝓤ω where
 field
  axiom-C0 : Axiom-C0 R
  base-point : (j : J) → R j

\end{code}

The nLab page "axiom of punctual cohesion" [2], to which the problems'
"axiom C1" links, instead uses a single pointed generator.
Literally, it says that there is a pointed type I such that "every
crisp type T is discrete if and only if every function from I into
Disc(T) is a constant function", where Disc takes a type of the crisp
mode of the nLab's two-mode presentation to a type of the cohesive
mode. As written, this mixes the two modes: T is a type of the crisp
mode, whereas discreteness is a property of types of the cohesive
mode. Reading "T is discrete" as "Disc(T) is discrete" doesn't help,
because Disc(T) is discrete in any case, so the axiom would only say
that maps from I to types of the form Disc(T) are constant, losing
the direction that I detects discreteness. Moreover, the page defines
discreteness using a canonical function ♭(−) : A → ♭A, whereas the
canonical function goes the other way, ♭A → A (our ♭-counit). We
repair the definition
by reading it in Shulman's single-mode spatial type theory: a crisp
type A is ♭-discrete if and only if every function from I into A is
constant. We read "every function f from I into A is constant" as
(i : I) → f i ＝ f p, which for a pointed type I is equivalent to the
other usual readings, and, by null-iff-maps-are-constant, to A being
null with respect to I.

To distinguish the repaired definition from Shulman's Axiom C1, we
call it singly generated punctual cohesion. (The nLab writes I for the
generator itself.) In real cohesion [1], there is a single generator,
the type of real numbers, pointed by 0, and the axiom is Shulman's
Axiom R♭.

\begin{code}

Singly-Generated-Punctual-Cohesion : {𝓥 : Universe} (I : 𝓥 ̇ ) → I → 𝓤ω
Singly-Generated-Punctual-Cohesion I p =
   {@♭ 𝓦 : Universe} (@♭ A : 𝓦 ̇ )
 → is-♭-discrete A ↔ ((f : I → A) (i : I) → f i ＝ f p)

\end{code}

Singly generated punctual cohesion is the same as Shulman's Axiom C1
for a family with exactly one generator.

\begin{code}

singly-generated-punctual-cohesion-gives-Axiom-C1
 : {𝓥 : Universe}
 → Fun-Ext
 → (I : 𝓥 ̇ ) (p : I)
 → Singly-Generated-Punctual-Cohesion I p
 → Axiom-C1 (λ (_ : 𝟙 {𝓤₀}) → I)
singly-generated-punctual-cohesion-gives-Axiom-C1 fe I p spc =
 record { axiom-C0 = c0 ; base-point = λ _ → p }
 where
  c0 : Axiom-C0 (λ (_ : 𝟙 {𝓤₀}) → I)
  c0 A = (λ d _ → rl-implication (null-iff-maps-are-constant fe I p A)
                   (lr-implication (spc A) d)) ,
         (λ n → rl-implication (spc A)
                 (lr-implication (null-iff-maps-are-constant fe I p A)
                   (n ⋆)))

Axiom-C1-gives-singly-generated-punctual-cohesion
 : {𝓥 : Universe}
 → Fun-Ext
 → (I : 𝓥 ̇ )
 → (c1 : Axiom-C1 (λ (_ : 𝟙 {𝓤₀}) → I))
 → Singly-Generated-Punctual-Cohesion I (Axiom-C1.base-point c1 ⋆)
Axiom-C1-gives-singly-generated-punctual-cohesion fe I c1 A =
 (λ d → lr-implication (null-iff-maps-are-constant fe I p A)
         (lr-implication (axiom-C0 A) d ⋆)) ,
 (λ h → rl-implication (axiom-C0 A)
         (λ _ → rl-implication (null-iff-maps-are-constant fe I p A) h))
 where
  open Axiom-C1 c1

  p : I
  p = base-point ⋆

\end{code}
