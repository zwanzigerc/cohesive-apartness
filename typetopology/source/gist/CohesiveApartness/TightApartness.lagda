Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.CohesiveApartness.index.

We discuss the two open problems listed in the section "In cohesive
homotopy type theory" of the nLab page [1], which read as follows
(24 October 2026):

 (1) Suppose a discrete cohesive type A comes with a tight apartness
     relation. Then, assuming crisp excluded middle and axiom C1, is
     the tight apartness relation on A a crisp relation?

 (2) Suppose a cohesive type A comes with a tight apartness relation.
     Then, assuming crisp excluded middle and axiom C1, is the tight
     apartness relation on ♭A in the cohesive mode decidable?

These problems were posed by the prolific nLab contributor Anonymouse.
The words "axiom C1" in them link to the nLab page [3], which defines
axiom C1 with a single pointed generator I. After a small repair of
its literal wording (see gist.CohesiveApartness.Flat), it says that a
crisp type is discrete if and only if every function from I into it
is constant. Technically, then, the problems are stated for this
definition, which we call singly generated punctual cohesion. We take
Shulman's paper [2], where Axioms C0, C1 and C2 come from, as the
authority on Axiom C1. There, the discrete types are characterized by
a family of pointed generators, and the nLab definition is the case of
a single generator. We give our main results for both definitions.

How we read the problems.

 * We formulate both statements for crisp types A, which is the
   setting in which spatial type theory provides ♭A and the
   ♭-discreteness of A. In (1), we also take the proof that A is
   ♭-discrete to be crisp. Under Shulman's Axiom C1 this is no
   restriction [2, Lemma 8.10], and our results hold for either
   reading anyway, since excluded middle implies the stronger one.
   The tight apartness relation, on the other hand, is arbitrary: it
   is an ordinary, not necessarily crisp, variable. Nothing in the
   problems says that it is crisp, and if it were, problem (1) would
   be trivial.

 * A relation _♯_ on a crisp type X is crisp if it is pointwise
   logically equivalent to ♭-counit r for some crisp relation r, that
   is, some r : ♭ (X → X → Ω (𝓤 ⊔ 𝓥)). This is a property, so we
   truncate it.

 * The tight apartness relation on ♭A is the restriction of the given
   one along ♭-counit : ♭ A → A. (When ♭-counit is an embedding, as it
   is for crisp sets under axiom C1, this restriction is again a tight
   apartness relation. We don't formalize this remark.)

The two problems thus become the types

 * Tight-Apartnesses-On-♭-Discrete-Types-Are-Crisp 𝓤 𝓥,
 * Induced-Apartnesses-On-♭-Are-Decidable 𝓤 𝓥

defined below. Here is what we show.

 (a) Excluded middle implies both statements. For the first, this uses
     the result EM-gives-tight-apartness-is-≠ of Apartness.Properties.

 (b) For 𝓤 = 𝓤₀, each statement implies double negation elimination
     for propositions in 𝓥. For the first we assume crisp excluded
     middle and that the booleans 𝟚 are ♭-discrete (a theorem of [2],
     taken as a hypothesis here; see below); the second needs no
     assumption. This uses the tight apartness on 𝟚 with ₀ apart from
     ₁ precisely when a given ¬¬-dense proposition holds. The
     construction is due to Andrew Swan: following his idea, Tom de
     Jong showed that if ℕ has at most one tight apartness then double
     negation elimination holds, and that the argument works for any
     discrete type with two distinct points [4]. It is formalized in
     Apartness.Properties.

     A second proof of the first half of (b), for 𝓥 = 𝓤₀ and assuming
     propositional extensionality, applies directly the theorem of
     Apartness.Properties that a discrete type with two distinct points
     and at most one tight apartness relation gives double negation
     elimination.

     So, over crisp excluded middle, each statement is equivalent to
     excluded middle (in the cohesive mode).

 (c) Under Shulman's Axiom C1 [2, §8.2] for a family of pointed
     generators, and assuming that 𝟚 is ♭-discrete, crisp excluded
     middle and propositional extensionality, each of the two
     statements is equivalent to every generator being 0-connected,
     that is, to every point of every generator being merely equal to
     its base point.

 (d) Under singly generated punctual cohesion for a pointed type
     (I , p), the nLab definition, the same holds with I as the only
     generator: each statement is equivalent to every point of I being
     merely equal to p. When I is a set, this says that every point of
     I is equal to p, and then propositional extensionality isn't
     needed.

 (e) Consequently, if some generator has two distinct points, as in
     Shulman's Axiom C2 [2, §9], then both statements are false. For
     singly generated punctual cohesion, this means a point q ≠ p of
     I. This is the case in real-cohesive homotopy type theory [2],
     where there is a single generator, the type of real numbers, and
     p = 0 and q = 1. More generally, both statements fail as soon as
     some type with two distinct points has only constant maps to 𝟚
     (for the first statement assuming crisp excluded middle and that
     𝟚 is ♭-discrete). This needs no form of axiom C1.

So, for either definition of axiom C1, the answer to both problems is
negative in the sense that crisp excluded middle and axiom C1 don't
imply the statements: they fail in any model of these axioms in which
some generator has two distinct points, such as the intended models of
real cohesion [2]. Neither do these axioms refute the statements,
which hold in the degenerate model in which ♭ is the identity, the
only generator is a singleton and excluded middle holds. The
model-theoretic claims in this paragraph are not formalized here.

The fact that 𝟚 = 𝟙 + 𝟙 is ♭-discrete follows from [2, Theorems 6.19
and 6.21], the second of which rests on the crisp induction principles
of [2, §5]. In Agda, crisp induction on 𝟚 requires --flat-split, which
is not available with --safe and --without-K. We therefore take the
♭-discreteness of 𝟚 as a hypothesis here. The module
gist.CohesiveApartness.FlatSplit, which uses --flat-split and is not
--safe, proves it and restates the main theorems without this
hypothesis.

[1] nLab. Open problems in homotopy type theory.
    https://ncatlab.org/nlab/show/open+problems+in+homotopy+type+theory

[2] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584
    Numbering as in version 3 of the arXiv preprint.

[3] nLab. Axiom of punctual cohesion (axiom C1).
    https://ncatlab.org/nlab/show/axiom+of+punctual+cohesion

[4] Tom de Jong. A little thread on constructive mathematics and
    (tight) apartness relations in particular. Mathstodon, February
    2025. https://mathstodon.xyz/@de_Jong_Tom/113930642479158387

Function extensionality is assumed crisply, as it is a global axiom.

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module gist.CohesiveApartness.TightApartness
        (@♭ fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where

open import Apartness.Definition
open import Apartness.Properties pt
open import MLTT.Two-Properties
open import UF.Base
open import UF.ClassicalLogic
open import UF.DiscreteAndSeparated
 using (is-discrete ; 𝟚-is-discrete ; 𝟚-is-set ; discrete-is-¬¬-separated)
open import UF.Equiv
open import UF.Retracts
open import UF.Sets
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import gist.CohesiveApartness.Flat

open Apartness pt
open PropositionalTruncation pt

\end{code}

Crisp relations, and the two problems as types.

\begin{code}

is-crisp-relation : {@♭ 𝓤 𝓥 : Universe} {@♭ X : 𝓤 ̇ }
                  → (X → X → 𝓥 ̇ )
                  → (𝓤 ⊔ 𝓥) ⁺ ̇
is-crisp-relation {𝓤} {𝓥} {X} R =
 ∃ r ꞉ ♭ (X → X → Ω (𝓤 ⊔ 𝓥)) , ((x y : X) → (♭-counit r x y) holds ↔ R x y)

Tight-Apartnesses-On-♭-Discrete-Types-Are-Crisp
 : (@♭ 𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
Tight-Apartnesses-On-♭-Discrete-Types-Are-Crisp 𝓤 𝓥 =
   (@♭ X : 𝓤 ̇ )
 → @♭ is-♭-discrete X
 → ((_♯_ , _) : Tight-Apartness X 𝓥)
 → is-crisp-relation _♯_

Induced-Apartnesses-On-♭-Are-Decidable
 : (@♭ 𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
Induced-Apartnesses-On-♭-Are-Decidable 𝓤 𝓥 =
   (@♭ X : 𝓤 ̇ )
 → ((_♯_ , _) : Tight-Apartness X 𝓥)
 → (x y : ♭ X) → is-decidable (♭-counit x ♯ ♭-counit y)

\end{code}

The construction from Apartness.Properties. On a discrete type X (in
the sense of decidable equality), given a proposition P, the relation
x ♯ y := P × (x ≠ y) is an apartness, and it is tight if ¬¬ P holds.
Apart points exist only if P holds. We name it after Andrew Swan,
whose idea it is [4].

\begin{code}

module _ {𝓤 𝓥 : Universe}
         {X : 𝓤 ̇ }
         (X-is-discrete : is-discrete X)
         (P : 𝓥 ̇ )
         (P-is-prop : is-prop P)
       where

 Swan-apartness : ¬¬ P → Tight-Apartness X (𝓤 ⊔ 𝓥)
 Swan-apartness ¬¬P = _♯_ , (pv , ir , sy , ct) , tg
  where
   _♯_ : X → X → 𝓤 ⊔ 𝓥 ̇
   x ♯ y = P × (x ≠ y)

   pv : is-prop-valued _♯_
   pv x y = ×-is-prop P-is-prop (negations-are-props fe)

   ir : is-irreflexive _♯_
   ir x (_ , ν) = ≠-is-irrefl x ν

   sy : is-symmetric _♯_
   sy x y (p , ν) = p , ≠-sym ν

   ct : is-cotransitive _♯_
   ct x y z (p , ν) = κ (X-is-discrete x z)
    where
     κ : is-decidable (x ＝ z) → (x ♯ z) ∨ (y ♯ z)
     κ (inl refl) = ∣ inr (p , ≠-sym ν) ∣
     κ (inr ν')   = ∣ inl (p , ν') ∣

   tg : is-tight _♯_
   tg x y na = discrete-is-¬¬-separated X-is-discrete x y
                (λ ν → ¬¬P (λ p → na (p , ν)))

\end{code}

Problem (1). Excluded middle implies a positive answer. By
EM-gives-tight-apartness-is-≠, the tight apartness is then equivalent
to inequality, and inequality on a crisp type is a crisp relation.

\begin{code}

EM-gives-tight-apartnesses-on-♭-discrete-types-are-crisp
 : {@♭ 𝓤 𝓥 : Universe}
 → EM 𝓥
 → Tight-Apartnesses-On-♭-Discrete-Types-Are-Crisp 𝓤 𝓥
EM-gives-tight-apartnesses-on-♭-discrete-types-are-crisp
 {𝓤} {𝓥} em X _ t@(_♯_ , _) = ∣ r , I ∣
  where
   r : ♭ (X → X → Ω (𝓤 ⊔ 𝓥))
   r = (λ x y → (x ＝ y → 𝟘 {𝓥}) , Π-is-prop fe (λ _ → 𝟘-is-prop)) ^♭

   I : (x y : X) → (♭-counit r x y) holds ↔ x ♯ y
   I x y = (λ ν → rl-implication II (λ e → 𝟘-elim (ν e))) ,
           (λ a e → 𝟘-elim (lr-implication II a e))
    where
     II : x ♯ y ↔ x ≠ y
     II = EM-gives-tight-apartness-is-≠ (EM-gives-DNE em) X t x y

\end{code}

Conversely, a positive answer gives double negation elimination. Given
a ¬¬-dense proposition P, the tight apartness on 𝟚 constructed above
is crisp. By crisp excluded middle, the crisp proposition that ₀ and ₁
are apart in the crisp relation is decided, and the negative case
contradicts ¬¬ P.

\begin{code}

tight-apartnesses-on-♭-discrete-types-are-crisp-gives-DNE
 : {@♭ 𝓥 : Universe}
 → Crisp-EM 𝓥
 → @♭ is-♭-discrete 𝟚
 → Tight-Apartnesses-On-♭-Discrete-Types-Are-Crisp 𝓤₀ 𝓥
 → DNE 𝓥
tight-apartnesses-on-♭-discrete-types-are-crisp-gives-DNE
 {𝓥} cem 𝟚-is-♭-discrete φ P P-is-prop ¬¬P = ∥∥-rec P-is-prop II I
  where
   t : Tight-Apartness 𝟚 𝓥
   t = Swan-apartness 𝟚-is-discrete P P-is-prop ¬¬P

   _♯_ : 𝟚 → 𝟚 → 𝓥 ̇
   _♯_ = pr₁ t

   I : is-crisp-relation _♯_
   I = φ 𝟚 𝟚-is-♭-discrete t

   II : (Σ r ꞉ ♭ (𝟚 → 𝟚 → Ω 𝓥)
             , ((x y : 𝟚) → (♭-counit r x y) holds ↔ x ♯ y))
      → P
   II ((r ^♭) , e) = III (cem (r ₀ ₁ holds) (holds-is-prop (r ₀ ₁)))
    where
     III : is-decidable (r ₀ ₁ holds) → P
     III (inl h) = pr₁ (lr-implication (e ₀ ₁) h)
     III (inr ν) = 𝟘-elim (¬¬P (λ p → ν (rl-implication (e ₀ ₁)
                                           (p , zero-is-not-one))))

\end{code}

A second proof, for 𝓥 = 𝓤₀, which uses the theorem of
Apartness.Properties directly, at the cost of assuming propositional
extensionality. By crisp excluded middle, every tight apartness on 𝟚
which is a crisp relation is equivalent to ≠. If they are all crisp,
then 𝟚 has at most one tight apartness, which gives double negation
elimination by the following instance of that theorem.

\begin{code}

at-most-one-tight-apartness-on-𝟚-gives-DNE
 : At-Most-One-Tight-Apartness 𝟚 𝓤₀ → DNE 𝓤₀
at-most-one-tight-apartness-on-𝟚-gives-DNE =
 At-Most-One-Tight-Apartness-on-discrete-type-with-two-distinct-points-gives-DNE
  fe 𝟚 ((₀ , ₁) , zero-is-not-one) 𝟚-is-discrete

tight-apartnesses-on-♭-discrete-types-are-crisp-gives-DNE'
 : propext 𝓤₀
 → Crisp-EM 𝓤₀
 → @♭ is-♭-discrete 𝟚
 → Tight-Apartnesses-On-♭-Discrete-Types-Are-Crisp 𝓤₀ 𝓤₀
 → DNE 𝓤₀
tight-apartnesses-on-♭-discrete-types-are-crisp-gives-DNE'
 pe cem 𝟚-is-♭-discrete φ = at-most-one-tight-apartness-on-𝟚-gives-DNE γ
  where
   I : ((_♯_ , _) : Tight-Apartness 𝟚 𝓤₀) (x y : 𝟚) → x ♯ y ↔ x ≠ y
   I t@(_♯_ , a , τ) =
    ∥∥-rec
     (Π-is-prop fe (λ x → Π-is-prop fe (λ y →
       ↔-is-prop fe fe (apartness-is-prop-valued _♯_ a x y)
                       (negations-are-props fe))))
     II
     (φ 𝟚 𝟚-is-♭-discrete t)
    where
     II : (Σ r ꞉ ♭ (𝟚 → 𝟚 → Ω 𝓤₀)
               , ((x y : 𝟚) → (♭-counit r x y) holds ↔ x ♯ y))
        → (x y : 𝟚) → x ♯ y ↔ x ≠ y
     II ((r ^♭) , e) = III
      where
       IV : (x y : 𝟚) → x ≠ y → is-decidable (r x y holds) → x ♯ y ↔ x ≠ y
       IV x y ν (inl h) = (λ _ → ν) , (λ _ → lr-implication (e x y) h)
       IV x y ν (inr ν') =
        𝟘-elim (ν (τ x y (λ h → ν' (rl-implication (e x y) h))))

       V : (x : 𝟚) → x ♯ x ↔ x ≠ x
       V x = (λ h → 𝟘-elim (apartness-is-irreflexive _♯_ a x h)) ,
             (λ ν → 𝟘-elim (ν refl))

       III : (x y : 𝟚) → x ♯ y ↔ x ≠ y
       III ₀ ₀ = V ₀
       III ₀ ₁ = IV ₀ ₁ zero-is-not-one
                  (cem (r ₀ ₁ holds) (holds-is-prop (r ₀ ₁)))
       III ₁ ₀ = IV ₁ ₀ one-is-not-zero
                  (cem (r ₁ ₀ holds) (holds-is-prop (r ₁ ₀)))
       III ₁ ₁ = V ₁

   being-tight-apartness-is-prop
    : (_♯_ : 𝟚 → 𝟚 → 𝓤₀ ̇ ) → is-prop (is-apartness _♯_ × is-tight _♯_)
   being-tight-apartness-is-prop _♯_ = prop-criterion VI
    where
     VI : is-apartness _♯_ × is-tight _♯_
        → is-prop (is-apartness _♯_ × is-tight _♯_)
     VI ((pv , _) , _) =
      ×-is-prop
       (×-is-prop
         (Π-is-prop fe (λ x → Π-is-prop fe (λ y → being-prop-is-prop fe)))
         (×-is-prop
           (Π-is-prop fe (λ x → negations-are-props fe))
           (×-is-prop
             (Π-is-prop fe (λ x → Π-is-prop fe (λ y →
               Π-is-prop fe (λ _ → pv y x))))
             (Π-is-prop fe (λ x → Π-is-prop fe (λ y →
               Π-is-prop fe (λ z → Π-is-prop fe (λ _ → ∨-is-prop))))))))
       (Π-is-prop fe (λ x → Π-is-prop fe (λ y →
         Π-is-prop fe (λ _ → 𝟚-is-set))))

   γ : At-Most-One-Tight-Apartness 𝟚 𝓤₀
   γ t₁@(_♯₁_ , a₁ , _) t₂@(_♯₂_ , a₂ , _) =
    to-subtype-＝ being-tight-apartness-is-prop
     (dfunext fe (λ x → dfunext fe (λ y →
       pe (apartness-is-prop-valued _♯₁_ a₁ x y)
          (apartness-is-prop-valued _♯₂_ a₂ x y)
          (λ h → rl-implication (I t₂ x y) (lr-implication (I t₁ x y) h))
          (λ h → rl-implication (I t₁ x y) (lr-implication (I t₂ x y) h)))))

\end{code}

Problem (2). Excluded middle implies a positive answer, because the
values of a tight apartness relation are propositions.

\begin{code}

EM-gives-induced-apartnesses-on-♭-are-decidable
 : {@♭ 𝓤 𝓥 : Universe}
 → EM 𝓥
 → Induced-Apartnesses-On-♭-Are-Decidable 𝓤 𝓥
EM-gives-induced-apartnesses-on-♭-are-decidable em X (_♯_ , a , _) x y =
 em (♭-counit x ♯ ♭-counit y)
    (apartness-is-prop-valued _♯_ a (♭-counit x) (♭-counit y))

\end{code}

Conversely, a positive answer gives double negation elimination, now
without any assumption: ♭-counit (₀ ^♭) and ♭-counit (₁ ^♭) are apart
in the tight apartness on 𝟚 constructed above if and only if P holds.

\begin{code}

induced-apartnesses-on-♭-are-decidable-gives-DNE
 : {@♭ 𝓥 : Universe}
 → Induced-Apartnesses-On-♭-Are-Decidable 𝓤₀ 𝓥
 → DNE 𝓥
induced-apartnesses-on-♭-are-decidable-gives-DNE φ P P-is-prop ¬¬P = γ δ
 where
  δ : is-decidable (P × (₀ ≠ ₁))
  δ = φ 𝟚 (Swan-apartness 𝟚-is-discrete P P-is-prop ¬¬P) (₀ ^♭) (₁ ^♭)

  γ : is-decidable (P × (₀ ≠ ₁)) → P
  γ (inl (p , _)) = p
  γ (inr ν)       = 𝟘-elim (¬¬P (λ p → ν (p , zero-is-not-one)))

\end{code}

Summing up: the second statement is equivalent to excluded middle, and
so is the first, over crisp excluded middle and assuming that 𝟚 is
♭-discrete.

\begin{code}

tight-apartnesses-on-♭-discrete-types-are-crisp-iff-EM
 : {@♭ 𝓥 : Universe}
 → Crisp-EM 𝓥
 → @♭ is-♭-discrete 𝟚
 → Tight-Apartnesses-On-♭-Discrete-Types-Are-Crisp 𝓤₀ 𝓥 ↔ EM 𝓥
tight-apartnesses-on-♭-discrete-types-are-crisp-iff-EM cem 𝟚-is-♭-discrete =
   (λ φ → DNE-gives-EM fe
           (tight-apartnesses-on-♭-discrete-types-are-crisp-gives-DNE
             cem 𝟚-is-♭-discrete φ))
 , EM-gives-tight-apartnesses-on-♭-discrete-types-are-crisp

induced-apartnesses-on-♭-are-decidable-iff-EM
 : {@♭ 𝓥 : Universe}
 → Induced-Apartnesses-On-♭-Are-Decidable 𝓤₀ 𝓥 ↔ EM 𝓥
induced-apartnesses-on-♭-are-decidable-iff-EM =
   (λ φ → DNE-gives-EM fe
           (induced-apartnesses-on-♭-are-decidable-gives-DNE φ))
 , EM-gives-induced-apartnesses-on-♭-are-decidable

\end{code}

Refutations under minimal hypotheses. Suppose that a type I has two
distinct points, and that every map from I to 𝟚 is constant. Then
excluded middle fails, because the characteristic function of the
first point, which excluded middle would provide, separates the two
points. Hence both statements fail. For the first we assume crisp
excluded middle and that 𝟚 is ♭-discrete; the second needs neither.
We need neither axiom C1 nor the assumption that I is a set. The
refutations from Shulman's Axiom C2 and from singly generated
punctual cohesion below are instances.

\begin{code}

module _ {@♭ 𝓦 : Universe}
         (I : 𝓦 ̇ )
         (maps-to-𝟚-are-constant : (f : I → 𝟚) (x y : I) → f x ＝ f y)
         (q₀ q₁ : I)
         (q₀-is-not-q₁ : q₀ ≠ q₁)
       where

 two-distinct-points-refute-EM : ¬ EM 𝓦
 two-distinct-points-refute-EM em = not-merely-equal (γ (d q₁) refl)
  where
   d : (x : I) → is-decidable ∥ x ＝ q₀ ∥
   d x = em ∥ x ＝ q₀ ∥ ∥∥-is-prop

   δ : {A : 𝓦 ̇ } → is-decidable A → 𝟚
   δ (inl _) = ₁
   δ (inr _) = ₀

   χ : I → 𝟚
   χ x = δ (d x)

   χ-at-q₀ : χ q₀ ＝ ₁
   χ-at-q₀ = κ (d q₀)
    where
     κ : (e : is-decidable ∥ q₀ ＝ q₀ ∥) → δ e ＝ ₁
     κ (inl _) = refl
     κ (inr ν) = 𝟘-elim (ν ∣ refl ∣)

   γ : (e : is-decidable ∥ q₁ ＝ q₀ ∥) → e ＝ d q₁ → ∥ q₁ ＝ q₀ ∥
   γ (inl t) _ = t
   γ (inr ν) r = 𝟘-elim (zero-is-not-one
                          (ap δ r ∙ maps-to-𝟚-are-constant χ q₁ q₀ ∙ χ-at-q₀))

   not-merely-equal : ¬ ∥ q₁ ＝ q₀ ∥
   not-merely-equal = ∥∥-rec 𝟘-is-prop (λ e → q₀-is-not-q₁ (e ⁻¹))

 two-distinct-points-refute-that-tight-apartnesses-are-crisp
  : Crisp-EM 𝓦
  → @♭ is-♭-discrete 𝟚
  → ¬ Tight-Apartnesses-On-♭-Discrete-Types-Are-Crisp 𝓤₀ 𝓦
 two-distinct-points-refute-that-tight-apartnesses-are-crisp cem 𝟚-♭d φ =
  two-distinct-points-refute-EM
   (lr-implication
     (tight-apartnesses-on-♭-discrete-types-are-crisp-iff-EM cem 𝟚-♭d)
     φ)

 two-distinct-points-refute-that-induced-apartnesses-are-decidable
  : ¬ Induced-Apartnesses-On-♭-Are-Decidable 𝓤₀ 𝓦
 two-distinct-points-refute-that-induced-apartnesses-are-decidable φ =
  two-distinct-points-refute-EM
   (lr-implication induced-apartnesses-on-♭-are-decidable-iff-EM φ)

\end{code}

For comparison, here are the special cases in which the apartness
relation is crisp, where crisp excluded middle suffices. The first is
a crisp version of EM-gives-tight-apartness-is-≠. Neither uses axiom
C1, and the second doesn't use tightness.

\begin{code}

crisp-tight-apartness-on-♭-discrete-type-is-≠
 : {@♭ 𝓤 𝓥 : Universe}
 → Crisp-EM 𝓥
 → (@♭ X : 𝓤 ̇ )
 → is-♭-discrete X
 → (@♭ _♯_ : X → X → 𝓥 ̇ )
 → @♭ is-prop-valued _♯_
 → is-irreflexive _♯_
 → is-tight _♯_
 → (x y : X) → x ♯ y ↔ x ≠ y
crisp-tight-apartness-on-♭-discrete-type-is-≠
 cem X ((s , ε-s) , _) _♯_ pv ir τ x y =
  transport₂ (λ x y → x ♯ y ↔ x ≠ y) (ε-s x) (ε-s y) (I (s x) (s y))
  where
   I : (x' y' : ♭ X)
     → ♭-counit x' ♯ ♭-counit y' ↔ ♭-counit x' ≠ ♭-counit y'
   I (u ^♭) (v ^♭) = II (cem (u ♯ v) (pv u v))
    where
     II : is-decidable (u ♯ v) → u ♯ v ↔ u ≠ v
     II (inl h) = (λ h' e → ir u (transport (u ♯_) (e ⁻¹) h')) , (λ _ → h)
     II (inr ν) = (λ h → 𝟘-elim (ν h)) , (λ ν' → 𝟘-elim (ν' (τ u v ν)))

crisp-induced-apartness-on-♭-is-decidable
 : {@♭ 𝓤 𝓥 : Universe}
 → Crisp-EM 𝓥
 → (@♭ X : 𝓤 ̇ )
 → (@♭ _♯_ : X → X → 𝓥 ̇ )
 → @♭ is-prop-valued _♯_
 → (x y : ♭ X) → is-decidable (♭-counit x ♯ ♭-counit y)
crisp-induced-apartness-on-♭-is-decidable cem X _♯_ pv (u ^♭) (v ^♭) =
 cem (u ♯ v) (pv u v)

\end{code}

The role of axiom C1, in Shulman's formulation [2, §8.2]. We assume
a family R of generators indexed by J, with base points, such that a
crisp type is ♭-discrete if and only if it is null with respect to
every generator, and we assume that 𝟚 is ♭-discrete.

We prove the general criterion: each of the two statements is
equivalent to every generator being 0-connected.

\begin{code}

module _ {@♭ 𝓦 : Universe}
         {𝓥 : Universe}
         {J : 𝓥 ̇ }
         (R : J → 𝓦 ̇ )
         (c1 : Axiom-C1 R)
         (@♭ 𝟚-is-♭-discrete : is-♭-discrete 𝟚)
       where

 open Axiom-C1 c1

 maps-from-generators-to-𝟚-are-constant
  : (j : J) (f : R j → 𝟚) (x : R j) → f x ＝ f (base-point j)
 maps-from-generators-to-𝟚-are-constant j =
  lr-implication (null-iff-maps-are-constant fe (R j) (base-point j) 𝟚)
   (lr-implication (axiom-C0 𝟚) 𝟚-is-♭-discrete j)

\end{code}

Excluded middle makes every generator 0-connected. Otherwise the
characteristic function of the base point would be a non-constant map
from a generator to 𝟚.

\begin{code}

 EM-gives-generators-are-connected
  : EM 𝓦 → (j : J) (x : R j) → ∥ x ＝ base-point j ∥
 EM-gives-generators-are-connected em j x = γ (d x) refl
  where
   d : (y : R j) → is-decidable ∥ y ＝ base-point j ∥
   d y = em ∥ y ＝ base-point j ∥ ∥∥-is-prop

   δ : {A : 𝓦 ̇ } → is-decidable A → 𝟚
   δ (inl _) = ₁
   δ (inr _) = ₀

   χ : R j → 𝟚
   χ y = δ (d y)

   χ-at-base-point : χ (base-point j) ＝ ₁
   χ-at-base-point = κ (d (base-point j))
    where
     κ : (e : is-decidable ∥ base-point j ＝ base-point j ∥) → δ e ＝ ₁
     κ (inl _) = refl
     κ (inr ν) = 𝟘-elim (ν ∣ refl ∣)

   γ : (e : is-decidable ∥ x ＝ base-point j ∥)
     → e ＝ d x
     → ∥ x ＝ base-point j ∥
   γ (inl t) _ = t
   γ (inr ν) q = 𝟘-elim (zero-is-not-one
                          (ap δ q
                           ∙ maps-from-generators-to-𝟚-are-constant j χ x
                           ∙ χ-at-base-point))

\end{code}

Conversely, if every generator is 0-connected then, as Ω 𝓦 is a set,
every map from a generator to Ω 𝓦 is constant. So Ω 𝓦 is ♭-discrete by
Axiom C0, and crisp excluded middle gives excluded middle. We use
propositional extensionality to know that Ω 𝓦 is a set.

\begin{code}

 generators-are-connected-gives-EM
  : propext 𝓦
  → Crisp-EM 𝓦
  → ((j : J) (x : R j) → ∥ x ＝ base-point j ∥)
  → EM 𝓦
 generators-are-connected-gives-EM pe cem c =
  Ω-is-♭-discrete-gives-EM cem (pr₁ (rl-implication (axiom-C0 (Ω 𝓦)) I))
  where
   I : (j : J) → is-null (R j) (Ω 𝓦)
   I j = rl-implication
          (null-iff-maps-are-constant fe (R j) (base-point j) (Ω 𝓦))
          (λ f x → ∥∥-rec (Ω-is-set fe pe) (ap f) (c j x))

\end{code}

Hence each of the two statements is equivalent to every generator
being 0-connected.

\begin{code}

 tight-apartnesses-on-♭-discrete-types-are-crisp-iff-generators-are-connected
  : propext 𝓦
  → Crisp-EM 𝓦
  → Tight-Apartnesses-On-♭-Discrete-Types-Are-Crisp 𝓤₀ 𝓦
  ↔ ((j : J) (x : R j) → ∥ x ＝ base-point j ∥)
 tight-apartnesses-on-♭-discrete-types-are-crisp-iff-generators-are-connected
  pe cem =
   (λ φ → EM-gives-generators-are-connected (lr-implication II φ)) ,
   (λ c → rl-implication II (generators-are-connected-gives-EM pe cem c))
  where
   II : Tight-Apartnesses-On-♭-Discrete-Types-Are-Crisp 𝓤₀ 𝓦 ↔ EM 𝓦
   II = tight-apartnesses-on-♭-discrete-types-are-crisp-iff-EM
         cem 𝟚-is-♭-discrete

 induced-apartnesses-on-♭-are-decidable-iff-generators-are-connected
  : propext 𝓦
  → Crisp-EM 𝓦
  → Induced-Apartnesses-On-♭-Are-Decidable 𝓤₀ 𝓦
  ↔ ((j : J) (x : R j) → ∥ x ＝ base-point j ∥)
 induced-apartnesses-on-♭-are-decidable-iff-generators-are-connected
  pe cem =
   (λ φ → EM-gives-generators-are-connected (lr-implication II φ)) ,
   (λ c → rl-implication II (generators-are-connected-gives-EM pe cem c))
  where
   II : Induced-Apartnesses-On-♭-Are-Decidable 𝓤₀ 𝓦 ↔ EM 𝓦
   II = induced-apartnesses-on-♭-are-decidable-iff-EM

\end{code}

Shulman's Axiom C2 [2, §9] adds that some generator R j₀ is a set with
two distinct points r₀ and r₁. Then neither statement holds. This is
an instance of the refutations under minimal hypotheses above, because
every map from a generator to 𝟚 is constant. We don't need R j₀ to be
a set, and for the second statement we don't need crisp excluded
middle. We also record directly that such a generator isn't
0-connected.

\begin{code}

 module _ (j₀ : J)
          (r₀ r₁ : R j₀)
          (r₀-is-not-r₁ : r₀ ≠ r₁)
        where

  maps-from-R-j₀-to-𝟚-are-constant
   : (f : R j₀ → 𝟚) (x y : R j₀) → f x ＝ f y
  maps-from-R-j₀-to-𝟚-are-constant f x y =
   maps-from-generators-to-𝟚-are-constant j₀ f x
   ∙ maps-from-generators-to-𝟚-are-constant j₀ f y ⁻¹

  generator-with-distinct-points-is-not-connected
   : ¬ ((j : J) (x : R j) → ∥ x ＝ base-point j ∥)
  generator-with-distinct-points-is-not-connected c =
   ∥∥-rec 𝟘-is-prop
    (λ e₀ → ∥∥-rec 𝟘-is-prop
             (λ e₁ → r₀-is-not-r₁ (e₀ ∙ e₁ ⁻¹))
             (c j₀ r₁))
    (c j₀ r₀)

  Axiom-C2-refutes-that-tight-apartnesses-are-crisp
   : Crisp-EM 𝓦
   → ¬ Tight-Apartnesses-On-♭-Discrete-Types-Are-Crisp 𝓤₀ 𝓦
  Axiom-C2-refutes-that-tight-apartnesses-are-crisp cem =
   two-distinct-points-refute-that-tight-apartnesses-are-crisp
    (R j₀) maps-from-R-j₀-to-𝟚-are-constant r₀ r₁ r₀-is-not-r₁
    cem 𝟚-is-♭-discrete

  Axiom-C2-refutes-that-induced-apartnesses-are-decidable
   : ¬ Induced-Apartnesses-On-♭-Are-Decidable 𝓤₀ 𝓦
  Axiom-C2-refutes-that-induced-apartnesses-are-decidable =
   two-distinct-points-refute-that-induced-apartnesses-are-decidable
    (R j₀) maps-from-R-j₀-to-𝟚-are-constant r₀ r₁ r₀-is-not-r₁

\end{code}

The definition used on the nLab, singly generated punctual cohesion,
for a pointed type (I , p), again assuming that 𝟚 is ♭-discrete. By
singly-generated-punctual-cohesion-gives-Axiom-C1, this is Shulman's
Axiom C1 for a single generator, so the above applies. We record the
resulting general criterion, and, when I is a set, give direct proofs
that don't use propositional extensionality.

\begin{code}

module _ {@♭ 𝓥 : Universe}
         (I : 𝓥 ̇ )
         (p : I)
         (sgpc : Singly-Generated-Punctual-Cohesion I p)
         (@♭ 𝟚-is-♭-discrete : is-♭-discrete 𝟚)
       where

 private
  c1 : Axiom-C1 (λ (_ : 𝟙 {𝓤₀}) → I)
  c1 = singly-generated-punctual-cohesion-gives-Axiom-C1 fe I p sgpc

 tight-apartnesses-on-♭-discrete-types-are-crisp-iff-I-is-connected
  : propext 𝓥
  → Crisp-EM 𝓥
  → Tight-Apartnesses-On-♭-Discrete-Types-Are-Crisp 𝓤₀ 𝓥
  ↔ ((x : I) → ∥ x ＝ p ∥)
 tight-apartnesses-on-♭-discrete-types-are-crisp-iff-I-is-connected pe cem =
  (λ φ → lr-implication II φ ⋆) , (λ c → rl-implication II (λ _ → c))
  where
   II : Tight-Apartnesses-On-♭-Discrete-Types-Are-Crisp 𝓤₀ 𝓥
      ↔ ((j : 𝟙) (x : I) → ∥ x ＝ p ∥)
   II =
    tight-apartnesses-on-♭-discrete-types-are-crisp-iff-generators-are-connected
     (λ _ → I) c1 𝟚-is-♭-discrete pe cem

 induced-apartnesses-on-♭-are-decidable-iff-I-is-connected
  : propext 𝓥
  → Crisp-EM 𝓥
  → Induced-Apartnesses-On-♭-Are-Decidable 𝓤₀ 𝓥 ↔ ((x : I) → ∥ x ＝ p ∥)
 induced-apartnesses-on-♭-are-decidable-iff-I-is-connected pe cem =
  (λ φ → lr-implication II φ ⋆) , (λ c → rl-implication II (λ _ → c))
  where
   II : Induced-Apartnesses-On-♭-Are-Decidable 𝓤₀ 𝓥
      ↔ ((j : 𝟙) (x : I) → ∥ x ＝ p ∥)
   II = induced-apartnesses-on-♭-are-decidable-iff-generators-are-connected
         (λ _ → I) c1 𝟚-is-♭-discrete pe cem

 maps-from-I-to-𝟚-are-constant : (f : I → 𝟚) (i : I) → f i ＝ f p
 maps-from-I-to-𝟚-are-constant =
  lr-implication (sgpc 𝟚) 𝟚-is-♭-discrete

\end{code}

If I is a set, excluded middle forces every point of I to be equal to
p, because the characteristic function of p is a map I → 𝟚.

\begin{code}

 EM-gives-every-point-of-I-is-p : is-set I → EM 𝓥 → (i : I) → i ＝ p
 EM-gives-every-point-of-I-is-p I-is-set em i = γ (d i) refl
  where
   d : (j : I) → is-decidable (j ＝ p)
   d j = em (j ＝ p) I-is-set

   δ : {A : 𝓥 ̇ } → is-decidable A → 𝟚
   δ (inl _) = ₁
   δ (inr _) = ₀

   χ : I → 𝟚
   χ j = δ (d j)

   χ-at-p : χ p ＝ ₁
   χ-at-p = κ (d p)
    where
     κ : (e : is-decidable (p ＝ p)) → δ e ＝ ₁
     κ (inl _) = refl
     κ (inr ν) = 𝟘-elim (ν refl)

   γ : (e : is-decidable (i ＝ p)) → e ＝ d i → i ＝ p
   γ (inl e) _ = e
   γ (inr ν) r = 𝟘-elim (zero-is-not-one
                          (ap δ r ∙ maps-from-I-to-𝟚-are-constant χ i ∙ χ-at-p))

\end{code}

Conversely, if every point of I is equal to p, then every map I → Ω 𝓥
is constant, so Ω 𝓥 is ♭-discrete by singly generated punctual
cohesion. Hence crisp excluded middle gives excluded middle.

\begin{code}

 every-point-of-I-is-p-gives-EM : Crisp-EM 𝓥 → ((i : I) → i ＝ p) → EM 𝓥
 every-point-of-I-is-p-gives-EM cem c =
  Ω-is-♭-discrete-gives-EM cem
   (pr₁ (rl-implication (sgpc (Ω 𝓥)) (λ f i → ap f (c i))))

\end{code}

Hence each of the two statements is equivalent to every point of I
being equal to p.

\begin{code}

 tight-apartnesses-on-♭-discrete-types-are-crisp-iff-every-point-of-I-is-p
  : is-set I
  → Crisp-EM 𝓥
  → Tight-Apartnesses-On-♭-Discrete-Types-Are-Crisp 𝓤₀ 𝓥 ↔ ((i : I) → i ＝ p)
 tight-apartnesses-on-♭-discrete-types-are-crisp-iff-every-point-of-I-is-p
  I-is-set cem = α , β
  where
   α : Tight-Apartnesses-On-♭-Discrete-Types-Are-Crisp 𝓤₀ 𝓥
     → (i : I) → i ＝ p
   α φ = EM-gives-every-point-of-I-is-p I-is-set
          (DNE-gives-EM fe
            (tight-apartnesses-on-♭-discrete-types-are-crisp-gives-DNE
              cem 𝟚-is-♭-discrete φ))

   β : ((i : I) → i ＝ p)
     → Tight-Apartnesses-On-♭-Discrete-Types-Are-Crisp 𝓤₀ 𝓥
   β c = EM-gives-tight-apartnesses-on-♭-discrete-types-are-crisp
          (every-point-of-I-is-p-gives-EM cem c)

 induced-apartnesses-on-♭-are-decidable-iff-every-point-of-I-is-p
  : is-set I
  → Crisp-EM 𝓥
  → Induced-Apartnesses-On-♭-Are-Decidable 𝓤₀ 𝓥 ↔ ((i : I) → i ＝ p)
 induced-apartnesses-on-♭-are-decidable-iff-every-point-of-I-is-p
  I-is-set cem = α , β
  where
   α : Induced-Apartnesses-On-♭-Are-Decidable 𝓤₀ 𝓥 → (i : I) → i ＝ p
   α φ = EM-gives-every-point-of-I-is-p I-is-set
          (DNE-gives-EM fe (induced-apartnesses-on-♭-are-decidable-gives-DNE φ))

   β : ((i : I) → i ＝ p) → Induced-Apartnesses-On-♭-Are-Decidable 𝓤₀ 𝓥
   β c = EM-gives-induced-apartnesses-on-♭-are-decidable
          (every-point-of-I-is-p-gives-EM cem c)

\end{code}

If I has a point q different from p, as in Shulman's Axiom C2 for a
single generator, then both statements are false. This is again an
instance of the refutations under minimal hypotheses, and I need not
be a set. For the second statement, crisp excluded middle isn't
needed.

\begin{code}

 module _ (q : I)
          (q-is-not-p : q ≠ p)
        where

  maps-from-I-to-𝟚-are-constant' : (f : I → 𝟚) (x y : I) → f x ＝ f y
  maps-from-I-to-𝟚-are-constant' f x y =
   maps-from-I-to-𝟚-are-constant f x ∙ maps-from-I-to-𝟚-are-constant f y ⁻¹

  not-all-tight-apartnesses-on-♭-discrete-types-are-crisp
   : Crisp-EM 𝓥
   → ¬ Tight-Apartnesses-On-♭-Discrete-Types-Are-Crisp 𝓤₀ 𝓥
  not-all-tight-apartnesses-on-♭-discrete-types-are-crisp cem =
   two-distinct-points-refute-that-tight-apartnesses-are-crisp
    I maps-from-I-to-𝟚-are-constant' q p q-is-not-p cem 𝟚-is-♭-discrete

  not-all-induced-apartnesses-on-♭-are-decidable
   : ¬ Induced-Apartnesses-On-♭-Are-Decidable 𝓤₀ 𝓥
  not-all-induced-apartnesses-on-♭-are-decidable =
   two-distinct-points-refute-that-induced-apartnesses-are-decidable
    I maps-from-I-to-𝟚-are-constant' q p q-is-not-p

\end{code}
