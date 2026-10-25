{-# OPTIONS --without-K --cohesion --flat-split #-}
-- --flat-split (crisp case analysis) is used only in Bool-discrete.

{-
  Tight apartness relations in crisp/cohesive type theory.

  Author: Claude Opus 5.5, an AI model made by Anthropic, prompted by
  Colin Zwanziger, 24-25 October 2026.  Thanks to GPT-6 Astra for
  reviewing this file.

  Checks the modal reasoning behind the answer to the two nLab
  "open problems in homotopy type theory" in the section
  "In cohesive homotopy type theory":

   (P1) A discrete, # a tight apartness on A, crisp LEM + C1:
        is # a crisp relation?
   (P2) A cohesive type with tight apartness #, crisp LEM + C1:
        is the induced tight apartness on ♭A decidable (cohesive mode)?

  Crisp variables are Agda's @♭ variables (Shulman's  u :: A).
  All hypotheses are module parameters; no global axioms except a
  propositional truncation (used only for the "∨" in cotransitivity
  and the "∃" in "is crisp").
-}

module CohesiveApartness where

open import Agda.Primitive using (Level; _⊔_; lzero; lsuc)

------------------------------------------------------------------------
-- Basic type formers

data ⊥ : Set where

⊥-elim : {ℓ : Level} {A : Set ℓ} → ⊥ → A
⊥-elim ()

¬_ : {ℓ : Level} → Set ℓ → Set ℓ
¬ A = A → ⊥
infix 3 ¬_

data _≡_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x
infix 4 _≡_

sym : {ℓ : Level} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

_∙_ : {ℓ : Level} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∙ q = q
infixr 5 _∙_

ap : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} (f : A → B) {x y : A}
   → x ≡ y → f x ≡ f y
ap f refl = refl

data Bool : Set where
  false true : Bool

false≢true : ¬ (false ≡ true)
false≢true ()

data _⊎_ {ℓ ℓ' : Level} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
infixr 1 _⊎_

record Σ {ℓ ℓ' : Level} (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor _,_
  field
    pr₁ : A
    pr₂ : B pr₁
open Σ public
infixr 4 _,_

_×_ : {ℓ ℓ' : Level} → Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
A × B = Σ A (λ _ → B)

_↔_ : {ℓ ℓ' : Level} → Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
A ↔ B = (A → B) × (B → A)
infix 2 _↔_

Dec : {ℓ : Level} → Set ℓ → Set ℓ
Dec A = A ⊎ ¬ A

¬¬-Dec : {ℓ : Level} {A : Set ℓ} → ¬ ¬ Dec A
¬¬-Dec n = n (inr (λ a → n (inl a)))

is-prop : {ℓ : Level} → Set ℓ → Set ℓ
is-prop A = (x y : A) → x ≡ y

is-set : {ℓ : Level} → Set ℓ → Set ℓ
is-set A = (x y : A) → is-prop (x ≡ y)

Ω : Set₁
Ω = Σ Set is-prop

_holds : Ω → Set
P holds = pr₁ P
infix 6 _holds

⊥-is-prop : is-prop ⊥
⊥-is-prop ()

𝟘ₚ : Ω
𝟘ₚ = ⊥ , ⊥-is-prop

------------------------------------------------------------------------
-- Propositional truncation (postulated, standard rules)

postulate
  ∥_∥    : {ℓ : Level} → Set ℓ → Set ℓ
  ∣_∣    : {ℓ : Level} {A : Set ℓ} → A → ∥ A ∥
  ∥∥-rec : {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'}
         → is-prop B → (A → B) → ∥ A ∥ → B
  ∥∥-is-prop : {ℓ : Level} {A : Set ℓ} → is-prop ∥ A ∥

------------------------------------------------------------------------
-- The flat modality (crisp type theory, as in agda-flat)

data ♭ {@♭ ℓ : Level} (@♭ A : Set ℓ) : Set ℓ where
  _^♭ : (@♭ a : A) → ♭ A

-- counit
ε : {@♭ ℓ : Level} {@♭ A : Set ℓ} → ♭ A → A
ε (a ^♭) = a

-- A crisp type is discrete if ε is an equivalence; we only ever use
-- that ε has a section (every x : A is ε of something).
has-♭-section : {@♭ ℓ : Level} (@♭ A : Set ℓ) → Set ℓ
has-♭-section A = (x : A) → Σ (♭ A) (λ x' → ε x' ≡ x)

------------------------------------------------------------------------
-- Tight apartness relations

record is-tight-apartness {A : Set} (_#_ : A → A → Ω) : Set where
  field
    irrefl  : (x : A) → ¬ (x # x) holds
    symm    : (x y : A) → (x # y) holds → (y # x) holds
    cotrans : (x y z : A) → (x # y) holds
            → ∥ ((x # z) holds ⊎ (z # y) holds) ∥
    tight   : (x y : A) → ¬ (x # y) holds → x ≡ y
open is-tight-apartness public

-- "# is a crisp relation":  # is (pointwise equivalent to) ε of an
-- element of ♭(A → A → Ω).  Pointwise ↔ and ∃ make this as weak
-- as possible, so refuting "every tight apartness is crisp" is as
-- strong as possible.
is-crisp : {@♭ A : Set} → (A → A → Ω) → Set₁
is-crisp {A} _#_ =
  ∥ Σ (♭ (A → A → Ω)) (λ r → (x y : A) → (ε r x y) holds ↔ (x # y) holds) ∥

------------------------------------------------------------------------
-- Swan / TypeTopology construction: tight apartnesses on Bool from
-- ¬¬-dense propositions.  0 #Q 1 :≡ Q.

module BoolApartness (Q : Ω) (¬¬Q : ¬ ¬ Q holds) where

  _#Q_ : Bool → Bool → Ω
  false #Q false = 𝟘ₚ
  true  #Q true  = 𝟘ₚ
  false #Q true  = Q
  true  #Q false = Q

  #Q-tight : is-tight-apartness _#Q_
  #Q-tight = record { irrefl = irr ; symm = sy ; cotrans = co ; tight = ti }
    where
      irr : (x : Bool) → ¬ (x #Q x) holds
      irr false h = h
      irr true  h = h

      sy : (x y : Bool) → (x #Q y) holds → (y #Q x) holds
      sy false false h = h
      sy false true  h = h
      sy true  false h = h
      sy true  true  h = h

      co : (x y z : Bool) → (x #Q y) holds
         → ∥ ((x #Q z) holds ⊎ (z #Q y) holds) ∥
      co false false z     h = ⊥-elim h
      co true  true  z     h = ⊥-elim h
      co false true  false h = ∣ inr h ∣
      co false true  true  h = ∣ inl h ∣
      co true  false false h = ∣ inl h ∣
      co true  false true  h = ∣ inr h ∣

      ti : (x y : Bool) → ¬ (x #Q y) holds → x ≡ y
      ti false false _ = refl
      ti true  true  _ = refl
      ti false true  n = ⊥-elim (¬¬Q n)
      ti true  false n = ⊥-elim (¬¬Q n)

------------------------------------------------------------------------
-- AUXILIARY LEMMAS (crisp excluded middle only).
-- Neither problem assumes the apartness is crisp; these lemmas only
-- explain what "crisp" amounts to, and why a crisp # would be easy.

module CrispLEM (crisp-LEM : (@♭ P : Ω) → Dec (P holds)) where

  irrefl-≡ : {A : Set} {_#_ : A → A → Ω} → is-tight-apartness _#_
           → (x y : A) → x ≡ y → ¬ (x # y) holds
  irrefl-≡ t x .x refl = irrefl t x

  -- For crisp #, and crisp u v, u # v is decided by crisp LEM, hence
  -- coincides with ≠ (the pointwise form of TypeTopology's
  -- EM-gives-tight-apartness-is-≠).
  crisp-pointwise : {@♭ A : Set} (@♭ _#_ : A → A → Ω)
                  → is-tight-apartness _#_
                  → (@♭ u v : A) → (u # v) holds ↔ ¬ (u ≡ v)
  crisp-pointwise _#_ t u v with crisp-LEM (u # v)
  ... | inl h = (λ h' e → irrefl-≡ t u v e h') , (λ _ → h)
  ... | inr n = (λ h → ⊥-elim (n h)) , (λ ne → ⊥-elim (ne (tight t u v n)))

  -- Lemma A: a crisp tight apartness on a discrete type is ≠.
  lemmaA : {@♭ A : Set} → has-♭-section A
         → (@♭ _#_ : A → A → Ω) → is-tight-apartness _#_
         → (x y : A) → (x # y) holds ↔ ¬ (x ≡ y)
  lemmaA disc _#_ t x y with disc x | disc y
  ... | (u ^♭ , refl) | (v ^♭ , refl) = crisp-pointwise _#_ t u v

  -- Under crisp LEM a discrete crisp set has decidable equality, i.e.
  -- it is "discrete" in TypeTopology's sense too.
  discrete-dec-eq : {@♭ A : Set} (@♭ A-set : is-set A) → has-♭-section A
                  → (x y : A) → Dec (x ≡ y)
  discrete-dec-eq A-set disc x y with disc x | disc y
  ... | (u ^♭ , refl) | (v ^♭ , refl) = crisp-LEM ((u ≡ v) , A-set u v)

  -- Side remark (NOT Problem 2, which assumes no crispness): if # happens
  -- to be crisp, the induced relation on ♭A is decidable by ♭-induction
  -- (into a cohesive motive) and crisp LEM alone.
  P2-crisp : {@♭ A : Set} (@♭ _#_ : A → A → Ω)
           → (x y : ♭ A) → Dec ((ε x # ε y) holds)
  P2-crisp _#_ (u ^♭) (v ^♭) = crisp-LEM (u # v)

  -- If Ω is discrete, crisp LEM gives LEM in the cohesive mode.
  -- (Under C1 this happens iff I is 0-connected.)
  Ω-discrete-gives-LEM : has-♭-section Ω → (P : Ω) → Dec (P holds)
  Ω-discrete-gives-LEM d P with d P
  ... | (P' ^♭ , refl) = crisp-LEM P'

------------------------------------------------------------------------
-- THE PROBLEMS AS STATED.  In Φ₁ and Φ₂ below the apartness # is an
-- ordinary bound variable: nothing about crispness is assumed (only
-- the type, Bool, is crisp, as it must be for ♭Bool to make sense).
--
-- Hypotheses: funext; a set I with points p, q and q ≠ p; and C0 for
-- Bool: every map I → Bool is constant (Bool is discrete, so this
-- follows from C1).  Real cohesion: I = ℝ, p = 0, q = 1.

module Negative
  (funext : {A : Set} {B : A → Set} {f g : (x : A) → B x}
          → ((x : A) → f x ≡ g x) → f ≡ g)
  (I : Set) (I-set : is-set I) (p q : I) (q≢p : ¬ (q ≡ p))
  (C0-Bool : (f : I → Bool) (i : I) → f i ≡ f p)
  where

  ¬-is-prop : {A : Set} → is-prop (¬ A)
  ¬-is-prop f g = funext (λ a → ⊥-elim (f a))

  Dec-is-prop : {A : Set} → is-prop A → is-prop (Dec A)
  Dec-is-prop pA (inl a) (inl b) = ap inl (pA a b)
  Dec-is-prop pA (inl a) (inr n) = ⊥-elim (n a)
  Dec-is-prop pA (inr n) (inl a) = ⊥-elim (n a)
  Dec-is-prop pA (inr n) (inr m) = ap inr (¬-is-prop n m)

  -- Q(i) :≡ (i = p) ∨ ¬(i = p); always ¬¬-dense.
  Qᵢ : I → Ω
  Qᵢ i = Dec (i ≡ p) , Dec-is-prop (I-set i p)

  toBool : {A : Set} → Dec A → Bool
  toBool (inl _) = true
  toBool (inr _) = false

  -- C0 rules out deciding i = p for all i.
  no-decider : ((i : I) → Dec (i ≡ p)) → ⊥
  no-decider d = false≢true (sym (l₂ (d q)) ∙ C0-Bool (λ i → toBool (d i)) q ∙ l₁ (d p))
    where
      l₁ : (x : Dec (p ≡ p)) → toBool x ≡ true
      l₁ (inl _) = refl
      l₁ (inr n) = ⊥-elim (n refl)
      l₂ : (x : Dec (q ≡ p)) → toBool x ≡ false
      l₂ (inl e) = ⊥-elim (q≢p e)
      l₂ (inr _) = refl

  module _ (i : I) where
    open BoolApartness (Qᵢ i) ¬¬-Dec public

  ----------------------------------------------------------------------
  -- Problem 1, internal reading: "every tight apartness on the discrete
  -- type Bool is crisp" is refutable (given crisp LEM).

  Φ₁ : Set₁
  Φ₁ = (_#_ : Bool → Bool → Ω) → is-tight-apartness _#_ → is-crisp _#_

  module _ (crisp-LEM : (@♭ P : Ω) → Dec (P holds)) where

    crisp-gives-Q : (i : I)
      → Σ (♭ (Bool → Bool → Ω))
          (λ r → (x y : Bool) → (ε r x y) holds ↔ (_#Q_ i x y) holds)
      → Dec (i ≡ p)
    crisp-gives-Q i ((r ^♭) , e) with crisp-LEM (r false true)
    ... | inl h = pr₁ (e false true) h
    ... | inr n = ⊥-elim (¬¬-Dec (λ d → n (pr₂ (e false true) d)))

    not-Φ₁ : ¬ Φ₁
    not-Φ₁ φ = no-decider (λ i →
      ∥∥-rec (Dec-is-prop (I-set i p)) (crisp-gives-Q i)
             (φ (_#Q_ i) (#Q-tight i)))

  ----------------------------------------------------------------------
  -- Problem 2, internal reading: "for every tight apartness # on a
  -- crisp type A, the induced relation ε x # ε y on ♭A is decidable"
  -- is refutable, already for A = Bool (♭Bool ≃ Bool).  No crisp LEM
  -- needed.

  Φ₂ : Set₁
  Φ₂ = (_#_ : Bool → Bool → Ω) → is-tight-apartness _#_
     → (x y : ♭ Bool) → Dec ((ε x # ε y) holds)

  not-Φ₂ : ¬ Φ₂
  not-Φ₂ φ = no-decider (λ i → f i (φ (_#Q_ i) (#Q-tight i) (false ^♭) (true ^♭)))
    where
      f : (i : I) → Dec (Dec (i ≡ p)) → Dec (i ≡ p)
      f i (inl d) = d
      f i (inr n) = ⊥-elim (¬¬-Dec n)

------------------------------------------------------------------------
-- EQUIVALENCES WITH LEM IN THE COHESIVE MODE
--
-- Problem-1 and Problem-2 are the two problems as internal statements,
-- quantifying over all (crisp; for P1 also discrete) types A and all
-- tight apartnesses # (an ordinary variable).  Over crisp LEM, each
-- is equivalent to LEM in the cohesive mode.  Given the two instances
-- of C1 used below (C0 for Bool; "I-null ⇒ discrete" for Ω) and I a
-- set, LEM is in turn equivalent to I being contractible.

-- Discreteness of a crisp type: ε : ♭A → A has a two-sided inverse.
is-discrete : {@♭ ℓ : Level} (@♭ A : Set ℓ) → Set ℓ
is-discrete A =
  Σ (A → ♭ A) (λ s → ((x : A) → ε (s x) ≡ x) × ((y : ♭ A) → s (ε y) ≡ y))

-- Bool is discrete (Shulman 2018, §6); crisp case analysis on b.
Bool-discrete : is-discrete Bool
Bool-discrete = s , sect , retr
  where
    s : Bool → ♭ Bool
    s false = false ^♭
    s true  = true ^♭

    sect : (x : Bool) → ε (s x) ≡ x
    sect false = refl
    sect true  = refl

    crisp-case : (@♭ b : Bool) → s b ≡ (b ^♭)
    crisp-case false = refl
    crisp-case true  = refl

    retr : (y : ♭ Bool) → s (ε y) ≡ y
    retr (b ^♭) = crisp-case b

dec→Bool : {A : Set} → Dec A → Bool
dec→Bool (inl _) = true
dec→Bool (inr _) = false

module Equivalences
  (funext : {A : Set} {B : A → Set} {f g : (x : A) → B x}
          → ((x : A) → f x ≡ g x) → f ≡ g)
  (crisp-LEM : (@♭ P : Ω) → Dec (P holds))
  where

  open CrispLEM crisp-LEM using (irrefl-≡ ; Ω-discrete-gives-LEM)

  ¬-prop : {A : Set} → is-prop (¬ A)
  ¬-prop f g = funext (λ a → ⊥-elim (f a))

  Dec-prop : {A : Set} → is-prop A → is-prop (Dec A)
  Dec-prop pA (inl a) (inl b) = ap inl (pA a b)
  Dec-prop pA (inl a) (inr n) = ⊥-elim (n a)
  Dec-prop pA (inr n) (inl a) = ⊥-elim (n a)
  Dec-prop pA (inr n) (inr m) = ap inr (¬-prop n m)

  LEM : Set₁
  LEM = (P : Ω) → Dec (P holds)

  Problem-1 : Set₁
  Problem-1 = (@♭ A : Set) → (@♭ dA : is-discrete A)
            → (_#_ : A → A → Ω) → is-tight-apartness _#_ → is-crisp _#_

  Problem-2 : Set₁
  Problem-2 = (@♭ A : Set) → (_#_ : A → A → Ω) → is-tight-apartness _#_
            → (x y : ♭ A) → Dec ((ε x # ε y) holds)

  -- LEM ⇒ Problem 1: every tight apartness is ≠ (as in TypeTopology's
  -- EM-gives-tight-apartness-is-≠), and ≠ on a crisp type is crisp.
  LEM→Problem-1 : LEM → Problem-1
  LEM→Problem-1 lem A dA _#_ t =
    ∣ ((λ x y → ∥ ¬ (x ≡ y) ∥ , ∥∥-is-prop) ^♭) , (λ x y → to x y , from x y) ∣
    where
      g : (x y : A) → ¬ (x ≡ y) → (x # y) holds
      g x y ne with lem (x # y)
      ... | inl h = h
      ... | inr n = ⊥-elim (ne (tight t x y n))

      to : (x y : A) → ∥ ¬ (x ≡ y) ∥ → (x # y) holds
      to x y = ∥∥-rec (pr₂ (x # y)) (g x y)

      from : (x y : A) → (x # y) holds → ∥ ¬ (x ≡ y) ∥
      from x y h = ∣ (λ e → irrefl-≡ t x y e h) ∣

  -- Problem 1 ⇒ LEM (uses crisp LEM), via the Swan/TypeTopology
  -- apartness on Bool with 0 # 1 :≡ (P ∨ ¬P).
  Problem-1→LEM : Problem-1 → LEM
  Problem-1→LEM φ P = ∥∥-rec (Dec-prop (pr₂ P)) g (φ Bool Bool-discrete _#Q_ #Q-tight)
    where
      Q : Ω
      Q = Dec (P holds) , Dec-prop (pr₂ P)

      open BoolApartness Q ¬¬-Dec

      g : Σ (♭ (Bool → Bool → Ω)) (λ r → (x y : Bool) → (ε r x y) holds ↔ (x #Q y) holds)
        → Dec (P holds)
      g ((r ^♭) , e) with crisp-LEM (r false true)
      ... | inl h = pr₁ (e false true) h
      ... | inr n = ⊥-elim (¬¬-Dec (λ d → n (pr₂ (e false true) d)))

  LEM→Problem-2 : LEM → Problem-2
  LEM→Problem-2 lem A _#_ t x y = lem (ε x # ε y)

  -- Problem 2 ⇒ LEM (does not use crisp LEM).
  Problem-2→LEM : Problem-2 → LEM
  Problem-2→LEM φ P = f (φ Bool _#Q_ #Q-tight (false ^♭) (true ^♭))
    where
      Q : Ω
      Q = Dec (P holds) , Dec-prop (pr₂ P)

      open BoolApartness Q ¬¬-Dec

      f : Dec (Q holds) → Dec (P holds)
      f (inl d) = d
      f (inr n) = ⊥-elim (¬¬-Dec n)

  -- LEM versus the interval: I a pointed set with the two instances of
  -- C1 that are needed.
  --
  -- Scope: C1-Ω assumes that this particular I detects
  -- the discreteness of Ω, as in the single-generator form of C1 on
  -- the nLab.  Shulman's Axiom C1 (arXiv:1509.07584, §8.2) uses a
  -- family of pointed generators, and does not give this for an
  -- arbitrary generator; the general criterion (every generator
  -- 0-connected) is not formalized here.  LEM→I-contractible, like
  -- the refutations in the module Negative, uses only C0-Bool, which
  -- holds for every generator in Shulman's form; so the refutations
  -- apply to a generator that is a set with two distinct points, as
  -- in Shulman's Axiom C2 (§9).  For a set I, being 0-connected
  -- amounts to being contractible.
  module _ (I : Set) (I-set : is-set I) (p : I)
           (C0-Bool : (f : I → Bool) (i : I) → f i ≡ f p)
           (C1-Ω : ((f : I → Ω) (i : I) → f i ≡ f p) → has-♭-section Ω)
    where

    LEM→I-contractible : LEM → (i : I) → i ≡ p
    LEM→I-contractible lem i = h (lem (Pᵢ i)) refl
      where
        Pᵢ : I → Ω
        Pᵢ j = (j ≡ p) , I-set j p

        χ : I → Bool
        χ j = dec→Bool (lem (Pᵢ j))

        l₁ : (x : Dec (p ≡ p)) → dec→Bool x ≡ true
        l₁ (inl _) = refl
        l₁ (inr n) = ⊥-elim (n refl)

        h : (d : Dec (i ≡ p)) → d ≡ lem (Pᵢ i) → i ≡ p
        h (inl e) _  = e
        h (inr n) eq = ⊥-elim (false≢true (ap dec→Bool eq ∙ C0-Bool χ i ∙ l₁ (lem (Pᵢ p))))

    I-contractible→LEM : ((i : I) → i ≡ p) → LEM
    I-contractible→LEM c = Ω-discrete-gives-LEM (C1-Ω (λ f i → ap f (c i)))

    Problem-1↔I-contractible : Problem-1 ↔ ((i : I) → i ≡ p)
    Problem-1↔I-contractible =
      (λ φ → LEM→I-contractible (Problem-1→LEM φ)) ,
      (λ c → LEM→Problem-1 (I-contractible→LEM c))

    Problem-2↔I-contractible : Problem-2 ↔ ((i : I) → i ≡ p)
    Problem-2↔I-contractible =
      (λ φ → LEM→I-contractible (Problem-2→LEM φ)) ,
      (λ c → LEM→Problem-2 (I-contractible→LEM c))
