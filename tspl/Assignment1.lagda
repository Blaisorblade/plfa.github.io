---
title     : "Assignment1: TSPL Assignment 1"
layout    : page
permalink : /Assignment1/
---

\begin{code}
module Assignment1 where
\end{code}

## YOUR NAME AND EMAIL GOES HERE

## Introduction

<!-- This assignment is due **1pm Friday 26 April**. -->

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises without a label are optional, and may be done if you want
some extra practice.

<!-- Submit your homework using the "submit" command. -->
Please ensure your files execute correctly under Agda!

## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm;
  ≤-refl; ≤-trans; ≤-antisym; ≤-total; +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
open import plfa.Relations using (_<_; z<s; s<s; zero; suc; even; odd; e+e≡e)
\end{code}

## Naturals

#### Exercise `seven` {#seven}

Write out `7` in longhand.


#### Exercise `+-example` {#plus-example}

Compute `3 + 4`, writing out your reasoning as a chain of equations.

\begin{code}
_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc (suc (1 + 4))
  ≡⟨⟩
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    suc (suc (suc 4))
  ≡⟨⟩
    7
  ∎
-- Your code goes here
\end{code}

#### Exercise `*-example` {#times-example}

Compute `3 * 4`, writing out your reasoning as a chain of equations.

\begin{code}
-- Your code goes here
_ : 3 * 4 ≡ 12
_ =
  begin
    3 * 4
  ≡⟨⟩    -- inductive case
    4 + (2 * 4)
  ≡⟨⟩    -- inductive case
    4 + (4 + (1 * 4))
  ≡⟨⟩    -- inductive case
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩    -- base
    4 + (4 + (4 + 0))
  ≡⟨⟩    -- simplify
    12
  ∎
\end{code}

#### Exercise `_^_` (recommended) {#power}

Define exponentiation, which is given by the following equations.

    n ^ 0        =  1
    n ^ (1 + m)  =  n * (n ^ m)

Check that `3 ^ 4` is `81`.

\begin{code}
_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ suc m = n * (n ^ m)

_ : 3 ^ 4 ≡ 81
_ = refl
\end{code}

#### Exercise `∸-examples` (recommended) {#monus-examples}

Compute `5 ∸ 3` and `3 ∸ 5`, writing out your reasoning as a chain of equations.


#### Exercise `Bin` (stretch) {#Bin}

A more efficient representation of natural numbers uses a binary
rather than a unary system.  We represent a number as a bitstring.
\begin{code}
data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin
\end{code}
For instance, the bitstring

    1011

standing for the number eleven is encoded, right to left, as

    x1 x1 x0 x1 nil

Representations are not unique due to leading zeros.
Hence, eleven is also represented by `001011`, encoded as

    x1 x1 x0 x1 x0 x0 nil

Define a function

    inc : Bin → Bin

that converts a bitstring to the bitstring for the next higher
number.  For example, since `1100` encodes twelve, we should have

    inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil

Confirm that this gives the correct answer for the bitstrings
encoding zero through four.

Using the above, define a pair of functions to convert
between the two representations.

    to   : ℕ → Bin
    from : Bin → ℕ

For the former, choose the bitstring to have no leading zeros if it
represents a positive natural, and represent zero by `x0 nil`.
Confirm that these both give the correct answer for zero through four.

\begin{code}
inc : Bin → Bin
inc nil = x1 nil
inc (x0 b) = x1 b
inc (x1 b) = x0 (inc b)

b0 = x0 nil
b1 = x1 nil
b2 = x0 x1 nil
b3 = x1 x1 nil
b4 = x0 x0 x1 nil

_ : inc b0 ≡ b1
_ = refl

_ : inc b1 ≡ b2
_ = refl

_ : inc b2 ≡ b3
_ = refl

_ : inc b3 ≡ b4
_ = refl

to : ℕ → Bin
to 0 = x0 nil
to (suc n) = inc (to n)

from : Bin → ℕ
from nil = 0
from (x0 b) = from b + from b
from (x1 b) = suc (from b + from b)

open import Data.List
open import Data.List.All
_ : All (λ n → n ≡ from (to n)) (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
_ = refl ∷ refl ∷ refl ∷ refl ∷ refl ∷ []
\end{code}

## Induction

#### Exercise `operators` {#operators}

Give another example of a pair of operators that have an identity
and are associative, commutative, and distribute over one another.

Give an example of an operator that has an identity and is
associative but is not commutative.


#### Exercise `finite-+-assoc` (stretch) {#finite-plus-assoc}

Write out what is known about associativity of addition on each of the first four
days using a finite story of creation, as
[earlier][plfa.Naturals#finite-creation]


#### Exercise `+-swap` (recommended) {#plus-swap} 

Show

    m + (n + p) ≡ n + (m + p)

for all naturals `m`, `n`, and `p`. No induction is needed,
just apply the previous results which show addition
is associative and commutative.  You may need to use
the following function from the standard library:

    sym : ∀ {m n : ℕ} → m ≡ n → n ≡ m


#### Exercise `*-distrib-+` (recommended) {#times-distrib-plus}

Show multiplication distributes over addition, that is,

    (m + n) * p ≡ m * p + n * p

for all naturals `m`, `n`, and `p`.

#### Exercise `*-assoc` (recommended) {#times-assoc}

Show multiplication is associative, that is,

    (m * n) * p ≡ m * (n * p)

for all naturals `m`, `n`, and `p`.

#### Exercise `*-comm` {#times-comm}

Show multiplication is commutative, that is,

    m * n ≡ n * m

for all naturals `m` and `n`.  As with commutativity of addition,
you will need to formulate and prove suitable lemmas.

#### Exercise `0∸n≡0` {#zero-monus}

Show

    zero ∸ n ≡ zero

for all naturals `n`. Did your proof require induction?

#### Exercise `∸-+-assoc` {#monus-plus-assoc}

Show that monus associates with addition, that is,

    m ∸ n ∸ p ≡ m ∸ (n + p)

for all naturals `m`, `n`, and `p`.

#### Exercise `Bin-laws` (stretch) {#Bin-laws}

Recall that 
Exercise [Bin][plfa.Naturals#Bin]
defines a datatype `Bin` of bitstrings representing natural numbers
and asks you to define functions

    inc   : Bin → Bin
    to    : ℕ → Bin
    from  : Bin → ℕ

Consider the following laws, where `n` ranges over naturals and `x`
over bitstrings.

    from (inc x) ≡ suc (from x)
    to (from n) ≡ n
    from (to x) ≡ x

For each law: if it holds, prove; if not, give a counterexample.


\begin{code}
from-succ-commute : ∀ x → from (inc x) ≡ suc (from x)
from-succ-commute nil = refl
from-succ-commute (x0 x) = refl
from-succ-commute (x1 x) rewrite from-succ-commute x | +-suc (from x) (from x) = refl

open import Relation.Nullary
to-from-id-not : ¬ (to (from nil) ≡ nil)
to-from-id-not ()
-- to-from-id : ∀ n → to (from n) ≡ n
-- to-from-id nil = {!!}
-- to-from-id (x0 n) = {!!}
-- to-from-id (x1 n) = {!!}

from-to-id : ∀ x → from (to x) ≡ x
from-to-id zero = refl
from-to-id (suc x) rewrite from-succ-commute (to x) | from-to-id x = refl
\end{code}
## Relations


#### Exercise `orderings` {#orderings}

Give an example of a preorder that is not a partial order.

Give an example of a partial order that is not a preorder.


#### Exercise `≤-antisym-cases` {#leq-antisym-cases} 

The above proof omits cases where one argument is `z≤n` and one
argument is `s≤s`.  Why is it ok to omit them?


#### Exercise `*-mono-≤` (stretch)

Show that multiplication is monotonic with regard to inequality.


#### Exercise `<-trans` (recommended) {#less-trans}

Show that strict inequality is transitive.

#### Exercise `trichotomy` {#trichotomy}

Show that strict inequality satisfies a weak version of trichotomy, in
the sense that for any `m` and `n` that one of the following holds:
  * `m < n`,
  * `m ≡ n`, or
  * `m > n`
Define `m > n` to be the same as `n < m`.
You will need a suitable data declaration,
similar to that used for totality.
(We will show that the three cases are exclusive after we introduce
[negation][plfa.Negation].)

#### Exercise `+-mono-<` {#plus-mono-less}

Show that addition is monotonic with respect to strict inequality.
As with inequality, some additional definitions may be required.

#### Exercise `≤-iff-<` (recommended) {#leq-iff-less}

Show that `suc m ≤ n` implies `m < n`, and conversely.

#### Exercise `<-trans-revisited` {#less-trans-revisited}

Give an alternative proof that strict inequality is transitive,
using the relating between strict inequality and inequality and
the fact that inequality is transitive.

#### Exercise `o+o≡e` (stretch) {#odd-plus-odd}

Show that the sum of two odd numbers is even.
\begin{code}
o+o≡e : ∀ {m n : ℕ}
  → odd m
  → odd n
    ------------
  → even (m + n)
o+o≡e {suc m} {suc n} (suc om) (suc on) rewrite +-suc m n = suc (suc (e+e≡e om on))
\end{code}

#### Exercise `Bin-predicates` (stretch) {#Bin-predicates}

Recall that 
Exercise [Bin][plfa.Naturals#Bin]
defines a datatype `Bin` of bitstrings representing natural numbers.
Representations are not unique due to leading zeros.
Hence, eleven may be represented by both of the following

    x1 x1 x0 x1 nil
    x1 x1 x0 x1 x0 x0 nil

Define a predicate

       Can : Bin → Set

over all bitstrings that holds if the bitstring is canonical, meaning
it has no leading zeros; the first representation of eleven above is
canonical, and the second is not.  To define it, you will need an
auxiliary predicate

    One : Bin → Set

that holds only if the bistring has a leading one.  A bitstring is
canonical if it has a leading one (representing a positive number) or
if it consists of a single zero (representing zero).

Show that increment preserves canonical bitstrings.

    Can x
    ------------
    Can (inc x)

Show that converting a natural to a bitstring always yields a
canonical bitstring.

    ----------
    Can (to n)

Show that converting a canonical bitstring to a natural
and back is the identity.

    Can x
    ---------------
    to (from x) ≡ x

\end{code}
(Hint: For each of these, you may first need to prove related
properties of `One`.)

\begin{code}
data One : Bin → Set where
  ox1nil : One (x1 nil)
  ox0 : ∀ {x} → (ox : One x) → One (x0 x)
  ox1 : ∀ {x} → (ox : One x) → One (x1 x)

data Can : Bin → Set where
  c1 : ∀ {x} → (ox : One x) → Can x
  cx0 : Can (x0 nil)

inc-one-preserve : ∀ x → One x → One (inc x)
inc-one-preserve .(x1 nil) ox1nil = ox0 ox1nil
inc-one-preserve .(x0 _) (ox0 ox) = ox1 ox
inc-one-preserve .(x1 _) (ox1 ox) = ox0 (inc-one-preserve _ ox)

inc-can-preserve : ∀ x → Can x → Can (inc x)
inc-can-preserve x (c1 cx) = c1 (inc-one-preserve x cx)
inc-can-preserve .(x0 nil) cx0 = c1 ox1nil

can-to : ∀ n → Can (to n)
can-to zero = cx0
can-to (suc n) = inc-can-preserve (to n) (can-to n)

_b+_ : Bin → Bin → Bin
nil b+ y = y
x b+ nil = x
-- (x0 x) b+ nil = x0 x
(x0 x) b+ (x0 y) = x0 (x b+ y)
(x0 x) b+ (x1 y) = x1 (x b+ y)
-- (x1 x) b+ nil = x1 x
(x1 x) b+ (x0 y) = x1 (x b+ y)
(x1 x) b+ (x1 y) = x0 inc (x b+ y)

b+-double : ∀ x → One x → x b+ x ≡ x0 x
b+-double .(x1 nil) ox1nil = refl
b+-double (x0 x) (ox0 ox) rewrite b+-double x ox = refl
b+-double (x1 x) (ox1 ox) rewrite b+-double x ox = refl
-- b+-double : ∀ x → x b+ x ≡ x0 x
-- b+-double nil = {!!}
-- b+-double (x0 x) rewrite b+-double x = refl
-- b+-double (x1 x) rewrite b+-double x = refl

one-b0-identity-left : ∀ x → One x → (x0 nil) b+ x ≡ x
one-b0-identity-left .(x1 nil) ox1nil = refl
one-b0-identity-left .(x0 _) (ox0 ox) = refl
one-b0-identity-left .(x1 _) (ox1 ox) = refl

can-b0-identity-left : ∀ x → Can x → (x0 nil) b+ x ≡ x
can-b0-identity-left x (c1 cx) = one-b0-identity-left x cx
can-b0-identity-left .(x0 nil) cx0 = refl

one-b0-identity-right' : ∀ x → x b+ nil ≡ x
one-b0-identity-right' nil = refl
one-b0-identity-right' (x0 x) = refl
one-b0-identity-right' (x1 x) = refl

one-b0-identity-right : ∀ x → One x → x b+ (x0 nil) ≡ x
one-b0-identity-right .(x1 nil) ox1nil = refl
one-b0-identity-right (x0 x) (ox0 ox) = cong x0_ (one-b0-identity-right' x)
one-b0-identity-right (x1 x) (ox1 ox) = cong x1_ (one-b0-identity-right' x)

can-b0-identity-right : ∀ x → Can x → x b+ (x0 nil) ≡ x
can-b0-identity-right x (c1 ox) = one-b0-identity-right x ox
can-b0-identity-right .(x0 nil) cx0 = refl

one-1-b+-inc : ∀ x → One x → (x1 nil) b+ x ≡ inc x
one-1-b+-inc .(x1 nil) ox1nil = refl
one-1-b+-inc .(x0 _) (ox0 ox) = refl
one-1-b+-inc .(x1 _) (ox1 ox) = refl

one-2-b+-inc : ∀ x → One x → (x0 (x1 nil)) b+ x ≡ inc ((x1 nil) b+ x)
one-2-b+-inc .(x1 nil) ox1nil = refl
one-2-b+-inc .(x0 _) (ox0 ox) rewrite one-1-b+-inc _ ox = refl
one-2-b+-inc .(x1 _) (ox1 ox) rewrite one-1-b+-inc _ ox = refl

one-b+-inc-l : ∀ x y → One x → One y → inc x b+ y ≡ inc (x b+ y)
one-b+-inc-l .(x1 nil) y ox1nil oy = one-2-b+-inc y oy
-- one-b+-inc-l .(x1 nil) (x0 y) ox1nil (ox0 oy) rewrite one-1-b+-inc y oy = refl
-- one-b+-inc-l .(x1 nil) (x1 y) ox1nil oy = {!!}
one-b+-inc-l .(x0 _) y (ox0 ox) oy = {!!}
one-b+-inc-l .(x1 _) y (ox1 ox) oy = {!!}

can-b+-inc-l : ∀ x y → Can x → Can y → inc x b+ y ≡ inc (x b+ y)
can-b+-inc-l x y (c1 ox) (c1 oy) = one-b+-inc-l x y ox oy
can-b+-inc-l x .(x0 nil) (c1 ox) cx0
  rewrite one-b0-identity-right (inc x) (inc-one-preserve _ ox)
  | one-b0-identity-right x ox = refl
can-b+-inc-l .(x0 nil) y cx0 (c1 oy)
  rewrite one-b0-identity-left y oy = one-1-b+-inc y oy
can-b+-inc-l .(x0 nil) .(x0 nil) cx0 cx0 = refl
-- one-b+-inc-l (x0 nil) y ? ox
--
-- can-b0-identity-right (inc x) (inc-can-preserve

to-+-hom : ∀ m n → to (m + n) ≡ (to m b+ to n)
to-+-hom zero n = sym (can-b0-identity-left (to n) (can-to n))
to-+-hom (suc m) n rewrite to-+-hom m n = sym (can-b+-inc-l (to m) (to n) (can-to m) (can-to n))

one-to-from-id : ∀ x → One x → to (from x) ≡ x

to-double-x0 : ∀ x → One x → to (from x + from x) ≡ x0 x
to-double-x0 x ox rewrite to-+-hom (from x) (from x) | one-to-from-id x ox =
  b+-double x ox

to-double-x0' : ∀ x → One x → to (from x + from x) ≡ x0 x
to-double-x0' x ox = {!sym (from-to-id (from (x0 x)))!}
-- rewrite sym (from-to-id (from x))
-- to-double-x0 nil ()
-- to-double-x0 (x0 x) (ox0 ox) = {!to-double-x0 x ox!}
-- to-double-x0 (x1 .nil) ox1nil = refl
-- to-double-x0 (x1 x) (ox1 ox) = {!!}
-- to-double-x0 : ∀ x → One x → to (from x + from x) ≡ x0 x
-- to-double-x0 nil ()
-- to-double-x0 (x0 x) (ox0 ox) = {!to-double-x0 x ox!}
-- to-double-x0 (x1 .nil) ox1nil = refl
-- to-double-x0 (x1 x) (ox1 ox) = {!!}

one-to-from-id .(x1 nil) ox1nil = refl
one-to-from-id (x0 x) (ox0 ox) = {! to-double-x0 x ox !}
one-to-from-id (x1 x) (ox1 ox) rewrite to-double-x0 x ox = refl

can-to-from-id : ∀ x → Can x → to (from x) ≡ x
can-to-from-id x (c1 ox) = one-to-from-id x ox
can-to-from-id .(x0 nil) cx0 = refl
-- to-from-id nil = {!!}
-- to-from-id (x0 n) = {!!}
-- to-from-id (x1 n) = {!!}
\end{code}
