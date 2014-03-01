----
author: Jan Malakhovski
id: 20121219
tags: fp, agda, dependent types, logic
----

# Brutal [Meta]Introduction to Dependent Types in Agda

## Introduction to introduction

Agda doesn't lack tutorials and introductions, there is a whole page of them on the Agda wiki [@agda-tutorials] (for a general documentation list see [@agda-documentation]).
Personally, I recommend:

* Anton Setzer's introduction (works especially very well for those with a logical background, but is easy enough to follow for everyone else too) [@Setzer:interactive-theorem-proving]
* Ana Bove's and Peter Dybjer's introduction [@Bove-Dybjer:deptypes-at-work].
* Ulf Norell's introduction for functional programmers [@Norell:afp08-tutorial].
* Thorsten Altenkirch's lectures [@Altenkirch:computer-aided-formal-reasoning-course].

(This list is not an order, the best practice is to read them (and this page) simultaneously.
By the way, this document is far from finished, but should be pretty useful in its current state.)

Same proposition holds for Coq [@coq-documentation], Idris [@idris-documentation] and, to a lesser extent, for Epigram [@epigram-documentation].

For a general introduction to type theory field look no further than:

* Morten Heine B. Sørensen's and Pawel Urzyczyn's lectures [@Sorensen-Urzyczyn:lectures-on-curry-howard-isomorphism:1998].
* Simon Thompson's book [@Thompson:TTFP].

There's also a number of theoretical books strongly related to the languages listed above:

* The notes of Per Martin-Löf's (the author of the core type theory used by all of Agda, Coq, Idris and Epigram) lectures [@MartinLoef:ITT-Sambin;@MartinLoef:ITT].
* A bit more practical-oriented book by Bengt Nordström et al [@Nordstoem:programming-in-MLTT].

And a number of tutorials which show how to implement a dependently typed language yourself:

* "Simpler Easier" [@augustss:simpler-easier].
* A tutorial by Andrej Bauer [@Bauer:implement-deptypes-1;@Bauer:implement-deptypes-2;@Bauer:implement-deptypes-3].

There's a lot to read already, why another introduction?
Because there is a gap.
Theory is huge and full of subtle details that are mostly ignored in tutorial implementations and hidden in language tutorials (so that unprepared are not scared away).
Which is hardly surprising since the current state of art takes years to implement correctly, and even then some (considerable) problems remain.

Nevertheless, I think it is the hard parts that matter, and I always wanted a tutorial that at least mentioned their existence (well, obviously there is a set of dependently typed problems most people appreciate, e.g. undecidable type inference, but there is still a lot of issues that are not so well-understood).
Moreover, after I stumbled upon some of these lesser known parts of dependently typed programming I started to suspect that hiding them behind the language goodnesses actually makes things _harder_ to understand.
"Dotted patterns" and "unification stuck" error in Agda are perfect examples.
I claim that:

* People find it hard to understand "dotted patterns" exactly because it's hard to explain them above the language abstraction level.
* Explicit access to unification engine is a useful interactive program construction tool.
I did a dozen of proofs I probably couldn't do otherwise by unifying expressions by hand.
As far as I'm aware, no proof checker automates this in a usable way yet.
There is [a proposal](http://code.google.com/p/agda/issues/detail?id=771) with my implementation ideas for `agda2-mode`.

Having said that, this article serves somewhat controversial purposes:

* It is a introduction to Agda, starting as a very basic one, written for those with half-way-through-undergrad-course (read "basic") discrete math, number theory, set theory and Haskell background.
I actually taught this to undergrad students [@Me:itmo-functional-programming-and-proof-checking-course] and it works.
* But it aims not to teach Agda, but to show how dependently typed languages work behind the scenes without actually going behind the scenes (because, as noted above, going behind the scenes takes years).
I'm pretty sure it is possible to write a very similar introduction to Coq, Idris, Epigram or whatever, but Agda works perfectly because of its syntax and heavy unification usage.
* There is also a number of *[italicized comments in brackets]* laying around, usually for those with type theory background. Don't be scared, you can completely ignore them. They give deeper insights if you research on them, though.
* The last two sections contain completely type theoretic stuff. They are the reason I started writing this, but, still, you may ignore them completely if you wish.
* You are expected to understand everything else.
Do exercises and switch to other tutorials when stuck.

Finally, before we start, a disclaimer: I verified my core thoughts about how all this stuff works by reading (parts of) Agda's source code, but still, as Plato's Socrates stated, "I know that I know nothing".

## Slow start

### You want to use Emacs, trust me

There is *agda2-mode* for Emacs. It allows to:

* input funny UNICODE symbols like ℕ or Σ,
* interactively interact with Agda (more on that below).

Installation:

* install `emacs`,
* install everything with `agda` substring from your package manager or `Agda` and `Agda-executable` with `cabal`,
* run `agda-mode setup`.

Running:

* run `emacs`,
* press `C-x C-f FileName RET` (Control+x, Control+f, type "FileName", press Return/Enter key).

Note that you can load [this article in Literate Agda format](../BrutalDepTypes.lagda) directly into Emacs.
This is actually a recommended way to use this text, you can't do exercises in HTML version.

### Syntax

In Agda a module definition always goes first:
\begin{code}
module BrutalDepTypes where
\end{code}

Nested modules and modules with parameters are supported.
One of the most common usages of nested modules is to hide some definitions from the top level namespace:

\begin{code}
module ThrowAwayIntroduction where
\end{code}

Datatypes are written in GADTs-style:
\begin{code}
  data Bool : Set where
    true false : Bool -- Note, we can list constructors of a same type
                      -- by interspersing them with spaces.
    
  -- input for ℕ is \bn,
  -- input for → is \to, but -> is fine too
  -- Naturals.
  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
  
  -- Identity container
  data Id (A : Set) : Set where
    pack : A → Id A
    
  -- input for ⊥ is \bot
  -- Empty type. Absurd. False proposition.
  data ⊥ : Set where
\end{code}
`Set` here means the same thing as kind `*` in Haskell, i.e. a type of types (more on that below).

Agda is a total language.
There is no `undefined`,  all functions are guaranteed to terminate on all possible inputs (if not explicitly stated otherwise by a compiler flag or a function definition itself), which means that `⊥` type is really empty.

Function declarations are very much like in Haskell:
\begin{code}
  -- input for ₀ is \_0, ₁ is \_1 and so on
  idℕ₀ : ℕ → ℕ
  idℕ₀ x = x
\end{code}
except function arguments have their names even in type expressions:
\begin{code}
  -- Note, argument's name in a type might differ from a name used in pattern-matching
  idℕ₁ : (n : ℕ) → ℕ
  idℕ₁ x = x -- this `x` refers to the same argument as `n` in the type
\end{code}
with `idℕ₀`'s definition being a syntax sugar for:
\begin{code}
  idℕ₂ : (_ : ℕ) → ℕ
  idℕ₂ x = x
\end{code}
where the underscore means "I don't care about the name", just like in Haskell.

Dependent types allow type expressions after an arrow to depend on expressions before the arrow,
this is used to type polymorphic functions:
\begin{code}
  id₀ : (A : Set) → A → A
  id₀ _ a = a
\end{code}
Note that this time `A` in the type cannot be changed into an underscore, but it's fine to ignore this name in pattern matching.

Pattern matching looks as usual:
\begin{code}
  not : Bool → Bool
  not true  = false
  not false = true
\end{code}
except if you make an error in a constructor name:
\begin{code}
  not₀ : Bool → Bool
  not₀ true  = false
  not₀ fals  = true
\end{code}
Agda will say nothing.
This might be critical sometimes:
\begin{spec}
  data Three : Set where
    COne CTwo CThree : Three

  three2ℕ : Three → ℕ
  three2ℕ COne = zero
  three2ℕ Ctwo = succ zero
  three2ℕ _    = succ (succ zero) -- intersects with the previous clause
\end{spec}

Finally, Agda supports implicit arguments:
\begin{code}
  id : {A : Set} → A → A
  id a = a

  idTest₀ : ℕ → ℕ
  idTest₀ = id
\end{code}
Values of implicit arguments are derived from other arguments' values and types by solving type equations (more on them below).
You don't have to apply them or pattern match on them explicitly, but you still can if you wish:
\begin{code}
  -- positional:
  id₁ : {A : Set} → A → A
  id₁ {A} a = a

  idTest₁ : ℕ → ℕ
  idTest₁ = id {ℕ}

  -- named:
  const₀ : {A : Set} {B : Set} → A → B → A
  const₀ {B = _} a _ = a

  constTest₀ : ℕ → ℕ → ℕ
  constTest₀ = const₀ {A = ℕ} {B = ℕ}
\end{code}

*[It's important to note that no proof search is ever done.
Implicit arguments are completely orthogonal to computational aspect of a program, being implicit doesn't imply anything else.
Implicit variables are not treated any way special, they are not type-erased any way differently than others.
They are just a kind of syntax sugar assisted by equation solving.]*

It's allowed to skip arrows between arguments in parentheses or braces:
\begin{code}
  id₃ : {A : Set} (a : A) → A
  id₃ a = a
\end{code}
and to intersperse names of values of the same type by spaces inside parentheses and braces:
\begin{code}
  const : {A B : Set} → A → B → A
  const a _ = a
\end{code}

What makes Agda's syntax so confusing is the usage of underscore.
In Haskell "I don't care about the name" is the only meaning for it, in Agda there are another two and a half.
The first one being "guess the value yourself":
\begin{code}
  idTest₃ : ℕ → ℕ
  idTest₃ = id₀ _
\end{code}
which works exactly the same way as implicit arguments.

Or, to be more precise, it is the implicit arguments that work like arguments implicitly applied with underscores, except Agda does this once for each function definition, not for each call.

The another half being "guess the type yourself":
\begin{code}
  unpack₀ : {A : _} → Id A → A
  unpack₀ (pack a) = a
\end{code}
which has a special `∀` syntax sugar:
\begin{code}
  -- input for ∀ is \all or \forall
  unpack : ∀ {A} → Id A → A
  unpack (pack a) = a

  -- explicit argument version:
  unpack₁ : ∀ A → Id A → A
  unpack₁ _ (pack a) = a
\end{code}

`∀` extends to the right up to the first arrow:
\begin{code}
  unpack₂ : ∀ {A B} → Id A → Id B → A
  unpack₂ (pack a) _ = a

  unpack₃ : ∀ {A} (_ : Id A) {B} → Id B → A
  unpack₃ (pack a) _ = a
\end{code}

Datatype syntax assumes implicit `∀` when there is no type specified:
\begin{code}
  data ForAllId A (B : Id A) : Set where
\end{code}

It is important to note that Agda's `∀` is quite different from Haskell's `∀` (`forall`).
When we say `∀ n` in Agda it's perfectly normal for `n : ℕ` to be inferred, but in Haskell `∀ n` always means `{n : Set}`, *[i.e. Haskell's `∀` is an implicit (Hindley-Milner) version of second order universal quantifier while in Agda it's just a syntax sugar]*.

Syntax misinterpreting becomes a huge problem when working with more than one universe level (more on that below).
It is important to train yourself to desugar type expressions subconsciously (by doing in consciously at first).
It will save hours of your time later.
For instance, `∀ {A} → Id A → A` means `{A : _} → (_ : Id A) → A` (where the last `→ A` should be interpreted as `→ (_ : A)`), i.e. the first `A` is a variable name, while the other expressions are types.

Finally, the last meaning of an underscore is to mark arguments' places in function names for the `MixFix` parser, i.e. an underscore in a function name marks the place where the arguments goes:
\begin{code}
  if_then_else_ : {A : Set} → Bool → A → A → A
  if true then a else _ = a
  if false then _ else b = b

  -- Are two ℕs equal?
  _=ℕ?_ : ℕ → ℕ → Bool
  zero   =ℕ? zero   = true
  zero   =ℕ? succ m = false
  succ m =ℕ? zero   = false
  succ n =ℕ? succ m = n =ℕ? m

  -- Sum for ℕ.
  infix 6 _+_
  _+_ : ℕ → ℕ → ℕ
  zero   + n = n
  succ n + m = succ (n + m)

  ifthenelseTest₀ : ℕ
  ifthenelseTest₀ = if (zero + succ zero) =ℕ? zero
    then zero
    else succ (succ zero)

  -- Lists
  data List (A : Set) : Set where
    []  : List A
    _∷_ : A → List A → List A

  [_] : {A : Set} → A → List A
  [ a ] = a ∷ []
  
  listTest₁ : List ℕ
  listTest₁ = []

  listTest₂ : List ℕ
  listTest₂ = zero ∷ (zero ∷ (succ zero ∷ []))
\end{code}
Note the fixity declaration `infix` which has the same meaning as in Haskell.
We didn't write `infixl` for a reason.
With declared associativity Agda would not print redundant parentheses, which is good in general, but would somewhat complicate explanation of a several things below.

There is a `where` construct, just like in Haskell:
\begin{code}
  ifthenelseTest₁ : ℕ
  ifthenelseTest₁ = if (zero + succ zero) =ℕ? zero
    then zero
    else x
    where
    x = succ (succ zero)
\end{code}

While pattern matching, there is a special case when a type we are trying to pattern match on is obviously (*[type inhabitance problem is undecidable in a general case]*) empty.
This special case is called an "absurd pattern":
\begin{code}
  -- ⊥ implies anything.
  ⊥-elim : {A : Set} → ⊥ → A
  ⊥-elim ()
\end{code}
which allows you to skip a right-hand side of a definition.

You can bind variables like that still:
\begin{code}
  -- Absurd implies anything, take two.
  ⊥-elim₀ : {A : Set} → ⊥ → A
  ⊥-elim₀ x = ⊥-elim x
\end{code}

Agda has records, which work very much like `newtype` declarations in Haskell, i.e. they are datatypes with a single constructor that is not stored.

\begin{code}
  record Pair (A B : Set) : Set where
    field
      first  : A
      second : B

  getFirst : ∀ {A B} → Pair A B → A
  getFirst = Pair.first
\end{code}

Note, however, that to prevent name clashes record definition generates a module with field extractors inside.

There is a convention to define a type with one element as a record with no fields:
\begin{code}
  -- input for ⊤ is \top
  -- One element type. Record without fields. True proposition.
  record ⊤ : Set where

  tt : ⊤
  tt = record {}
\end{code}

A special thing about this convention is that an argument of an empty record type automatically gets the value `record {}` when applied implicitly or with underscore.

Lastly, Agda uses oversimplified lexer that splits tokens by spaces, parentheses, and braces.
For instance (note the name of the variable binding):
\begin{code}
  -- input for ‵ is \`
  -- input for ′ is \'
  ⊥-elim‵′ : {A : Set} → ⊥ → A
  ⊥-elim‵′ ∀x:⊥→-- = ⊥-elim ∀x:⊥→--
\end{code}
is totally fine. Also note that `--` doesn't generate a comment here.

### The magic of dependent types

Let's define the division by two:
\begin{code}
  div2 : ℕ → ℕ
  div2 zero = zero
  div2 (succ (succ n)) = succ (div2 n)
\end{code}
the problem with this definition is that Agda is total and we have to extend this function for odd numbers
\begin{code}
  div2 (succ zero) = {!check me!}
\end{code}
by changing `{!check me!}` into some term, most common choice being `zero`.

Suppose now, we know that inputs to `div2` are always even and we don't want to extend `div2` for the `succ zero` case.
How do we constrain `div2` to even naturals only?
With a predicate! That is, `even` predicate:
\begin{code}
  even : ℕ → Set
  even zero = ⊤
  even (succ zero) = ⊥
  even (succ (succ n)) = even n
\end{code}
which returns `⊤` with with a trivial proof `tt` when argument is even and empty `⊥` then the argument is odd.

Now the definition of `div2e` constrained to even naturals only becomes:
\begin{code}
  div2e : (n : ℕ) → even n → ℕ -- Note, we have to give a name `n` to the first argument here
  div2e zero p = zero
  div2e (succ zero) ()
  div2e (succ (succ y)) p = succ (div2e y p) -- Note, a proof of `even (succ (succ n))` translates
                                             -- to a proof of `even n` by the definition of `even`.
\end{code}

When programming with dependent types, a predicate on `A` becomes a function from `A` to types, i.e. `A → Set`.
If `a : A` satisfies the predicate `P : A → Set` then the function `P` returns a type with each element being a proof of `P a`, in a case `a` doesn't satisfy `P` it returns an empty type.

The magic of dependent types makes the type of the second argument of `div2e` change every time we pattern match on the first argument `n`.
From the callee side, if the first argument is odd then the second argument would get `⊥` type sometime (after a number of recursive calls) enabling the use of an absurd pattern.
From the caller side, we are not able to call the function with an odd `n`, since we have no means to construct a value for the second argument in this case.

### Type families and Unification

There is another way to define "even" predicate. This time with a datatype _indexed_ by ℕ:
\begin{code}
  data Even : ℕ → Set where
    ezero  : Even zero
    e2succ : {n : ℕ} → Even n → Even (succ (succ n))

  twoIsEven : Even (succ (succ zero))
  twoIsEven = e2succ ezero
\end{code}

`Even : ℕ → Set` is a family of types indexed by ℕ and obeying the following rules:

* `Even zero` has one element `ezero`.
* For any given `n` type `Even (succ (succ n))` has one element if `Even n` is nonempty.
* There are no other elements.

Compare this to `even : ℕ → Set` definition translation:

* There is a trivial proof that `zero` has property `even`.
* There is no proof that `succ zero` has property `even`.
* If `n` has property `even` then so has `succ (succ n)`.

In other words, the difference is that `Even : ℕ → Set` _constructs_ a type whereas `even : ℕ → Set` _returns_ a type when applied to an element of `ℕ`.

The proof that two is even `even (succ (succ zero))` literally says "two is even because it has a trivial proof", whereas the proof that two is even `twoIsEven` says "two is even because zero is even and two is the successor of the successor of zero".

`Even` datatype allows us to define another non-extended division by two for `ℕ`:
\begin{code}
  div2E : (n : ℕ) → Even n → ℕ
  div2E zero ezero = zero
  div2E (succ zero) ()
  div2E (succ (succ n)) (e2succ stilleven) = succ (div2E n stilleven) -- Compare this case to div2e.
\end{code}
Note, there is no case for `div2E zero (e2succ x)` since `e2succ x` has the wrong type, there is no such constructor in `Even zero`.
For the `succ zero` case the type of the second argument is not `⊥`, but is empty.
How do we know that?
Unification!

Unification is the most important (at least with pattern matching on inductive datatypes involved) and easily forgotten aspect of dependently typed programming.
Given two terms `M` and `N` unification tries to find a substitution `s` such that using `s` on `M` gives the same result as using `s` on `N`.
The precise algorithm definition is pretty long, but the idea is simple: to decide if two expressions could be unified we

* reduce them as much as possible,
* then traverse their spines until we
    * hit an obvious difference between them,
    * find a place where we can not decide for sure,
    * or successfully finish the traversal generating a substitution `s`.

For instance:

* To unify [`(succ a) + b` with `succ (c + d)`] we need reduce both of them, now we need to unify [`succ (a + b)` with `succ (c + d)`], which means that we need to unify [`a + b` with `c + d`], which means that we need to unify [`a` with `c`] and [`b` with `d`], which means that [`a = c`, `b = d`].
* On the other hand, `succ a` can not be unified with `zero` for any `a`, and `succ b` can not be unified with `b` for any `b`.
* We don't know if it's possible to unify `foo n` with `zero` for some unknown function `foo` (it might or might not reduce to `zero` for some `n`).
    
In the code above `succ zero` doesn't unify with any of the `Even` constructors' indexes [`zero`, `succ (succ n)`] which makes this type obviously empty by its definition.

*[Refer to "The view from the left" paper by McBride and McKinna [@McBride-McKinna:the-view-from-the-left] for more details on pattern matching with type families.]*

### More type families and less Unification

In datatype declarations things before a `:` are called "parameters", things after the colon but before a `Set` are called "indexes".

There is a famous datatype involving both of them:
\begin{code}
  data Vec (A : Set) : ℕ → Set where
    []  : Vec A zero
    _∷_ : ∀ {n} → A → Vec A n → Vec A (succ n)
\end{code}

`Vec A n` is a vector of values of type `A` and length `n`, `Vec` has a parameter of type `Set` and is indexed by values of type `ℕ`.
Compare this definition to the definition of `List` and `Even`.
Note also, that Agda tolerates different datatypes with constructors of the same name (see below for how this is resolved).

We can not omit the clause for an `[]` case in a function which takes a head of a `List`:
\begin{code}
  head₀ : ∀ {A} → List A → A
  head₀ []       = {!check me!}
  head₀ (a ∷ as) = a
\end{code}
but we have nothing to write in place of `{!check me!}` there (if we want to be total).

On the other hand, there is no `[]` constructor in a `Vec A (succ n)` type:
\begin{code}
  head : ∀ {A n} → Vec A (succ n) → A
  head (a ∷ as) = a
\end{code}
Note that there are no absurd patterns here, `Vec A (succ n)` is inhabited, it just happens that there is no `[]` in there.

By the way, the `Vec` type is famous for a concatenation function:
\begin{code}
  -- Concatenation for `List`s
  _++_ : ∀ {A} → List A → List A → List A
  []       ++ bs = bs
  (a ∷ as) ++ bs = a ∷ (as ++ bs)

  -- Concatenation for `Vec`tors
  -- The length of a concatenation is the sum of lengths of arguments and is available in types.
  _++v_ : ∀ {A n m} → Vec A n → Vec A m → Vec A (n + m)
  []       ++v bs = bs
  (a ∷ as) ++v bs = a ∷ (as ++v bs)
\end{code}
Compare `_+_`, `_++_`, and `_++v_` definitions.

Why does the definition of `_++v_` work?
Because we defined `_+_` this way!
In the first clause of `_++v_` the type of `[]` gives `n = zero` by unification, `zero + m = m` by the `_+_` definition, `bs : Vec A m`.
Similarly, in the second clause `n = succ n0`, `as : Vec A n0`, `(succ n0) + m = succ (n0 + m)` by the `_+_` definition, `a ∷ (as ++ bs) : succ (n0 + m)`.

### Dotted patterns and Unification

Let's define a substraction:
\begin{code}
  infix 6 _-_
  _-_ : ℕ → ℕ → ℕ
  zero   - _      = zero
  succ n - zero   = succ n
  succ n - succ m = n - m
\end{code}
Note that `n - m = zero` for `m > n`.

Let us get rid of this `(succ n) - zero` case with `_≤_` relation:
\begin{code}
  data _≤_ : ℕ → ℕ → Set where
    z≤n : ∀ {n}           → zero ≤ n
    s≤s : ∀ {n m} → n ≤ m → succ n ≤ succ m
\end{code}

We are now able to write a substraction that is not extended for `m > n`.
\begin{code}
  sub₀ : (n m : ℕ) → m ≤ n → ℕ
  sub₀ n zero (z≤n .{n}) = n
  sub₀ .(succ n) .(succ m) (s≤s {m} {n} y) = sub₀ n m y
\end{code}

Note the dots, these are called "dotted patterns".
Ignore them for a second.

Consider the case
`sub₀ n zero (z≤n {k})`.
The type of the third argument is `zero ≤ n`.
The type of `z≤n {k}` is `zero ≤ k`.
Unification of these two types gives [`k = n`, `m = zero`].
After a substitution we get
`sub₀ n zero (z≤n {n})`.
Which of the `n`s we want to bind/match on?
In the code above we say "on the first" and place a dot before the second occurrence to mark this intention.
Dotted pattern says "do not match on this, it is the only possible value" to the compiler.

The second clause is
`sub₀ n m (s≤s {n'} {m'} y)`.
The type of the third argument is `m ≤ n`.
The type of `s≤s {n'} {m'} y` is `succ n' ≤ succ m'`.
This gives [`n = succ n'`, `m = succ m'`].
This time we decided to match on `n'` and `m'`.

Rewritten with a `case` construct from Haskell (Agda doesn't have `case`, see below) the code above becomes (in pseudo-Haskell):
\begin{spec}
  sub₀ n m even = case even of
    z≤n {k}     -> case m of -- [`k = n`, `m = zero`]
      zero    -> n
      succ m' -> __IMPOSSIBLE__  -- since `m = zero` doesn't merge with `m = succ m'`
    s≤s n' m' y -> sub₀ n' m' y  -- [`n = succ n'`, `m = succ n'`]
\end{spec}

Where `__IMPOSSIBLE__` is just like an `undefined` but is never executed.

Note, that we have [`k = n`, `m = zero`] in the first case for even.
This means we can dot the first usage of `zero` to optimize the match on `m` away: 
\begin{code}
  sub₁ : (n m : ℕ) → m ≤ n → ℕ
  sub₁ n .zero (z≤n .{n}) = n
  sub₁ .(succ n) .(succ m) (s≤s {m} {n} y) = sub₁ n m y
\end{code}
which translates to
\begin{spec}
sub₁ n m even = case even of
  z≤n {k}     -> n
  s≤s n' m' y -> sub₁ n' m' y
\end{spec}

Finally, we can also rewrite `sub` to match on the first two arguments (usual, common sense definition):
\begin{code}
  sub : (n m : ℕ) → m ≤ n → ℕ
  sub n zero (z≤n .{n}) = n
  sub (succ n) (succ m) (s≤s .{m} .{n} y) = sub n m y
\end{code}
which translates into the following:
\begin{spec}
  sub n m even = case m of
    zero   -> case even of
        z≤n {k}       -> n
        s≤s {k} {l} y -> __IMPOSSIBLE__ -- since `zero` (`m`) can't be unified
                                        -- with `succ k`
    succ m' -> case n of
      zero   -> case even of
        z≤n {k}       -> __IMPOSSIBLE__ -- since `succ m'` (`m`) can't be unified
                                        -- with `zero`
        s≤s {k} {l} y -> __IMPOSSIBLE__ -- since `zero` (`n`) can't be unified
                                        -- with `succ l`
      succ n' -> case even of
        z≤n {k}       -> __IMPOSSIBLE__ -- since `succ n'` (`n`) can't be unified
                                        -- with `zero`
        s≤s {k} {l} y -> sub n' m' y
\end{spec}

**Exercise.** Write out the unification constraints for the pseudo-Haskell translation above.

Note, that `sub n m p` computes the difference between `n` and `m` while `sub₀` and `sub₁` extract it from the proof `p`.
Note also, that for `sub n zero` the third argument is always `z≤n {n}`, so we would like to write
\begin{spec}
  sub₂ : (n m : ℕ) → m ≤ n → ℕ
  sub₂ n zero .(z≤n {n}) = n
  sub₂ (succ n) (succ m) (s≤s .{m} .{n} y) = sub₂ n m y
\end{spec}
but Agda doesn't allow this. See below for why.

We can write
\begin{code}
  sub₃ : (n m : ℕ) → m ≤ n → ℕ
  sub₃ n zero _ = n
  sub₃ (succ n) (succ m) (s≤s .{m} .{n} y) = sub₃ n m y
\end{code}
still.

**Exercise.** Translate the following definition into pseudo-Haskell with unification constraints:
\begin{code}
  sub₄ : (n m : ℕ) → m ≤ n → ℕ
  sub₄ n zero (z≤n .{n}) = n
  sub₄ (succ .n) (succ .m) (s≤s {m} {n} y) = sub₄ n m y
\end{code}

The moral is that **dotted patterns are inlined unification constraints**.
This is why we couldn't dot `z≤n {n}` in the first clause of `sub₂`, Agda didn't generate such a constraint (it could, have it tried a bit harder).

### Propositional equality and Unification

We shall now define the most useful type family, that is, Martin-Löf's equivalence (values only version, though):
\begin{code}
  -- ≡ is \==
  infix 4 _≡_
  data _≡_ {A : Set} (x : A) : A → Set where
    refl : x ≡ x
\end{code}

For `x y : A` the type `x ≡ y` has exactly one constructor `refl` if `x` and `y` are _convertible_, i.e. there exist such `z` that `z →β✴ x` and `z →β✴ y`, where `→β✴` is "β-reduces in zero or more steps".
By a consequence from a Church-Rosser theorem and strong normalization convertibility can be solved by normalization.
Which means that unification will both check convertibility and fill in any missing parts.
In other words, `x y : A` the type `x ≡ y` has exactly one constructor `refl` if `x` and `y` unify with each other.

Let's prove some of `_≡_`'s properties:
\begin{code}
  -- _≡_ is symmetric
  sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
  sym refl = refl

  -- transitive
  trans : {A : Set}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
  trans refl refl = refl

  -- and congruent
  cong : {A B : Set} {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
  cong f refl = refl
\end{code}

Consider the case `sym {A} {a} {b} (refl {x = a})`.
Matching on `refl` gives [`b = a`] equation, i.e. the clause actually is `sym {A} {a} .{a} (refl {x = a})` which allows to write `refl` on the right-hand side.
Other proofs are similar.

Note, we can prove `sym` the other way:
\begin{code}
  sym′ : {A : Set}{a b : A} → a ≡ b → b ≡ a
  sym′ {A} .{b} {b} refl = refl
\end{code}

`sym` packs `a` into `refl`. `sym′` packs `b`. "Are these two definitions equal?" is an interesting philosophical question.
(From the Agda's point of view they are.)

Since dotted patterns are just unification constraints, you don't have to dot implicit arguments when you don't bind or match on them.

`_≡_` type family is called "propositional equality".
In Agda's standard library it has a bit more general definition, see below.

### Proving things interactively

With `_≡_` we can finally prove something from basic number theory.
Let's do this interactively.

Our first victim is the associativity of `_+_`.
\begin{code}
  +-assoc₀ : ∀ a b c → (a + b) + c ≡ a + (b + c)
  +-assoc₀ a b c = {!!}
\end{code}

Note a mark `{!!}`.
Anything of the form `{!expr!}` with `expr` being any string (including empty) a _goal_ after a buffer is loaded by agda2-mode.
Typing `{!!}` is quite tedious, so there is a shortcut `?`.
All `?` symbols are automatically transformed into `{!!}` when a buffer is loaded.

Goals appear as green holes in a buffer, pressing special key sequences while in a goal allows to ask Agda questions about and perform actions on a code.
In this document "check me" in a goal means that this goal is not expected to be filled, it's just an example.

Press `C-c C-l` (load) to load and typecheck the buffer.

Placing the cursor in the goal above (the green hole in the text) and pressing `C-c C-c a RET` (case by `a`) gives (ignore changes to the name of a function and "check me"s everywhere):
\begin{code}
  +-assoc₁ : ∀ a b c → (a + b) + c ≡ a + (b + c)
  +-assoc₁ zero b c = {!check me!}
  +-assoc₁ (succ a) b c = {!check me!}
\end{code}
Press `C-c C-,` (goal type and context) while in the goal.
This will show the goal type and the context inside the hole.
Write `refl` in there and press `C-c C-r` (refine), this gives:
\begin{code}
  +-assoc₂ : ∀ a b c → (a + b) + c ≡ a + (b + c)
  +-assoc₂ zero b c = refl
  +-assoc₂ (succ a) b c = {!check me!}
\end{code}
`C-c C-f` (next goal), write `cong succ` there, `C-c C-r`:
\begin{code}
  +-assoc₃ : ∀ a b c → (a + b) + c ≡ a + (b + c)
  +-assoc₃ zero b c = refl
  +-assoc₃ (succ a) b c = cong succ {!check me!}
\end{code}
Next goal, goal type and context, press `C-c C-a` (auto proof search):
\begin{code}
  +-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
  +-assoc zero b c = refl
  +-assoc (succ a) b c = cong succ (+-assoc a b c)
\end{code}
Done.

(In Agda 2.3.2 you have to reload a buffer for proof search to work, it's probably a bug.)

Similarly, we prove
\begin{code}
  lemma-+zero : ∀ a → a + zero ≡ a
  lemma-+zero zero = refl
  lemma-+zero (succ a) = cong succ (lemma-+zero a)

  lemma-+succ : ∀ a b → succ a + b ≡ a + succ b
  lemma-+succ zero b = refl
  lemma-+succ (succ a) b = cong succ (lemma-+succ a b)
\end{code}

The commutativity for `_+_` is not hard to follow too:
\begin{code}
  -- A fun way to write transitivity
  infixr 5 _~_
  _~_ = trans

  +-comm : ∀ a b → a + b ≡ b + a
  +-comm zero b = sym (lemma-+zero b)
  +-comm (succ a) b = cong succ (+-comm a b) ~ lemma-+succ b a
\end{code}

Nice way to "step" through a proof is to wrap some subexpression with `{! !}`, e.g.:
\begin{spec}
  +-comm (succ a) b = cong succ {!(+-comm a b)!} ~ lemma-+succ b a
\end{spec}
and ask for a type, context and inferred type of a goal with `C-c C-l` followed by `C-c C-.`, refine, wrap another subexpression, repeat.
I dream of a better interface for this.

### Solving type equations

The second case of `+-comm` is pretty fun example to infer implicit arguments by hand. Let's do that.
Algorithm is as follows:

* First, expand all implicit arguments and explicit arguments applied with `_` in a term into "metavariables", that is, special meta-level variables not bound anywhere in the program.
* Look at the types of all symbols and construct a system of equations.
For instance, if you see `term1 term2 : D`, `term1 : A → B` and `term2 : C`, add equations `A == C` and `B == D` to the system.
* Solve the system with a help from unification. Two possible results:
    * All the metavariables got their values from the solution. Success.
    * There are some that didn't. This situation is reported to a user as "unsolved metas" type checking result.
      These act like warnings while you are not trying to compile or to type check in a "safe mode".
      In the latter two cases unsolved metas transform into errors.
* Substitute the values of metavariables back into the term.

Applying the first step of the algorithm to a term
\begin{spec}
trans (cong succ (+-comm1 a b)) (lemma-+succ b a)
\end{spec}
gives:
\begin{spec}
trans {ma} {mb} {mc} {md} (cong {me} {mf} {mg} {mh} succ (+-comm a b)) (lemma-+succ b a)
\end{spec}
with `m*` being metavariables.

`a b : ℕ` since `_+_ : ℕ → ℕ → ℕ` in the type of `+comm`.
This gives the following system (with duplicated equations and metavariable applications skipped):
\begin{spec}
trans (cong succ (+-comm a b)) (lemma-+succ b a) : _≡_ {ℕ} (succ a + b) (b + succ a)
trans (cong succ (+-comm a b)) (lemma-+succ b a) : _≡_ {ℕ} (succ (a + b)) (b + succ a) -- after normalization
ma = ℕ
mb = succ (a + b)
md = b + succ a
+-comm a b : _≡_ {ℕ} (a + b) (b + a)
mg = (a + b)
me = ℕ
mh = (b + a)
mf = ℕ
cong succ (+-comm a b) : _≡_ {ℕ} (succ (a + b)) (succ (b + a))
mc = succ (b + a)
lemma-+succ b a : _≡_ {ℕ} (succ b + a) (b + succ a)
lemma-+succ b a : _≡_ {ℕ} (succ (b + a)) (b + succ a) -- after normalization
trans (cong succ (+-comm a b)) (lemma-+succ b a) : _≡_ {ℕ} (succ a + b) (b + succ a)
\end{spec}

The most awesome thing about this is that from Agda's point of view, a goal is just a metavariable of a special kind.
When you ask for a type of a goal with `C-c C-t` or `C-c C-,` Agda prints everything it has for the corresponding metavariable.
Funny things like `?0`, `?1`, and etc in agda2-mode outputs are references to these metavariables.
For instance, in the following:
\begin{code}
  metaVarTest : Vec ℕ (div2 (succ zero)) → ℕ
  metaVarTest = {!check me!}
\end{code}
the type of the goal mentions the name of very first goal metavariable from this article.

By the way, to resolve datatype constructor overloading Agda infers the type for a constructor call expected at the call site, and unifies the inferred type with the types of all possible constructors of the same name.
If there are no matches found, an error is reported.
In case with more than one alternative available, an unsolved meta (for the return type metavariable) is produced.

### Termination checking, well-founded induction

Work in progress.

### Propositional equality exercises

**Exercise.** Define multiplication by induction on the first argument:
\begin{code}
  module Exercise where
    infix 7 _*_
    _*_ : ℕ → ℕ → ℕ
    n * m = {!!}
\end{code}
so that the following proof works:
\begin{code}
    -- Distributivity.
    *+-dist : ∀ a b c → (a + b) * c ≡ a * c + b * c
    *+-dist zero b c = refl
    -- λ is \lambda
    *+-dist (succ a) b c = cong (λ x → c + x) (*+-dist a b c) ~ sym (+-assoc c (a * c) (b * c))
\end{code}

Now, fill in the following goals:
\begin{code}
    *-assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)
    *-assoc zero b c = refl
    *-assoc (succ a) b c = *+-dist b (a * b) c ~ cong {!!} (*-assoc a b c)

    lemma-*zero : ∀ a → a * zero ≡ zero
    lemma-*zero a = {!!}

    lemma-+swap : ∀ a b c → a + (b + c) ≡ b + (a + c)
    lemma-+swap a b c = sym (+-assoc a b c) ~ {!!} ~ +-assoc b a c

    lemma-*succ : ∀ a b → a + a * b ≡ a * succ b 
    lemma-*succ a b = {!!}

    *-comm : ∀ a b → a * b ≡ b * a
    *-comm a b = {!!}
\end{code}
Pressing `C-c C-.` while there is a term in a hole shows a goal type, context and the term's inferred type.
Incredibly useful key sequence for interactive proof editing.

### Pattern matching with `with`

Consider the following implementation of a `filter` function in Haskell:
\begin{spec}
  filter :: (a → Bool) → [a] → [a]
  filter p [] = []
  filter p (a : as) = case p a of
    True  -> a : (filter p as)
    False -> filter p as
\end{spec}

It could be rewritten into Agda like this:
\begin{code}
  filter : {A : Set} → (A → Bool) → List A → List A
  filter p [] = []
  filter p (a ∷ as) with p a
  ... | true  = a ∷ (filter p as)
  ... | false = filter p as
\end{code}
which doesn't look very different.
But desugaring `...` by the rules of Agda syntax makes it a bit less similar: 
\begin{code}
  filter₀ : {A : Set} → (A → Bool) → List A → List A
  filter₀ p [] = []
  filter₀ p (a ∷ as) with p a
  filter₀ p (a ∷ as) | true  = a ∷ (filter₀ p as)
  filter₀ p (a ∷ as) | false = filter₀ p as
\end{code}

There's no direct analogue to `case` in Agda, `with` construction allows pattern matching on intermediate expressions (just like Haskell's `case`), but (unlike `case`) on a top level only.
Thus `with` effectively just adds a "derived" argument to a function.
Just like with normal arguments, pattern matching on a derived argument might change some types in a context.

The top level restriction simplifies all the dependently typed stuff (mainly related to dotted patterns), but makes some things a little bit more awkward (in most cases you can emulate `case` with a subterm placed into a `where` block).
Syntactically, vertical bars separate normal arguments from a derived ones and a derived ones from each other.

Obfuscating the function above gives:
\begin{code}
  filterN : {A : Set} → (A → Bool) → List A → List A
  filterN p [] = []
  filterN p (a ∷ as) with p a
  filterN p (a ∷ as) | true  with as
  filterN p (a ∷ as) | true | [] = a ∷ []
  filterN p (a ∷ as) | true | b ∷ bs with p b
  filterN p (a ∷ as) | true | b ∷ bs | true  = a ∷ (b ∷ filterN p bs)
  filterN p (a ∷ as) | true | b ∷ bs | false = a ∷ filterN p bs
  filterN p (a ∷ as) | false = filterN p as
  -- or alternatively
  filterP : {A : Set} → (A → Bool) → List A → List A
  filterP p [] = []
  filterP p (a ∷ []) with p a
  filterP p (a ∷ []) | true = a ∷ []
  filterP p (a ∷ []) | false = []
  filterP p (a ∷ (b ∷ bs)) with p a | p b
  filterP p (a ∷ (b ∷ bs)) | true  | true  = a ∷ (b ∷ filterP p bs)
  filterP p (a ∷ (b ∷ bs)) | true  | false = a ∷ filterP p bs
  filterP p (a ∷ (b ∷ bs)) | false | true  = b ∷ filterP p bs
  filterP p (a ∷ (b ∷ bs)) | false | false = filterP p bs
\end{code}
which shows that `with` could be nested and multiple matches are allowed to be done in parallel.

Let us prove that all these functions produce equal results when applied to equal arguments:
\begin{code}
  filter≡filterN₀ : {A : Set} → (p : A → Bool) → (as : List A) → filter p as ≡ filterN p as
  filter≡filterN₀ p [] = refl
  filter≡filterN₀ p (a ∷ as) = {!check me!}
\end{code}
note the goal type `(filter p (a ∷ as) | p a) ≡ (filterN p (a ∷ as) | p a)` which shows `p a` as derived argument to `filter` function.

Remember that to reduce `a + b` we had to match on `a` in the proofs above, matching on `b` gave nothing interesting because `_+_` was defined by induction on the first argument.
Similarly, to finish the `filter≡filterN` proof we have to match on `p a`, `as`, and `p b`, essentially duplicating the form of `filterN` term:
\begin{code}
  filter≡filterN : {A : Set} → (p : A → Bool) → (as : List A) → filter p as ≡ filterN p as
  filter≡filterN p [] = refl
  filter≡filterN p (a ∷ as) with p a
  filter≡filterN p (a ∷ as) | true with as
  filter≡filterN p (a ∷ as) | true | [] = refl
  filter≡filterN p (a ∷ as) | true | b ∷ bs with p b
  filter≡filterN p (a ∷ as) | true | b ∷ bs | true = cong (λ x → a ∷ (b ∷ x)) (filter≡filterN p bs)
  filter≡filterN p (a ∷ as) | true | b ∷ bs | false = cong (_∷_ a) (filter≡filterN p bs)
  filter≡filterN p (a ∷ as) | false = filter≡filterN p as
\end{code}

***Exercise.*** Guess the types for `filter≡filterP` and `filterN≡filterP`. Argue which of these is easier to prove? Do it (and get the other one almost for free by transitivity).

### Rewriting with `with` and Unification

When playing with the proofs about filters you might had noticed that `with` does something interesting with a goal.

In the following hole
\begin{code}
  filter≡filterN₁ : {A : Set} → (p : A → Bool) → (as : List A) → filter p as ≡ filterN p as
  filter≡filterN₁ p [] = refl
  filter≡filterN₁ p (a ∷ as) = {!check me!}
\end{code}
the type of the goal is `(filter p (a ∷ as) | p a) ≡ (filterN p (a ∷ as) | p a)`.
But after the following `with`
\begin{code}
  filter≡filterN₂ : {A : Set} → (p : A → Bool) → (as : List A) → filter p as ≡ filterN p as
  filter≡filterN₂ p [] = refl
  filter≡filterN₂ p (a ∷ as) with p a | as
  ... | r | rs = {!check me!}
\end{code}
it becomes `(filter p (a ∷ rs) | r) ≡ (filterN p (a ∷ rs) | r)`.

Same things might happen not only to a goal but to a context as a whole:
\begin{code}
  strange-id : {A : Set} {B : A → Set} → (a : A) → (b : B a) → B a
  strange-id {A} {B} a ba with B a
  ... | r = {!check me!}
\end{code}
in the hole, both the type of `ba` and the goal's type are `r`.

From these observations we conclude that `with expr` creates a new variable, say `w`, and "backwards-substitutes" `expr` to `w` in a context, changing all the occurrences of `expr` the _types_ of the context to `w`.
Which means that in a resulting context every type that had `expr` as a subterm starts dependending on `w`.

This property allows using `with` for _rewriting_:
\begin{code}
  lemma-+zero′ : ∀ a → a + zero ≡ a
  lemma-+zero′ zero = refl
  lemma-+zero′ (succ a) with a + zero | lemma-+zero′ a
  lemma-+zero′ (succ a) | ._ | refl = refl

  -- same expression with expanded underscore:
  lemma-+zero′₀ : ∀ a → a + zero ≡ a
  lemma-+zero′₀ zero = refl
  lemma-+zero′₀ (succ a) with a + zero | lemma-+zero′₀ a
  lemma-+zero′₀ (succ a) | .a | refl = refl
\end{code}

In these terms `a + zero` is replaced by a new variable, say `w`, which gives `lemma-+zero‵ a : a ≡ w`.
Pattern matching on `refl` gives [`w = a`] and so the dotted pattern appears.
After that the goal type becomes `a ≡ a`.

This pattern
\begin{spec}
f ps with a | eqn
... | ._ | refl = rhs
\end{spec}
is so common that it has [its own short hand](https://lists.chalmers.se/pipermail/agda/2009/001513.html):
\begin{spec}
f ps rewrite eqn = rhs
\end{spec}

***Exercise.*** Prove (on paper) that rewriting a goal type with `with` and propositional equality is a syntax sugar for expressions built from `refl`, `sym`, `trans` and `cong`.

### Universes and postulates

When moving from Haskell to Agda expression "every type is of kind `*`, i.e. for any type `X`, `X : *`" transforms into "every _ground_ type is of type `Set`, i.e. for any ground type `X`, `X : Set`".
If we are willing to be consistent, we can't afford `Set : Set` because it leads to a number of paradoxes (more on them below).
Still, we might want to construct things like "a list of types" and our current implementation of `List` can not express this.

To solve this problem Agda introduces an infinite tower of `Set`s, i.e. `Set0 : Set1`, `Set1 : Set2`, and so on with `Set` being an alias for `Set0`.
Agda is also a predicative system which means that `Set0 → Set0 : Set1`, `Set0 → Set1 : Set2`, and so on, but not `Set0 → Set1 : Set1`.
Note, however, that this tower is not cumulative, e.g. `Set0 : Set2` and `Set0 → Set1 : Set3` are false typing judgments.

*[As far as I know, in theory nothing prevents us from making the tower cumulative, it's just so happened that Agda selected this route and not another. Predicativity is a much more subtle matter (more on that below).]*

A list of types now becomes:
\begin{code}
  data List1 (A : Set1) : Set1 where
    []  : List1 A
    _∷_ : A → List1 A → List1 A
\end{code}
which looks very much like the usual `List` definition.

To prevent a code duplication like that Agda allows _universe polymorphic_ definitions.
To define the type `Level` of _universe levels_ we need a bit of _postulate_ magic:
\begin{spec}
  postulate Level : Set
  postulate lzero : Level
  postulate lsucc : Level → Level
  postulate _⊔_   : Level → Level → Level
\end{spec}

Postulates essentially define propositions without proofs, i.e. they say "trust me, I know this to be true".
Obviously, this can be exploited to infer contradictions:
\begin{code}
  postulate undefined : {A : Set} → A
\end{code}
but for every postulate Agda expects to be safe there is a `BUILTIN` pragma that checks the postulated definition promoting it from a simple postulate to an axiom. For `Level` there are the following `BUILTIN`s:
\begin{spec}
  {-# BUILTIN LEVEL     Level #-}
  {-# BUILTIN LEVELZERO lzero #-}
  {-# BUILTIN LEVELSUC  lsucc #-}
  {-# BUILTIN LEVELMAX  _⊔_   #-}
\end{spec}

The `Level` type works very much like `ℕ`.
It has two constructors `lzero` and `lsucc` that signify zero and successor, there is also an operator `_⊔_` which returns a maximum from its arguments.
The difference between `ℕ` and `Level` is that we are not allowed to pattern match on elements of the latter.

Given the definition above, expression `Set α` for `α : Level` means "the `Set` of level `α`".

We are now able to define universe polymorphic list in the following way:
\begin{spec}
  data PList₀ {α : Level} (A : Set α) : Set α where
    []  : PList₀ A
    _∷_ : A → PList₀ A → PList₀ A
  -- or a bit nicer:
  data PList₁ {α} (A : Set α) : Set α where
    []  : PList₁ A
    _∷_ : A → PList₁ A → PList₁ A
\end{spec}

It is interesting to note that Agda could have gone another route, say "GHC route", by defining all the builtin things inside with fixed names.
Instead, `BUILTIN` pragma allows us to redefine the names of the builtins, which is very helpful when we want to write our own standard library.
This is exactly what we are now going to do.

## Library

### Modules and the end of throw away code

Note that we have been writing everything above inside a module called `ThrowAwayIntroduction`.
From here on we are going to (mostly) forget about it and write a small standard library for Agda from scratch.
The idea is to remove any module with a name prefixed by "ThrowAway" from this file to produce the library code.
To make the implementation of this idea as simple as possible we place markers like:
\begin{code}
{- end of ThrowAwayIntroduction -}
\end{code}
at the ends of throw away code.
It allows to generate the library by a simple shell command:

    cat BrutalDepTypes.lagda | sed '/^\\begin{code}/,/^\\end{code}/ ! d; /^\\begin{code}/ d; /^\\end{code}/ c \
    ' | sed '/^ *module ThrowAway/,/^ *.- end of ThrowAway/ d;'

We are now going to redefine everything useful from above in a universe polymorphic way (when applicable), starting with `Level`s:
\begin{code}
module Level where
  -- Universe levels
  postulate Level : Set
  postulate lzero : Level
  postulate lsucc : Level → Level
  -- input for ⊔ is \sqcup
  postulate _⊔_   : Level → Level → Level

  infixl 5 _⊔_
  
  -- Make them work
  {-# BUILTIN LEVEL     Level #-}
  {-# BUILTIN LEVELZERO lzero #-}
  {-# BUILTIN LEVELSUC  lsucc #-}
  {-# BUILTIN LEVELMAX  _⊔_   #-}
\end{code}

Each module in Agda has an export list.
Everything defined in a module gets appended to it.
To place things defined for export in another module into a current context there is an `open` construct:
\begin{spec}
open ModuleName
\end{spec}
This doesn't append `ModuleName`'s export list to current module's export list.
To do that we need to add `public` keyword at the end:
\begin{code}
open Level public
\end{code}

### Common functions with types not for the faint of heart

**Exercise.** Understand what is going on in types of the following functions:
\begin{code}
module Function where
  -- Dependent application
  infixl 0 _$_
  _$_ : ∀ {α β}
      → {A : Set α} {B : A → Set β}
      → (f : (x : A) → B x)
      → ((x : A) → B x)
  f $ x = f x
  
  -- Simple application
  infixl 0 _$′_
  _$′_ : ∀ {α β}
      → {A : Set α} {B : Set β}
      → (A → B) → (A → B)
  f $′ x = f $ x

  -- input for ∘ is \o
  -- Dependent composition
  _∘_ : ∀ {α β γ}
      → {A : Set α} {B : A → Set β} {C : {x : A} → B x → Set γ}
      → (f : {x : A} → (y : B x) → C y)
      → (g : (x : A) → B x)
      → ((x : A) → C (g x))
  f ∘ g = λ x → f (g x)
  
  -- Simple composition
  _∘′_ : ∀ {α β γ}
      → {A : Set α} {B : Set β} {C : Set γ}
      → (B → C) → (A → B) → (A → C)
  f ∘′ g = f ∘ g
  
  -- Flip
  flip : ∀ {α β γ}
       → {A : Set α} {B : Set β} {C : A → B → Set γ} 
       → ((x : A) → (y : B) → C x y)
       → ((y : B) → (x : A) → C x y)
  flip f x y = f y x
  
  -- Identity
  id : ∀ {α} {A : Set α} → A → A
  id x = x
  
  -- Constant function
  const : ∀ {α β}
       → {A : Set α} {B : Set β}
       → (A → B → A)
  const x y = x

open Function public
\end{code}
Especially note the scopes of variable bindings in types.

### Logic

Intuitionistic `Logic` module:
\begin{code}
module Logic where
  -- input for ⊥ is \bot
  -- False proposition
  data ⊥ : Set where

  -- input for ⊤ is \top
  -- True proposition
  record ⊤ : Set where
 
  -- ⊥ implies anything at any universe level
  ⊥-elim : ∀ {α} {A : Set α} → ⊥ → A
  ⊥-elim ()
\end{code}

Propositional negation is defined as follows:
\begin{code}
  -- input for ¬ is \lnot
  ¬ : ∀ {α} → Set α → Set α
  ¬ P = P → ⊥
\end{code} 

The technical part of the idea of this definition is that the principle of explosion ("from a contradiction, anything follows") gets a pretty straightforward proof.

**Exercise.** Prove the following propositions:
\begin{code}
  module ThrowAwayExercise where
    contradiction : ∀ {α β} {A : Set α} {B : Set β} → A → ¬ A → B
    contradiction = {!!}
   
    contraposition : ∀ {α β} {A : Set α} {B : Set β} → (A → B) → (¬ B → ¬ A)
    contraposition = {!!}

    contraposition¬ : ∀ {α β} {A : Set α} {B : Set β} → (A → ¬ B) → (B → ¬ A)
    contraposition¬ = {!!}

    →¬² : ∀ {α} {A : Set α} → A → ¬ (¬ A)
    →¬² a = {!!}

    ¬³→¬ : ∀ {α} {A : Set α} → ¬ (¬ (¬ A)) → ¬ A
    ¬³→¬ = {!!}
\end{code}
Hint. Use `C-c C-,` here to see the goal type in its normal form.

From a more logical standpoint the idea of `¬` is that false proposition `P` should be isomorphic to `⊥` (i.e. they should imply each other: `⊥ → P ∧ P → ⊥`).
Since `⊥ → P` is true for all `P` there is only `P → ⊥` left for us to prove.

From a computational point of view having a variable of type `⊥` in a context means that there is no way execution of a program could reach this point.
Which means we can match on the variable and use absurd pattern, `⊥-elim` does exactly that.

Note that, being an intuitionistic system, Agda has no means to prove "double negation" rule.
See for yourself:
\begin{code}
    ¬²→ : ∀ {α} {A : Set α} → ¬ (¬ A) → A
    ¬²→ ¬¬a = {!check me!}
  {- end of ThrowAwayExercise -}
\end{code}

By the way, proofs in the exercise above amounted to a serious scientific paper at the start of 20th century.

Solution for the exercise:
\begin{code}
  private
   module DummyAB {α β} {A : Set α} {B : Set β} where
    contradiction : A → ¬ A → B
    contradiction a ¬a = ⊥-elim (¬a a)

    contraposition : (A → B) → (¬ B → ¬ A)
    contraposition = flip _∘′_

    contraposition¬ : (A → ¬ B) → (B → ¬ A)
    contraposition¬ = flip

  open DummyAB public

  private
   module DummyA {α} {A : Set α} where
    →¬² : A → ¬ (¬ A)
    →¬² = contradiction

    ¬³→¬ : ¬ (¬ (¬ A)) → ¬ A
    ¬³→¬ ¬³a = ¬³a ∘′ →¬²

  open DummyA public
\end{code}
**Exercise.** Understand this solution.

Note clever module usage.
Opening a module with parameters prefixes types of all the things defined there with these parameters.
We will use this trick a lot.

Let us define conjunction, disjunction, and logical equivalence:
\begin{code}
  -- input for ∧ is \and
  record _∧_ {α β} (A : Set α) (B : Set β) : Set (α ⊔ β) where
    constructor _,′_
    field
      fst : A
      snd : B

  open _∧_ public

  -- input for ∨ is \or
  data _∨_ {α β} (A : Set α) (B : Set β) : Set (α ⊔ β) where
    inl : A → A ∨ B
    inr : B → A ∨ B

  -- input for ↔ is \<->
  _↔_ : ∀ {α β} (A : Set α) (B : Set β) → Set (α ⊔ β)
  A ↔ B = (A → B) ∧ (B → A)
\end{code}

Make all this goodness available:
\begin{code}
open Logic public
\end{code}

### MLTT: types and properties

Some definitions from Per Martin-Löf's type theory [@MartinLoef:ITT-Sambin]:
\begin{code}
module MLTT where
  -- input for ≡ is \==
  -- Propositional equality
  infix 4 _≡_
  data _≡_ {α} {A : Set α} (x : A) : A → Set α where
    refl : x ≡ x

  -- input for Σ is \Sigma
  -- Dependent pair
  record Σ {α β} (A : Set α) (B : A → Set β) : Set (α ⊔ β) where
    constructor _,_
    field
      projl : A
      projr : B projl

  open Σ public

  -- Make rewrite syntax work
  {-# BUILTIN EQUALITY _≡_ #-}
  {-# BUILTIN REFL    refl #-}
\end{code}

The `Σ` type is a dependent version of `_∧_` (the second field depends on the first), i.e. `_∧_` is a specific case of `Σ`:
\begin{code}
  -- input for × is \x
  _×_ : ∀ {α β} (A : Set α) (B : Set β) → Set (α ⊔ β)
  A × B = Σ A (λ _ → B)
  
  ×↔∧ : ∀ {α β} {A : Set α} {B : Set β} → (A × B) ↔ (A ∧ B)
  ×↔∧ = (λ z → projl z ,′ projr z) ,′ (λ z → fst z , snd z)
\end{code}

Personally, I use both `_∧_` and `_×_` occasionally since `_×_` looks ugly in the normal form and makes goal types hard to read.

Some properties:
\begin{code}
  module ≡-Prop where
   private
    module DummyA {α} {A : Set α} where
      -- _≡_ is symmetric
      sym : {x y : A} → x ≡ y → y ≡ x
      sym refl = refl
  
      -- _≡_ is transitive
      trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
      trans refl refl = refl
  
      -- _≡_ is substitutive
      subst : ∀ {γ} {P : A → Set γ} {x y} → x ≡ y → P x → P y
      subst refl p = p
  
    private
     module DummyAB {α β} {A : Set α} {B : Set β} where
      -- _≡_ is congruent
      cong : ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
      cong f refl = refl
  
      subst₂ : ∀ {ℓ} {P : A → B → Set ℓ} {x y u v} → x ≡ y → u ≡ v → P x u → P y v
      subst₂ refl refl p = p
  
    private
     module DummyABC {α β γ} {A : Set α} {B : Set β} {C : Set γ} where
      cong₂ : ∀ (f : A → B → C) {x y u v} → x ≡ y → u ≡ v → f x u ≡ f y v
      cong₂ f refl refl = refl
  
    open DummyA public
    open DummyAB public
    open DummyABC public
\end{code}

Make all this goodness available:
\begin{code}
open MLTT public
\end{code}

### Decidable propositions

\begin{code}
module Decidable where
\end{code}

*Decidable proposition* it is a proposition that has an explicit proof or disproval:
\begin{code}
  data Dec {α} (A : Set α) : Set α where
    yes : ( a :   A) → Dec A
    no  : (¬a : ¬ A) → Dec A
\end{code}
This datatype is very much like `Bool`, except it also explains _why_ the proposition holds or why it must not.

Decidable propositions are the glue that make your program work with the real world.

Suppose we want to write a program that reads a natural number, say `n`, from `stdin` and divides it by two with `div2E`.
To do that we need a proof that `n` is `Even`.
The easiest way to do it is to define a function that decides if a given natural is `Even`:
\begin{code}
  module ThrowAwayExample₁ where
    open ThrowAwayIntroduction

    ¬Even+2 : ∀ {n} → ¬ (Even n) → ¬ (Even (succ (succ n)))
    ¬Even+2 ¬en (e2succ en) = contradiction en ¬en

    Even? : ∀ n → Dec (Even n)
    Even? zero        = yes ezero
    Even? (succ zero) = no (λ ()) -- note an absurd pattern in
                                  -- an anonymous lambda expression
    Even? (succ (succ n)) with Even? n
    ... | yes a       = yes (e2succ a)
    ... | no  a¬      = no (¬Even+2 a¬)
  {- end of ThrowAwayExample₁ -}
\end{code}
then read `n` from `stdin`, feed it to `Even?`, match on the result and call `div2E` if `n` is `Even`.

Same idea applies to almost everything:

* Want to write a parser?
Parser is a procedure that decides if a string conforms to a syntax.
* Want to type check a program?
Type checker is a procedure that decides if the program conforms to a given set of typing rules.
* Want an optimizing compiler?
Parse, match on `yes`, type check, match on `yes`, optimize typed representation, generate output.
* And so on.

Using same idea we can define decidable dichotomous and trichotomous propositions:
\begin{code}
  data Di {α β} (A : Set α) (B : Set β) : Set (α ⊔ β) where
    diyes : ( a :   A) (¬b : ¬ B) → Di A B
    dino  : (¬a : ¬ A) ( b :   B) → Di A B

  data Tri {α β γ} (A : Set α) (B : Set β) (C : Set γ) : Set (α ⊔ (β ⊔ γ)) where
    tri< : ( a :   A) (¬b : ¬ B) (¬c : ¬ C) → Tri A B C
    tri≈ : (¬a : ¬ A) ( b :   B) (¬c : ¬ C) → Tri A B C
    tri> : (¬a : ¬ A) (¬b : ¬ B) ( c :   C) → Tri A B C
\end{code}

Make all this goodness available:
\begin{code}
open Decidable public
\end{code}

### Natural numbers: operations, properties and relations

Consider this to be the answer (encrypted with `rewrite`s) for the exercise way above:
\begin{code}
module Data-ℕ where
  -- Natural numbers (positive integers)
  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  module ℕ-Rel where
    infix 4 _≤_ _<_ _>_
  
    data _≤_ : ℕ → ℕ → Set where
      z≤n : ∀ {n}           → zero ≤ n
      s≤s : ∀ {n m} → n ≤ m → succ n ≤ succ m
  
    _<_ : ℕ → ℕ → Set
    n < m = succ n ≤ m
  
    _>_ : ℕ → ℕ → Set
    n > m = m < n
  
    ≤-unsucc : ∀ {n m} → succ n ≤ succ m → n ≤ m
    ≤-unsucc (s≤s a) = a 
  
    <-¬refl : ∀ n → ¬ (n < n)
    <-¬refl zero ()
    <-¬refl (succ n) (s≤s p) = <-¬refl n p
  
    ≡→≤ : ∀ {n m} → n ≡ m → n ≤ m
    ≡→≤ {zero}   refl = z≤n
    ≡→≤ {succ n} refl = s≤s (≡→≤ {n} refl) -- Note this
  
    ≡→¬< : ∀ {n m} → n ≡ m → ¬ (n < m)
    ≡→¬< refl = <-¬refl _
  
    ≡→¬> : ∀ {n m} → n ≡ m → ¬ (n > m)
    ≡→¬> refl = <-¬refl _
  
    <→¬≡ : ∀ {n m} → n < m → ¬ (n ≡ m)
    <→¬≡ = contraposition¬ ≡→¬<
  
    >→¬≡ : ∀ {n m} → n > m → ¬ (n ≡ m)
    >→¬≡ = contraposition¬ ≡→¬>
  
    <→¬> : ∀ {n m} → n < m → ¬ (n > m)
    <→¬> {zero} (s≤s z≤n) ()
    <→¬> {succ n} (s≤s p<) p> = <→¬> p< (≤-unsucc p>)
  
    >→¬< : ∀ {n m} → n > m → ¬ (n < m)
    >→¬< = contraposition¬ <→¬>
  
  module ℕ-Op where
    open ≡-Prop
  
    pred : ℕ → ℕ
    pred zero = zero
    pred (succ n) = n
  
    infixl 6 _+_
    _+_ : ℕ → ℕ → ℕ
    zero   + n = n
    succ n + m = succ (n + m)
  
    infixr 7 _*_
    _*_ : ℕ → ℕ → ℕ
    zero   * m = zero
    succ n * m = m + (n * m)
  
    private
     module Dummy₀ where
      lemma-+zero : ∀ a → a + zero ≡ a
      lemma-+zero zero = refl
      lemma-+zero (succ a) rewrite lemma-+zero a = refl
    
      lemma-+succ : ∀ a b → succ a + b ≡ a + succ b
      lemma-+succ zero b = refl
      lemma-+succ (succ a) b rewrite lemma-+succ a b = refl
  
    open Dummy₀
  
    -- + is associative
    +-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
    +-assoc zero b c = refl
    +-assoc (succ a) b c rewrite (+-assoc a b c) = refl
  
    -- + is commutative
    +-comm : ∀ a b → a + b ≡ b + a
    +-comm zero b = sym $ lemma-+zero b
    +-comm (succ a) b rewrite +-comm a b | lemma-+succ b a = refl
  
    -- * is distributive by +
    *+-dist : ∀ a b c → (a + b) * c ≡ a * c + b * c
    *+-dist zero b c = refl
    *+-dist (succ a) b c rewrite *+-dist a b c | +-assoc c (a * c) (b * c) = refl
  
    -- * is associative
    *-assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)
    *-assoc zero b c = refl
    *-assoc (succ a) b c rewrite *+-dist b (a * b) c | *-assoc a b c = refl
    
    private
     module Dummy₁ where
      lemma-*zero : ∀ a → a * zero ≡ zero
      lemma-*zero zero = refl
      lemma-*zero (succ a) = lemma-*zero a
      
      lemma-+swap : ∀ a b c → a + (b + c) ≡ b + (a + c)
      lemma-+swap a b c rewrite sym (+-assoc a b c) | +-comm a b | +-assoc b a c = refl
      
      lemma-*succ : ∀ a b → a + a * b ≡ a * succ b 
      lemma-*succ zero b = refl
      lemma-*succ (succ a) b rewrite lemma-+swap a b (a * b) | lemma-*succ a b = refl
    
    open Dummy₁
  
    -- * is commutative
    *-comm : ∀ a b → a * b ≡ b * a
    *-comm zero b = sym $ lemma-*zero b
    *-comm (succ a) b rewrite *-comm a b | lemma-*succ b a = refl

  module ℕ-RelOp where
    open ℕ-Rel
    open ℕ-Op
    open ≡-Prop
    
    infix 4 _≡?_ _≤?_ _<?_
  
    _≡?_ : (n m : ℕ) → Dec (n ≡ m)
    zero    ≡? zero   = yes refl
    zero    ≡? succ m = no (λ ())
    succ n  ≡? zero   = no (λ ())
    succ n  ≡? succ m with n ≡? m
    succ .m ≡? succ m | yes refl = yes refl
    succ n  ≡? succ m | no ¬a    = no (¬a ∘ cong pred) -- Note this
  
    _≤?_ : (n m : ℕ) → Dec (n ≤ m)
    zero ≤? m = yes z≤n
    succ n ≤? zero = no (λ ())
    succ n ≤? succ m with n ≤? m
    ... | yes a = yes (s≤s a)
    ... | no ¬a = no (¬a ∘ ≤-unsucc)
   
    _<?_ : (n m : ℕ) → Dec (n < m)
    n <? m = succ n ≤? m
  
    cmp : (n m : ℕ) → Tri (n < m) (n ≡ m) (n > m)
    cmp zero zero     = tri≈ (λ ()) refl (λ ())
    cmp zero (succ m) = tri< (s≤s z≤n) (λ ()) (λ ())
    cmp (succ n) zero = tri> (λ ()) (λ ()) (s≤s z≤n)
    cmp (succ n) (succ m) with cmp n m
    cmp (succ n) (succ m) | tri< a ¬b ¬c = tri< (s≤s a) (¬b ∘ cong pred) (¬c ∘ ≤-unsucc)
    cmp (succ n) (succ m) | tri≈ ¬a b ¬c = tri≈ (¬a ∘ ≤-unsucc) (cong succ b) (¬c ∘ ≤-unsucc)
    cmp (succ n) (succ m) | tri> ¬a ¬b c = tri> (¬a ∘ ≤-unsucc) (¬b ∘ cong pred) (s≤s c)

open Data-ℕ public
\end{code}
**Exercise.** Understand this. Now, remove all term bodies from `ℕ-RelProp` and `ℕ-RelOp` and reimplement everything yourself.

### Lists and Vectors

\begin{code}
module Data-List where
  -- List
  infixr 5 _∷_
  data List {α} (A : Set α) : Set α where
    []  : List A
    _∷_ : A → List A → List A

  module List-Op where
  private
   module DummyA {α} {A : Set α} where
    -- Singleton `List`
    [_] : A → List A
    [ a ] = a ∷ []

    -- Concatenation for `List`s
    infixr 5 _++_
    _++_ : List A → List A → List A
    []       ++ bs = bs
    (a ∷ as) ++ bs = a ∷ (as ++ bs)

    -- Filtering with decidable propositions
    filter : ∀ {β} {P : A → Set β} → (∀ a → Dec (P a)) → List A → List A
    filter p [] = []
    filter p (a ∷ as) with p a
    ... | yes _ = a ∷ (filter p as)
    ... | no  _ = filter p as

  open DummyA public

module Data-Vec where
  -- Vector
  infixr 5 _∷_
  data Vec {α} (A : Set α) : ℕ → Set α where
    []  : Vec A zero
    _∷_ : ∀ {n} → A → Vec A n → Vec A (succ n)
  
  module Vec-Op where
    open ℕ-Op
  
    private
     module DummyA {α} {A : Set α} where
      -- Singleton `Vec`
      [_] : A → Vec A (succ zero)
      [ a ] = a ∷ []
  
      -- Concatenation for `Vec`s
      infixr 5 _++_
      _++_ : ∀ {n m} → Vec A n → Vec A m → Vec A (n + m)
      []       ++ bs = bs
      (a ∷ as) ++ bs = a ∷ (as ++ bs)
  
      head : ∀ {n} → Vec A (succ n) → A
      head (a ∷ as) = a
  
      tail : ∀ {n} → Vec A (succ n) → A
      tail (a ∷ as) = a
  
    open DummyA public
\end{code}

\begin{code}
{-
Work in progress. TODO.

I find the following definition quite amusing:

module VecLists where
  open Data-Vec

  private
   module DummyA {α} {A : Set α} where
     VecList = Σ ℕ (Vec A)
-}
\end{code}

### Being in a `List`

Indexing allows to define pretty fun things:
\begin{code}
module ThrowAwayMore₁ where
  open Data-List
  open List-Op

  -- input for ∈ is \in
  -- `a` is in `List`
  data _∈_ {α} {A : Set α} (a : A) : List A → Set α where
    here  : ∀ {as}   → a ∈ (a ∷ as)
    there : ∀ {b as} → a ∈ as → a ∈ (b ∷ as)
  
  -- input for ⊆ is \sub= 
  -- `xs` is a sublist of `ys`
  _⊆_ : ∀ {α} {A : Set α} → List A → List A → Set α
  as ⊆ bs = ∀ {x} → x ∈ as → x ∈ bs
\end{code}

The `_∈_` relation says that "being in a `List`" for an element `a : A` means that `a` in the head of a `List` or in the tail of a `List`.
For some `a` and `as` a value of type `a ∈ as`, that is "`a` is in a list `as`" is a position of an element `a` in `as` (there might be any number of elements in this type).
Relation `⊆`, that is "being a sublist", carries a function that for each `a` in `xs` gives its position in `as`.

Examples:
\begin{code}
  listTest₁ = zero ∷ zero ∷ succ zero ∷ []
  listTest₂ = zero ∷ succ zero ∷ []
  
  ∈Test₀ : zero ∈ listTest₁
  ∈Test₀ = here
  
  ∈Test₁ : zero ∈ listTest₁
  ∈Test₁ = there here

  ⊆Test : listTest₂ ⊆ listTest₁
  ⊆Test here = here
  ⊆Test (there here) = there (there here)
  ⊆Test (there (there ()))
\end{code}

Let us prove some properties for `⊆` relation:
\begin{code}
  ⊆-++-left : ∀ {A : Set} (as bs : List A) → as ⊆ (bs ++ as)
  ⊆-++-left as [] n = n
  ⊆-++-left as (b ∷ bs) n = there (⊆-++-left as bs n)
  
  ⊆-++-right : ∀ {A : Set} (as bs : List A) → as ⊆ (as ++ bs)
  ⊆-++-right [] bs ()
  ⊆-++-right (a ∷ as) bs here = here
  ⊆-++-right (a ∷ as) bs (there n) = there (⊆-++-right as bs n)
{- end of ThrowAwayMore₁ -}
\end{code}
Note how these proofs renumber elements of a given list.

### Being in a `List` generalized: Any

By generalizing `_∈_` relation from propositional equality (in `x ∈ (x ∷ xs)` both `x`s are propositionally equal) to arbitrary predicates we arrive at:
\begin{code}
module Data-Any where
  open Data-List
  open List-Op

  -- Some element of a `List` satisfies `P`
  data Any {α γ} {A : Set α} (P : A → Set γ) : List A → Set (α ⊔ γ) where
    here  : ∀ {a as} → (pa  : P a)      → Any P (a ∷ as)
    there : ∀ {a as} → (pas : Any P as) → Any P (a ∷ as)

  module Membership {α β γ} {A : Set α} {B : Set β} (P : B → A → Set γ) where
    -- input for ∈ is \in
    -- `P b a` holds for some element `a` from the `List`
    -- when P is `_≡_` this becomes the usual "is in" relation
    _∈_ : B → List A → Set (α ⊔ γ)
    b ∈ as = Any (P b) as

    -- input for ∉ is \notin
    _∉_ : B → List A → Set (α ⊔ γ)
    b ∉ as = ¬ (b ∈ as)

    -- input for ⊆ is \sub=
    _⊆_ : List A → List A → Set (α ⊔ β ⊔ γ)
    as ⊆ bs = ∀ {x} → x ∈ as → x ∈ bs

    -- input for ⊈ is \sub=n
    _⊈_ : List A → List A → Set (α ⊔ β ⊔ γ)
    as ⊈ bs = ¬ (as ⊆ bs)

    -- input for ⊇ is \sup=
    _⊆⊇_ : List A → List A → Set (α ⊔ β ⊔ γ)
    as ⊆⊇ bs = (as ⊆ bs) ∧ (bs ⊆ as)

    ⊆-refl : ∀ {as} → as ⊆ as
    ⊆-refl = id

    ⊆-trans : ∀ {as bs cs} → as ⊆ bs → bs ⊆ cs → as ⊆ cs
    ⊆-trans f g = g ∘ f

    ⊆⊇-refl : ∀ {as} → as ⊆⊇ as
    ⊆⊇-refl = id ,′ id
    
    ⊆⊇-sym : ∀ {as bs} → as ⊆⊇ bs → bs ⊆⊇ as
    ⊆⊇-sym (f ,′ g) = g ,′ f

    ⊆⊇-trans : ∀ {as bs cs} → as ⊆⊇ bs → bs ⊆⊇ cs → as ⊆⊇ cs
    ⊆⊇-trans f g = (fst g ∘ fst f) ,′ (snd f ∘ snd g)

    ∉[] : ∀ {b} → b ∉ []
    ∉[]()

    -- When P is `_≡_` this becomes `b ∈ [ a ] → b ≡ a`
    ∈singleton→P : ∀ {a b} → b ∈ [ a ] → P b a
    ∈singleton→P (here pba) = pba
    ∈singleton→P (there ())
    
    P→∈singleton : ∀ {a b} → P b a → b ∈ [ a ]
    P→∈singleton pba = here pba

    ⊆-++-left : (as bs : List A) → as ⊆ (bs ++ as)
    ⊆-++-left as [] n = n
    ⊆-++-left as (b ∷ bs) n = there (⊆-++-left as bs n)

    ⊆-++-right : (as : List A) (bs : List A) → as ⊆ (as ++ bs)
    ⊆-++-right [] bs ()
    ⊆-++-right (x ∷ as) bs (here pa) = here pa
    ⊆-++-right (x ∷ as) bs (there n) = there (⊆-++-right as bs n)

    ⊆-filter : ∀ {σ} {Q : A → Set σ} → (q : ∀ x → Dec (Q x)) → (as : List A) → filter q as ⊆ as
    ⊆-filter q [] ()
    ⊆-filter q (a ∷ as) n with q a
    ⊆-filter q (a ∷ as) (here pa) | yes qa = here pa
    ⊆-filter q (a ∷ as) (there n) | yes qa = there (⊆-filter q as n)
    ⊆-filter q (a ∷ as) n         | no ¬qa = there (⊆-filter q as n)
\end{code}

**Exercise.** Note how general this code is.
`⊆-filter` covers a broad set of propositions, with "filtered list is a sublist (in the usual sense) of the original list" being a special case.
Do `C-c C-.` in the following goal and explain the type:
\begin{code}
module ThrowAwayMore₂ where
  goal = {!Data-Any.Membership.⊆-filter!}
{- end of ThrowAwayMore₂ -}
\end{code}
Explain the types of all the terms in `Membership` module.

### Dual predicate: All

\begin{code}
{-
Work in progress. TODO.

I didn't have a chance to use `All` yet (and I'm too lazy to implement this module right now),
but here is the definition:

module Data-All where
  open Data-List
  -- All elements of a `List` satisfy `P`
  data All {α β} {A : Set α} (P : A → Set β) : List A → Set (α ⊔ β) where
    []∀  : All P []
    _∷∀_ : ∀ {a as} → P a → All P as → All P (a ∷ as)
-}
\end{code}

### Booleans

Are not that needed with `Dec`, actually.

\begin{code}
module Data-Bool where
  -- Booleans
  data Bool : Set where
    true false : Bool
  
  module Bool-Op where
    if_then_else_ : ∀ {α} {A : Set α} → Bool → A → A → A
    if true  then a else _ = a
    if false then _ else b = b

    not : Bool → Bool
    not true  = false
    not false = true
    
    and : Bool → Bool → Bool
    and true  x = x
    and false _ = false
    
    or : Bool → Bool → Bool
    or false x = x
    or true  x = true

open Data-Bool public
\end{code} 

### Other stuff

Work in progress. TODO.
We need to prove something from A to Z.
Quicksort maybe.

## Pre-theoretical corner

This section discusses interesting things about Agda which are somewhere in between practice and pure theory.

\begin{code}
module ThrowAwayPreTheory where
  open ≡-Prop
  open ℕ-Op
\end{code}

### Equality and unification

Rewriting with equality hides a couple of catches.

Remember the term of `lemma-+zero′` from above:
\begin{code}
  lemma-+zero′ : ∀ a → a + zero ≡ a
  lemma-+zero′ zero = refl
  lemma-+zero′ (succ a) with a + zero | lemma-+zero′ a
  lemma-+zero′ (succ a) | ._ | refl = refl
\end{code}
it typechecks, but the following proof doesn't:
\begin{spec}
  lemma-+zero′′ : ∀ a → a + zero ≡ a
  lemma-+zero′′ zero = refl
  lemma-+zero′′ (succ a) with a | lemma-+zero′′ a
  lemma-+zero′′ (succ a) | ._ | refl = refl
\end{spec}

The problem here is that for arbitrary terms `A` and `B` to pattern match on `refl : A ≡ B` these `A` and `B` must unify.
In `lemma-+zero′` case we have `a + zero` backward-substituted into a new variable `w`, then we match on `refl` we get `w ≡ a`.
On the other hand, in `lemma-+zero′′` case we have `a` changed into `w`, an `refl` gets `w + zero ≡ w` type which is a malformed (recursive) unification constraint.

There is another catch.
Our current definition of `_≡_` allows to express equality on types, e.g. `Bool ≡ ℕ`.

This enables us to write the following term:
\begin{spec}
  lemma-unsafe-eq : (P : Bool ≡ ℕ) → Bool → ℕ
  lemma-unsafe-eq P b with Bool | P
  lemma-unsafe-eq P b | .ℕ | refl = b + succ zero
\end{code}
which type checks without errors.

Note, however, that `lemma-unsafe-eq` cannot be proven by simply pattern matching on `P`:
\begin{spec}
  lemma-unsafe-eq₀ : (P : Bool ≡ ℕ) → Bool → ℕ
  lemma-unsafe-eq₀ refl b = b
\end{spec}

\begin{code}
{- end of ThrowAwayPreTheory -}
\end{code}

**Exercise.** `lemma-unsafe-eq` is a food for thought about computation safety under false assumptions.

## Theoretical corner

In this section we shall talk about some theoretical stuff like datatype encodings and paradoxes.
You might want to read some of the theoretical references like [@Sorensen-Urzyczyn:lectures-on-curry-howard-isomorphism:1998;@MartinLoef:ITT-Sambin] first.

\begin{code}
module ThrowAwayTheory where
\end{code}

In literature Agda's arrow `(x : X) → Y` (where `Y` might have `x` free) is called *dependent product type*, or Π-type ("Pi-type") for short.
Dependent pair `Σ` is called *dependent sum type*, or Σ-type ("Sigma-type") for short.

### Finite types

Given `⊥`, `⊤` and `Bool` it is possible to define any *finite type*, that is a type with finite number of elements.

\begin{code}
  module FiniteTypes where
    open Bool-Op
    
    _∨′_ : (A B : Set) → Set
    A ∨′ B = Σ Bool (λ x → if x then A else B)
  
    zero′  = ⊥
    one′   = ⊤
    two′   = Bool
    three′ = one′ ∨′ two′
    four′  = two′ ∨′ two′
    --- and so on
\end{code}

TODO. Say something about extensional setting and `⊤ = ⊥ → ⊥`.

### Simple datatypes

\begin{code}
  module ΠΣ-Datatypes where
\end{code}

Given finite types, Π-types, and Σ-types it is possible to define non-inductive datatypes using the same scheme the definition of `_∨′_` uses.

Non-inductive datatype without indexes has the following scheme:
\begin{spec}
data DataTypeName (Param1 : Param1Type) (Param2 : Param2Type) ... : Set whatever
  Cons1 : (Cons1Arg1 : Cons1Arg1Type) (Cons1Arg2 : Cons1Arg2Type) ... → DataTypeName Param1 Param2 ...
  Cons2 : (Cons2Arg1 : Cons2Arg1Type) ... → DataTypeName Param1 Param2 ...
  ...
  ConsN : (ConsNArg1 : ConsNArg1Type) ... → DataTypeName Param1 Param2 ...
\end{spec}

Re-encoded into Π-types, Σ-types, and finite types it becomes:
\begin{spec}
DataTypeName : (Param1 : Param1Type) (Param2 : Param2Type) ... → Set whatever
DataTypeName Param1 Param2 ... = Σ FiniteTypeWithNElements choice where
  choice : FiniteTypeWithNElements → Set whatever
  choice element1 = Σ Cons1Arg1Type (λ Cons1Arg1 → Σ Cons1Arg2Type (λ Cons1Arg2 → ...))
  choice element2 = Σ Cons2Arg1Type (λ Cons2Arg1 → ...)
  ...
  choice elementN = Σ ConsNArg1Type (λ ConsNArg1 → ...)
\end{spec}

For instance, `Di` type from above translates into:
\begin{code}
    Di′ : ∀ {α β} (A : Set α) (B : Set β) → Set (α ⊔ β)
    Di′ {α} {β} A B = Σ Bool choice where
      choice : Bool → Set (α ⊔ β)
      choice true  = A × ¬ B
      choice false = ¬ A × B
\end{code}

### Datatypes with indices

Work in progress. TODO.
The general idea: add them as parameters and place an equality proof inside.

### Recursive datatypes

Work in progress. TODO.
General ideas: W-types and μ.

#### Curry's paradox

Negative occurrences make the system inconsistent.

Copy this to a separate file and typecheck:
\begin{spec}
{-# OPTIONS --no-positivity-check #-}
module CurrysParadox where
  data CS (C : Set) : Set where
    cs : (CS C → C) → CS C

  paradox : ∀ {C} → CS C → C
  paradox (cs b) = b (cs b)

  loop : ∀ {C} → C
  loop = paradox (cs paradox)

  contr : ⊥
  contr = loop
\end{spec}

### Universes and impredicativity 

Work in progress. TODO.
* Russell's paradox
* Hurkens' paradox

\begin{code}
{- end of ThrowAwayTheory -}
\end{code}

## References
