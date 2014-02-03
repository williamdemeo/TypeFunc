# Algebra and Logic Seminar: Spring 2014


## Feb 7: Intuitionistic type theory and paranormal programs.

**Abstract:**

Can we write a computer program that takes as input two functions
defined on an infinite set and outputs in finite time whether or not
the functions are equal?

In this introductory lecture, I present some basic ideas of Per
Martin-Lof's intuitionistic type theory with the goal convincing
members of the seminar that the question above makes sense. I will
describe Martin Escardo's "seemingly impossible" functional program
that performs an exhaustive search over the Cantor space of infinite
binary sequences in finite time. If time permits, I will present a
proof of Diaconescu's Theorem that the Axiom of Choice implies the Law
of Excluded Middle.


---------------------------------------------------------------------------------

## Diaconescu's Theorem
([Fran&#199;ois Dorais][] has [a better blog post][]  on this topic.)

+ **Law of the Excluded Middle** (LEM) states that for any proposition P
  either P or &not;P holds.

+ **The Axiom of Choice** (AC) states that if S is a collection of nonempty sets,
  then there is a choice function f that can be used to select an element from
  each set in S.

+ **Diaconescu's Theorem:** AC implies LEM.
  
  *Proof:*  Assume AC.  Let P be any proposition.  We will show that either P=0
  or P=1.  Define **2** = {0, 1}.  Define two sets A and B as follows:
   
  A = {x | x = 0 or x = P}

  B = {x | x = 1 or x = P}
   
  Both of these sets are nonempty since 0 belongs to A and 1 belongs to
  B. Therefore, {A, B} is a set of nonempty sets so there is a choice function, 
   
  f : {A, B} --> **2**
   
  If f(A) = 0 = f(B), then 0 in B, so P=0.

  If f(A) = 1 = f(B), then 1 in A, so P=1.

  If f(A) &ne; f(B), then 1 in A, so P=1.

  ...to be continued...

[Fran&#199;ois Dorais]: http://dorais.org
[a better blog post]: http://dorais.org/archives/1031
