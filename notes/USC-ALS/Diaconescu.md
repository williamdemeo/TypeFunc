---------------------------------------------------------------------------------

## Diaconescu's Theorem

These are very rough notes for my own reference.  Please see
[Fran&#199;ois Dorais' blog post][] for a nice discussion of this topic.

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

[Fran&#231;ois Dorais' blog post]: http://dorais.org/archives/1031
