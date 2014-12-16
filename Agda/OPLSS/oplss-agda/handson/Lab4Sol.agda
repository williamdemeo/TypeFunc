open import Preliminaries
import handson.Lab3Sol

module handson.Lab4Sol where

  {- TASK 2a: -}
  maybemap : {A B : Set} (f : A → B) → Maybe A → Maybe B
  maybemap f (Some x) = Some (f x)
  maybemap f None = None

  data Functor : Set1 where
    K      : (A : Set) -> Functor
    X      : Functor 
    list   : (F : Functor) -> Functor
    _×u_   : (F1 F2 : Functor) → Functor
    {- TASK 2
       Extend the datatype with a constructor maybe F
       that represents disjoint sums (represented by the Agda type Maybe A).
       Extend _·_ and 'map' and the proofs of identity and composition.

       First define maybemap above, because you will want to refer to it in proofs later.  
    -}
    maybe : (F : Functor) → Functor        
    {- TASK 3
       Define a code _→u_ representing functions, and extend 
       the operations and proofs.

       Hint: First try a fully general _→u_ : (F1 F2 : Functor) → Functor.
             and you will get stuck.  Then restrict →u in some 
             way so that the rest of the definitions go through.

       Hint 2: to do the proofs, you will need to use function extensionality,
               which says that pointwise-equal functions are equal:
       λ=  : {A : Set} {B : A -> Set} {f g : (x : A) -> B x} 
           -> ((x : A) -> (f x) == (g x)) 
           -> f == g
    -}
    --    _→u'_  : (F1 F2 : Functor) → Functor
    _→u_   : (A : Set) (F : Functor) → Functor

  _·_ : Functor -> Set → Set
  (K B) · _ = B
  X · A = A
  (list F) · A = List (F · A)
  (F1 ×u F2) · A = F1 · A × F2 · A
  (maybe F) · A = Maybe (F · A)
  -- (F1 →u' F2) · A = F1 · A → F2 · A
  (B →u F) · A = B → F · A

  infixr 10 _×u_

  map : (F : Functor) {A B : Set} → (A → B) → F · A → F · B 
  map (K A) f x = x
  map X f x = f x
  map (list F) f x = List.map (map F f) x
  map (F1 ×u F2) f (x1 , x2) = map F1 f x1 , map F2 f x2
  map (maybe F) f x = maybemap (map F f) x
  --  map (F1 →u' F2) f g = λ b → map F2 f (g {!!})  -- stuck here!
  map (A0 →u F) f g = λ a0 → map F f (g a0)

  {- TASK 1: Do the proof of map-id, which we didn't get to in lecture.  
             The answer is in Lecture4Finish but try not to peek. 
  -}
  map-id : (F : Functor) {A : Set} (x : F · A) → map F (\y -> y) x == x
  map-id (K A) x = Refl
  map-id X x = Refl
  map-id (list F) [] = Refl
  map-id (list F) (x :: xs) = ap2 _::_ (map-id F x) (map-id (list F) xs)
  map-id (F1 ×u F2) (x1 , x2) = ap2 _,_ (map-id F1 x1) (map-id F2 x2)
  map-id (maybe F) (Some x) = ap Some (map-id F x) 
  map-id (maybe F) None = Refl
  map-id (A →u F) x = λ= (λ a0 → map-id F (x a0))
  --  map-id (F1 →u' F2) f = {!!}

  map-fusion : (F : Functor) {A B C : Set} → {g : B -> C} {f : A → B} → (x : F · A) → map F (g o f) x == map F g (map F f x)
  map-fusion (K A) x = Refl
  map-fusion X x = Refl
  map-fusion (list F) [] = Refl
  map-fusion (list F) (x :: xs) = ap2 _::_ (map-fusion F x) (map-fusion (list F) xs)
  map-fusion (F1 ×u F2) (x1 , x2) = ap2 _,_ (map-fusion F1 x1) (map-fusion F2 x2)
  map-fusion (maybe F) (Some x) = ap Some (map-fusion F x)
  map-fusion (maybe F) None = Refl
  map-fusion (A →u F) x = λ= (λ a0 → map-fusion F (x a0))
  --  map-fusion (F1 →u' F2) f = {!!}


  -- definition of bijection from lecture

  IsBijection : {A B : Set} (f : A → B) -> Set
  IsBijection {A}{B} f = 
     Σ \ (g : B → A) →
       ((x : A) → (g (f x)) == x) ×
       ((y : B) → (f (g y)) == y)

  Bijection : Set -> Set -> Set
  Bijection A B = Σ(\(f : A → B) → IsBijection f)

  {- TASK 4: prove that map is a bijection 
             The answer is in Lecture4Finish.agda but try not to peek.
             
             You may want to use an equality chain, which lets you write out
             a two-column proof as a series of equality steps.

             Note: you will need to use function extensionality, which says 
                   that pointwise-equal functions are equal
             λ=  : {A : Set} {B : A -> Set} {f g : (x : A) -> B x} 
                 -> ((x : A) -> (f x) == (g x)) 
                 -> f == g
  -}

  open Nat using (_+_)
  example-equality-chain : 2 + 2 == 4
  example-equality-chain = 2 + 2 =〈 Refl 〉    --- type =\langle \rangle
                           S (1 + 2) =〈 Refl 〉
                           4 ∎ -- type \qed
  {- 
      The idea with this proof is that we show that 2+2 = 4 by two steps.
        2 + 2 == S (1 + 2) (by reflexivity)
        S (1 + 2) == 4 (also by reflexivity)
        Therefore 2 + 2 = 4 by transitivity.  
      (Of course, 2 + 2 is definitionally equal to 4, so in this case
       we could have just written Refl.)

      Note that equation chains are just a clever use of mixfix syntax:
      _=〈_〉 and _∎ are defined in Preliminaries.agda
  -}
  

  {- prove map-is-bijection -}
  map-is-bijection : (F : Functor) {A B : Set} (f : Bijection A B) 
                   → IsBijection (map F (fst f))
  map-is-bijection F (f , g , α , β) =
     map F g , 
     (λ x → map F g (map F f x) =〈 ! (map-fusion F x) 〉 
            map F (g o f) x =〈 ap (λ y → map F y x) (λ= α) 〉
            map F (\ z -> z) x =〈 map-id F x 〉
            x ∎) , 
     (λ x → map F f (map F g x) =〈 ! (map-fusion F x) 〉 
            map F (f o g) x =〈 ap (λ y → map F y x) (λ= β) 〉
            map F (\ x -> x) x =〈 map-id F x 〉
            x ∎) 


  open handson.Lab3Sol 
  open List using (_++_)
  open CSL using (csl)

  {- recall format1 from Task 4 of Lab 3. -}
  format1 = nat then \ _ → bit then \ _ -> csl char 

  {- TASK 5a: Give a bijection between String (List Char) and 
              (Σ n → Vec Char n)

              Hint: see the functions in Preliminaries.Vector
  -}
  bij : Bijection String (Σ \ n -> Vector.Vec Char n)
  bij = Vector.fromList , Vector.toList' , Vector.to-from , Vector.from-to

  {- TASK 5b: Define write1 by composing write with map -}
  write1 : (Nat × Bool × String) → String
  write1 = (write format1) o map (K Nat ×u K Bool ×u X) Vector.fromList

  {- TASK 5c: Define read1 by composing read with map -}
  read1 : String -> Maybe ((Nat × Bool × String) × String)
  read1 = map (maybe ((K Nat ×u K Bool ×u X) ×u K String)) Vector.toList'  o read format1

  {- TASK 5d: prove spec1.
              You may want to use an equality chain.
              It might also be helpful to write out the proof on paper first.

              You will want to use ap
              ap :  {A : Set} {B : Set} {M N : A}
                    (f : A → B) → M == N → (f M) == (f N)
  -}
  spec1 : (p : (Nat × Bool × String)) (s : String) → read1 (write1 p ++ s) == Some (p , s)
  spec1 p s = read1 (write1 p ++ s) =〈 Refl 〉 
              maybemap (\ p' -> map (K Nat ×u K Bool ×u X) Vector.toList' (fst p') , snd p') 
                       (read format1 (write format1 
                                            (map (K Nat ×u K Bool ×u X) Vector.fromList p) 
                                             ++ s))     =〈 ap
                                                           (maybemap
                                                            (λ p₁ →
                                                               map (K Nat ×u K Bool ×u X) Vector.toList' (fst p₁) , snd p₁))
                                                           (spec format1 (map (K Nat ×u K Bool ×u X) Vector.fromList p) s) 〉 
              maybemap (\ p -> map (K Nat ×u K Bool ×u X) Vector.toList' (fst p) , snd p) 
                       (Some (map (K Nat ×u K Bool ×u X) Vector.fromList p , s))  =〈 Refl 〉 
              Some (map (K Nat ×u K Bool ×u X) Vector.toList' 
                        (map (K Nat ×u K Bool ×u X) Vector.fromList p)  , s)      =〈 ap (λ x → Some (x , s)) (fst (snd (map-is-bijection (K Nat ×u K Bool ×u X) bij)) p) 〉
              Some (p , s) ∎ 





