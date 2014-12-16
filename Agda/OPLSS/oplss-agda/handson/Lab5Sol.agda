
{-# OPTIONS --without-K #-}

open import PreliminariesHoTT
open import handson.Lab3Sol
open CSL using (csl)
open List using (_++_)
module handson.Lab5Sol where

  -- here's maybemap from last time.  
  maybemap : {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) → Maybe A → Maybe B
  maybemap f (Some x) = Some (f x)
  maybemap f None = None

  {- TASK 1A:
     Prove that maybemap on the identity function is the identity.  
  -}
  maybemap-id : {l1 : Level} {A : Set l1} (m : Maybe A) → m == maybemap (\ (x : A) → x) m
  maybemap-id (Some x) = Refl
  maybemap-id None = Refl

  {- TASK 1B: 
     Prove that transport at Maybe behaves like maybemap.
  -}
  transport-Maybe : {l1 l2 : Level} {A : Set l1} 
                    (F : A → Set l2) {a1 a2 : A} (p : a1 == a2) (x : Maybe (F a1))
                  → transport (\ a -> Maybe (F a)) p x == maybemap (transport F p) x
  transport-Maybe F Refl x = (maybemap-id x)

  -- ----------------------------------------------------------------------

  {- TASK 2:
     Redo Task 5 from Lab 4 (a better version of Task 4 from lab 3) 
     using transport (yes, I know this should have been Task 6 :) )
  -}
  
  {- recall format1 from Task 4 of Lab 3. -}
  format1 = nat then \ _ → bit then \ _ -> csl char 

  {- Here's the a bijection between String (List Char) and (Σ n → Vec Char n) -}
  bij : Bijection String (Σ \ n -> Vector.Vec Char n)
  bij = Vector.fromList , is-bijection  Vector.toList' Vector.to-from Vector.from-to

  {- TASK 2a: Define write1 by composing write with transport -}
  write1 : (Nat × Bool × String) → String
  write1 = (write format1) o transport (λ X → Nat × Bool × X) (ua bij) 

  {- TASK 2b: Define read1 by composing read with transport -}
  read1 : String -> Maybe ((Nat × Bool × String) × String)
  read1 = transport (λ X₁ → Maybe ((Nat × Bool × X₁) × String)) (! (ua bij)) o read format1

  {- TASK 3c: do an informal calculation on paper that proves spec1, 
              calculating with the rules for 'transport' like transport-Maybe and transport-× and 
              transport-constant.

     Then, if you're feeling brave, do an Agda proof as an equality chain.  
     You may need to make use of

       ap :  {l1 l2 : Level} {A : Set l1} {B : Set l2} {M N : A}
             (f : A → B) → M == N → (f M) == (f N)

       ap= : {l1 l2 : Level} {A : Type- l1} {B : A → Type- l2} {f g : (x : A) → B x} 
           → f == g → {x : A} → (f x) == (g x)
 
       transport-inv-1 : {l1 l2 : Level} {A : Type- l1} (B : A -> Type- l2) {M N : A} (α : M == N) 
                       -> (\y -> transport B (! α) (transport B α y)) == (\ x -> x)
  
       transport-inv-2 : {l1 l2 : Level} {A : Type- l1} (B : A -> Type- l2) {M N : A} (α : M == N) 
                       -> (\y -> transport B α (transport B (! α) y)) == (\ x -> x)
  -}
  spec1 : (p : (Nat × Bool × String)) (s : String) → read1 (write1 p ++ s) == Some (p , s)
  spec1 p s = read1 (write1 p ++ s) =〈 Refl 〉
              read1 (write format1 (transport (λ X → Nat × Bool × X) (ua bij) p) ++ s) =〈 Refl 〉
              transport (λ X₁ → Maybe ((Nat × Bool × X₁) × String)) 
                        (! (ua bij)) 
                        (read format1 (write format1 (transport (λ X → Nat × Bool × X) (ua bij) p) ++ s)) =〈 ap (transport (λ X₁ → Maybe ((Nat × Bool × X₁) × String)) (! (ua bij)))
                                                                                                                (spec format1 _ _) 〉
              transport (λ X₁ → Maybe ((Nat × Bool × X₁) × String)) 
                        (! (ua bij)) 
                        (Some (transport (λ X → Nat × Bool × X) (ua bij) p , s)) =〈 (transport-Maybe (λ X₁ → (Nat × Bool × X₁) × String) (! (ua bij)) _) 〉
              maybemap (transport (λ X₁ →((Nat × Bool × X₁) × String)) (! (ua bij))) 
                       (Some (transport (λ X → Nat × Bool × X) (ua bij) p , s)) =〈 Refl 〉
              Some ((transport (λ X₁ →((Nat × Bool × X₁) × String)) (! (ua bij))) 
                    (transport (λ X → Nat × Bool × X) (ua bij) p , s)) =〈 ap Some (ap= (transport-× (! (ua bij)) (λ X₁ → Nat × Bool × X₁) (λ _ → String))) 〉
              Some
                (×map (transport (λ X₁ → Nat × Bool × X₁) (! (ua bij)))
                      (transport (λ _ → String) (! (ua bij)))
                      (transport (λ X₁ → Nat × Bool × X₁) (ua bij) p , s)) =〈 Refl 〉 
              Some
                (transport (λ X₁ → Nat × Bool × X₁) (! (ua bij))
                           (transport (λ X₁ → Nat × Bool × X₁) (ua bij) p) , 
                 transport (λ _ → String) (! (ua bij)) s) =〈 ap (λ x → Some (x , transport (λ _ → String) (! (ua bij)) s)) (ap= (transport-inv-1 (λ X₁ → Nat × Bool × X₁) (ua bij))) 〉 
              Some
                (p ,
                 transport (λ _ → String) (! (ua bij)) s) =〈 ap (λ x → Some (p , x)) (ap= (transport-constant (! (ua bij)))) 〉 
              Some (p , s) ∎


  -- ----------------------------------------------------------------------

  {- TASK 3: Extend the Semigroup example that we did in lecture to monoids.
     A monoid is a semigroup that additional has a unit (u) for ⊙.
     So we have an additional field u, as well as proofs that it is a left and right unit.  
   -}

  record Monoid (A : Type) : Type where
    constructor monoid
    field
      _⊙_ : A → A → A
      u   : A
      assoc : (x y z : A) → x ⊙ (y ⊙ z) == (x ⊙ y) ⊙ z
      unitl : (x : A) → u ⊙ x == x
      unitr : (x : A) → x ⊙ u == x

  {- TASK 3a: implement transport for Monoid by hand: show that you can 
              coerce a Monoid by a bijection -}
  transport-Monoid-byhand  : ∀ {A B} -> Bijection A B → Monoid A → Monoid B
  transport-Monoid-byhand {A}{B} (f , is-bijection g α β) (monoid _⊙_ u assoc unitl unitr) = (monoid _⊙'_ u' assoc' unitl' unitr') where  
    _⊙'_ : B → B → B
    y1 ⊙' y2 = f (g y1 ⊙ g y2) 

    u' : B 
    u' = f u

    assoc' : ∀ y1 y2 y3 -> y1 ⊙' (y2 ⊙' y3) == (y1 ⊙' y2) ⊙' y3
    assoc' y1 y2 y3 = y1 ⊙' (y2 ⊙' y3)               =〈 Refl 〉 
                      f (g y1 ⊙ g (f (g y2 ⊙ g y3))) =〈 ap (λ z → f (g y1 ⊙ z)) (α (g y2 ⊙ g y3)) 〉 
                      f (g y1 ⊙ (g y2 ⊙ g y3))       =〈 ap f (assoc (g y1) (g y2) (g y3)) 〉 
                      f ((g y1 ⊙ g y2) ⊙ g y3)       =〈 ap (λ z → f (z ⊙ g y3)) (! (α (g y1 ⊙ g y2))) 〉 
                      f (g (f (g y1 ⊙ g y2)) ⊙ g y3) =〈 Refl 〉 
                      (y1 ⊙' y2) ⊙' y3 ∎

    unitl' : (y : B) → u' ⊙' y == y
    unitl' y = f (g (f u) ⊙ g y) =〈 ap (λ x → f (x ⊙ g y)) (α u) 〉
               f (u ⊙ g y) =〈 ap f (unitl (g y)) 〉
               f (g y) =〈 β y 〉
               y ∎

    unitr' : (y : B) → y ⊙' u' == y
    unitr' y = f (g y ⊙ g (f u)) =〈 ap (λ x → f (g y ⊙ x)) (α u) 〉
               f (g y ⊙ u) =〈 ap f (unitr (g y)) 〉 
               f (g y) =〈 β y 〉 
               y ∎

  {- this lemma says that two monoids with the same multiplication and unit,
     but different proofs of associativity and unit laws, are the same
     provided that the proofs of the laws are pointwise equal.
     this saves a little effort below because it builds in some
     uses of function extensionality.
  -}
  monoid-equality-lemma : {A : Type}
      {_⊙_ : A → A → A}
      {u   : A}
      {assoc assoc' : (x y z : A) → x ⊙ (y ⊙ z) == (x ⊙ y) ⊙ z}
      {unitl unitl' : (x : A) → u ⊙ x == x}
      {unitr unitr' : (x : A) → x ⊙ u == x}
      (assoc-eq : (x y z : A) → assoc x y z == assoc' x y z)
      (unitl-eq : (x : A) → unitl x == unitl' x)
      (unitr-eq : (x : A) → unitr x == unitr' x)
      → (monoid _⊙_ u assoc unitl unitr) ==  (monoid _⊙_ u assoc' unitl' unitr') 
  monoid-equality-lemma assoc-eq unitl-eq unitr-eq with (λ= \ x → λ= \ y -> λ= \ z -> assoc-eq x y z) | (λ= unitl-eq) | (λ= unitr-eq)
  monoid-equality-lemma assoc-eq unitl-eq unitr-eq | Refl | Refl | Refl = Refl

  {- TASK 3b 
     Prove that coercing by the identity bijection is the identity.
     You will need to use some of the lemmas from PreliminariesHoTT.    
  -}
  transport-Monoid-byhand-id : {A : Type} (s : Monoid A) -> transport-Monoid-byhand{A}{A} id-bijection s == s
  transport-Monoid-byhand-id {A} (monoid _⊙_ u assoc unitl unitr) = 
    monoid-equality-lemma
      (λ y1 y2 y3 →
         ap-id (assoc y1 y2 y3) ∘ ∘-unit-l (ap (λ x → x) (assoc y1 y2 y3)))
      (λ x → ap-id (unitl x) ∘ ∘-unit-l (ap (λ x₁ → x₁) (unitl x))) 
      (λ x → ap-id (unitr x) ∘ ∘-unit-l (ap (λ x₁ → x₁) (unitr x)))

  {- TASK 3c
     prove that "transport Monoid α" behaves the same as the code you wrote by hand.
     It helps to first prove this for a general equality α.
  -}
  transport-Monoid : ∀ {A B : Type} (α : A == B) (s : Monoid A)
                      →  transport Monoid α s
                      == transport-Monoid-byhand (transport-equiv α) s
  transport-Monoid Refl s = ! (transport-Monoid-byhand-id s)

  {- TASK 3d
     prove that "transport Monoid α" behaves the same as the code you wrote by hand.
     Specialize Task 3c to an application of univalence to a bijection.  
     You will need to use some of the lemmas from PreliminariesHoTT.
  -}
  transport-Monoid' : ∀ {A B : Type} (b : Bijection A B) (s : Monoid A)
                      →  transport Monoid (ua b) s
                      == transport-Monoid-byhand b s
  transport-Monoid' b s = transport Monoid (ua b) s =〈 transport-Monoid (ua b) s 〉 
                          transport-Monoid-byhand (transport-equiv (ua b)) s =〈 ap (λ x → transport-Monoid-byhand x s) (transport-equiv-ua b) 〉 
                          transport-Monoid-byhand b s ∎

  -- ----------------------------------------------------------------------

  {- TASK 4: Do the same thing as the Monoid problem, but for functors -}

  record Functor (F : Type → Type) : Type1 where
    constructor functor
    field
      map         : {A B : Type} → (A → B) → F A → F B
      identity    : {A : Type} (a : F A) → map (\ (x : A) → x) a == a
      composition : {A B C : Type} {g : B → C} {f : A → B} (a : F A) → map (g o f) a == map g (map f a)

  {- TASK 4a: implement it by hand -}
  transport-Functor-byhand : {F G : Type → Type} (n : (X : Type) → Bijection (F X) (G X)) → Functor F → Functor G
  transport-Functor-byhand {F}{G} n (functor map ident comp) = functor map' identity' composition' where
    map' : ∀ {A B} → (A → B) → G A → G B
    map' {A}{B} f a with n B | n A
    ...                | (fB , _) | (_ , is-bijection gA _ _) = fB (map f (gA a))

    identity' : ∀ {A} (a : G A) → map' (\ (x : A) → x) a == a
    identity' {A} a with n A
    ...                | (fA , is-bijection gA αA βA) = βA a ∘ ap (λ h → fA h) (ident (gA a))

    composition' : ∀ {A B C} {g : B → C} {f : A → B} (a : G A) → map' (g o f) a == map' g (map' f a)
    composition' {A}{B}{C} {g}{f} a with n A | n B | n C 
    ... | (fA , is-bijection gA αA βA) | (fB , is-bijection gB αB βB) | (fC , is-bijection gC αC βC) = 
      fC (map (λ x₁ → g (f x₁)) (gA a)) =〈 ap fC (comp (gA a)) 〉
      fC (map g (map f (gA a))) =〈 ap (λ h → fC (map g h)) (! (αB (map f (gA a)))) 〉
      fC (map g (gB (fB (map f (gA a))))) ∎

  functor-equality-lemma : {F : Type → Type} 
                           {map : ∀ {A B} → (A → B) → F A → F B}
                           {identity identity'  : ∀ {A} (a : F A) → map (\ (x : A) → x) a == a}
                           {composition composition' : ∀ {A B C} {g : B → C} {f : A → B} (a : F A) → map (g o f) a == map g (map f a)}
                           → ({A : Type} (a : F A) → identity a == identity' a)
                           → ({A B C : Type} {g : B → C} {f : A → B} (a : F A) → composition{A}{B}{C}{g}{f} a == composition' a)
                           → (functor map identity composition) == (functor map identity' composition')
  functor-equality-lemma {F}{map} ident-eq comp-eq = ap2
                                                       (λ (x : {A : _} (a : F A) → map (λ (x₁ : A) → x₁) a == a)
                                                          (y : {A B C : _} {g : B → C} {f : A → B} (a : F A) → map (g o f) a == map g (map f a)) → functor map x y)
                                                       (λ=i (λ A → λ= (λ a → ident-eq a)))
                                                       (λ=i (λ A → λ=i (λ B → λ=i (λ C → λ=i (λ g → λ=i (λ f → λ= (λ a → comp-eq a)))))))

  {- TASK 4b: show that the by-hand implementation preserves identities -}
  transport-Functor-byhand-id : {F : Type → Type} (func : Functor F)
                             → transport-Functor-byhand (\ A -> id-bijection {F A}) func  == func
  transport-Functor-byhand-id {F} (functor map identity comp) = functor-equality-lemma (λ a → ap-id (identity a) ∘ ∘-unit-l (ap (λ x → x) (identity a)))
                                                                                    (λ a → ap-id (comp a) ∘ ∘-unit-l (ap (λ x → x) (comp a)))

  {- TASK 4c+d: Show that "transport Functor α" behaves the same as the version you wrote by hand. -}
  transport-Functor : {F G : Type → Type} (func : Functor F) (α : F == G) 
                   → transport Functor α func == transport-Functor-byhand (λ X → transport-equiv (ap= α {X})) func
  transport-Functor func Refl = ! (transport-Functor-byhand-id func)

  transport-Functor' : {F G : Type → Type} (func : Functor F) (n : (X : Type) → Bijection (F X) (G X)) 
                   → transport Functor (λ= \ X -> ua (n X)) func == transport-Functor-byhand n func
  transport-Functor' func n = transport Functor (λ= (λ X → ua (n X))) func =〈 transport-Functor func (λ= (λ X → ua (n X))) 〉
                              transport-Functor-byhand (\ X -> transport-equiv (ap= (λ= (λ X → ua (n X))) {X})) func =〈 ap (λ H → transport-Functor-byhand H func) (λ= (λ X → ap transport-equiv (Π=β (λ X₁ → ua (n X₁))))) 〉
                              transport-Functor-byhand (\ X -> transport-equiv (ua (n X))) func =〈 ap (λ x → transport-Functor-byhand x func) (λ= (λ X → transport-equiv-ua (n X))) 〉
                              transport-Functor-byhand n func ∎
