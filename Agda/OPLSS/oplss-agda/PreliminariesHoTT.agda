
{-# OPTIONS --without-K #-}

import Preliminaries 

module PreliminariesHoTT where

   open Preliminaries public

   Type : Set1
   Type = Set

   Type1 : Set2
   Type1 = Set1

   Type-_ : (l : Level) → Set (lS l)
   Type- l = Set l

   record IsBijection {l : Level} {A B : Type- l} (f : A → B) : Type- l where
     constructor is-bijection 
     field 
        g : B → A
        α : (x : A) → (g (f x)) == x
        β : (y : B) → (f (g y)) == y

   Bijection : Type -> Type -> Type
   Bijection A B = Σ \(f : A → B) → IsBijection f

   -- this can be proved, but it would require importing a bunch more of the HoTT library,
   -- so we'll just postulate it here.  
   postulate 
     bijection= : {A B : Type} {f1 f2 : A → B} {g1 : IsBijection f1} {g2 : IsBijection f2} 
                → f1 == f2
                → _==_ {_}{Bijection A B} (f1 , g1) (f2 , g2)

   id-bijection : {A : Type} → Bijection A A
   id-bijection = ((\ x -> x) , is-bijection (\ x -> x) (\ _ -> Refl) (\ _ -> Refl))

   ap-id : {A : Type} {M N : A} (α : M == N)
         → (ap (\ x → x) α) == α
   ap-id Refl = Refl

   ap= : {l1 l2 : Level} {A : Type- l1} {B : A → Type- l2} {f g : (x : A) → B x} 
        → f == g → {x : A} → (f x) == (g x)
   ap= α {x} = ap (\ f → f x) α

   ∘-assoc  : {A : Type} {M N P Q : A} 
            (γ : P == Q) (β : N == P) (α : M == N) 
            → (γ ∘ (β ∘ α)) == ((γ ∘ β) ∘ α)
   ∘-assoc Refl Refl Refl = Refl
   
   !-inv-l  : {A : Type} {M N : A} (α : M == N) → (! α ∘ α) == Refl
   !-inv-l Refl = Refl
   
   !-inv-r : {A : Type} {M N : A} (α : M == N) → (α ∘ (! α)) == Refl
   !-inv-r Refl = Refl

   ∘-unit-l  : {A : Type} {M N : A} (α : M == N)
               → (Refl ∘ α) == α
   ∘-unit-l Refl = Refl
  
   ∘-unit-r  : {A : Type} {M N : A} (α : M == N)
             → (α ∘ Refl) == α
   ∘-unit-r Refl = Refl

   transport-inv-1 : {l1 l2 : Level} {A : Type- l1} (B : A -> Type- l2) {M N : A} (α : M == N) -> (\y -> transport B (! α) (transport B α y)) == (\ x -> x)
   transport-inv-1 _ Refl = Refl
  
   transport-inv-2 : {l1 l2 : Level} {A : Type- l1} (B : A -> Type- l2) {M N : A} (α : M == N) -> (\y -> transport B α (transport B (! α) y)) == (\ x -> x)
   transport-inv-2 _ Refl = Refl

   transport-is-bijection : {l1 l2 : Level} {A : Type- l1} {M N : A} (B : A → Type- l2) (α : M == N) -> IsBijection (transport B α)
   transport-is-bijection {A}{M} B α = is-bijection (transport B (! α)) (λ x → ap= (transport-inv-1 B α)) (λ x → ap= (transport-inv-2 B α)) 

   transport-bijection : {A B : Type} (α : A == B) -> Bijection A B
   transport-bijection α = (transport (\ X -> X) α , transport-is-bijection (\ X -> X) α)

   postulate 
     ua : {A B : Type} → Bijection A B → _==_{_}{Type} A B

     transport-Here  : {A B : Type} → (b : Bijection A B) → transport (\ X -> X) (ua b) == fst b
     transport-Here! : {A B : Type} → (b : Bijection A B) → transport (\ X -> X) (! (ua b)) == IsBijection.g (snd b)

     Π=β : {l1 l2 : Level} {A : Type- l1} {B : A -> Type- l2} {f g : (x : A) -> B x} -> (α : (x : A) -> (f x) == (g x)) {N : A}
         -> ap= (λ= α) {N} == (α N)

   transport-List : {l1 l2 : Level} {A : Type- l1} {M N : A} (C : A -> Type- l2) (α : M == N)
                   → transport (\ x -> List (C x)) α
                   == List.map (transport C α) 
   transport-List C Refl = ! (λ= List.map-id)

   ×map : {l1 l2 l3 l4 : Level} {A : Type- l1} {A' : Type- l2} {B : Type- l3} {B' : Type- l4} → (A → A') → (B → B') → A × B → A' × B'
   ×map f g (x , y) = (f x , g y)
 
   transport-× : {l1 : Level} {l2 : Level} {A : Type- l1} {a1 a2 : A} (α : a1 == a2) (B1 B2 : A -> Type- l2) 
         -> transport (\ a -> B1 a × B2 a) α == ×map (transport B1 α) (transport B2 α)
   transport-× Refl _ _ = Refl

   transport-constant : {l1 l2 : Level} {A : Type- l1} {C : Type- l2} {M N : A} -> (p : M == N) -> (transport (\ _ -> C) p) == (\ x -> x)
   transport-constant Refl = Refl

   transport-equiv : {A B : Type} (α : A == B) → Bijection A B
   transport-equiv α = (transport (\ X -> X) α , transport-is-bijection (\ X -> X) α)

   transport-equiv-ua : {A B : Type} (b : Bijection A B) → transport-equiv {A} {B} (ua b) == b
   transport-equiv-ua b = bijection= (transport-Here b)

   transport-ap-assoc : {A : Type} (C : A → Type) {M N : A} (α : M == N) 
                      → (transport C α) == (transport (\ x → x) (ap C α))
   transport-ap-assoc _ Refl = Refl

   ap-! : {l1 l2 : Level} {A : Type- l1} {B : Type- l2} (F : A → B) {M N : A} (α : M == N)
       → (ap F (! α)) == (! (ap F α))
   ap-! _ Refl = Refl

   transport-→ :  {A : Type} (B1 B2 : A → Type) {a1 a2 : A} 
                  (α : a1 == a2) (f : B1 a1 → B2 a1) 
               → (transport (\ a → (B1 a) → B2 a) α f)  ==
                 (transport B2 α o f o (transport B1 (! α)))
   transport-→ _ _ Refl f = Refl 

   transport-Path-right :  {A : Type} {M N P : A} 
                           (α' : N == P) (α : M == N)
     → (transport (\ x → M == x) α' α) == (α' ∘ α)
   transport-Path-right Refl Refl = Refl
   
   move-left-! :  {A : Type} {M N P : A} (α : M == N) (β : N == P) (γ : M == P)
            → α == (! β ∘ γ)
            → (β ∘ α) == γ
   move-left-! Refl Refl γ x = ∘-unit-l γ ∘ x

   transport-∘ : {A : Type} (C : A → Type) {M N P : A} (β : N == P) (α : M == N)
               → (transport C (β ∘ α)) == (\ x → transport C β (transport C α x))
   transport-∘ _ Refl Refl = Refl

   path-induction : {A : Type} {M : A}
                  (C : (x : A) → M == x → Type)
               → (C M Refl)
               → {N : A} → (P : M == N)
               → C N P
   path-induction C b Refl = b


   {- DO NOT READ THIS!  It requires some tricks to implement higher inductive 
      types in Agda.  See Lab5-Circle.agda for a description of the interface that this exports.  
   -}
   module S¹ where
       data Phantom {l : Level} {A : Type- l} (x : A) : Type where
         phantom : Phantom x
 
       private
         data S¹' : Type where
           Base : S¹'
 
         data S¹'' : Type where
           mkS¹'' : S¹' → (Unit -> Unit) → S¹''
     
       S¹ : Type
       S¹ = S¹''
     
       base : S¹
       base = mkS¹'' Base _
     
       postulate {- HoTT Axiom -}
         loop : base == base
     
       S¹-rec' : {l : Level} {C : Type- l} 
              -> (c : C)
              -> (α : c == c) (_ : Phantom α)
              -> S¹ -> C
       S¹-rec' a _ phantom (mkS¹'' Base _) = a
 
       S¹-rec : {l : Level} {C : Type- l} 
              -> (c : C)
              -> (α : c == c)
              -> S¹ -> C
       S¹-rec a α = S¹-rec' a α phantom
     
       S¹-elim' :  (C : S¹ -> Type)
               -> (c : C base) 
                  (α : (transport C loop c) == c) (_ : Phantom α)
               -> (x : S¹) -> C x
       S¹-elim' _ x _ phantom (mkS¹'' Base _) = x
 
       S¹-elim :  (C : S¹ -> Type)
               -> (c : C base) 
                  (α : (transport C loop c) == c)
               -> (x : S¹) -> C x
       S¹-elim C c α = S¹-elim' C c α phantom
   
       S¹-induction :  (C : S¹ -> Type)
               -> (c : C base) 
                  (α : (transport C loop c) == c)
               -> (x : S¹) -> C x
       S¹-induction = S¹-elim
     
       postulate {- HoTT Axiom -} 
         βloop/rec : {l : Level} {C : Type- l} 
              -> (c : C)
              -> (α : c == c)
              -> (ap (S¹-rec c α) loop) == α




     