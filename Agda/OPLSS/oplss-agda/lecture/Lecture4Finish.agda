open import Preliminaries

module lecture.Lecture4Finish where

  data Functor : Set1 where
    K      : (A : Set) -> Functor
    X      : Functor 
    list   : (F : Functor) -> Functor
    _×u_   : (F1 F2 : Functor) → Functor

  infixr 10 _×u_

  _·_ : Functor -> Set → Set
  (K B) · _ = B
  X · A = A
  (list F) · A = List (F · A)
  (F1 ×u F2) · A = F1 · A × F2 · A

  map : (F : Functor) {A B : Set} → (A → B) → F · A → F · B 
  map (K A) f x = x
  map X f x = f x
  map (list F) f xs = List.map (map F f) xs
  map (F1 ×u F2) f (x1 , x2) = map F1 f x1 , map F2 f x2

  map-id : (F : Functor) {A : Set} (x : F · A) → map F (\y -> y) x == x
  map-id (K A) x = Refl
  map-id X x = Refl
  map-id (list F) [] = Refl
  map-id (list F) (x :: xs) = ap2 _::_ (map-id F x) (map-id (list F) xs)
  map-id (F1 ×u F2) (x1 , x2) = ap2 _,_ (map-id F1 x1) (map-id F2 x2)

  map-fusion : (F : Functor) {A B C : Set} → {g : B -> C} {f : A → B} → (x : F · A) → map F (g o f) x == map F g (map F f x)
  map-fusion (K A) x = Refl
  map-fusion X x = Refl
  map-fusion (list F) [] = Refl
  map-fusion (list F) (x :: xs) = ap2 _::_ (map-fusion F x) (map-fusion (list F) xs)
  map-fusion (F1 ×u F2) (x1 , x2) = ap2 _,_ (map-fusion F1 x1) (map-fusion F2 x2)


  module Example where

    open String using (String)

    DB : Set
    DB = List (Nat × String × ((Nat × Nat) × Nat))

    euro : DB
    euro = 
      (4  , "John"  , ((30 , 5) , 1956)) ::
      (8  , "Hugo"  , ((29 , 12) , 1978)) ::
      (15 , "James" , ((1 , 7) , 1968)) ::
      (16 , "Sayid" , ((2 , 10) , 1967)) ::
      (23 , "Jack"  , ((3 , 12) , 1969)) ::
      (42 , "Sun"   , ((20 , 3) , 1969)) ::
      []
  
    american : DB 
    american = 
      (4  , "John"  , ((5 , 30) , 1956)) ::
      (8  , "Hugo"  , ((12 , 29) , 1978)) ::
      (15 , "James" , ((7 , 1) , 1968)) ::
      (16 , "Sayid" , ((10 , 2) , 1967)) ::
      (23 , "Jack"  , ((12 , 3) , 1969)) ::
      (42 , "Sun"   , ((3 , 20) , 1969)) ::
      []

    swapf : (Nat × Nat) → (Nat × Nat)
    swapf (x , y) = (y , x)

    There : Functor
    There = list (K Nat ×u K String ×u X ×u K Nat)

    convert : DB → DB
    convert d = map There swapf d

    test : convert euro == american
    test = Refl

    There1 = (K Nat ×u K String ×u X ×u K Nat)
    There2 = (K String ×u X ×u K Nat)

    eval = map There swapf                                                    =〈 Refl 〉 

           List.map (map There1 swapf)                                        =〈 Refl 〉 

           List.map (\ { (k , r) → map (K Nat) swapf k , map There2 swapf r}) =〈 Refl 〉 

           List.map (\ { (k , r) → k , map There2 swapf r})                   =〈 Refl 〉 

           List.map (\ { (k , n , (m , d) , y) → k , n , map X swapf (m , d) , y}) =〈 Refl 〉 

           List.map (\ { (k , n , (m , d) , y) → (k , n , (d , m) , y)}) ∎ 


    IsBijection : {A B : Set} (f : A → B) -> Set
    IsBijection {A}{B} f = 
       Σ \ (g : B → A) →
         ((x : A) → (g (f x)) == x) ×
         ((y : B) → (f (g y)) == y)
  
    Bijection : Set -> Set -> Set
    Bijection A B = Σ(\(f : A → B) → IsBijection f)

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

    swap : Bijection (Nat × Nat) (Nat × Nat)
    swap = (swapf , swapf , (λ _ → Refl) , (λ _ → Refl))

    convert-bijection : Bijection DB DB
    convert-bijection = convert , map-is-bijection There swap

    