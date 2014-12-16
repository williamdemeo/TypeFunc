
open import PreliminariesHoTT

module lecture.Lecture5Finish where


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

  swap : Bijection (Nat × Nat) (Nat × Nat)
  swap = (swapf , is-bijection swapf (λ _ → Refl) (λ _ → Refl))

  There : Set → Set
  There A = List (Nat × String × A × Nat)

  convert : DB → DB
  convert d = transport There (ua swap) d

  convert-bijection : Bijection DB DB
  convert-bijection = (convert , transport-is-bijection There (ua swap))



  Semigroup : Set → Set
  Semigroup A = Σ \  (_⊙_ : A → A → A) → 
                     (x y z : A) → x ⊙ (y ⊙ z) == (x ⊙ y) ⊙ z

  transport-Semigroup-byhand  : {A B : Set} → Bijection A B → Semigroup A → Semigroup B
  transport-Semigroup-byhand {A}{B} (f , is-bijection g α β) (_⊙_ , assoc) = (_⊙'_ , assoc') where  
    _⊙'_ : B → B → B
    y1 ⊙' y2 = f (g y1 ⊙ g y2) 

    assoc' : (y1 y2 y3 : B) → y1 ⊙' (y2 ⊙' y3) == (y1 ⊙' y2) ⊙' y3
    assoc' y1 y2 y3 = y1 ⊙' (y2 ⊙' y3)               =〈 Refl 〉 
                      f (g y1 ⊙ g (f (g y2 ⊙ g y3))) =〈 ap (λ z → f (g y1 ⊙ z)) (α (g y2 ⊙ g y3)) 〉 
                      f (g y1 ⊙ (g y2 ⊙ g y3))       =〈 ap f (assoc (g y1) (g y2) (g y3)) 〉 
                      f ((g y1 ⊙ g y2) ⊙ g y3)       =〈 ap (λ z → f (z ⊙ g y3)) (! (α (g y1 ⊙ g y2))) 〉 
                      f (g (f (g y1 ⊙ g y2)) ⊙ g y3) =〈 Refl 〉 
                      (y1 ⊙' y2) ⊙' y3 ∎
