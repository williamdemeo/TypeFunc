
open import PreliminariesHoTT

module lecture.Lecture5Start where

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
