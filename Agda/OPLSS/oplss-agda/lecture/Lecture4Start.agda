open import Preliminaries

module lecture.Lecture4Start where











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


    