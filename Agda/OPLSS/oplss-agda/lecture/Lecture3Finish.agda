open import Preliminaries

module lecture.Lecture3Finish where

  open Vector using (Vec ; [] ; _::_)
  open Nat using (_+_)
  open List using (_++_ ; [_] ; ++-assoc)

  String = List Char

  lit : Char → String
  lit c = c :: []

  mutual
    data Format : Set where
      bit    : Format
      char   : Format
      nat    : Format
      vec    : (F : Format) (n : Nat) → Format
      done   : Format
      error  : Format
      _then_ : (F1 : Format) (F2 : Data F1 → Format) → Format 
  
    Data : Format → Set
    Data bit = Bool
    Data char = Char
    Data nat  = Nat
    Data (vec F n) = Vec (Data F) n
    Data done = Unit
    Data error = Void
    Data (F1 then F2) = Σ \(d : Data F1) → Data (F2 d)
    
  write : (F : Format) → Data F -> String
  write bit True = lit '1'
  write bit False = lit '0'
  write char c = lit c
  write nat Z = lit 'Z'
  write nat (S n) = lit 'S' ++ write nat n
  write (vec F 0) [] = [] 
  write (vec F (S n)) (x :: xs) = write F x ++ write (vec F n) xs
  write done <> = []
  write error ()
  write (F1 then F2) (d1 , d2) = write F1 d1 ++ write (F2 d1) d2

  mutual
    readVec : (n : Nat) (F : Format) → String -> Maybe (Vec (Data F) n × String)
    readVec Z T s = Some ([] , s)
    readVec (S n) T s with read T s 
    ...                  | None = None 
    ...                  | Some (x , s') with readVec n T s'
    ...                                     | None = None
    ...                                     | Some (xs , s'') = Some (x :: xs , s'')

    read : (F : Format) → String -> Maybe (Data F × String)
    read bit ('0' :: xs) = Some (False , xs)
    read bit ('1' :: xs) = Some (True , xs)
    read bit _ = None
    read char [] = None
    read char (x :: xs) = Some (x , xs)
    read nat ('Z' :: xs) = Some (Z , xs)
    read nat ('S' :: xs) with read nat xs 
    ... | None = None
    ... | Some (n , s') = Some (S n , s')
    read nat _ = None
    read (vec F n) s = readVec n F s
    read done s = Some (<> , s)
    read error s = None
    read (F1 then F2) s with read F1 s
    ...                    | None = None
    ...                    | Some (d1 , s') with read (F2 d1) s' 
    ...                                        | None = None
    ...                                        | Some (d2 , s'') = Some ( (d1 , d2) , s'')

  mutual
    readwrite-vec : (F : Format) (n : Nat) (s : String) (d : Data (vec F n)) → readVec n F (write (vec F n) d ++ s) == Some (d , s)
    readwrite-vec F .0 s [] = Refl
    readwrite-vec F (S n) s (x :: xs) with ((write F x ++ write (vec F n) xs) ++ s) | ++-assoc (write F x) (write (vec F n) xs) s
    readwrite-vec F (S n) s (x :: xs) | .(write F x ++ write (vec F n) xs ++ s) | Refl with read F (write F x ++ write (vec F n) xs ++ s) | readwrite F x (write (vec F n) xs ++ s) 
    readwrite-vec F (S n) s (x :: xs) | .(write F x ++ write (vec F n) xs ++ s) | Refl | .(Some (x , write (vec F n) xs ++ s)) | Refl with readVec n F (write (vec F n) xs ++ s) | readwrite-vec F n s xs 
    readwrite-vec F (S n) s (x :: xs) | .(write F x ++ write (vec F n) xs ++ s) | Refl | .(Some (x , write (vec F n) xs ++ s)) | Refl | .(Some (xs , s)) | Refl = Refl
  
    readwrite : (F : Format) (d : Data F) (s : String) → read F (write F d ++ s) == Some (d , s)
    readwrite bit True s = Refl
    readwrite bit False s = Refl
    readwrite char v s = Refl
    readwrite nat Z s = Refl
    readwrite nat (S y) s with read nat (write nat y ++ s)  | readwrite nat y s
    readwrite nat (S y) s    | .(Some (y , s)) | Refl = Refl
    readwrite (vec F n) d s = readwrite-vec F n s d
    readwrite done d s = Refl
    readwrite error () s
    readwrite (F1 then F2) (d1 , d2) s with ((write F1 d1 ++ write (F2 d1) d2) ++ s) | ++-assoc (write F1 d1) (write (F2 d1) d2) s
    readwrite (F1 then F2) (d1 , d2) s | .(write F1 d1 ++ write (F2 d1) d2 ++ s) | Refl with read F1 (write F1 d1 ++ write (F2 d1) d2 ++ s) | readwrite F1 d1 (write (F2 d1) d2 ++ s) 
    readwrite (F1 then F2) (d1 , d2) s | .(write F1 d1 ++ write (F2 d1) d2 ++ s) | Refl | .(Some (d1 , write (F2 d1) d2 ++ s)) | Refl with read (F2 d1) (write (F2 d1) d2 ++ s) | readwrite (F2 d1) d2 s 
    readwrite (F1 then F2) (d1 , d2) s | .(write F1 d1 ++ write (F2 d1) d2 ++ s) | Refl | .(Some (d1 , write (F2 d1) d2 ++ s)) | Refl | .(Some (d2 , s)) | Refl = Refl

  module Example where

    f : Format 
    f = nat then \ _ -> (vec (vec bit 2) 2)

    example : Data f
    example = (3 , ((True :: False :: []) :: (False :: True :: []) :: []))

    s : String
    s = write f example

    test : s == String.toList "SSSZ1001"
    test = Refl

    test1 : read f s == Some ((3 , ((True :: False :: []) :: (False :: True :: []) :: [])) , [])
    test1 = Refl

    test2 : read nat s == Some (3 , _)
    test2 = Refl

  module Example2 where
    matrix : Format
    matrix = nat then (\ r -> nat then (\ c -> vec (vec bit c) r))

    test : String
    test = write matrix (2 , 3 , (True :: False :: True :: []) :: (False :: True :: False :: []) :: [])


  _suchthat_ : (F : Format) → (Data F → Bool) → Format
  F suchthat p = {!!}

  module Example3 where

    sum : ∀ {n} → Vec Bool n → Nat
    sum = Vector.Vec-elim _ 0 (λ {True _ n → S n; False _ n → n})

    sum2 : ∀ {n m} → Vec (Vec Bool n) m → Nat
    sum2 = Vector.Vec-elim _ 0 (λ v _ r → sum v + r)

    matrix : Format
    matrix = nat then \ r -> 
             nat then \ c -> 
             vec (vec bit c) r then \ mat -> 
             (nat suchthat \ checksum → Nat.equal (sum2 mat) checksum)

    s = String.toList "SSZSSSZ101010SSSZ"

    -- should work after you define suchthat
    -- test : read matrix s == Some _
    -- test = Refl
