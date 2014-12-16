open import Preliminaries
open Vector using (Vec ; [] ; _::_)

module handson.Lab3Sol where

  open Nat using (_+_)
  open List using (_++_ ; [_] ; ++-assoc)

  {- Note: for this code, we define a String to be a list of characters -}
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
      {- 
         
         Note: Task 1 is further down the file.  Scroll down and do that, and
         then come back up here and do Task 2.

         
         TASK 2a
         Sometimes we need to deal with file formats that have "extra" stuff in 
         them that we don't want the Agda Data to include.
         For example, a comma-separated list of values would be 
         serialized as "x1,x2,x3,...", but in Agda, we don't want a 
         data structure that contains the ',' characters.

         One way to do this is with a format 
            skip F1 d1 F2 
         The idea is that F1 and F2 are formats, and d1:Data F1.  
         
         The data associated with skip F1 d1 F2 is just the data for F2.

         Reading skip F1 d1 F2 reads an F1, then reads an F2, and 
         returns the second value, ignoring the first.

         Writing writes the default value d1:Data F1 followed by the 
         given value d2:F2.

         Add a constructor for skip, and then, in Tasks 2b-e extend the rest of 
         the code.  
      -}
      skip   : (F1 : Format) (default : Data F1) (F2 : Format) → Format
  
    Data : Format → Set
    Data bit = Bool
    Data char = Char
    Data nat  = Nat
    Data (vec F n) = Vec (Data F) n
    Data done = Unit
    Data error = Void
    Data (F1 then F2) = Σ \(d : Data F1) → Data (F2 d)
    {- TASK 2b -}
    Data (skip F1 _ F2) = Data F2
    
  write : (F : Format) → Data F -> String
  write bit True = lit '1'
  write bit False = lit '0'
  write char c = [ c ]
  write nat Z = lit 'Z'
  write nat (S n) = lit 'S' ++ write nat n
  write (vec T 0) [] = [] 
  write (vec T (S n)) (x :: xs) = write T x ++ write (vec T n) xs
  write done <> = []
  write error ()
  write (F1 then F2) (d1 , d2) = write F1 d1 ++ write (F2 d1) d2
  {- TASK 2c -}
  write (skip F1 d1 F2) d2 = write F1 d1 ++ write F2 d2

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
    {- TASK 2d -}
    read (skip F1 d1 F2) s with read F1 s
    ...                    | None = None
    ...                    | Some (_ , s') = read F2 s'


  mutual
    spec-vec : (F : Format) (n : Nat) (s : String) (d : Data (vec F n)) → readVec n F (write (vec F n) d ++ s) == Some (d , s)
    spec-vec F .0 s [] = Refl
    spec-vec F (S n) s (x :: xs) with ((write F x ++ write (vec F n) xs) ++ s) | ++-assoc (write F x) (write (vec F n) xs) s
    spec-vec F (S n) s (x :: xs) | .(write F x ++ write (vec F n) xs ++ s) | Refl with read F (write F x ++ write (vec F n) xs ++ s) | spec F x (write (vec F n) xs ++ s) 
    spec-vec F (S n) s (x :: xs) | .(write F x ++ write (vec F n) xs ++ s) | Refl | .(Some (x , write (vec F n) xs ++ s)) | Refl with readVec n F (write (vec F n) xs ++ s) | spec-vec F n s xs 
    spec-vec F (S n) s (x :: xs) | .(write F x ++ write (vec F n) xs ++ s) | Refl | .(Some (x , write (vec F n) xs ++ s)) | Refl | .(Some (xs , s)) | Refl = Refl
  
    spec : (F : Format) (d : Data F) (s : String) → read F (write F d ++ s) == Some (d , s)
    spec bit True s = Refl
    spec bit False s = Refl
    spec char v s = Refl
    spec nat Z s = Refl
    spec nat (S y) s with read nat (write nat y ++ s)  | spec nat y s
    spec nat (S y) s    | .(Some (y , s)) | Refl = Refl
    spec (vec F n) d s = spec-vec F n s d
    spec done d s = Refl
    spec error () s
    spec (F1 then F2) (d1 , d2) s with ((write F1 d1 ++ write (F2 d1) d2) ++ s) | ++-assoc (write F1 d1) (write (F2 d1) d2) s
    spec (F1 then F2) (d1 , d2) s | .(write F1 d1 ++ write (F2 d1) d2 ++ s) | Refl with read F1 (write F1 d1 ++ write (F2 d1) d2 ++ s) | spec F1 d1 (write (F2 d1) d2 ++ s) 
    spec (F1 then F2) (d1 , d2) s | .(write F1 d1 ++ write (F2 d1) d2 ++ s) | Refl | .(Some (d1 , write (F2 d1) d2 ++ s)) | Refl with read (F2 d1) (write (F2 d1) d2 ++ s) | spec (F2 d1) d2 s 
    spec (F1 then F2) (d1 , d2) s | .(write F1 d1 ++ write (F2 d1) d2 ++ s) | Refl | .(Some (d1 , write (F2 d1) d2 ++ s)) | Refl | .(Some (d2 , s)) | Refl = Refl
    {- TASK 2e -}
    spec (skip F1 d1 F2) d2 s with ((write F1 d1 ++ write F2 d2) ++ s) | ++-assoc (write F1 d1) (write F2 d2) s
    spec (skip F1 d1 F2) d2 s | .(write F1 d1 ++ write F2 d2 ++ s) | Refl with read F1 (write F1 d1 ++ write F2 d2 ++ s) | spec F1 d1 (write F2 d2 ++ s)
    spec (skip F1 d1 F2) d2 s | .(write F1 d1 ++ write F2 d2 ++ s) | Refl | .(Some (d1 , write F2 d2 ++ s)) | Refl = spec F2 d2 s 

  module Example where

    f : Format 
    f = nat then (\ _ -> (vec (vec bit 2) 2))

    example : String
    example = write f (3 , ((True :: False :: []) :: (False :: True :: []) :: []))

    test' : read f example == Some ((3 , ((True :: False :: []) :: (False :: True :: []) :: [])) , [])
    test' = Refl

    test'' : read nat example == Some (3 , _)
    test'' = Refl

  module Matrix where
    matrix : Format
    matrix = nat then (\ r -> nat then (\ c -> vec (vec bit c) r))

    example : String
    example = write matrix (2 , 3 , (True :: False :: True :: []) :: (False :: True :: False :: []) :: [])


  {- TASK 1a

     Define a format F suchthat p that represents
     "those elements of Data F where p returns true" 
     The precise value of Data(F suchthat p) is up to you,
     but Data(F suchthat p) should be bijective with 
     (Σ\(d : Data F) → p d == True)

     F suchthat p should be a defined format, in terms of the above 
     constructors---you don't need to extend the above datatype!
  -}
     
  check : Bool -> Format
  check True = done
  check False = error

  _suchthat_ : (F : Format) → (Data F → Bool) → Format
  F suchthat p = F then (\ d → check (p d))

  module MatrixChecksum where

    sum : ∀ {n} → Vec Bool n → Nat
    sum = Vector.Vec-elim _ 0 (λ {True _ n → S n; False _ n → n})

    sum2 : ∀ {n m} → Vec (Vec Bool n) m → Nat
    sum2 = Vector.Vec-elim _ 0 (λ v _ r → sum v + r)

    matrix : Format
    matrix = nat then \ r -> 
             nat then \ c -> 
             vec (vec bit c) r then \ mat -> 
             (nat suchthat \ checksum → Nat.equal (sum2 mat) checksum)

    {- Task 1b 
       The checksum for the matrix represented by the string 's' is 3.
       Corrupt the checksum and see read returns None.
    -}
    s = String.toList "SSZSSSZ101010SSSZ"

    test : read matrix s == Some _
    test = Refl
    

  module CSL where

     {- Task 3a 
        Define a format 'exactly c' that reads and writes exactly the character c.
        Data(exactly c) is up to you.  
     -}
     exactly : Char → Format
     exactly c = char suchthat (λ c' → Char.equalb c c')

     {- Task 3b
        Define a format csl F representing comma-separated lists of elements of type F.  

        The string representation should be a header field describing the length,   
        then a comma, then the elements of the list, separated by commas:
        <length>,x_1,...,x_<length>
        (where length is the string representation of a nat).

        Data (csl F) should be Σ \n → Vec (Data F n)
        i.e. the data should not include the commas.  
     -}
     csl : Format → Format
     csl F = nat then (\ l -> vec (skip (exactly ',') (',' , <>) F) l)

     {- When you're done, the following two tests should pass: -}
     test1 : write (csl char) (2 , ('a' :: 'b' :: [])) == 'S' :: 'S' :: 'Z' :: ',' :: 'a' :: ',' :: 'b' :: []
     test1 = Refl

     test2 : read (csl char) ('S' :: 'S' :: 'Z' :: ',' :: 'h' :: ',' :: 'i' :: []) == Some (String.toVec "hi" , [])
     test2 = Refl

     {- Task 4 
        Consider the following format1, where
        Data format1 = Nat × Bool × (Σ \n → Vec Char n)

        For some purposes, it may be more useful to convert (Σ \n → Vec Char n) 
        to a string (list of characters), rather than representing the list as "header + vector".    

        Define functions read1 and write1 that do this conversion, and then prove that they
        still satisfy the spec.

        Hint: see Vector.fromList, Vector.toList', and Vector.from-to in Preliminaries.agda
     -}

     format1 = nat then \ _ → bit then \ _ -> csl char 

     write1 : (Nat × Bool × String) → String
     write1 (n , b , s) = write format1 (n , b , Vector.fromList s)

     read1 : String -> Maybe ((Nat × Bool × String) × String)
     read1 s with read format1 s
     ...      | None = None
     ...      | Some ((n , b , cv) , s') = Some ((n , b , Vector.toList' cv) , s')
  
     spec1 : (p : (Nat × Bool × String)) (s : String) 
           → read1 (write1 p ++ s) == Some (p , s)
     spec1 (n , b , s) s' with read format1 ((write format1 (n , b , Vector.fromList s)) ++ s') | spec format1 (n , b , Vector.fromList s) s' 
     spec1 (n , b , s) s' | .(Some ((n , b , Vector.fromList s) , s')) | Refl with Vector.toList' (Vector.fromList s) | Vector.to-from s 
     spec1 (n , b , s) s' | .(Some ((n , b , Vector.fromList s) , s')) | Refl | .s | Refl = Refl
  

