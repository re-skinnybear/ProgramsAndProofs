{- Theodore (Ted) Kim
-}

open import lib.Preliminaries
open Vector using (Vec ; [] ; _::_)

module Hw08 where

  open Nat using (_+_)
  open List using (_++_ ; [_] ; ++-assoc)

  lit : Char → List Char
  lit c = c :: []

  mutual
    data Format : Set where
      bit    : Format
      char   : Format
      nat    : Format
      vec    : (F : Format) (n : Nat) → Format
      _then_ : (F1 : Format) (F2 : Data F1 → Format) → Format 
      done   : Format
      error  : Format
      {- for PROBLEM 3 -}
      skip   : (F1 : Format) (default : Data F1) (F2 : Format) → Format
  
    Data : Format → Set
    Data bit = Bool
    Data char = Char
    Data nat  = Nat
    Data (vec F n) = Vec (Data F) n
    Data done = Unit
    Data error = Void
    Data (F1 then F2) = Σ \(d : Data F1) → Data (F2 d)
    {- for PROBLEM 3 -}
    Data (skip F1 _ F2) = Data F2


  {- ----------------------------------------------------------------------
     PROBLEM 1
     ---------------------------------------------------------------------- -}
    
  {- TASK 1.1: add cases to read and write for
     the formats 'done' and 'error'.

     As you can see from the above definitions, the format done represents Unit;
     the format error represents Void.  Given an implementation of read and write
     for these types that satisfies the readwrite spec discussed in class.
  -}

  write : (F : Format) → Data F -> List Char
  write bit True = lit '1'
  write bit False = lit '0'
  write char c = [ c ]
  write nat Z = lit 'Z'
  write nat (S n) = lit 'S' ++ write nat n
  write (vec T 0) [] = [] 
  write (vec T (S n)) (x :: xs) = write T x ++ write (vec T n) xs
  write done <> = []
  write error v = abort v
  write (F1 then F2) (d1 , d2) = write F1 d1 ++ write (F2 d1) d2
  write (skip F1 default F2) d2 = write F1 default ++ write F2 d2

  mutual
    readVec : (n : Nat) (F : Format) → List Char -> Maybe (Vec (Data F) n × List Char)
    readVec Z T s = Some ([] , s)
    readVec (S n) T s with read T s 
    ...                  | None = None 
    ...                  | Some (x , s') with readVec n T s'
    ...                                     | None = None
    ...                                     | Some (xs , s'') = Some (x :: xs , s'')

    read : (F : Format) → List Char -> Maybe (Data F × List Char)
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
    read (F1 then F2) s with read F1 s
    ...                    | None = None
    ...                    | Some (d1 , s') with read (F2 d1) s' 
    ...                                        | None = None
    ...                                        | Some (d2 , s'') = Some ( (d1 , d2) , s'')
    read done s = Some (<> , s)
    read error s = None
    read (skip F1 default F2) s with (read F1 s)
    ... | None = None
    ... | Some (d1 , s') with read F2 s'
    ...        | None = None
    ...        | Some (d2 , s'') = Some (d2 , s'')


  {- Here are some example using the library: -}

  module Examples where

    f : Format 
    f = nat then (\ _ -> (vec (vec bit 2) 2))

    example : List Char
    example = write f (3 , ((True :: False :: []) :: (False :: True :: []) :: []))

    test' : read f example == Some ((3 , ((True :: False :: []) :: (False :: True :: []) :: [])) , [])
    test' = Refl

    test'' : read nat example == Some (3 , _)
    test'' = Refl


    matrix : Format
    matrix = nat then (\ r -> nat then (\ c -> vec (vec bit c) r))

    examplemat : Data matrix
    examplemat = (2 , 3 , (True :: False :: True :: []) :: (False :: True :: False :: []) :: [])
    
    test1 : write matrix examplemat == String.toList "SSZSSSZ101010"
    test1 = Refl


  {- TASK 1.2

     Define a format F suchthat p that represents
     "those elements of Data F where p returns true" 

     F suchthat p should be a defined format, in terms of the above 
     constructors---you don't need to extend the above datatype!

     Hint: use Task 1.1!
  -}
  suchthat' : (p : Bool) → Format
  suchthat' True = done
  suchthat' False = error
   
  _suchthat_ : (F : Format) → (Data F → Bool) → Format
  F suchthat p = F then (λ x → suchthat' (p x))

  module MatrixChecksum where

    sum : ∀ {n} → Vec Bool n → Nat
    sum = Vector.Vec-elim _ 0 (λ {True _ n → S n; False _ n → n})

    sum2 : ∀ {n m} → Vec (Vec Bool n) m → Nat
    sum2 = Vector.Vec-elim _ 0 (λ v _ r → sum v + r)

    {- TASK 1.3: 
       First, review the matrix format defined above ("matrix").

       Now, define a matrix format that includes a "checksum": an
       extra number that is the sum of all of the entries in the matrix.
       The data for this format should be something like:

       (<rows>,<cols>, <data>:vec (vec bit cols) rows, <checksum>)

       where checksum is the sum of all entries in <data>.

       Hints: use Task 1.2!
              You can use the function sum2 defined above to sum a nxm vector.
              You can use the function
                Nat.equal : Nat → Nat → Bool
              to test whether two nats are equal.
    -}
       
    matrix : Format
    matrix = nat then (λ r → nat then (λ c → vec (vec bit c) r then (λ n → nat suchthat (Nat.equal (sum2 n)))))

    {- For example, when you have completed task 1.3, the following test should pass,
       because the sum of the matrix is 3.  -}
    s = String.toList "SSZSSSZ101010SSSZ"

    test : read matrix s == Some _
    test = Refl


  {- ----------------------------------------------------------------------
     PROBLEM 2:
     ----------------------------------------------------------------------
  -}

  postulate
      readwrite-vec : (F : Format) (n : Nat) (s : List Char) (d : Data (vec F n)) → readVec n F (write (vec F n) d ++ s) == Some (d , s)
  
  mutual
    {- TASK 2.1: Finish the case of the proof of the read/write spec for 'then' and 'done' and 'error'.
       You do not need to do the case for vec.
    -}
    readwrite : (F : Format) (d : Data F) (s : List Char) → read F (write F d ++ s) == Some (d , s)
    readwrite bit True s = Refl
    readwrite bit False s = Refl
    readwrite char v s = Refl
    readwrite nat Z s = Refl
    readwrite nat (S y) s with read nat (write nat y ++ s)  | readwrite nat y s
    readwrite nat (S y) s    | .(Some (y , s)) | Refl = Refl
    readwrite (vec F n) d s = readwrite-vec F n s d
    readwrite done <> s = Refl
    readwrite error () s
    readwrite (F1 then F2) (d1 , d2) s with ((write F1 d1 ++ write (F2 d1) d2) ++ s) | ++-assoc (write F1 d1) (write (F2 d1) d2) s
    readwrite (F1 then F2) (d1 , d2) s | .(write F1 d1 ++ write (F2 d1) d2 ++ s) | Refl with (read F1 (write F1 d1 ++ write (F2 d1) d2 ++ s)) | readwrite F1 d1 (write (F2 d1) d2 ++ s)
    readwrite (F1 then F2) (d1 , d2) s | .(write F1 d1 ++ write (F2 d1) d2 ++ s) | Refl | .(Some (d1 , write (F2 d1) d2 ++ s)) | Refl with (read (F2 d1) (write (F2 d1) d2 ++ s)) | readwrite (F2 d1) d2 s
    readwrite (F1 then F2) (d1 , d2) s | .(write F1 d1 ++ write (F2 d1) d2 ++ s) | Refl | .(Some (d1 , write (F2 d1) d2 ++ s)) | Refl | .(Some (d2 , s)) | Refl = Refl
    readwrite (skip F1 d1 F2) d2 s with (write F1 d1 ++ write F2 d2) ++ s | ++-assoc (write F1 d1) (write F2 d2) s
    readwrite (skip F1 d1 F2) d2 s | .(write F1 d1 ++ write F2 d2 ++ s) | Refl with (read F1 (write F1 d1 ++ write F2 d2 ++ s)) | readwrite F1 d1 (write F2 d2 ++ s)
    readwrite (skip F1 d1 F2) d2 s | .(write F1 d1 ++ write F2 d2 ++ s) | Refl | .(Some (d1 , write F2 d2 ++ s)) | Refl with (read F2 (write F2 d2 ++ s)) | readwrite F2 d2 s
    readwrite (skip F1 d1 F2) d2 s | .(write F1 d1 ++ write F2 d2 ++ s) | Refl | .(Some (d1 , write F2 d2 ++ s)) | Refl | .(Some (d2 , s)) | Refl = Refl

    

  {- ----------------------------------------------------------------------
     PROBLEM 3: 
     ---------------------------------------------------------------------- -}

  {- 
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
  -}

  {-
     TASK 3.1: uncomment the constructor Skip in the definition of Format,
     and the case for Data (Skip ...).

     Then, add cases for read, write, and readwrite.
  -}

  module CSL where

     {- Task 3.2 
        Define a format 'exactly c' that reads and writes exactly the character c.
        Data(exactly c) is up to you.  
        Hint: You can use 
          Char.equalb : Char → Char → bool
        to test equality of two characters
     -}
     exactly : Char → Format
     exactly c = char suchthat (Char.equalb c)

     {- Task 3.3
        Define a format csl F representing comma-separated lists of elements of type F.  

        The string representation should be a header field describing the length,   
        then a comma, then the elements of the list, separated by commas:
        <length>,x_1,...,x_<length>
        (where length is the string representation of a nat).

        Data (csl F) should be Σ \n → Vec (Data F n)
        i.e. the data should not include the commas.  

        Hint: use Task 3.2!
     -}
     csl : Format → Format
     csl F = nat then (λ n → vec (skip (exactly ',') (',' , <>) F) n)

     {- When you're done, the following two tests should pass: -}
     test1 : write (csl char) (2 , ('a' :: 'b' :: [])) == 'S' :: 'S' :: 'Z' :: ',' :: 'a' :: ',' :: 'b' :: []
     test1 = Refl

     test2 : read (csl char) ('S' :: 'S' :: 'Z' :: ',' :: 'h' :: ',' :: 'i' :: []) == Some (String.toVec "hi" , [])
     test2 = Refl


