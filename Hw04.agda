{- Name: Theodore (Ted) Kim
-}

module Hw04 where

  -- ----------------------------------------------------------------------
  -- library code 

  -- natural numbers
  data Nat : Set where
    Z : Nat
    1+ : Nat -> Nat

  plus : Nat → Nat → Nat 
  plus Z m = m
  plus (1+ n) m = 1+ (plus n m)

  {-# BUILTIN NATURAL Nat #-}
  {-# BUILTIN SUC 1+ #-}
  {-# BUILTIN ZERO Z #-}

  -- ('a,'b) choice from last HW
  data Either (A B : Set) : Set where
    Inl : A → Either A B
    Inr : B → Either A B

  data Maybe (A : Set) : Set where
    Some : A → Maybe A
    None : Maybe A

  -- pairs
  data _×_ (A B : Set) : Set where
    _,_ : A → B → A × B

  fst : {A B : Set} → A × B → A
  fst (x , _) = x

  snd : {A B : Set} → A × B → B
  snd (_ , y) = y

  infixr 10 _,_

  -- unit
  data Unit : Set where
    <> : Unit

  -- existential quantifier
  data Σ (A : Set) (B : A → Set) : Set where
    _,_ : (a : A) → B a → Σ A B

  syntax Σ A (\ x  -> B) = Σ[ x ∈ A ] B

  -- empty type
  data Void : Set where

  abort : ∀ {C : Set} → Void → C
  abort ()

  -- lists
  data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A

  infixr 99 _::_ 

  data Bool : Set where
    True : Bool
    False : Bool

  -- inductive families from lecture

  data Length {A : Set} : List A → Nat → Set where
    L[] : Length [] 0
    L:: : (x : A) (xs : List A) (n : Nat) → Length xs n → Length (x :: xs) (1+ n)

  data _==_ {A : Set} (x : A) : A → Set where
    Refl : x == x

  sym : {A : Set} (x y : A) (p : x == y) → y == x
  sym y .y Refl = Refl

  trans : {A : Set} (x y z : A) (p : x == y) (q : y == z) → x == z
  trans .z .z z Refl Refl = Refl

  {- ----------------------------------------------------------------------
     PROBLEM 1: inductive families warmup
     ----------------------------------------------------------------------
  -}

  {- TASK 1.1:
     Define head (gets the first element of a list) and
     tail (gets the rest of a list with the first element removed) 
     that are guaranteed to succeed, because they can be applied only to 
     non-empty lists.

     Explain why any missing cases are impossible.
  -}
  head : {A : Set} → (xs : List A) (n : Nat) → Length xs (1+ n) -> A
  head .(x :: xs) n (L:: x xs .n L) = x

  tail : {A : Set} → (xs : List A) (n : Nat) → Length xs (1+ n) -> List A
  tail .(x :: xs) n (L:: x xs .n L) = xs

  {- The functions head and tail are missing the empty list cases. The empty list ([])
     cases are impossible, since head and tail require there to be a first element in
     the list. head returns the first element, which cannot occur with [] as there are
     no elements and thus no first element. Similarly, tail returns the rest of a list
     without the first element, which cannot occur with [], as there is no first element
     to remove.
  -}

  {- TASK 1.2:
     Prove that :: takes equals to equals:
     if x == y and xs == ys then x::xs = y::ys
  -}
  ::-cong : {A : Set} (x y : A) (xs ys : List A) → x == y → xs == ys → (x :: xs) == (y :: ys)
  ::-cong .y y .ys ys Refl Refl = Refl

  {- ----------------------------------------------------------------------
     PROBLEM 2: Map fusion
     ----------------------------------------------------------------------
  
     Map fusion is a program optimization: suppose you make two passes over a list,
     by calling map g (map f xs).  Traversing the list twice takes 2n time,
     and builds an intermediate data structure, the result of map f xs,
     which takes O(n) space.  However, this intermediate data structure 
     is immediately used by map g, and never used again.  
     
     We can optimize away the intermediate data structure, and reduce the running time 
     to 1n by "fusing" the two passes into one: replace map g (map f xs) with 
     map (g o f) xs.  In this problem, you will prove that this optimization 
     is correct, in the sense that it preserves the behavior of the program.
  -}

  map : {A B : Set} → (A → B) → List A → List B
  map f [] = []
  map f (x :: xs) = f x :: map f xs

  {- TASK 2.1: Prove map fusion -}
  map-fusion : {A B C : Set} → (f : A → B) (g : B → C) → (xs : List A) → map g (map f xs) == map (\ x -> g (f x)) xs
  map-fusion f g [] = Refl
  map-fusion f g (x :: xs) = ::-cong (g (f x)) (g (f x)) (map g (map f xs)) (map (λ y → g (f y)) xs) Refl (map-fusion f g xs)

  {- ----------------------------------------------------------------------
     PROBLEM 3 : Zip/unzip
     ---------------------------------------------------------------------- -}

  {- TASK 3.1 
     Define a function zip that combines two lists into a list of pairs.
     e.g. zip [1,2,3] [4,5,6] should equal [(1,4),(2,5),(3,6)].
     Do something reasonable for the cases not forced by the above example.  
  -}
  zip : {A B : Set} → List A → List B → List (A × B)
  zip [] [] = []
  zip [] (y :: ys) = []
  zip (x :: xs) [] = []
  zip (x :: xs) (y :: ys) = (x , y) :: zip xs ys

  {- TASK 3.2 
     Define a function unzip that takes a list of pairs and 
     returns the list of left-hand-sides and the list of right-hand-sides.
     e.g. unzip [(1,4),(2,5),(3,6)] should equal ([1,2,3], [4,5,6])
  -}
  unzip : {A B : Set} → List (A × B) → List A × List B 
  unzip [] = [] , []
  unzip (x :: xs) = fst x :: fst (unzip xs) , snd x :: snd (unzip xs)

  {- TASK 3.3:
     The following two propostions state that zip and unzip are 
     _mutually inverse_.  

     For each of these propositions, EITHER
     (1) prove it, or 
     (2) give a counter-example, and then
         strengthen the assumptions about the input so that the conclusion is true,
         and prove your strengthened version.  
  -}

  zip-unzip : {A B : Set} (xs : List (A × B)) → (zip (fst (unzip xs)) (snd (unzip xs))) == xs
  zip-unzip [] = Refl
  zip-unzip ((a , b) :: xs) = ::-cong (a , b) (a , b) (zip (fst (unzip xs)) (snd (unzip xs))) xs Refl (zip-unzip xs)

  {- Counter-example: A: ([1, 2, 3, 4]) and B: ([1, 2, 3]).
     zip xs ys = [(1, 1), (2, 2), (3, 3)]
     unzip (zip xs ys) = ([1, 2, 3]) x ([1, 2, 3])
     Therefore, fst (unzip (zip xs ys)) ≠ xs
     We need to assume that the length of the lists are the same.
  -}
  unzip-zip : {A B : Set} (xs : List A) (ys : List B) (n : Nat) → Length xs n → Length ys n → (fst (unzip (zip xs ys)) == xs) × (snd (unzip (zip xs ys)) == ys)
  unzip-zip .[] .[] .0 L[] L[] = Refl , Refl
  unzip-zip .(x :: xs) .(y :: ys) .(1+ n) (L:: x xs n L1) (L:: y ys .n L2) = ::-cong x x (fst (unzip (zip xs ys))) xs Refl (fst (unzip-zip xs ys n L1 L2)) , ::-cong y y (snd (unzip (zip xs ys))) ys Refl (snd (unzip-zip xs ys n L1 L2))

  {- ----------------------------------------------------------------------
     PROBLEM 4
     ----------------------------------------------------------------------
  -}

  {- recall ≤ from Lecture 5 -}
  _≤_ : Nat → Nat → Set
  Z ≤ m = Unit
  1+ n ≤ Z = Void
  1+ n ≤ 1+ m = n ≤ m

  ≤-1+ : (n : Nat) → n ≤ (1+ n)
  ≤-1+ Z = <>
  ≤-1+ (1+ n) = ≤-1+ n

  {- TASK 4.1: define an inductive family (datatype that tells you stuff)
     Sorted xs, which means that the list xs is sorted in *decreasing* order.
     (e.g. [5,3,1])
  -}

  data Sorted : List Nat → Set where
    S[]  : Sorted []
    S[x] : (x : Nat) → Sorted (x :: [])
    S::  : (x₁ x₂ : Nat) (xs : List Nat) → x₁ ≤ x₂ → Sorted (x₂ :: x₁ :: xs) 

  {- TASK 4.2: to test your definition,
     prove that the function that returns the list [n,n-1,...,0] is sorted 
     in decreasing order.
  -}
  decreasing : Nat → List Nat
  decreasing 0 = 0 :: []
  decreasing (1+ n) = (1+ n) :: decreasing n

  decreasing-sorted : ∀(n : Nat) → Sorted (decreasing n)
  decreasing-sorted Z = S[x] 0
  decreasing-sorted 1 = S:: 0 1 [] (≤-1+ 0)
  decreasing-sorted (1+ (1+ n)) = S:: (1+ n) (1+ (1+ n)) (decreasing n) (≤-1+ (1+ n))