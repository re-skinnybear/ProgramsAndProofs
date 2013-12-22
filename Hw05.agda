{- Name: Theodore (Ted) Kim
-}

module Hw05 where

  -- ----------------------------------------------------------------------
  -- library code 

  -- natural numbers
  data Nat : Set where
    Z : Nat
    1+ : Nat -> Nat

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

  _≤_ : Nat → Nat → Set
  Z ≤ m = Unit
  1+ n ≤ Z = Void
  1+ n ≤ 1+ m = n ≤ m

  ≤-refl : (x : Nat) → x ≤ x 
  ≤-refl Z = <>
  ≤-refl (1+ x) = ≤-refl x

  ≤-1+ : (x : Nat) → x ≤ 1+ x
  ≤-1+ Z = <>
  ≤-1+ (1+ x) = ≤-1+ x

  ≤-trans : (x y z : Nat) → x ≤ y → y ≤ z → x ≤ z
  ≤-trans Z Z Z e1 e2 = <>
  ≤-trans Z Z (1+ z) e1 e2 = <>
  ≤-trans Z (1+ y) Z e1 e2 = <>
  ≤-trans Z (1+ y) (1+ z) e1 e2 = <>
  ≤-trans (1+ x) Z Z e1 e2 = e1
  ≤-trans (1+ x) Z (1+ z) e1 e2 = abort e1
  ≤-trans (1+ x) (1+ y) Z e1 e2 = abort e2
  ≤-trans (1+ x) (1+ y) (1+ z) e1 e2 = ≤-trans x y z e1 e2

  data _==_ {A : Set} (x : A) : A → Set where
    Refl : x == x

  plus : Nat → Nat → Nat 
  plus Z m = m
  plus (1+ n) m = 1+ (plus n m)

  plus-rh-Z : (n : Nat) → n == (plus n Z)
  plus-rh-Z Z = Refl
  plus-rh-Z (1+ n) with plus n 0 | plus-rh-Z n
  ... | .n | Refl = Refl

  plus-rh-S : (n m : Nat) → (1+ (plus n m)) == (plus n (1+ m))
  plus-rh-S Z m = Refl 
  plus-rh-S (1+ n) m with 1+ (plus n m) | plus-rh-S n m
  ... | .(plus n (1+ m)) | Refl = Refl


  {- ----------------------------------------------------------------------
     PROBLEM 1: Correctness of insertion sort

     In this problem, you will use Agda to formalize the proof that 
     insertion sort is correct that we did on HW 1.  This will involve practicing 
     using 'with' and implicit arguments.  

     ---------------------------------------------------------------------- -}

  {- TASK 1.1: Define a function that tests whether one number
               is ≤ another.
  -}
  check≤ : (m n : Nat) → Either (m ≤ n) (n ≤ m)
  check≤ Z Z = Inl <>
  check≤ Z (1+ n) = Inl <>
  check≤ (1+ m) Z = Inr <>
  check≤ (1+ m) (1+ n) = check≤ m n

  {- TASK 1.2: Define a function insert n l that, given 
     a list l that is sorted in increasing order,
     inserts n into the correct place so that 
     the resulting list is sorted. -}
  insert : Nat → List Nat → List Nat
  insert n [] = n :: []
  insert n (x :: xs) with check≤ n x
  ... | Inl less  = n :: x :: xs
  ... | Inr greater  = x :: insert n xs

  {- TASK 1.3: Use insert to define insertion sort, 
     which takes a list and returns a sorted list 
     with all the same elements. -}
  isort : List Nat → List Nat
  isort [] = []
  isort (x :: xs) = insert x (isort xs)


  {- Next, we define what it means for a list to be sorted. 

     NOTE: ***This is a slightly different definition than we used in HW 1.  
     You may want to redo your informal proof for this definition before
     trying the Agda version.***

     This definition allows a slightly simpler proof, where we can avoid 
     the lemma that insert n xs is a permutation of n::xs.  
  -}

  {- The inductive family (x ≤Head xs) means 
     "if xs has a head then x ≤ the head of xs".  

     This captures the idea that "x is ≤ everything in xs", when xs is a sorted list:
     When xs is empty, x is trivially ≤ everything in the empty list, so there 
     is nothing to prove.   When xs has a head, x ≤ the head, and the head ≤ everything in xs 
     (because it is sorted), so x ≤ everything in xs by transitivity.  
  -}
  data _≤Head_ (n : Nat) : List Nat → Set where
    NoHead  : n ≤Head []
    HasHead : (x : Nat) (xs : List Nat) → n ≤ x → n ≤Head (x :: xs) 

  {- The empty list is sorted.
     x :: xs is sorted if xs is sorted, and x is ≤ the head of xs (if it has one). -}
  data Sorted : List Nat → Set where
    Sorted[] : Sorted []
    Sorted:: : (x : Nat) (xs : List Nat) → x ≤Head xs → Sorted xs → Sorted (x :: xs) 

  {- TASK 1.4: prove the following lemma, which says that 
     if x ≤ n and x ≤ the head of xs, then x ≤ the head of insert n xs.
  -}
  head-lemma : (x n : Nat) (xs : List Nat) → x ≤ n → x ≤Head xs → x ≤Head (insert n xs)
  head-lemma x n .[] x≤n NoHead = HasHead n [] x≤n
  head-lemma x n .(x' :: xs) x≤n (HasHead x' xs p) with check≤ n x'
  ... | Inl less = HasHead n (x' :: xs) x≤n
  ... | Inr greater = HasHead x' (insert n xs) p

  {- TASK 1.5: prove that inserting into a sorted list computes a sorted list. -}
  insert-sorted : {n : Nat} {l : List Nat}
                → Sorted l
                → Sorted (insert n l)
  insert-sorted Sorted[] = Sorted:: _ [] NoHead Sorted[]
  insert-sorted {n = n'} (Sorted:: x xs p S) with check≤ n' x
  ... | Inl less = Sorted:: n' (x :: xs) (HasHead x xs less) (Sorted:: x xs p S)
  ... | Inr greater = Sorted:: x (insert n' xs) (head-lemma x n' xs greater p) (insert-sorted S)
   
  {- TASK 1.6: prove that insertion sort computes a sorted list. -}
  isort-sorted : (l : List Nat) → Sorted (isort l)
  isort-sorted [] = Sorted[]
  isort-sorted (x :: xs) = insert-sorted (isort-sorted xs)

  
  {- ----------------------------------------------------------------------
     PROBLEM 2: Intrinsic verification
     ---------------------------------------------------------------------- -}

  data Vec (A : Set) : Nat → Set where
    []v   : Vec A 0
    _::v_ : {n : Nat} → A → Vec A n → Vec A (1+ n)

  {- TASK 2.1: define filter on vectors.
     The type of filter expresses what it does to the length of the vector.  
  -}
  vfilter : {A : Set} {n : Nat} → (A → Bool) → Vec A n → Σ[ m ∈ Nat ] ((m ≤ n) × Vec A m)
  vfilter p []v = 0 , <> , []v
  vfilter {n = (1+ n')} p (x ::v v) with p x | vfilter p v
  ... | True | (m , m≤n , vfiltered) = 1+ m , (m≤n , x ::v vfiltered)
  ... | False | (m , n≤m , vfiltered) = m , (≤-trans m _ (1+ _) n≤m (≤-1+ (1+ n')) , vfiltered)

  {- TASK 2.2: Define a function that, given two vectors v1 and v2, appends them into one vector
               I.e. it should concatenate them into one vector, with the elements of v1 before the elements of v2.

               Give a type for this function, and fill in the definition.  
     -}
  vappend : {A : Set} {n₁ n₂ : Nat} → Vec A n₁ → Vec A n₂ → Vec A (plus n₁ n₂)
  vappend []v v₂ = v₂
  vappend (x ::v v₁) v₂ = x ::v vappend v₁ v₂