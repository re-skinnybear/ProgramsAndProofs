{- 
Out: Thursday, 9/12/2013
Due: Thursday, 9/19/2013, 10:30am (before class)  

HANDIN INSTRUCTIONS: place Hw02.agda in your handin directory.  
-}

module Hw02 where

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


  -- end library code

  -- ----------------------------------------------------------------------
  -- code from lecture

  double : Nat → Nat
  double Z = Z
  double (1+ n) = 1+ (1+ (double n))

  Equals : Nat → Nat → Set
  Equals Z Z = Unit
  Equals Z (1+ n) = Void
  Equals (1+ n) Z = Void
  Equals (1+ n) (1+ m) = Equals n m

  Even : Nat -> Set 
  Even n = Σ[ k ∈ Nat ] Equals n (double k)

  Odd : Nat -> Set 
  Odd n = Σ[ k ∈ Nat ] Equals n (1+ (double k))

  even0 : Even 0
  even0 = 0 , <>

  evenS : ∀ {n} -> Odd n -> Even (1+ n)
  evenS {n} (k , eq) = 1+ k , eq 

  odd1 : Odd 1
  odd1 = 0 , <>

  oddS : ∀ {n} -> Even n -> Odd (1+ n)
  oddS (k , eq) = k , eq

  div2 : ∀ (n : Nat) -> Either (Even n) (Odd n)
  div2 0 = Inl even0
  div2 (1+ n) 
   with div2 n 
  ... | Inl nIsEven = Inr (oddS {n} nIsEven)
  ... | Inr nIsOdd = Inl (evenS nIsOdd)

  test = div2 9

  -- ----------------------------------------------------------------------
  -- problems

  {- ----------------------------------------------------------------------
     PROBLEM 1 : Basic properties of equality

     Recall the definition "Equals" above.
     In this problem, you will prove some basic properties of equality,
     like reflexivity, symmetry, and transitivity.
  
     ---------------------------------------------------------------------- -}

  {- TASK 1.1: Prove that equality is reflexive, i.e. 
     ∀n:Nat. n = n 
  -}
  refl : (n : Nat) → Equals n n
  refl Z = <>
  refl (1+ n) = refl n

  {- TASK 1.2: Prove that equality is symmetric, i.e., 
     ∀n,m:Nat. (n = m) ⊃ (m = n)
  -}
  sym : (n m : Nat) → Equals n m → Equals m n 
  sym Z Z e = <>
  sym Z (1+ m) e = e
  sym (1+ n) Z e = e
  sym (1+ n) (1+ m) e = sym n m e

  {- TASK 1.3: Prove that equality is transitive, i.e., 
     ∀n,m,p:Nat. (n = m) ⊃ (m = p) ⊃ (n = p)

     Hint: You can case-analyze several variables at once by putting them all 
     in the goal and doing a make-case (C-c C-c).  E.g. if you make-case with the 
     goal {! n m p !} Agda will generate all 8 cases on the three variables.  
  -}
  trans : (n m p : Nat) → Equals n m → Equals m p → Equals n p
  trans Z Z Z e1 e2 = <>
  trans Z Z (1+ p) e1 e2 = e2
  trans Z (1+ m) Z e1 e2 = <>
  trans Z (1+ m) (1+ p) e1 e2 = e1
  trans (1+ n) Z Z e1 e2 = e1
  trans (1+ n) Z (1+ p) e1 e2 = trans n Z p (abort e1) (abort e2)
  trans (1+ n) (1+ m) Z e1 e2 = e2
  trans (1+ n) (1+ m) (1+ p) e1 e2 = trans n m p e1 e2

  {- TASK 1.4: translate the following proposition to an Agda type and prove it:
     ∀n,m:Nat. (n = m) ∨ ¬(n = m)

     Explain what the computational content of this proof is.
     
     This proves that for all natural numbers n and m,  either n and m are equal
     or they are not equal.

  -}

  equality : (n m : Nat) → Either (Equals n m) (Equals n m → Void)
  equality Z Z = Inl (refl Z)
  equality Z (1+ m) = Inr (sym Z (1+ m))
  equality (1+ n) Z = Inr (sym (1+ n) Z)
  equality (1+ n) (1+ m) = equality n m 


  {- ----------------------------------------------------------------------
     PROBLEM 2 : Properties of addition
     ---------------------------------------------------------------------- -}

  -- here is a definition of addition by recursion on the first argument.  
  plus : Nat → Nat → Nat 
  plus Z m = m
  plus (1+ n) m = 1+ (plus n m)

  {- TASK 2.1: Prove that ∀n. n = n + 0 
     Note that 0 + n = n is true by definition, but n = n + 0 
     requires an inductive proof.  
  -}
  plus-rh-Z : (n : Nat) → Equals n (plus n Z)
  plus-rh-Z Z = <>
  plus-rh-Z (1+ n) = plus-rh-Z n

  {- TASK 2.2: Prove that ∀n. 1+(n + m) = n + (1+ m).
     Note that (1+ n) + m = 1+(n + m) is true by definition, but one
     requires an inductive proof.  
     Hint: you may need some of the basic properties about equality that
     you proved above.
  -}
  plus-rh-S : (n m : Nat) → Equals (1+ (plus n m)) (plus n (1+ m))
  plus-rh-S Z Z = <>
  plus-rh-S Z (1+ m) = refl m
  plus-rh-S (1+ n) Z = plus-rh-S n Z
  plus-rh-S (1+ n) (1+ m) = plus-rh-S n (1+ m)

  {- TASK 2.2: Prove that addition is commutative, i.e.
          ∀ n,m.  n + m  =  m + n
  -}
  plus-comm : (n m : Nat) → Equals (plus n m) (plus m n)
  plus-comm Z Z = <>
  plus-comm Z (1+ m) = plus-rh-Z m
  plus-comm (1+ n) Z = plus-comm n Z
  plus-comm (1+ n) (1+ m) = trans (plus n (1+ m)) (plus (1+ m) n) (plus m (1+ n)) (plus-comm n (1+ m)) (plus-rh-S m n)

  {- ----------------------------------------------------------------------
     PROBLEM 3 : Lists
  
     Lists are defined by a datatype with two constructors, [] and ::.  
     E.g. the list [1,2,3] would be written
        1 :: (2 :: (3 :: []))
     or 1 :: 2 :: 3 :: []

     ---------------------------------------------------------------------- -}

  {- The predicate In n l means that the number n is in the list l.
     Informally:
     n is not in []
     n is in x :: xs iff n = x or n is in xs
  -}
  In : (n : Nat) → List Nat → Set
  In n [] = Void
  In n (x :: xs) = Either (Equals n x) (In n xs)

  {- The predicate AllOdd l means that every number n in the list l is odd.
     Informally:
     every number in [] is odd
     every number in (x :: xs) is odd iff x is odd and every number in xs is odd.
  -}
  AllOdd : List Nat → Set
  AllOdd [] = Unit
  AllOdd (x :: xs) = (Odd x) × AllOdd xs

  {- TASK 3.1: Prove the following theorem, i.e.
     ∀ xs. (∃ n. n is in xs  ∧  n is even) ∨ (every number in xs is odd)
  -}
  findEven : (xs : List Nat) → Either (Σ[ n ∈ Nat ] In n xs × Even n) (AllOdd xs) 
  findEven [] = Inr <>
  findEven (x :: xs)
   with div2 x
  ... | Inl p = Inl {!x!}
  ... | Inr q with findEven xs
  ...            | Inl nIsE = {!!}
  ...            | Inr nIsO = {!!}

  {- TASK 3.2: Suggest a better name for the function 'problem3' and
               explain its computational content. 

               Are there other proofs besides the one you gave
               that have different computational content? Explain.  
  -}