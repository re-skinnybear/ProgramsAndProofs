{-Name: Theodore (Ted) Kim -}

module Hw03 where

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

  refl : (n : Nat) → Equals n n
  refl Z = <>
  refl (1+ n) = refl n

  sym : (n m : Nat) → Equals n m → Equals m n 
  sym Z Z e = <>
  sym Z (1+ m) e = e
  sym (1+ n) Z e = e
  sym (1+ n) (1+ m) e = sym n m e

  trans : (n m p : Nat) → Equals n m → Equals m p → Equals n p
  trans Z Z Z eq1 eq2 = <>
  trans Z Z (1+ p) eq1 eq2 = eq2
  trans Z (1+ m) Z eq1 eq2 = <>
  trans Z (1+ m) (1+ p) eq1 eq2 = eq1
  trans (1+ n) Z Z eq1 eq2 = eq1
  trans (1+ n) Z (1+ p) () eq2
  trans (1+ n) (1+ m) Z eq1 eq2 = eq2
  trans (1+ n) (1+ m) (1+ p) eq1 eq2 = trans n m p eq1 eq2


  {- ----------------------------------------------------------------------
     PROBLEM 1 
     ----------------------------------------------------------------------

     We can define equality of lists of a natural numbers
     in a similar way to equality of numbers:
     - [] = []
     - x :: xs = y :: ys iff x = y and xs = ys
     - [] is not equal to x :: xs
  -}

  ListEquals : List Nat → List Nat → Set
  ListEquals [] [] = Unit
  ListEquals [] (x :: ys) = Void
  ListEquals (x :: xs) [] = Void
  ListEquals (x :: xs) (y :: ys) = Equals x y × ListEquals xs ys

  {- TASK 1.1: Prove that equality is reflexive. 
     Note that the lemmas about nat equality from last HW are up above.
  -}
  listrefl : (xs : List Nat) → ListEquals xs xs
  listrefl [] = <>
  listrefl (x :: xs) = refl x , listrefl xs

  {- TASK 1.2: Prove that equality is transitive. 
  -}
  listtrans : (xs ys zs : List Nat) → ListEquals xs ys → ListEquals ys zs → ListEquals xs zs
  listtrans [] [] [] p q = <>
  listtrans [] [] (z :: zs) p q = q
  listtrans [] (y :: ys) [] p q = <>
  listtrans [] (y :: ys) (z :: zs) p q = p
  listtrans (x :: xs) [] [] p q = p
  listtrans (x :: xs) [] (z :: zs) p q = abort p
  listtrans (x :: xs) (y :: ys) [] p q = q
  listtrans (x :: xs) (y :: ys) (z :: zs) p q = trans x y z (fst p) (fst q) , listtrans xs ys zs (snd p) (snd q)

  {- ----------------------------------------------------------------------
     PROBLEM 2 
     ----------------------------------------------------------------------
  -}

  {- TASK 2.1: 
     Define a function append xs ys such that) 
     append [x1,...xn] [y1,...ym] = [x1,...xn,y1,...ym]
  -}
  append : List Nat → List Nat → List Nat
  append [] ys  = ys
  append (x :: xs) (ys) = x :: append xs (ys)

  {- TASK 2.2:
     Prove that append xs [] = xs.
  -}
  append-rh-[] : (xs : List Nat) → ListEquals (append xs []) xs
  append-rh-[] [] = <>
  append-rh-[] (x :: xs) = (refl x) , append-rh-[] xs

  {- TASK 2.2:
     Prove that append is associative.

     Hint: Think carefully about which variable(s) you need to case-analyze.
  -}
  append-assoc : (xs ys zs : List Nat) → ListEquals (append xs (append ys zs)) (append (append xs ys) zs)
  append-assoc [] ys zs = listrefl (append ys zs)
  append-assoc (x :: xs) ys zs = (refl x) , append-assoc xs ys zs

  {- ----------------------------------------------------------------------
     PROBLEM 3 
     ----------------------------------------------------------------------
  -}

  {- Using append, one can define an inefficient (O(n^2)) function to reverse 
     a list of length n:
     At each step, take the first element and put it at the end.
  -}
  reverse : List Nat → List Nat
  reverse [] = []
  reverse (x :: xs) = append (reverse xs) (x :: [])

  {- TASK 3.1:
     Define a fast (O(n)) revese function named fastreverse.
     
     The idea is to use a helper function fastreverse' that takes two lists.
     Hint: think about how you would reverse a deck of cards
           by dealing it into a second pile.
  -}
  fastreverse' : List Nat → List Nat → List Nat
  fastreverse' [] (ys) = ys
  fastreverse' (x :: xs) (ys) = fastreverse' xs (x :: ys)

  {- Define fastreverse by calling fastreverse' -}
  fastreverse : List Nat → List Nat
  fastreverse (xs) =  fastreverse' (xs) []


  {- Next, you will prove that fastreverse is correct, in the sense that
     it behaves the same as reverse: 
     fastreverse xs = reverse xs

     To prove this, you need to state and prove a lemma about fastreverse'.
     Coming up with the right lemma requires some cleverness, so I recommend that
     you start this problem EARLY and ask me if you get stuck.  

     Hints: 
     It may be helpful to try to prove fastreverse-correct by induction,
     and to see where you get stuck.  

     If you're having trouble, it may help to try to do an on-paper proof first.
  -}

  {- TASK 3.2: Finish stating a spec for fastreverse', 
               and then prove it. 

               Hint: you may find some of the lemmas that you proved above to be helpful.
  -}
 
  fastreverse'-correct : (xs ys : List Nat) → ListEquals (fastreverse' xs ys) (append (reverse xs) ys)
  fastreverse'-correct [] ys = listrefl ys
  fastreverse'-correct (x :: xs) ys = listtrans (fastreverse' xs (x :: ys)) (append (reverse xs) (x :: ys)) (append (append (reverse xs) (x :: [])) ys) (fastreverse'-correct xs (x :: ys)) (append-assoc (reverse xs) (x :: []) ys)

  {- TASK 3.3: Prove fastreverse-correct using fastreverse'-correct.
               Hint: you may find some of the lemmas that you proved above to be helpful.
  -}
  fastreverse-correct : (xs : List Nat) → ListEquals (fastreverse xs) (reverse xs)
  fastreverse-correct xs = listtrans (fastreverse' xs []) (append (reverse xs) []) (reverse xs) (fastreverse'-correct xs []) (append-rh-[] (reverse xs))


  {- ----------------------------------------------------------------------
     PROBLEM 4 
     ----------------------------------------------------------------------
  -}

  {- Every element is even -}
  AllEven : List Nat → Set
  AllEven [] = Unit
  AllEven (x :: xs) = (Even x) × AllEven xs

  {- TASK 4.1: Define a function filter-evens/simple
     such that filter-evens/simple xs computes a list ys
     containing all and only the even elements of xs -}
  filter-evens/simple : List Nat → List Nat
  filter-evens/simple [] = []
  filter-evens/simple (x :: xs) with div2 x
  ... | Inl xIsEven = x :: filter-evens/simple xs
  ... | Inr xIsOdd = filter-evens/simple xs

  {- TASK 4.2: Define a function filter-evens
     such that filter-evens xs computes a list ys
     containing all and only the even elements of xs.
     Use the type system to enforce the invariant that every element 
     of ys is even.  -}

  fste : {A : Set}{B : A → Set} → (Σ[ x ∈ A ] B x) → A 
  fste (x , _) = x

  snde : {A : Set}{B : A → Set} → (p : Σ[ x ∈ A ] B x) → B(fste p) 
  snde (_ , y) = y

  filter-evens : (xs : List Nat) → Σ[ ys ∈ List Nat ] AllEven ys
  filter-evens [] = [] , <>
  filter-evens (x :: xs) with div2 x 
  ... | Inl xIsEven = x :: fste (filter-evens xs) , xIsEven , snde (filter-evens xs)
  ... | Inr xIsOdd = filter-evens xs
