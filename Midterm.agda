{- Name: Theodore (Ted) Kim
-}

{- COMP 360-1.  Fall 2013.  Midterm exam.

INSTRUCTIONS

* This midterm exam is due Friday, October 18, 5PM EST.
  You should hand in the exam by copying it into your handin directory.

* The only sources you are allowed to use while working on this exam are
  the course materials (materials on the course web site or your notes
  and work from the course) and the instructor.  You may not refer to
  any other person or source regarding this exam.
  
* You are free to use the library code defined in this file or any other
  code discussed in the course in any task.  You are free to use any
  tasks in the exam in any subsequent tasks.

* Each task will be graded independently.  If you cannot figure out how
  to do one part of a problem, you should still attempt to do the
  remaining parts.  

* If you cannot figure out how to do a proof task in Agda, 
  partial credit may be given for a written proof.  

-}

module Midterm where

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

  map : {A B : Set} → (A → B) → List A → List B
  map f [] = []
  map f (x :: xs) = f x :: map f xs

  append : {A : Set} → List A → List A → List A
  append [] ys = ys
  append (x :: xs) ys = x :: append xs ys 

  length : {A : Set} → List A → Nat
  length [] = 0
  length (x :: xs) = 1+ (length xs)
  
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

  -- note: these have more implicit args than before
  sym : {A : Set} {x y : A} (p : x == y) → y == x
  sym Refl = Refl

  trans : {A : Set} {x y z : A} (p : x == y) (q : y == z) → x == z
  trans Refl Refl = Refl

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

  check≤ : (m n : Nat) → Either (m ≤ n) (n ≤ m)
  check≤ Z Z = Inl <>
  check≤ Z (1+ n) = Inl <>
  check≤ (1+ m) Z = Inr <>
  check≤ (1+ m) (1+ n) = check≤ m n

  -- note: more implicit args than before
  ::-cong : {A : Set} {x y : A} {xs ys : List A} → x == y → xs == ys → (x :: xs) == (y :: ys)
  ::-cong Refl Refl = Refl

  append-rh-[] : {A : Set} (xs : List A) → (append xs []) == xs
  append-rh-[] [] = Refl
  append-rh-[] (x :: xs) = ::-cong Refl (append-rh-[] xs)

  append-assoc : {A : Set} (xs ys zs : List A) → (append xs (append ys zs)) == (append (append xs ys) zs)
  append-assoc [] ys zs = Refl
  append-assoc (x :: xs) ys zs = ::-cong Refl (append-assoc xs ys zs)

  -- end library code
  ----------------------------------------------------------------------



  {- ----------------------------------------------------------------------
     PROBLEM 1 (14%): Recursion/induction on natural numbers

     This problem asks you to show that you can write a simple recursive function, 
     and prove some simple equational specifications about it.  

     ---------------------------------------------------------------------- -}

  {- TASK 1.1 (4%): Define a function mult m n that multiplies m and n. -}
  mult : Nat → Nat → Nat 
  mult m Z = Z
  mult m (1+ n) = (plus m (mult m n))

  {- TASK 1.2 (5%): Prove that multiplication by 0 (on the left) is 0.
     I.e. 0 * m = 0
  -}
  mult-lh-Z : (m : Nat) → (mult 0 m) == 0
  mult-lh-Z Z = Refl
  mult-lh-Z (1+ m) = mult-lh-Z m

  {- TASK 1.3 (5%): Prove that multiplication by 0 (on the right) is 0.
     I.e. m * 0 = 0
  -}
  mult-rh-Z : (m : Nat) → (mult m 0) == 0
  mult-rh-Z Z = Refl
  mult-rh-Z (1+ m) = Refl


  {- ----------------------------------------------------------------------
     PROBLEM 2 (12%): Constructive Logic

     In classical logic, there are de Morgan dualities between ∀ and ∃.
     (You may wish to review the problem on de Morgan dualities between
      ∧ and ∨ on HW 1.)

     ¬ (∀x.A(X)) <-> ∃x.¬A(x)
     ¬ (∃x.A(X)) <-> ∀x.¬A(x)

     This problem asks you to show that you can investigate whether these 
     theorems hold in constructive logic.  For each of the following,
     either
     - give an Agda proof, or 
     - state that the proposition is not provable, and explain why not.

     ---------------------------------------------------------------------- -}

  ¬ : Set → Set
  ¬ A = A → Void

  {- TASK 2.1 (3%) -}
  -- ¬ (∃x.B(x)) ⊃ (∀x.¬B(x))
  demorgan1 : {A : Set} {B : A → Set} → 
            ¬ (Σ[ x ∈ A ] (B x)) → ((x : A) → ¬ (B x))
  demorgan1 p x y = p (x , y)

  {- TASK 2.2 (3%) -}
  -- (∀x.¬B(x)) ⊃ ¬ (∃x.B(x))
  demorgan2 : {A : Set} {B : A → Set} → 
            ((x : A) → ¬ (B x)) → ¬ (Σ[ x ∈ A ] (B x)) 
  demorgan2 p (x , y) = p x y

  {- TASK 2.3 (3%) -}
  -- ¬ (∀x.B(x)) ⊃ (∃x.¬B(x))
  demorgan3 : {A : Set} {B : A → Set} → 
            (¬ ((x : A) → B x)) → Σ[ x ∈ A ] (¬ (B x))
  demorgan3 p = {!!}
  
  {- This proposition is not provable.
     We are given p : ((x : .A) → .B x) → Void and must show Σ .A (λ x → .B x → Void).
     However, there is no way to make ((x : .A) → .B x) pass to the function.
     Therefore, we cannot return Σ .A (λ x → .B x → Void) in this function to prove the proposition.
  -}

  {- TASK 2.4 (3%) -}
  -- (∃x.¬B(x)) ⊃ ¬ (∀x.B(x)) 
  demorgan4 : {A : Set} {B : A → Set} → 
            Σ[ x ∈ A ] (¬ (B x)) → ¬ ((x : A) → B x) 
  demorgan4 (x , p) q = p (q x)


  {- ----------------------------------------------------------------------
     PROBLEM 3 (29%): 
     Extrinsic verification.

     This problem asks you to show that you can prove some
     equational properties of some functions on lists and trees,
     using propositional equality (==).

     ----------------------------------------------------------------------  -}


  {- TASK 3.1 (8%): prove that map "preserves" append, in the sense that
                    mapping a function over the append of two lists is the same
                    as mapping over each list separately, and then appending the results. -}
  map-append : {A B : Set} → (f : A → B) (xs ys : List A) 
             → map f (append xs ys) == append (map f xs) (map f ys)
  map-append f [] ys = Refl
  map-append f (x :: xs) (ys) = ::-cong Refl (map-append f xs ys)


  {- TASK 3.2 (4%): Prove that append takes equal lists to equal lists -}
  append-cong : {A : Set} {xs xs' ys ys' : List A} → xs == xs' -> ys == ys' -> append xs ys == append xs' ys' 
  append-cong Refl Refl = Refl


  {- For this problem, we will use a datatype of trees with data at the nodes.
     (These are like red-black trees, but without the color.).
    -}
  data Tree (A : Set) : Set where
    Empty : Tree A
    Node  : Tree A → A → Tree A → Tree A

  {- The following function converts a tree to a list, using an "in order" traversal. 
     For example,
     tolist (Node (Node Empty 1 Empty) 2 (Node Empty 3 Empty)) = 1 :: 2 :: 3 :: []
  -}
  tolist : {A : Set} → Tree A → List A
  tolist Empty = []
  tolist (Node l x r) = append (tolist l) (x :: tolist r)
  
  {- TASK 3.3 (5%): 
     Define a function 'treemap' such that treepmap f t computes the tree
     resulting from applying f to the data at each node in t.

     For example 
     treemap 1+ (Node (Node Empty 1 Empty) 2 (Node Empty 3 Empty))
     = Node (Node Empty 2 Empty) 3 (Node Empty 4 Empty)
  -}
  treemap : {A B : Set} → (A → B) → Tree A → Tree B
  treemap f Empty = Empty
  treemap f (Node l x r) = Node (treemap f l) (f x) (treemap f r)

  {- TASK 3.4 (12%):
     Prove the following specification about treemap, which says that 
     if you use treemap to apply a function to a tree, and then 
     convert the tree to a list, that's the same as converting the
     original tree to a list, and then using List map to apply the
     function to each element.
  -}
  treemap-correct : {A B : Set} → (f : A → B) (t : Tree A) → (tolist (treemap f t)) == map f (tolist t)
  treemap-correct f Empty = Refl
  treemap-correct f (Node l x r) = trans (append-cong (treemap-correct f l) (::-cong Refl (treemap-correct f r))) (sym (map-append f (tolist l) (x :: tolist r)))


  {- ----------------------------------------------------------------------

     PROBLEM 4 (20%): Intrinsic Verification.

     This problem asks you to show that you can take an extrinsic verification
     of an algorithm and turn it into an intrinsically verified piece of code.

     You may wish to review examples of intrinsic vs extrinsic verification, such as
     - proving Length invariants of list functions extrinsically, vs. using vectors
       intrinsically.
     - red-black trees, where we verified the black height both extrinsically
       and intrinsically.

     In this problem, you will give an intrinsic version of insertion sort.  
     You may wish to review the insertion sort correctness 
     proof in HW5 for the extrinsic version of this proof.

     ---------------------------------------------------------------------- -}

  {- First, we define a sorted list data structure. 
     There are two constructors for sorted lists, S[] (the empty sorted list) 
     and SCons which takes *three* arguments, the head of the list (x), 
     the tail of the list (xs, another sorted list), and a proof that x
     is less than or equal to the head of xs.

     The inductive family x ≤Head xs is defined simultaneously with 
     SortedList.  This is necessary because, in the proposition x ≤Head xs,
     xs *is* a sorted list, but the proposition ≤Head also is used in the definition 
     of SortedList (in the SCons constructor).  We do this with a 'mutual' definition. 
    -}
  mutual
    data SortedList : Set where
      S[] : SortedList
      SCons : (x : Nat) (xs : SortedList) → x ≤Head xs → SortedList

    data _≤Head_ (x : Nat) : (xs : SortedList) → Set where
      NoHead : x ≤Head S[]
      HasHead : {y : Nat} {ys : SortedList} {yh : y ≤Head ys} → x ≤ y → x ≤Head (SCons y ys yh)

  mutual
    {- TASK 4.1 (10%): 
       Define insert, in such a way that it takes a sorted list and returns a sorted list
       containing all the elements of the given list, as well as the new element. -}
    insert : Nat → SortedList → SortedList
    insert n S[] = SCons n S[] NoHead
    insert n (SCons x xs p) with check≤ n x
    ... | Inl less = SCons n (SCons x xs p) (HasHead less)
    ... | Inr greater = SCons x (insert n xs) (head-lemma greater p)

    {- TASK 4.2 (5%):
       Prove the following lemma, which says that if x ≤ n and 
       x ≤ the head of xs, then x ≤ the head of (insert n xs).
    -}
    head-lemma : ∀ {n x xs} → x ≤ n → x ≤Head xs → x ≤Head (insert n xs)
    head-lemma p NoHead = HasHead p
    head-lemma {n} p (HasHead {y} q) with check≤ n y
    ... | Inl _ = HasHead p
    ... | Inr _ = HasHead q

  {- TASK 4.3 (5%)
     Define insertion sort, which takes *any* list (not necessarily sorted)
     and produces a sorted list containing exactly the same elements. -}
  isort : List Nat → SortedList
  isort [] = S[]
  isort (x :: xs) = insert x (isort xs)

  
  {- ---------------------------------------------------------------------

     PROBLEM 5 (25%): Inductive families

     This problem asks you to show that you can use more complicated inductive 
     families to do extrinsic verification.

     In particular, you will prove correctness of an algorithm for the
     longest common subsequence problem.  Longest common subsequence has some
     applications in biology, since it is a very simple form of DNA matching.

     Given a sequence like
       AGTCTTA
     a *subsequence* is a sequence of letters that appear in the original 
     sequence in the same order.  For example,
       ATA
       ACTA
     are subsequences but
       ATG 
     is not (order matters).  

     Given two sequences xs and ys, zs is a *common subsequence* of xs and ys
     iff zs is both a subsequence of xs and a subsequence of ys.

     Given two sequences xs and ys, a _longest common subsequence_ is a 
     common subsequence zs of xs and ys with the property that
     for any common subsequence zs', length zs' ≤ length zs.
     I.e. it is at least as long as any common subsequence.  

     Note that two sequences may have multiple different longest common
     subsequences.  For example, for the sequences
       ATC
       TAC
     both TC and AC are longest common subsequences.   

     In this problem, you will consider an algorithm for computing 
     a longest common subsequence of two sequences. 
  
     --------------------------------------------------------------------- -}

  module DNA where
  
    {- Datatype for representing DNA bases. -}
    data Base : Set where
      A : Base
      T : Base
      C : Base
      G : Base
  
    {- Equality test for bases -}
    check= : (x y : Base) → Either (x == y) (x == y -> Void)
    check= A A = Inl Refl
    check= A T = Inr (λ ())
    check= A C = Inr (λ ())
    check= A G = Inr (λ ())
    check= T A = Inr (λ ())
    check= T T = Inl Refl
    check= T C = Inr (λ ())
    check= T G = Inr (λ ())
    check= C A = Inr (λ ())
    check= C T = Inr (λ ())
    check= C C = Inl Refl
    check= C G = Inr (λ ())
    check= G A = Inr (λ ())
    check= G T = Inr (λ ())
    check= G C = Inr (λ ())
    check= G G = Inl Refl
  
    {- We represent sequences by lists.  We can define *subsequence* (sublist)
       as an inductive family: Sublist xs ys means "xs is a subsequence of ys".  

       Done: [] is a subsequence of any list.
       Skip: xs is a subsequence of y::ys if xs is a subsequence of ys.
             You can always skip an element.  
       Keep: (x :: xs) is a subsequence of (y :: ys) if x = y and xs is a subsequence of ys.
             When the heads of the lists match, you can keep the head.  
    -}
    data Sublist : (xs ys : List Base) → Set where
      Done : {ys : List Base} → Sublist [] ys
      Skip : {y : Base} {xs ys : List Base} → Sublist xs ys → Sublist xs (y :: ys)
      Keep : {x y : Base} {xs ys : List Base} → x == y → Sublist xs ys → Sublist (x :: xs) (y :: ys)

    {- This function returns the longer of the two given lists. -}
    longer : List Base → List Base → List Base
    longer xs ys with check≤ (length xs) (length ys)
    ... | Inl _ = ys
    ... | Inr _ = xs
  

    {- A simple recursive algorithm for computing 
       the longest common sublist of two lists is as follows: 

       If one list is empty, the lcs is empty.
       If the heads match, then a lcs is the head added to the lcs of the tails.
       If the heads do not match, then a lcs is the longer of two recursive calls,
       one where you drop the head of one list, and one where you drop the head of the other.

       Note that this algorithm takes exponential time (but can be made efficient by memoization).  
  
       The simplest way to translate this algorithm into Agda is as follows:
    -}
    lcs' : List Base → List Base → List Base
    lcs' [] ys = []
    lcs' xs [] = []
    lcs' (x :: xs) (y :: ys) with check= x y 
    ... | Inl _ = x :: lcs' xs ys
    ... | Inr _ = longer (lcs' (x :: xs) ys) (lcs' xs (y :: ys))

    {- Unfortunately, the termination checker does not accept this
       version, due to an issue with how 'with' is treated.  Morally,
       the recursion is OK because in the three recursive calls, at
       least one of x::xs and y::ys gets smaller.  But Agda loses track
       of this because of the 'with'.
       A solution is to move the recursive calls into the with:
    -}

    lcs : List Base → List Base → List Base
    lcs [] ys = []
    lcs xs [] = []
    lcs (x :: xs) (y :: ys) with check= x y | lcs xs ys | lcs (x :: xs) ys | lcs xs (y :: ys)
    ... | Inl _ | skipxy | skipx | skipy = x :: skipxy
    ... | Inr _ | skipxy | skipx | skipy = longer skipx skipy
  
    {- This is the version of the algorithm that you will verify.  
       (It's running time is even worse, because it makes all three recursive calls
        at each step, but this would only be a constant factor if it were memoized.)
    -}

    {- TASK 5.1 (5%):
       Prove that if xs and ys are both sublists of zs, 
       then the longer of xs and ys is a sublist of zs. 

       HINT: Think carefully about what to pattern-match.
    -}
    longer-sublist : (xs ys : List Base) {zs : List Base} 
                   → Sublist xs zs → Sublist ys zs → Sublist (longer xs ys) zs
    longer-sublist xs ys p q with check≤ (length xs) (length ys)
    ... | Inl _ = q
    ... | Inr _ = p

    {- TASK 5.2 (20%): Prove that (lcs xs ys) is a common sublist of xs and ys. -} 
    lcs-sublist : (xs ys : List Base) → Sublist (lcs xs ys) xs × Sublist (lcs xs ys) ys
    lcs-sublist [] [] = Done , Done
    lcs-sublist [] (y :: ys) = Done , Done
    lcs-sublist (x :: xs) [] = Done , Done
    lcs-sublist (x :: xs) (y :: ys) with check= x y | lcs-sublist xs ys | lcs-sublist (x :: xs) ys | lcs-sublist xs (y :: ys)
    ... | Inl equal | skipxy | skipx | skipy = Keep Refl (fst skipxy) , Keep equal (snd skipxy)
    ... | Inr nequal | skipxy | skipx | skipy with check≤ (length (lcs (x :: xs) ys)) (length (lcs xs (y :: ys)))
    ... | Inl _ = Skip (fst skipy) , snd skipy
    ... | Inr _ = fst skipx , Skip (snd skipx)
 
    {- EXTRA CREDIT BONUS TASK: 

       You should only attempt this task once you have completed the
       entire rest of the midterm.  Credit for this task will *not*
       replace credit on the other questions on the exam; it will only
       be used in determining your final letter grade in the course.

       This is a longer proof than we have done so far, and you may need
       to define a few lemmas.  

       Your task is to complete the proof that (lcs xs ys) is a longest
       common subsequence of xs and ys, by showing that it is at least
       as long as any other common subsequence:
    -}   


   {-

    Approach 1: Brute force. Solved the cases for Inr noequal, but Agda colors it salmon, similarly to 
    function lcs'. Tried to change it similarly to lcs, but got stuck.

    lcs-least {(x :: xs)} {(y :: ys)} {zs} (Skip p) (Skip q) with check= x y
    ... | Inl equal = {!!}
    ... | Inr noequal with check≤ (length (lcs (x :: xs) ys)) (length (lcs xs (y :: ys)))
    ... | Inl less = lcs-least p (Skip q)
    ... | Inr greater = lcs-least (Skip p) q
    lcs-least {(x :: xs)} {(y :: ys)} {(z :: zs)} (Skip p) (Keep y₁ q) with check= x y
    ... | Inl equal = {!!}
    ... | Inr nequal with check≤ (length (lcs (x :: xs) ys)) (length (lcs xs (y :: ys)))
    ... | Inl less = {!!}
    ... | Inr greater = {!!}
    lcs-least {(x :: xs) } {(y :: ys)} {(z :: zs)} (Keep x₁ p) (Skip q) with check= x y
    ... | Inl equal = {!!}
    ... | Inr nequal with check≤ (length (lcs (x :: xs) ys)) (length (lcs xs (y :: ys)))
    ... | Inl less = {!!}
    ... | Inr greater = {!!}
    lcs-least {(x :: xs) } {(y :: ys)} {(z :: zs)} (Keep x₁ p) (Keep y₁ q) with check= x y
    ... | Inl equal = {!!}
    ... | Inr nequal with check≤ (length (lcs (x :: xs) ys)) (length (lcs xs (y :: ys)))
    ... | Inl less = {!!}
    ... | Inr greater = {!!}

    Approach 2: Make cases on implicit arguments rather than p q. For the first three cases, I would need to write a
    lemma that stated if Sublist zs [] , then length zs = 0 (similar to lcs-sublist but with length). In the last case, 
    I could use the syntax seen in lcs, but with check= x y | lcs-least (Skip p) (Skip q) | lcs-least (Skip p) (Keep y q)
    | lcs-least (Keep x q) (Skip q) | lcs-least (Keep x q) (Skip y q)...
    
    lcs-least : {xs ys zs : List Base} → Sublist zs xs -> Sublist zs ys -> length zs ≤ length (lcs xs ys)
    lcs-least {[]} {[]} {zs} p q = {!!}
    lcs-least {[]} {y :: ys} p q = {!!}
    lcs-least {x :: xs} {[]} p q = {!!}
    lcs-least {x :: xs} {y :: ys} p q = {!!}
    
    -}