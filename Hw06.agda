{- Name: Theodore (Ted) Kim
   If only I had more time~
-}

module Hw06 where

  data Order : Set where
    Less : Order
    Equal : Order
    Greater : Order

  record Σ {A : Set} (B : A -> Set) : Set where
    constructor _,_
    field
      fst : A
      snd : B fst
  open Σ public

  infixr 0 _,_

  _×_ : Set -> Set -> Set
  A × B = Σ (\ (_ : A) -> B)

  infixr 10 _×_

  data Either (A B : Set) : Set where
    Inl : A → Either A B
    Inr : B → Either A B

  module RBT (Key : Set) (compare : Key -> Key -> Order) (Value : Set) where 

    -- ----------------------------------------------------------------------
    -- the code

    data Color : Set where
      Red : Color
      Black : Color

    mutual
      data WellRedTree : Set where
        Empty : WellRedTree
        RedNode  : (l : WellRedTree)
                 → (kv : Key × Value)
                 → (r : WellRedTree)
                 → (rl : RootColored l Black)
                 → (rr : RootColored r Black)
                 → WellRedTree
        BlackNode : (l : WellRedTree)
                 → (kv : Key × Value)
                 → (r : WellRedTree)
                 → WellRedTree

      data RootColored : WellRedTree -> Color -> Set where
        RC-Empty : RootColored Empty Black
        RC-Red   : {l : WellRedTree} {kv : Key × Value} {r : WellRedTree}
                   {cl : RootColored l Black} {cr : RootColored r Black}
                 → RootColored (RedNode l kv r cl cr) Red
        RC-Black : {l : WellRedTree} {kv : Key × Value} {r : WellRedTree}
                 → RootColored (BlackNode l kv r) Black
  

    {- TASK 1.1 : Define a datatype representing almost well-red trees, where in an
       almost well red tree, no red node has a red child, except possibly the root -}
    data AlmostWellRedTree : Set where
       Empty : AlmostWellRedTree
       AWRT : (l : WellRedTree) → (kv : Key × Value) → Color → (r : WellRedTree) → AlmostWellRedTree

    {- TASK 1.2: in class, we observed that every well-red tree is also almost well-red:
                 for all t:tree, if t is well-red, then t is almost-well-red.
  
                 Define a function "promote" that casts a well-red tree
                 to an almost-well-red tree.  This function should have
                 the following type:
    -}
    promote : WellRedTree → AlmostWellRedTree
    promote Empty = Empty
    promote (RedNode l kv r cl cr) = AWRT l kv Red r
    promote (BlackNode l kv r) = AWRT l kv Black r

    {- TASK 1.3: in class, we used the fact that every tree has either a black root or a red root. 
                 Prove this here:
    -}
    decide-root : (t : WellRedTree) → Either (RootColored t Black) (RootColored t Red)
    decide-root Empty = Inl RC-Empty
    decide-root (RedNode l kv r lc rc) = Inr RC-Red
    decide-root (BlackNode l kv r) = Inl RC-Black


    {- TASK 2.1: In class, we said that balance has the following three specs:
       (1) For all l:tree, kv:Key × Value, r:tree
           if l is almost well red
              r is well-red
           then balance l kv Black r is well-red.

       (2) For all l:tree, kv:Key × Value, r:tree
           if l is well-red
              r is almost-well-red
           then balance l kv Black r is well-red.

       (3) For all l:tree, kv:Key × Value, r:tree,
           if l is well-red 
              r is well-red
           then balance l kv Red r is almost-well-red

       In your intrinstically verified version of this code, balance
       will be split into three different functions, corresponding to these three specs.
       Give types for each of these three functions below.
    -}

    {- TASK 2.2: Fill in the implementations of these functions.
                 Your implementation should borrow ingredients from the old code for balance,
                 though it will be a little different, because the *proof* for balance
                 is a little more involved than the code.

                 Note: this is harder than some of the other code in the assignment,
                 so you may wish to do it after considering the other functions.
    -}

    {- Give a type for a function balance-left that corresponds to spec (1) above.  Then fill in the function. -}

    balance-left : (l : AlmostWellRedTree) → (kv : Key × Value) → (r : WellRedTree) → WellRedTree
    balance-left Empty kv Empty = RedNode Empty kv Empty RC-Empty RC-Empty
    balance-left Empty kv (RedNode l kv' r lc rc) = {!!}
    balance-left Empty kv (BlackNode l kv' r) = {!!}
    balance-left (AWRT l kv' c' r) kv Empty = {!!}
    balance-left (AWRT l kv' c' r) kv (RedNode l' kv'' r' lc rc) = {!!}
    balance-left (AWRT l kv' c' r) kv (BlackNode l' kv'' r') = {!!}

    {- Give a type for a function balance-right that corresponds to spec (2) above.  Then fill in the function. -}
    balance-right : (l : WellRedTree) → (kv : Key × Value) → (r : AlmostWellRedTree) → WellRedTree
    balance-right Empty kv Empty = RedNode Empty kv Empty RC-Empty RC-Empty
    balance-right Empty kv (AWRT l kv' c r) = {!!}
    balance-right (RedNode l kv' r lc rc) kv Empty = {!!}
    balance-right (RedNode l kv' r lc rc) kv (AWRT l' kv'' c r') = {!!}
    balance-right (BlackNode l kv' r) kv Empty = {!!}
    balance-right (BlackNode l kv' r) kv (AWRT l' kv'' c r') = {!!}

    {- Give a type for a function balance-break that corresponds to spec (3) above.  Then will in the function. -}
    balance-break : (l : WellRedTree) → (kv : Key × Value) → (r : WellRedTree) → AlmostWellRedTree
    balance-break Empty kv Empty = AWRT Empty kv Red Empty
    balance-break Empty kv (RedNode l kv' r lc rc) = {!!}
    balance-break Empty kv (BlackNode l kv' r) = {!!}
    balance-break (RedNode l kv r lc rc) kv' Empty = {!!}
    balance-break (RedNode l kv r lc rc) kv' (RedNode l' kv'' r' lc' rc') = {!!}
    balance-break (RedNode l kv r lc rc) kv' (BlackNode l' kv'' r') = {!!}
    balance-break (BlackNode l kv' r) kv Empty = {!!}
    balance-break (BlackNode l kv' r) kv (RedNode l' kv'' r' lc rc) = {!!}
    balance-break (BlackNode l kv' r) kv (BlackNode l' kv'' r') = {!!}


    {- TASK 3.1: 
       In class, we said that ins has the following three specs:

       (1) For all t, if t is well-red and the root of t is black, then
           ins t (k,v) is well-red.
       
       (2) For all t, if t is well-red and the root of t is red, then
           ins t (k,v) is almost-well-red.

       (3) Therefore, for all t, if t is well-red, then ins t (k,v) is almost-well-red.

       Give types for three ins functions, corresponding to these three specs.
    -}

    {- TASK 3.2: Fill in the implementations of these functions. -}

    mutual
      {- Give a type for ins-black, corresponding to spec (1) for ins above.  Then implement it. -}
      ins-black : (t : WellRedTree) → {c : RootColored t Black} → (kv : Key × Value) → WellRedTree
      ins-black .Empty {RC-Empty} (k' , v') = RedNode Empty (k' , v') Empty RC-Empty RC-Empty
      ins-black .(BlackNode l (k , v) r) {RC-Black {l} {(k , v)} {r}} (k' , v') with compare k k'
      ... | Less = balance-left (ins-any l (k' , v')) (k , v) r
      ... | Equal = BlackNode l (k' , v') r
      ... | Greater = balance-right l (k , v) (ins-any r (k' , v'))

      {- Give a type for ins-red, corresponding to spec (2) for ins above.  Then implement it. -}
      {- Have to left-balance ins-black l (k' , v') and vice versa?
      -}

      ins-red : (t : WellRedTree) → {c : RootColored t Red} → (kv : Key × Value) → AlmostWellRedTree
      ins-red .(RedNode l (k , v) r cl cr) {RC-Red {l} {(k , v)} {r} {cl} {cr}} (k' , v') with compare k k'
      ... | Less = balance-break (ins-black l (k' , v')) (k , v) r
      ... | Equal = AWRT l (k' , v') Red r
      ... | Greater = balance-break l (k , v) (ins-black r (k' , v'))

      {- Give a type for ins-any, corresponding to spec (3) for ins above.  Then implement it. -}
      ins-any : (t : WellRedTree) → (kv : Key × Value) → AlmostWellRedTree
      ins-any Empty (k' , v') = promote (RedNode Empty (k' , v') Empty RC-Empty RC-Empty)
      ins-any (RedNode l (k , v) r lc rc) (k' , v') = ins-red (RedNode l (k , v) r lc rc) (k' , v')
      ins-any (BlackNode l (k , v) r) (k' , v') = promote (ins-black (BlackNode l (k , v) r) (k' , v'))


    {- TASK 4: In class, we said that blacken-root has the spec
               For all t, if t is almost-well-red, then blacken-root t is well-red.

               Give a type corresponding to this spec, and implement it.
    -}
    blacken-root : AlmostWellRedTree → WellRedTree
    blacken-root Empty = Empty
    blacken-root (AWRT l kv _ r) = BlackNode l kv r


    {- TASK 5: Define an intrinsically verified insertion function: -}
    insert : WellRedTree → Key × Value → WellRedTree
    insert t kv = blacken-root (ins-any t kv)


    {- TASK 6: Do you like this version better or worse than the original code for insertion? Why? 
       I like this version better than the original code for insertion since it keeps the black height, but
       it also keeps the well-red invariant. However, it is less intuitive than the original code for
       insertion. Thus, this code trades-off transparency for efficiency.
       
    -}
