open import lib.Preliminaries
open String

module Hw07 where

  -- here is the universe we defined in class

  data U : Set where
    `nat    : U
    `string   : U
    `list   : U → U
    _`×_ : U → U → U

  infixr 8 _`×_

  El : U → Set
  El `string = String
  El `nat = Nat
  El (`list t) = List (El t)
  El (t1 `× t2) = El t1 × El t2

  {- ----------------------------------------------------------------------
     PROBLEM 1: Generic programming
     ---------------------------------------------------------------------- -}

  {- TASK 1.1: Define a type-generic equality function for this universe. -}

  injectiveS : (x y : Nat) → (S x) == (S y) → x == y
  injectiveS .y y Refl = Refl

  injective:: : {A : Set} (x y : A) (xs ys : List A) → (x :: xs) == (y :: ys) → x == y
  injective:: .y y .ys ys Refl = Refl

  injective::' : {A : Set} (x y : A) (xs ys : List A) → (x :: xs) == (y :: ys) → xs == ys
  injective::' .y y .ys ys Refl = Refl

  injective× : {A B : Set} (xs : (A × B)) (ys : (A × B)) → xs == ys → fst xs == fst ys 
  injective× (.fst2 , .snd2) (fst2 , snd2) Refl = Refl

  injective×' : {A B : Set} (xs : (A × B)) (ys : (A × B)) → xs == ys → snd xs == snd ys
  injective×' .y y Refl = Refl

  check= : (t : U) → (x y : El t) → Either (x == y) (x == y → Void)
  check= `nat Z Z = Inl Refl
  check= `nat Z (S y) = Inr (λ ())
  check= `nat (S x) Z = Inr (λ ())
  check= `nat (S x) (S y) with check= `nat x y
  ... | Inr nequal = Inr(λ nequal' → nequal (injectiveS x y nequal'))
  check= `nat (S .y) (S y) | Inl Refl = Inl Refl
  check= `string x y with String.equal x y
  ... | Inl equal = Inl equal
  ... | Inr nequal = Inr nequal
  check= (`list t) [] [] = Inl Refl
  check= (`list t) [] (y :: ys) = Inr (λ ())
  check= (`list t) (x :: xs) [] = Inr (λ ())
  check= (`list t) (x :: xs) (y :: ys) with check= t x y
  ...                                    | Inr nequal = Inr (λ nequal' → nequal (injective:: x y xs ys nequal'))
  check= (`list t) (.y :: xs) (y :: ys)  | Inl Refl with check= (`list t) xs ys
  check= (`list t) (.y :: .ys) (y :: ys) | Inl Refl | Inl Refl = Inl Refl
  ...                                               | Inr nequal = Inr (λ nequal' → nequal (injective::' y y xs ys nequal'))
  check= (t1 `× t2) (fst1 , snd1) (fst2 , snd2) with check= t1 fst1 fst2
  ...                                    | Inr nequal = Inr (λ nequal' → nequal (injective× (fst1 , snd1) (fst2 , snd2) nequal'))
  check= (t1 `× t2) (.fst2 , snd1) (fst2 , snd2) | Inl Refl with check= t2 snd1 snd2
  ...                                                       | Inr nequal = Inr (λ nequal' → nequal (injective×' (_ , snd1) (_ , snd2) nequal'))
  check= (t1 `× t2) (.fst2 , .snd2) (fst2 , snd2)| Inl Refl | Inl Refl = Inl Refl
 

  {- TASK 1.2: Define a "database" to be a list of (name,birthday) records. 
     Use your type-generic equality to define an equality function for databases:
  -}

  DB = List (String × Nat × Nat × Nat)

  example : DB
  example = ("Dan" , (8 , 26 , 82)) :: ("Matt" , (8 , 8 , 86)) :: []

  check=/DB : (x y : DB) → Either (x == y) (x == y → Void)
  check=/DB x y = check= (`list (`string `× `nat `× `nat `× `nat)) x y



  {- ----------------------------------------------------------------------
     PROBLEM 2: More general recursion
     ---------------------------------------------------------------------- -}

  {- In the lecture 18 code, you will find the following version of parseFormat1,
     which Agda's termination checker does not accept.

  parseFormat1 : String → Maybe (U × String)
  parseFormat1 s with peelOff "%s" s 
  ...              | Some s' = Some (`string , s')
  ...              | None with peelOff "%u" s 
  ...                        | Some s' = Some (`nat , s')
  ...                        | None    with peelOff "%l" s 
  ...                                     | None = None
  ...                                     | Some s' with parseFormat1 s'
  ...                                                  | Some (f' , s'') = Some (`list f' , s'')
  ...                                                  | None = None

  In this problem, you will write a version of this code that passes the termination checker.

  Informally, the idea is that parseFormat1 terminates because it recurs
  on some suffix of the original string.  The same termination argument
  applies to Args and printf from that lecture.
  
  -}

  {- Suffix xs ys means that xs is a suffix of ys -}

  data Suffix {A : Set} : List A → List A → Set where
    Stop : ∀ {x xs} → Suffix xs (x :: xs)
    Drop : ∀ {y xs ys} → Suffix xs ys → Suffix xs (y :: ys)

  {- TASK 2.1 : Show that suffix is transitive. -}
  suffix-trans : {A : Set} → {xs ys zs : List A} → Suffix xs ys → Suffix ys zs → Suffix xs zs
  suffix-trans p Stop = Drop p
  suffix-trans p (Drop q) = Drop (suffix-trans p q)

  {- TASK 2.2: The first thing we need to do is to write a version of peelOff
               that tells you that it returns a suffix.
               
               Define a function peelOff xs ys that returns
               Some (zs , suff) if xs is a non-empty prefix of ys, and 
                                   zs is the suffix left after removing xs, 
                                   and suff is a proof that Suffix zs ys.
               None otherwise.
     Note that unlike the code from lecture, peelOff [] xs should return None;
     you're not supposed to call peelOff when the first list is empty.
     This is necessary for peelOff to return *strict* suffix in the Some branch.
  -}
  peelOff : List Char → (ys : List Char) → Maybe (Σ \ (zs : List Char) → Suffix zs ys)
  peelOff [] ys = None
  peelOff (_ :: _) [] = None
  peelOff (x :: xs) (y :: ys) with Char.equal x y
  ... | Inr _ = None
  ... | Inl _ with peelOff xs ys
  ...             | Some ys' = Some (fst ys' , Drop (snd ys'))
  ...             | None = None

  {- To convince Agda that parseFormat1 terminates, we give it
     an extra argument that is a "recursion permission".  Recursion
     permission is a datatype with one constructor CanRec, where 
          CanRec f : RecursionPermissions ys
     when f : (xs : List A) -> Suffix xs ys -> RecursionPermission xs.

     That is, a recursion permission for ys has, under the CanRec constructor, 
     permission to recur on any suffix of xs.  This way, we can encode
     recursion on the suffix of a list as constructor-guarded recursion,
     so it will pass Agda's termination checker.
  -}

  data RecursionPermission {A : Set} : List A → Set where
    CanRec : {ys : List A} → ((xs : List A) → Suffix xs ys → RecursionPermission xs) → RecursionPermission ys

  {- TASK 2.3: Fill in a definition of parseFormat1 that has this recursion permission argument.
     Unlike above, your definition should pass the termination checker.
  -}
  parseFormat1' : (s : List Char) → RecursionPermission s → Maybe (U × Σ \ (s' : List Char) → Suffix s' s)
  parseFormat1' s (CanRec perm) with peelOff (String.toList "%s") s 
  ...                           | Some z = Some (`string , z)
  ...                           | None with peelOff (String.toList "%u") s 
  ...                                     | Some z = Some (`nat , z)
  ...                                     | None    with peelOff (String.toList "%l") s 
  ...                                                  | None = None
  ...                                                  | Some z with parseFormat1' (fst z) (perm (fst z) (snd z))
  ...                                                              | Some z' = Some ((`list (fst z')) , fst (snd z') , suffix-trans (snd (snd z')) (snd z))
  ...                                                              | None = None

  {- We don't want client functions that use parseFormat1 (like Args or printf)
     to have to create RecursionPermissions for each list they call parseFormat1 with.
     We can solve this problem by showing that you can always create
     a recursion permissions for any list.  This amounts to showing that
     recursion on suffixes is OK, using only constructor-guarded recursion.
  -}

  {- TASK 2.4: Prove that you can make a recursion permission for any suffix of [] -}
  lemma1 : {A : Set} (xs : List A) → Suffix xs [] → RecursionPermission xs
  lemma1 xs ()

  {- TASK 2.5: Prove the following lemma: -}
  lemma2 : {A : Set} {y : A} {xs ys : List A} → Suffix xs (y :: ys) → RecursionPermission ys → RecursionPermission xs
  lemma2 Stop (CanRec x) = CanRec x
  lemma2 {A} {y} {xs} {ys} (Drop p) (CanRec x) = x xs p

  {- TASK 2.6: Using lemma1 and lemma2, make a recursion permission for any list. -}
  well-founded : {A : Set} (ys : List A) → RecursionPermission ys
  well-founded [] = CanRec lemma1
  well-founded {A} (y :: ys) = CanRec (λ ys' p → lemma2 p (well-founded ys))
  
  {- TASK 2.7: Put it all together to give a function parseFormat1 with
               the same type we started with. -}
  parseFormat1 : (s : List Char) → Maybe (U × List Char)
  parseFormat1 s with parseFormat1' s (well-founded s)
  ... | Some (u , s' , suff) = Some (u , s')
  ... | None = None
 
  {- TASK 2.8: Briefly describe one other function that would
               require this technique to be defined in Agda.

  Another function that would require this technique to be defined in Agda would be a function that
  takes in a string (converted to List Char) and removes a user defined list of characters. For 
  example, the user may wish to run a poem through the poem and remove all punctuation and special
  characters so that they are left with just the words. The function would require the recursion permission
  argument to pass the termination checker, similarly to parseFormat1.
  -}
