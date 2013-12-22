{- Name: Bowornmet (Ben) Hudson and Theodore (Ted) Kim
-}

open import lib.Preliminaries

module finaldemo where

  -- operation
  Op : Set → Set
  Op el = el → el → el

  -- record of Group
  record Group : Set1 where
    field
      el : Set
      _*_ : Op el
      e : el
      inv : el → el
      assoc :  ∀ x y z → ((x * y) * z) == (x * (y * z))
      ident-l : ∀ x → (e * x) == x
      ident-r : ∀ x → (x * e) == x
      inv-l : ∀ x → ((inv x) * x) == e
      inv-r : ∀ x → (x * (inv x)) == e

  -- first example, Bools with "multiplication" operation. Comparable to Z mod 2
  -- with addition

  -- multiplication of bools
  multB : Bool → Bool → Bool
  multB True True = True
  multB True False = False
  multB False True = False
  multB False False = True

  -- associativity of bools
  assocB : (x y z : Bool) → multB (multB x y) z == multB x (multB y z)
  assocB True True True = Refl
  assocB True True False = Refl
  assocB True False True = Refl
  assocB True False False = Refl
  assocB False True True = Refl
  assocB False True False = Refl
  assocB False False True = Refl
  assocB False False False = Refl

  -- proof of identity
  multTruel : (x : Bool) → (multB True x == x)
  multTruel True = Refl
  multTruel False = Refl

  multTruer : (x : Bool) → (multB x True == x)
  multTruer True = Refl
  multTruer False = Refl

  -- inverses of bools
  invB : Bool → Bool
  invB True = True
  invB False = False

  -- proof of inverses with identity
  invBMultl : (x : Bool) → (multB (invB x) x == True)
  invBMultl True = Refl
  invBMultl False = Refl

  invBMultr : (x : Bool) → (multB x (invB x) == True)
  invBMultr True = Refl
  invBMultr False = Refl

  example1 : Group
  example1 = record {
               el = Bool;
               _*_ = multB;
               e = True;
               inv = invB;
               assoc = assocB;
               ident-l = multTruel;
               ident-r = multTruer;
               inv-l = invBMultl;
               inv-r = invBMultr }

  record AbelianGroup (G : Group) : Set where
    open Group G
    field
      comm : ∀ (x y : el) → x * y == y * x

  -- proof of commutativity for multiplication on bools
  commB : (x y : Bool) → multB x y == multB y x
  commB True True = Refl
  commB True False = Refl
  commB False True = Refl
  commB False False = Refl

  example3 : AbelianGroup example1
  example3 = record {
               comm = commB }

  -- homomorphisms
  -- problem regarding open Group: constructor _*_
  record homomorphism (G : Group) (H : Group) : Set where
    open Group renaming (_*_ to *)
    field
      f : el G → el H
      id : f (e G) == e H
      hm : (a b : el G) → (f (* G a b)) == * H (f a) (f b)

  -- some theorems
  module Theorems (G : Group) where
    open Group G
    congruenceOP : {a b c : el} → a == b → a * c == b * c
    congruenceOP Refl = Refl 

    theorembaby : {a b : el} → ((a * e) * b) == (a * b)
    theorembaby = λ {a} {b} → congruenceOP (ident-r a)

    theorem1 : {a b : el} → inv (a * b) == (inv a * inv b)
    theorem1 = λ {a} {b} → {!_=⟨_⟩_!}

    theorem2 : {G : Group} (a b c : el) → (a * c) == (b * c) → a == b
    theorem2 a b c p = {!p!}

    theorem3 : {G : Group} (g : el) → (g * g) == g → g == e
    theorem3 g p = {!!}

    theorem5 : {G : Group} (a b c : el) → ((a * b) * c) == e → ((b * c) * a) == e 
    theorem5 {G} a b c p = {!!}

