module CS400-Lib where

----------------------------------------------------------------------
-- Propositional Equality

infix 4 _=P_
data _=P_ {A : Set} (x : A) : A -> Set where
  instance refl : x =P x

{-# BUILTIN EQUALITY _=P_ #-}

=P-cong : {A B : Set} {x y : A} (f : A -> B) -> x =P y -> f x =P f y
=P-cong f refl = refl

=P-cong2 : {A B C : Set} {x y : A} {z w : B} (f : A -> B -> C) -> x =P y -> z =P w -> f x z =P f y w
=P-cong2 f refl refl = refl

=P-sym : {A : Set} {x y : A} -> x =P y -> y =P x
=P-sym refl = refl

=P-trans : {A : Set} {x y z : A} -> x =P y -> y =P z -> x =P z
=P-trans refl refl = refl

infixl 2 _=P=_
_=P=_ = =P-trans

infix 1 _=P_by[_]
_=P_by[_] : {A : Set} -> (x y : A) -> x =P y -> x =P y
x =P y by[ eq ] = eq

infix 1 _&=_by[_]
_&=_by[_] : {A : Set} -> {x y : A} -> x =P y -> (z : A) -> y =P z -> x =P z
x=y &= z by[ eq ] = =P-trans x=y eq

----------------------------------------------------------------------
-- Booleans

data Bool : Set where
  true : Bool
  false : Bool

module Bools where
  not : Bool -> Bool
  not true = false
  not false = true

  and : Bool -> Bool -> Bool
  and false _ = false
  and true true = true
  and true false = false

  or : Bool -> Bool -> Bool
  or true _ = true
  or false true = true
  or false false = false

  eq : Bool -> Bool -> Bool
  eq true true = true
  eq false false = true
  eq _ _ = false

  xor : Bool -> Bool -> Bool
  xor true true = false
  xor true false = true
  xor false true = true
  xor false false = false

  infix 4 _==_
  _==_ = eq

notB = Bools.not
andB = Bools.and
orB = Bools.or
eqB = Bools.eq
xorB = Bools.xor

infixr 5 _||_
infixr 6 _&&_
infixr 4 _=B_
~ = Bools.not
_&&_ = Bools.and
_||_ = Bools.or
_=B_ = Bools.eq

----------------------------------------------------------------------
-- Natural Numbers

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

module Nats where
  eq : Nat -> Nat -> Bool
  eq zero zero = true
  eq zero (suc n) = false
  eq (suc n) zero = false
  eq (suc m) (suc n) = eq m n

  _==_ = eq

  neq : Nat -> Nat -> Bool
  neq m n = ~ (eq m n)

  leq : Nat -> Nat -> Bool
  leq zero n = true
  leq (suc m) zero = false
  leq (suc m) (suc n) = leq m n

  lt : Nat -> Nat -> Bool
  lt m n = leq m n && neq m n

  max : Nat -> Nat -> Nat
  max zero n = n
  max (suc m) zero = (suc m)
  max (suc m) (suc n) = suc (max m n)

  min : Nat -> Nat -> Nat
  min m zero = zero
  min zero (suc _) = zero
  min (suc m) (suc n) = suc (min m n)

  add : Nat -> Nat -> Nat
  add zero n = n
  add (suc m) n = suc (add m n)

  mul : Nat -> Nat -> Nat
  mul zero n = zero
  mul (suc m) n = add n (mul m n)

  sub : Nat -> Nat -> Nat
  sub zero _ = zero
  sub (suc m) zero = (suc m)
  sub (suc m) (suc n) = sub m n

max = Nats.max
min = Nats.min

infix 4 _<_ _<=_ _=N_
infixl 6 _+_ _-_
infixl 7 _*_
_=N_ = Nats.eq
_<=_ = Nats.leq
_<_ = Nats.lt
_+_ = Nats.add
_*_ = Nats.mul
_-_ = Nats.sub

m+suc-n=suc-m+n : {m n : Nat} -> suc m + n =P m + suc n
m+suc-n=suc-m+n {zero} = refl
m+suc-n=suc-m+n {suc m} = =P-cong suc m+suc-n=suc-m+n

----------------------------------------------------------------------
-- List

infixr 5 _::_
data List A : Set where
  [] : List A
  _::_ : A -> List A -> List A

module Lists where
  map : {A : Set} -> {B : Set} -> (A -> B) -> List A -> List B
  map f [] = []
  map f (x :: xs) = f x :: map f xs

  all : {A : Set} -> (A -> Bool) -> List A -> Bool
  all f [] = true
  all f (x :: l) = (f x) && (all f l)

  any : {A : Set} -> (A -> Bool) -> List A -> Bool
  any f [] = false
  any f (x :: xs) = (f x) || (any f xs)

  append : {A : Set} -> List A -> List A -> List A
  append [] l = l
  append (x :: xs) l = x :: append xs l

mapL = Lists.map
allL = Lists.all
anyL = Lists.any

infixr 5 _++_
_++_ = Lists.append

----------------------------------------------------------------------
-- Maybe

data Maybe A : Set where
  Nothing : Maybe A
  Just : A -> Maybe A

module Maybes where
  map : {A : Set} -> {B : Set} -> (A -> B) -> Maybe A -> Maybe B
  map f Nothing = Nothing
  map f (Just x) = Just (f x)

mapM = Maybes.map

----------------------------------------------------------------------
-- Products

infixr 4 _,_

data And A B : Set where
  _,_ : A -> B -> And A B

infixr 2 _&_
_&_ : Set -> Set -> Set
A & B = And A B

infixr 2 _/\_
_/\_ = _&_

fst : {A : Set} -> {B : Set} -> And A B -> A
fst (a , b) = a

snd : {A : Set} -> {B : Set} -> And A B -> B
snd (a , b) = b

----------------------------------------------------------------------
-- Eithers (Unions)

data Or A B : Set where
  left : A -> Or A B
  right : B -> Or A B

Either : Set -> Set -> Set
Either = Or

infixr 3 _\/_
_\/_ = Or

case : {A B C : Set} -> A \/ B -> (A -> C) -> (B -> C) -> C
case (left x) f g = f x
case (right x) f g = g x

----------------------------------------------------------------------
-- Fins

data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc : {n : Nat} -> Fin n -> Fin (suc n)

module Fins where

  shift : {n : Nat} -> (m p : Nat) -> Fin (m + n) -> Fin (m + (p + n))
  shift m zero f = f
  shift zero (suc p) f = suc (shift zero p f)
  shift (suc m) (suc p) zero = zero
  shift (suc m) (suc p) (suc f) = suc (shift m (suc p) f)

  toNat : {n : Nat} -> Fin n -> Nat
  toNat zero = zero
  toNat (suc f) = suc (toNat f)

  lift : {m n : Nat} -> Fin n -> Fin (m + n)
  lift {zero} f = f
  lift {suc m} zero = zero
  lift {suc m} {suc n} (suc f)
    rewrite =P-sym (m+suc-n=suc-m+n {m} {n}) = suc (lift f)

  pred : {n : Nat} -> Fin n -> Fin n
  pred zero = zero
  pred (suc f) = lift f

  monus : {n : Nat} -> Fin n -> Fin n -> Fin n
  monus x zero = x
  monus zero (suc y) = zero
  monus (suc x) (suc y) = lift (monus x y)

  last : {n : Nat} -> Fin (suc n)
  last {zero} = zero
  last {suc n} = suc last

  dual : {n : Nat} -> Fin n -> Fin n
  dual {suc n} f = monus last f

toNatF = Fins.toNat
liftF = Fins.lift
shiftF = Fins.shift
lastF = Fins.last


----------------------------------------------------------------------
-- Vectors

data Vec A : Nat -> Set where
  [] : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

module Vecs where
  lookup : {A : Set} -> {n : Nat} -> Vec A n -> Fin n -> A
  lookup (x :: _) zero = x
  lookup (_ :: xs) (suc i) = lookup xs i

  lookup-rev : {A : Set} -> {n : Nat} -> Vec A n -> Fin n -> A
  lookup-rev v f = lookup v (Fins.dual f)

  map : {A B : Set} -> {n : Nat} -> (f : A -> B) (v : Vec A n) -> Vec B n
  map f [] = []
  map f (x :: xs) = f x :: map f xs

  append : {A : Set} -> {m n : Nat} -> (u : Vec A m) -> (v : Vec A n) -> Vec A (m + n)
  append [] v = v
  append (x :: xs) v = x :: (append xs v)

lookupV = Vecs.lookup
mapV = Vecs.map

infixl 5 _++V_
_++V_ = Vecs.append

lookupV-mapV :
  {A B : Set} ->
  {n : Nat} ->
  {f : A -> B} ->
  {v : Vec A n} ->
  {i : Fin n} ->
  lookupV (mapV f v) i =P f (lookupV v i)
lookupV-mapV {v = x :: xs} {i = zero} = refl
lookupV-mapV {v = x :: xs} {i = suc j} = lookupV-mapV {v = xs} {i = j}

lookupV-shiftF :
  {A : Set} ->
  {m n : Nat} ->
  {x : A} ->
  {u : Vec A m} ->
  {v : Vec A n} ->
  {i : Fin (m + n)} ->

  lookupV (u ++V v) i =P lookupV (u ++V (x :: v)) (shiftF m 1 i)

lookupV-shiftF {u = []} {i = i} = refl
lookupV-shiftF {u = x :: xs} {v} {i = zero} = refl
lookupV-shiftF {u = x :: xs} {v} {i = suc k} = lookupV-shiftF {u = xs} {i = k}

----------------------------------------------------------------------
-- Empty

data Empty : Set where

False : Set
False = Empty

explode : {A : Set} -> Empty -> A
explode ()

Not : Set -> Set
Not A = A -> Empty

----------------------------------------------------------------------
-- Unit

record Unit : Set where
  instance constructor unit

True : Set
True = Unit

----------------------------------------------------------------------
-- Existential Quantification

data Exists {A : Set} (P : A -> Set) : Set where
  wit : (x : A) -> (prf : P x) -> Exists P

syntax Exists (\x -> B) = [ x ] B

----------------------------------------------------------------------
-- Decidability

IsTrue : Bool -> Set
IsTrue true = Unit
IsTrue false = Empty

IsFalse : Bool -> Set
IsFalse true = Empty
IsFalse false = Unit

IsJust : {A : Set} -> Maybe A -> Set
IsJust Nothing = Empty
IsJust (Just _) = Unit
