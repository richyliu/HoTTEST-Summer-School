```agda
{-# OPTIONS --without-K --safe #-}

open import general-notation

data Bool : Type where
  true false : Bool

not : Bool → Bool
not true = false
not false = true

not' : Bool → Bool
not' true = false
not' false = true

idBool : Bool → Bool
idBool = λ (x : Bool) → x

-- Π type
id' : (X : Type) → X → X
id' X x = x

-- implicit
id : {X : Type} → X → X
id x = x

idBool'' : Bool → Bool
idBool'' = id' _

example : {P Q : Type} → P → Q → P
example {P} {Q} p = f
  where
    f : Q → P
    f _ = p

example' : {P Q : Type} → P → Q → P
example' p = λ q → p

open import binary-products

ex : {P Q : Type} → P × Q → Q × P
ex (p , q) = (q , p)

data ℕ : Type where
  zero : ℕ
  suc : ℕ → ℕ

three : ℕ
three = suc (suc (suc zero))

{-# BUILTIN NATURAL ℕ #-}

three' : ℕ
three' = 3 -- synonym for above

D : Bool → Type
D true = ℕ
D false = Bool

-- "mix-fix" operator
if_then_else_ : {X : Type} → Bool → X → X → X
if true  then x else y = x
if false then x else y = y

if[_]_then_else_ : (X : Bool → Type)
                 → (b : Bool)
                 → X true
                 → X false
                 → X b
if[ X ] true  then x else y = x
if[ X ] false then x else y = y

unfamiliar : (b : Bool) → D b
unfamiliar b = if[ D ] b then 3 else false

data List (A : Type) : Type where
  [] : List A
  _::_ : A → List A → List A

infixr 10 _::_

ff : Type → Type
ff = List

sample-list₀ : List ℕ
sample-list₀ = 0 :: 1 :: 2 :: []

length : {X : Type} → List X → ℕ
length [] = 0
length (x :: xs) = suc (length xs)

-- Principle of induction on ℕ
ℕ-elim : {A : ℕ → Type}
       → A 0
       → ((k : ℕ) → A k → A (suc k))
       → (n : ℕ) → A n
ℕ-elim {A} a₀ f = h
  where
    h : (n : ℕ) → A n
    h 0 = a₀
    h (suc n) = f n IH
     where
       IH : A n
       IH = h n

ℕ-elim' : {A : ℕ → Type}
       → A 0
       → ((k : ℕ) → A k → A (suc k))
       → (n : ℕ) → A n
ℕ-elim' {A} a₀ f zero = a₀
ℕ-elim' {A} a₀ f (suc n) = f n (ℕ-elim' a₀ f n)

data 𝟘 : Type where

data 𝟙 : Type where
  ⋆ : 𝟙

_≣_ : ℕ → ℕ → Type
zero ≣ zero = 𝟙
zero ≣ suc y = 𝟘
suc x ≣ zero = 𝟘
suc x ≣ suc y = x ≣ y

infixr 0 _≣_

ℕ-refl : (x : ℕ) → x ≣ x
ℕ-refl zero = ⋆
ℕ-refl (suc x) = ℕ-refl x

_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

_++_ : {A : Type} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

lh : {X : Type} (xs ys : List X)
   → length (xs ++ ys) ≣ length xs + length ys
lh [] ys = ℕ-refl (length ys)
lh (x :: xs) ys = IH
  where
    IH : length (xs ++ ys) ≣ (length xs + length ys)
    IH = lh xs ys
```
