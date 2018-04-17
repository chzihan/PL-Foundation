module test1 where

data Bool : Set where
     false : Bool
     true  : Bool

not : Bool → Bool
not false = true
not true = false

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
  

{-# BUILTIN NATURAL ℕ #-}

data List (A : Set) : Set where
  [] : List A
  _∷_  : A → List A → List A

infixr 5 _∷_

ex1 : List ℕ
ex1 = 1 ∷ []

id : {A : Set} → A → A
id x = x


ex2 : {A B C : Set} →
      (A → B → C) → B → A → C
ex2 f y x = f x y


ex3 : {A B C : Set} →
      (A → B) → (B → C) → A → C
Ex3 f1 f2 x = f2 (f1 x)


ex4 : {A B C : Set} →
      (A → B → C) → (A → B) → A → C
ex4 f1 f2 x =   ex2 f1 (f2 x) x
