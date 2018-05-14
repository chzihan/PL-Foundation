module Day2Term where

open import Data.List
open import Day2Type public
open import Data.String
open import Data.Nat
open import Relation.Binary
open import Data.Product using (_,_)
open import Data.Bool


Name = String

module Unchecked where

  data Term : Set where
    var  : Name → Term
    lit  : ℕ    → Term
    suc  : Term
    app  : Term → Term → Term
    lam  : Name → Type → Term → Term


module WellTyped where

  Cxt = List Type

  data Term : Cxt → Type → Set where
    var : ∀ {Γ a} (x : Name) (i : (x , a) ∈ Γ) → Term Γ a
    app : ∀ {Γ a b} (u : Term Γ (a => b)) (v : Term Γ a) →
            Term Γ b
    lam : ∀ {Γ} x a {b} (v : Term ((x , a) ∷ Γ) b) → Term Γ (a => b)
    lit : ∀ {Γ} (n : Nat) → Term Γ nat
    suc : ∀ {Γ} → Term Γ (nat => nat)

  open Unchecked renaming (Term to Expr)
