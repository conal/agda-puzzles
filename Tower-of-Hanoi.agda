module Tower-of-Hanoi where

open import Level using (0ℓ)
open import Data.Nat using (ℕ; zero; suc; s≤s)
open import Data.Fin using (Fin; zero; suc; _>_)
open import Data.Fin.Patterns using () renaming (0F to A; 1F to B; 2F to C)
open import Data.Vec using (Vec; _∷_; lookup; replicate; _[_]≔_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star)
open import Data.Fin.Permutation
open import Function.Bundles using (Inverse)

---- Puzzle

Peg = Fin 3

Disk Pos : ℕ → Set
Disk = Fin
Pos  = Vec Peg  -- *descending* size

-- Permutation to ensure distinctness.
Perm : Set
Perm = Permutation′ 3

module abc (π : Perm) where open Inverse π; a = to A; b = to B; c = to C

infix 7 _·_; _·_ = replicate
infix 8 _!_; _!_ = lookup

private variable n : ℕ

-- One step: disk k can move from peg a to c if all smaller disks are at b.
infix 0 _⇾_
data _⇾_ : Rel (Pos n) 0ℓ where
  mk⇾ : (π : Perm) (open abc π) {k : Disk n} {u : Pos n}
      → u ! k ≡ a
      → (∀ {j} → j > k → u ! j ≡ b)
      → u ⇾ u [ k ]≔ c

-- Zero or more steps (reflexive-transitive closure).
infix 0 _↝_
_↝_ : Rel (Pos n) _
_↝_ = Star _⇾_

-- Main theorem: All n disks can move from A to C
A↝C : n · A ↝ n · C
