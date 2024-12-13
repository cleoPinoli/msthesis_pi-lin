{-# OPTIONS --guardedness #-}

open import Data.Nat

-- data Nat : Set

-- record ∞Nat : Set where
--   coinductive
--   field
--     force : Nat
-- open ∞Nat

-- data Nat where
--   zero : Nat
--   succ : ∞Nat -> Nat

-- infinito : ∞Nat
-- infinito .force = succ infinito

data List : Set

record ∞List : Set where
  coinductive
  field
    force : List
open ∞List

data List where
  [] : List
  _::_ : ℕ -> ∞List -> List

uni : ∞List
uni .force = 1 :: uni

map : (ℕ -> ℕ) -> List -> ∞List
map f [] .force = []
map f (x :: xs) .force = f x :: map f (xs .force)

due : ∞List
due = map suc (uni .force)

record Stream : Set where
  coinductive
  field
    hd : ℕ
    tl : Stream
open Stream

mapS : (ℕ -> ℕ) -> Stream -> Stream
mapS f xs .hd = f (xs .hd)
mapS f xs .tl = mapS f (xs .tl)

data Type : Set

record ∞Type : Set where
  coinductive
  field
    force : Type
open ∞Type

data Type where
  Zero One Top Bot : Type
  _⊕_ _&_ : ∞Type -> ∞Type -> Type

nat : ∞Type
nat .force = record { force = One } ⊕ nat

nat' : ∞Type
nat' .force = record { force = Bot } & nat'

data Dual : Type -> Type -> Set

record ∞Dual (t s : ∞Type) : Set where
  coinductive
  field
    force : Dual (t .force) (s .force)
open ∞Dual

data Dual where
  dual-one-bot : Dual One Bot
  dual-plus-with : ∀{t s t' s'} -> ∞Dual t t' -> ∞Dual s s' -> Dual (t ⊕ s) (t' & s')
  dual-with-plus : ∀{t s t' s'} -> ∞Dual t t' -> ∞Dual s s' -> Dual (t & s) (t' ⊕ s')

ok : ∞Dual nat nat'
ok .force = dual-plus-with (record { force = dual-one-bot }) ok

dual-symm : ∀{t s} -> Dual (t .force) (s .force) -> ∞Dual s t
dual-symm p = {!!}
