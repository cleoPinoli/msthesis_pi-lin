{-# OPTIONS --guardedness #-}

module Type where

open import Data.Nat

data Type : Set

record ∞Type : Set where
  constructor box
  coinductive
  field
    unbox : Type
open ∞Type

data Type where
  Zero One Top Bot : Type
  _⊕_ _&_ : ∞Type -> ∞Type -> Type

data Dual : Type -> Type -> Set

record ∞Dual (t s : Type) : Set where
  constructor box
  coinductive
  field
    unbox : Dual t s
open ∞Dual

data Dual where
  dual-one-bot : Dual One Bot
  dual-bot-one : Dual Bot One
  dual-plus-with : ∀{t s t' s'} -> ∞Dual (t .unbox) (t' .unbox) -> ∞Dual (s .unbox) (s' .unbox) -> Dual (t ⊕ s) (t' & s')
  dual-with-plus : ∀{t s t' s'} -> ∞Dual (t .unbox) (t' .unbox) -> ∞Dual (s .unbox) (s' .unbox) -> Dual (t & s) (t' ⊕ s')


dual-symm : ∀{t s} -> Dual t s -> ∞Dual s t
dual-symm dual-one-bot .unbox = dual-bot-one
dual-symm dual-bot-one .unbox = dual-one-bot
dual-symm (dual-plus-with p q) .unbox = dual-with-plus (dual-symm (p .unbox)) (dual-symm (q .unbox))
dual-symm (dual-with-plus p q) .unbox = dual-plus-with (dual-symm (p .unbox)) (dual-symm (q .unbox))
