module Run where

open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Data.List
open import Data.List.All

open import Typing
open import Syntax
open import Global
open import Channel
open import Values
open import Session
open import Schedule

open import Examples
open import Aexamples

gas : ℕ → Gas
gas zero = Empty
gas (suc n) = More (gas n)
