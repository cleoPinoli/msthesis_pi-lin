open import Data.Nat using (suc)
open import Data.Sum
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List.Base using ([]; _∷_; [_])
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Binary.PropositionalEquality using (refl)

open import Type
open import Context
open import Permutations
open import Process
open import Reduction
open import Congruence

data Cut {n} : ∀{Γ : Context n} → Process Γ → Set where
  cut :
    ∀{Γ Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A ∷ Γ₁)} {Q : Process (B ∷ Γ₂)} →
    Cut (cut d p P Q)

data Link {n} : ∀{Γ : Context n} → Process Γ → Set where
  link :
    ∀{Γ A B} (d : Dual A B) (p : Γ ≃ [ A ] + [ B ]) → Link (link d p)

data Input {n} : ∀{Γ : Context n} → Process Γ → Set where
  fail :
    ∀{Γ Δ}
    (p : Γ ≃ [] + Δ) → Input (fail (split-l p))
  wait : ∀{Γ Δ} (p : Γ ≃ [] + Δ) {P : Process Δ} → Input (wait (split-l p) P)
  case :
    ∀{Γ Δ A B} (p : Γ ≃ [] + Δ) {P : Process (A ∷ Δ)} {Q : Process (B ∷ Δ)} →
    Input (case (split-l p) P Q)
  join :
    ∀{Γ Δ A B} (p : Γ ≃ [] + Δ) {P : Process (B ∷ A ∷ Δ)} →
    Input (join (split-l p) P)
  all :
    ∀{A : Type (suc n)} {Γ Δ : Context n} (p : Γ ≃ [] + Δ)
    {F : {B C : Type n} -> Subst (make-subst C) A B -> Process (B ∷ Δ)} ->
    Input (all (split-l p) F)

data Output {n} : ∀{Γ : Context n} → Process Γ → Set where
  close : Output close
  select :
    ∀{Γ Δ A B} (x : Bool) (p : Γ ≃ [] + Δ) {P : Process ((if x then A else B) ∷ Δ)} →
    Output (select x (split-l p) P)
  fork :
    ∀{Γ Δ Δ₁ Δ₂ A B} (p : Γ ≃ [] + Δ) (q : Δ ≃ Δ₁ + Δ₂)
    {P : Process (A ∷ Δ₁)} {Q : Process (B ∷ Δ₂)} →
    Output (fork (split-l p) q P Q)
  ex :
    ∀{A : Type (suc n)} {B C : Type n} {Γ Δ} (p : Γ ≃ [] + Δ)
    {σ : Subst (make-subst C) A B} {P : Process (B ∷ Δ)} ->
    Output (ex (split-l p) σ P)

data Delayed {n} : ∀{Γ : Context n} → Process Γ → Set where
  fail :
    ∀{A Γ Δ}
    (p : Γ ≃ ⊤ , Δ) → Delayed (fail (split-r {_} {A} p))
  wait : ∀{C Γ Δ} (p : Γ ≃ ⊥ , Δ) {P : Process (C ∷ Δ)} →
         Delayed (wait (split-r p) P)
  case :
    ∀{Γ Δ C A B} (p : Γ ≃ A & B , Δ) {P : Process (A ∷ C ∷ Δ)} {Q : Process (B ∷ C ∷ Δ)} →
    Delayed (case (split-r p) P Q)
  join :
    ∀{Γ Δ C A B} (p : Γ ≃ A ⅋ B , Δ) {P : Process (B ∷ A ∷ C ∷ Δ)} →
    Delayed (join (split-r p) P)
  select :
    ∀{Γ Δ C A B} (x : Bool) (p : Γ ≃ A ⊕ B , Δ) {P : Process ((if x then A else B) ∷ C ∷ Δ)} →
    Delayed (select x (split-r p) P)
  fork-l :
    ∀{Γ Δ Δ₁ Δ₂ C A B} (p : Γ ≃ A ⊗ B , Δ) (q : Δ ≃ Δ₁ + Δ₂)
    {P : Process (A ∷ C ∷ Δ₁)} {Q : Process (B ∷ Δ₂)} →
    Delayed (fork (split-r p) (split-l q) P Q)
  fork-r :
    ∀{Γ Δ Δ₁ Δ₂ C A B} (p : Γ ≃ A ⊗ B , Δ) (q : Δ ≃ Δ₁ + Δ₂)
    {P : Process (A ∷ Δ₁)} {Q : Process (B ∷ C ∷ Δ₂)} →
    Delayed (fork (split-r p) (split-r q) P Q)
  client :
    ∀{Γ Δ A C} (p : Γ ≃ ¿ A , Δ) {P : Process (A ∷ C ∷ Δ)} →
    Delayed (client (split-r p) P)
  weaken :
    ∀{Γ Δ A C} (p : Γ ≃ ¿ A , Δ) {P : Process (C ∷ Δ)} →
    Delayed (weaken (split-r p) P)
  contract :
    ∀{Γ Δ A C} (p : Γ ≃ ¿ A , Δ) {P : Process (¿ A ∷ ¿ A ∷ C ∷ Δ)} →
    Delayed (contract (split-r p) P)
  ex :
    ∀{A : Type (suc n)} {B C D : Type n} {Γ Δ} (p : Γ ≃ $∃ A , Δ)
    {σ : Subst (make-subst C) A B} {P : Process (B ∷ D ∷ Δ)} ->
    Delayed (ex (split-r p) σ P)
  all :
    ∀{A : Type (suc n)} {D : Type n} {Γ Δ : Context n} (p : Γ ≃ $∀ A , Δ)
    {F : {B C : Type n} -> Subst (make-subst C) A B -> Process (B ∷ D ∷ Δ)} ->
    Delayed (all (split-r p) F)

data Client {n} : ∀{Γ : Context n} → Process Γ → Set where
  client :
    ∀{Γ Δ A} (p : Γ ≃ [] + Δ)
    {P : Process (A ∷ Δ)} →
    Client (client (split-l p) P)
  weaken :
    ∀{Γ Δ A} (p : Γ ≃ [] + Δ)
    {P : Process Δ} →
    Client (weaken {A = A} (split-l p) P)
  contract :
    ∀{Γ Δ A} (p : Γ ≃ [] + Δ)
    {P : Process (¿ A ∷ ¿ A ∷ Δ)} →
    Client (contract (split-l p) P)

data Server {n} : ∀{Γ : Context n} → Process Γ → Set where
  server :
    ∀{Γ Δ A} (p : Γ ≃ [] + Δ) (un : Un Δ) {P : Process (A ∷ Δ)} →
    Server (server (split-l p) un P)

data DelayedServer {n} : ∀{Γ : Context n} → Process Γ → Set where
  server :
    ∀{Γ Δ A C} (p : Γ ≃ ¡ A , Δ) (un : Un Δ) {P : Process (A ∷ ¿ C ∷ Δ)} →
    DelayedServer (server (split-r p) (un-∷ un) P)

Thread : ∀{n} {Γ : Context n} → Process Γ → Set
Thread P = Link P ⊎ Delayed P ⊎ Output P ⊎ Input P ⊎
           Client P ⊎ Server P ⊎ DelayedServer P

Observable : ∀{n} {Γ : Context n} → Process Γ → Set
Observable P = ∃[ Q ] P ⊒ Q × Thread Q

Reducible : ∀{n} {Γ : Context n} → Process Γ → Set
Reducible P = ∃[ Q ] P ↝ Q

Alive : ∀{n} {Γ : Context n} → Process Γ → Set
Alive P = Observable P ⊎ Reducible P

link-thread : ∀{n} {A B : Type n} {Γ} (d : Dual A B) (p : Γ ≃ [ A ] + [ B ]) → Thread (link d p)
link-thread d p = inj₁ (link d p)

close-thread : ∀{n} -> Thread {n} close
close-thread = inj₂ (inj₂ (inj₁ close))

wait-thread : ∀{n} {Γ Δ : Context n} (p : Γ ≃ [ ⊥ ] + Δ) {P : Process Δ} → Thread (wait p P)
wait-thread (split-l p) = inj₂ (inj₂ (inj₂ (inj₁ (wait p))))
wait-thread (split-r p) = inj₂ (inj₁ (wait p))

fail-thread : ∀{n} {Γ Δ : Context n} (p : Γ ≃ [ ⊤ ] + Δ) → Thread (fail p)
fail-thread (split-l p) = inj₂ (inj₂ (inj₂ (inj₁ (fail p))))
fail-thread (split-r p) = inj₂ (inj₁ (fail p))

case-thread :
  ∀{n} {A B : Type n} {Γ Δ} (p : Γ ≃ [ A & B ] + Δ) {P : Process (A ∷ Δ)} {Q : Process (B ∷ Δ)} →
  Thread (case p P Q)
case-thread (split-l p) = inj₂ (inj₂ (inj₂ (inj₁ (case p))))
case-thread (split-r p) = inj₂ (inj₁ (case p))

join-thread :
  ∀{n} {A B : Type n} {Γ Δ} (p : Γ ≃ [ A ⅋ B ] + Δ) {P : Process (B ∷ A ∷ Δ)} →
  Thread (join p P)
join-thread (split-l p) = inj₂ (inj₂ (inj₂ (inj₁ (join p))))
join-thread (split-r p) = inj₂ (inj₁ (join p))

select-thread :
  ∀{n} {A B : Type n} {Γ Δ} (x : Bool) (p : Γ ≃ A ⊕ B , Δ) {P : Process ((if x then A else B) ∷ Δ)} →
  Thread (select x p P)
select-thread x (split-l p) = inj₂ (inj₂ (inj₁ (select x p)))
select-thread x (split-r p) = inj₂ (inj₁ (select x p))

fork-thread :
  ∀{n} {A B : Type n} {Γ Δ Δ₁ Δ₂} (p : Γ ≃ [ A ⊗ B ] + Δ) (q : Δ ≃ Δ₁ + Δ₂)
  {P : Process (A ∷ Δ₁)} {Q : Process (B ∷ Δ₂)} →
  Thread (fork p q P Q)
fork-thread (split-l p) q = inj₂ (inj₂ (inj₁ (fork p q)))
fork-thread (split-r p) (split-l q) = inj₂ (inj₁ (fork-l p q))
fork-thread (split-r p) (split-r q) = inj₂ (inj₁ (fork-r p q))

client-thread :
  ∀{n} {A : Type n} {Γ Δ} (p : Γ ≃ [ ¿ A ] + Δ)
  {P : Process (A ∷ Δ)} →
  Thread (client p P)
client-thread (split-l p) = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (client p)))))
client-thread (split-r p) = inj₂ (inj₁ (client p))

weaken-thread :
  ∀{n} {A : Type n} {Γ Δ} (p : Γ ≃ [ ¿ A ] + Δ)
  {P : Process Δ} →
  Thread (weaken {A = A} p P)
weaken-thread (split-l p) = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (weaken p)))))
weaken-thread (split-r p) = inj₂ (inj₁ (weaken p))

contract-thread :
  ∀{n} {A : Type n} {Γ Δ} (p : Γ ≃ [ ¿ A ] + Δ)
  {P : Process (¿ A ∷ ¿ A ∷ Δ)} →
  Thread (contract p P)
contract-thread (split-l p) = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (contract p)))))
contract-thread (split-r p) = inj₂ (inj₁ (contract p))

server-thread :
  ∀{n} {A : Type n} {Γ Δ} (p : Γ ≃ [ ¡ A ] + Δ) (un : Un Δ) {P : Process (A ∷ Δ)} →
  Thread (server p un P)
server-thread (split-l p) un = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (server p un))))))
server-thread (split-r p) (un-∷ un) = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (server p un))))))

ex-thread :
  ∀{n} {A : Type (suc n)} {B C : Type n} {Γ Δ} (p : Γ ≃ $∃ A , Δ)
  {σ : Subst (make-subst C) A B} {P : Process (B ∷ Δ)} ->
  Thread (ex p σ P)
ex-thread (split-l p) = inj₂ (inj₂ (inj₁ (ex p)))
ex-thread (split-r p) = inj₂ (inj₁ (ex p))

all-thread :
  ∀{n} {A : Type (suc n)} {Γ Δ : Context n} (p : Γ ≃ $∀ A , Δ)
  {F : {B C : Type n} -> Subst (make-subst C) A B -> Process (B ∷ Δ)} ->
  Thread (all p F)
all-thread (split-l p) = inj₂ (inj₂ (inj₂ (inj₁ (all p))))
all-thread (split-r p) = inj₂ (inj₁ (all p))

data CanonicalCut {n} {Γ : Context n} : Process Γ → Set where
  cc-link :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A ∷ Γ₁)} {Q : Process (B ∷ Γ₂)} →
    Link P → CanonicalCut (cut d p P Q)
  cc-delayed :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A ∷ Γ₁)} {Q : Process (B ∷ Γ₂)} →
    Delayed P → CanonicalCut (cut d p P Q)
  cc-delayed-server :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A ∷ Γ₁)} {Q : Process (B ∷ Γ₂)} →
    DelayedServer P → Server Q → CanonicalCut (cut d p P Q)
  cc-redex :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A ∷ Γ₁)} {Q : Process (B ∷ Γ₂)} →
    Output P → Input Q → CanonicalCut (cut d p P Q)
  cc-connect :
    ∀{Γ₁ Γ₂ A B} (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂)
    {P : Process (A ∷ Γ₁)} {Q : Process (B ∷ Γ₂)} →
    Server P → Client Q → CanonicalCut (cut d p P Q)

output-output :
  ∀{n} {A B : Type n} {Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (B ∷ Δ)} → Dual A B → ¬ (Output P × Output Q)
output-output d-𝟙-⊥ (close , ())
output-output (d-⊕-& d d₁) (select x p , ())
output-output (d-⊗-⅋ d d₁) (fork p q₁ , ())
output-output (d-∃-∀ d) (ex p , ())

output-client :
  ∀{n} {A B : Type n} {Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (B ∷ Δ)} → Dual A B → ¬ (Output P × Client Q)
output-client () (close , client p)

output-server :
  ∀{n} {A B : Type n} {Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (B ∷ Δ)} → Dual A B → ¬ (Output P × Server Q)
output-server () (close , server p un)

output-delayed-server :
  ∀{n} {A B : Type n} {Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (B ∷ Δ)} → Dual A B → ¬ (Output P × DelayedServer Q)
output-delayed-server () (close , server p un)

input-input :
  ∀{n} {A B : Type n} {Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (B ∷ Δ)} → Dual A B → ¬ (Input P × Input Q)
input-input d-⊤-𝟘 (fail p , ())
input-input d-⊥-𝟙 (wait p , ())
input-input (d-&-⊕ d d₁) (case p , ())
input-input (d-⅋-⊗ d d₁) (join p , ())
input-input (d-∀-∃ d) (all p , ())

input-client :
  ∀{n} {A B : Type n} {Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (B ∷ Δ)} → Dual A B → ¬ (Input P × Client Q)
input-client () (fail p₁ , client p)

input-server :
  ∀{n} {A B : Type n} {Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (B ∷ Δ)} → Dual A B → ¬ (Input P × Server Q)
input-server () (fail p₁ , server p un)

input-delayed-server :
  ∀{n} {A B : Type n} {Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (B ∷ Δ)} → Dual A B → ¬ (Input P × DelayedServer Q)
input-delayed-server () (fail p₁ , server p un)

client-client :
  ∀{n} {A B : Type n} {Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (B ∷ Δ)} → Dual A B → ¬ (Client P × Client Q)
client-client () (client p , client p₁)

client-delayed-server :
  ∀{n} {A B : Type n} {Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (B ∷ Δ)} → Dual A B → ¬ (Client P × DelayedServer Q)
client-delayed-server () (client p₁ , server p un)

server-server :
  ∀{n} {A B : Type n} {Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (B ∷ Δ)} → Dual A B → ¬ (Server P × Server Q)
server-server () (server p un , server p₁ un₁)

delayed-server-delayed-served :
  ∀{n} {A B : Type n} {Γ Δ} {P : Process (A ∷ Γ)} {Q : Process (B ∷ Δ)} → Dual A B → ¬ (DelayedServer P × DelayedServer Q)
delayed-server-delayed-served () (server p un , server p₁ un₁)

canonical-cut :
  ∀{n} {A B : Type n} {Γ Γ₁ Γ₂} {P : Process (A ∷ Γ₁)} {Q : Process (B ∷ Γ₂)}
  (d : Dual A B) (p : Γ ≃ Γ₁ + Γ₂) →
  Thread P → Thread Q → ∃[ R ] CanonicalCut R × cut d p P Q ⊒ R

canonical-cut dc pc (inj₁ x) Qt = _ , cc-link dc pc x , s-refl
canonical-cut dc pc (inj₂ x) (inj₁ y) = _ , cc-link (dual-symm dc) (+-comm pc) y , s-comm dc pc
canonical-cut dc pc (inj₂ (inj₁ x)) (inj₂ y) = _ , cc-delayed dc pc x , s-refl
canonical-cut dc pc (inj₂ (inj₂ x)) (inj₂ (inj₁ y)) = _ , cc-delayed (dual-symm dc) (+-comm pc) y , s-comm dc pc
canonical-cut dc pc (inj₂ (inj₂ (inj₁ x))) (inj₂ (inj₂ (inj₁ y))) = contradiction (x , y) (output-output dc)
canonical-cut dc pc (inj₂ (inj₂ (inj₁ x))) (inj₂ (inj₂ (inj₂ (inj₁ y)))) = _ , cc-redex dc pc x y , s-refl
canonical-cut dc pc (inj₂ (inj₂ (inj₁ x))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y))))) = contradiction (x , y) (output-client dc)
canonical-cut dc pc (inj₂ (inj₂ (inj₁ x))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y)))))) = contradiction (x , y) (output-server dc)
canonical-cut dc pc (inj₂ (inj₂ (inj₁ x))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ y)))))) = contradiction (x , y) (output-delayed-server dc)
canonical-cut dc pc (inj₂ (inj₂ (inj₂ (inj₁ x)))) (inj₂ (inj₂ (inj₁ y))) = _ , cc-redex (dual-symm dc) (+-comm pc) y x , s-comm dc pc
canonical-cut dc pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))) (inj₂ (inj₂ (inj₁ y))) = contradiction (y , x) (output-client (dual-symm dc))
canonical-cut dc pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))) (inj₂ (inj₂ (inj₁ y))) = contradiction (y , x) (output-server (dual-symm dc))
canonical-cut dc pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ x)))))) (inj₂ (inj₂ (inj₁ y))) = contradiction (y , x) (output-delayed-server (dual-symm dc))
canonical-cut dc pc (inj₂ (inj₂ (inj₂ (inj₁ x)))) (inj₂ (inj₂ (inj₂ (inj₁ y)))) = contradiction (x , y) (input-input dc)
canonical-cut dc pc (inj₂ (inj₂ (inj₂ (inj₁ x)))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y))))) = contradiction (x , y) (input-client dc)
canonical-cut dc pc (inj₂ (inj₂ (inj₂ (inj₁ x)))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y)))))) = contradiction (x , y) (input-server dc)
canonical-cut dc pc (inj₂ (inj₂ (inj₂ (inj₁ x)))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ y)))))) = contradiction (x , y) (input-delayed-server dc)
canonical-cut dc pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))) (inj₂ (inj₂ (inj₂ (inj₁ y)))) = contradiction (y , x) (input-client (dual-symm dc))
canonical-cut dc pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))) (inj₂ (inj₂ (inj₂ (inj₁ y)))) = contradiction (y , x) (input-server (dual-symm dc))
canonical-cut dc pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ x)))))) (inj₂ (inj₂ (inj₂ (inj₁ y)))) = contradiction (y , x) (input-delayed-server (dual-symm dc))
canonical-cut dc pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y))))) = contradiction (x , y) (client-client dc)
canonical-cut dc pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y)))))) = _ , cc-connect (dual-symm dc) (+-comm pc) y x , s-comm dc pc
canonical-cut dc pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ y)))))) = contradiction (x , y) (client-delayed-server dc)
canonical-cut dc pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y))))) = _ , cc-connect dc pc x y , s-refl
canonical-cut dc pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ x)))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y))))) = contradiction (y , x) (client-delayed-server (dual-symm dc))
canonical-cut dc pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y)))))) = contradiction (x , y) (server-server dc)
canonical-cut dc pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ x)))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ y)))))) = _ , cc-delayed-server (dual-symm dc) (+-comm pc) y x , s-comm dc pc
canonical-cut dc pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ x)))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ y)))))) = _ , cc-delayed-server dc pc x y , s-refl
canonical-cut dc pc (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ x)))))) (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ y)))))) = contradiction (x , y) (delayed-server-delayed-served dc)

⊒Alive : ∀{n} {Γ : Context n} {P Q : Process Γ} → P ⊒ Q → Alive Q → Alive P
⊒Alive pcong (inj₁ (_ , x , th)) = inj₁ (_ , s-tran pcong x , th)
⊒Alive pcong (inj₂ (_ , red)) = inj₂ (_ , r-cong pcong red)

canonical-cut-alive : ∀{n} {Γ : Context n} {P : Process Γ} → CanonicalCut P → Alive P
canonical-cut-alive (cc-link d p (link e (split-l (split-r split-e)))) with dual-fun-r e d
... | refl = inj₂ (_ , r-link d e p)
canonical-cut-alive (cc-link d p (link e (split-r (split-l split-e)))) with dual-fun-l e (dual-symm d)
... | refl = inj₂ (_ , r-cong (s-cong d p (s-link e (split-r (split-l split-e))) s-refl) (r-link d (dual-symm e) p))
canonical-cut-alive (cc-redex d-𝟙-⊥ p close (wait q)) with +-empty-l p | +-empty-l q
... | refl | refl = inj₂ (_ , r-close p q)
canonical-cut-alive (cc-redex (d-⊕-& d e) p (select false q) (case r)) with +-empty-l q | +-empty-l r
... | refl | refl = inj₂ (_ , r-select-r d e p q r)
canonical-cut-alive (cc-redex (d-⊕-& d e) p (select true q) (case r)) with +-empty-l q | +-empty-l r
... | refl | refl = inj₂ (_ , r-select-l d e p q r)
canonical-cut-alive (cc-redex (d-⊗-⅋ d e) p (fork q r) (join s)) with +-empty-l q | +-empty-l s
... | refl | refl = inj₂ (_ , r-fork d e p s r q)
canonical-cut-alive (cc-redex (d-∃-∀ d) p (ex q) (all r)) with +-empty-l q | +-empty-l r
... | refl | refl = inj₂ (_ , r-poly _ d p q r)
canonical-cut-alive (cc-connect (d-!-? d) p (server q un) (client r)) with +-empty-l q | +-empty-l r
... | refl | refl = inj₂ (_ , r-client d p q r un)
canonical-cut-alive (cc-connect (d-!-? d) p (server q un) (weaken r)) with +-empty-l q | +-empty-l r
... | refl | refl = inj₂ (_ , r-weaken d p q r un)
canonical-cut-alive (cc-connect (d-!-? d) p (server q un) (contract r)) with +-empty-l q | +-empty-l r
... | refl | refl = inj₂ (_ , r-contract d p q r un)
canonical-cut-alive (cc-delayed d p (wait q)) =
  let _ , _ , q′ = +-assoc-l p q in
  inj₁ (_ , s-wait d p q , wait-thread q′)
canonical-cut-alive (cc-delayed d p (case q)) =
  let _ , _ , q′ = +-assoc-l p q in
  inj₁ (_ , s-case d p q , case-thread q′)
canonical-cut-alive (cc-delayed d p (join q)) =
  let _ , _ , q′ = +-assoc-l p q in
  inj₁ (_ , s-join d p q , join-thread q′)
canonical-cut-alive (cc-delayed d p (select false q)) =
  let _ , _ , q′ = +-assoc-l p q in
  inj₁ (_ , s-select-r d p q , select-thread false q′)
canonical-cut-alive (cc-delayed d p (select true q)) =
  let _ , _ , q′ = +-assoc-l p q in
  inj₁ (_ , s-select-l d p q , select-thread true q′)
canonical-cut-alive (cc-delayed d p (fork-l q r)) =
  let _ , p′ , q′ = +-assoc-l p q in
  let _ , p′′ , r′ = +-assoc-l p′ r in
  let _ , q′′ , r′′ = +-assoc-r r′ (+-comm p′′) in
  inj₁ (_ , s-fork-l d p q r , fork-thread q′ r′′)
canonical-cut-alive (cc-delayed d p (fork-r q r)) =
  let _ , p′ , q′ = +-assoc-l p q in
  let _ , p′′ , r′ = +-assoc-l p′ r in
  inj₁ (_ , s-fork-r d p q r , fork-thread q′ r′)
canonical-cut-alive (cc-delayed d p (fail q)) =
  let _ , p′ , q′ = +-assoc-l p q in
  inj₁ (_ , s-fail d p q , fail-thread q′)
canonical-cut-alive (cc-delayed d p (client q)) =
  let _ , _ , q′ = +-assoc-l p q in
  inj₁ (_ , s-client d p q , client-thread q′)
canonical-cut-alive (cc-delayed d p (weaken q)) =
  let _ , _ , q′ = +-assoc-l p q in
  inj₁ (_ , s-weaken d p q , weaken-thread q′)
canonical-cut-alive (cc-delayed d p (contract q)) =
  let _ , _ , q′ = +-assoc-l p q in
  inj₁ (_ , s-contract d p q , contract-thread q′)
canonical-cut-alive (cc-delayed d p (ex q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , s-ex d p q , ex-thread q')
canonical-cut-alive (cc-delayed d p (all q)) =
  let _ , _ , q' = +-assoc-l p q in
  inj₁ (_ , s-all d p q , all-thread q')
canonical-cut-alive (cc-delayed-server (d-?-! d) p (server q un) (server r un′)) with +-empty-l r
... | refl =
  let _ , p′ , q′ = +-assoc-l p q in
  inj₁ (_ , s-server d p q r un un′ , server-thread q′ (#un+ p′ un un′))

deadlock-freedom : ∀{n} {Γ : Context n} (P : Process Γ) → Alive P
deadlock-freedom (link d p) = inj₁ (_ , s-refl , link-thread d p)
deadlock-freedom (fail p) = inj₁ (_ , s-refl , fail-thread p)
deadlock-freedom close = inj₁ (_ , s-refl , close-thread)
deadlock-freedom (wait p P) = inj₁ (_ , s-refl , wait-thread p)
deadlock-freedom (select x p P) = inj₁ (_ , s-refl , select-thread x p)
deadlock-freedom (case p P Q) = inj₁ (_ , s-refl , case-thread p)
deadlock-freedom (fork p q P Q) = inj₁ (_ , s-refl , fork-thread p q)
deadlock-freedom (join p P) = inj₁ (_ , s-refl , join-thread p)
deadlock-freedom (server p un P) = inj₁ (_ , s-refl , server-thread p un)
deadlock-freedom (client p P) = inj₁ (_ , s-refl , client-thread p)
deadlock-freedom (weaken p P) = inj₁ (_ , s-refl , weaken-thread p)
deadlock-freedom (contract p P) = inj₁ (_ , s-refl , contract-thread p)
deadlock-freedom (ex p σ P) = inj₁ (_ , s-refl , ex-thread p)
deadlock-freedom (all p F) = inj₁ (_ , s-refl , all-thread p)
deadlock-freedom (cut d p P Q) with deadlock-freedom P
... | inj₂ (_ , red) = inj₂ (_ , r-cut d p red)
... | inj₁ (_ , Pc , Pt) with deadlock-freedom Q
... | inj₂ (_ , red) = inj₂ (_ , r-cong (s-comm d p) (r-cut (dual-symm d) (+-comm p) red))
... | inj₁ (_ , Qc , Qt) with canonical-cut d p Pt Qt
... | _ , cc , pcong = ⊒Alive (s-tran (s-cong d p Pc Qc) pcong) (canonical-cut-alive cc)
