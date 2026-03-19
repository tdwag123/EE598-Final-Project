import Mathlib.Tactic
import EE598Project.GaussianInt


open GaussianInt

abbrev SqPair := Int × Int

-- Computes modular exponentiation a^b mod m using fast exponentiation
def modPow (a b m : Nat) : Nat :=
  if m = 0 then 0
  else go a b m 1
where
  go (base exp modulus acc : Nat) : Nat :=
    if hexp : exp = 0 then acc % modulus
    else if exp % 2 = 1 then go (base * base % modulus) (exp / 2) modulus (acc * base % modulus)
    else go (base * base % modulus) (exp / 2) modulus acc
  termination_by exp
  decreasing_by all_goals exact Nat.div_lt_self (by omega) (by norm_num)

-- Returns the prime factorization of n as a list of primes, with multiplicity
def factorsList (n : Nat) : List Nat :=
  go n 2 n []
where
  go (n d fuel : Nat) (acc : List Nat) : List Nat :=
    match fuel with
    | 0        => if n > 1 then (n :: acc).reverse else acc.reverse
    | fuel + 1 =>
      if n ≤ 1      then acc.reverse
      else if n % d = 0 then go (n / d) d  fuel (d :: acc)
      else                   go n (d + 1) fuel acc

/-- Remove consecutive duplicates from a sorted list. -/
def sortedDedup : List Nat → List Nat
  | []            => []
  | [x]           => [x]
  | x :: y :: rest =>
    if x == y then sortedDedup (y :: rest)
    else x :: sortedDedup (y :: rest)

-- Count occurrences of p in the list.
def countOccurrences (p : Nat) (lst : List Nat) : Nat :=
  lst.foldl (fun acc q => if q == p then acc + 1 else acc) 0

-- Algorithm A: Check if n is a sum of two squares (Fermat's criterion)
def isSolvable (n : Nat) : Bool :=
  let flat   := factorsList n
  let primes := sortedDedup flat
  primes.all fun p =>
    ¬ (p % 4 == 3 && countOccurrences p flat % 2 == 1)

-- Algorithm B: Compute (a, b) such that a² + b² = 2^e
def powerOfTwo : Nat → SqPair
  | 0     => (1, 0)
  | 1     => (1, 1)
  | e + 1 =>
    let (a, b) := powerOfTwo e
    (a - b, a + b)

-- Algorithm C: Compute (a, b) such that a² + b² = p^e for p ≡ 3 (mod 4)
def powerOfThreeMod4 (p e : Nat) : SqPair :=
  let k := e / 2
  (↑(p ^ k), 0)

-- Algorithm D1: Find t such that t² ≡ −1 (mod p)
def findQuadraticNonResidue (p : Nat) : Nat :=
  let rec go (a fuel : Nat) : Nat :=
    match fuel with
    | 0           => 0
    | fuel' + 1   =>
      if modPow a ((p - 1) / 2) p == p - 1 then a
      else go (a + 1) fuel'
  go 2 (p - 2)
-- sqrtMinusOneMod computes sqrt(-1) mod p
def sqrtMinusOneMod (p : Nat) : Nat :=
  let a := findQuadraticNonResidue p
  modPow a ((p - 1) / 4) p

-- Algorithm D2: Represent prime p as a² + b² using GCD in ℤ[i]
def repPrime (p : Nat) (t : Nat) : SqPair :=
  let pGi : GaussianInt := ⟨↑p, 0⟩
  let zGi : GaussianInt := ⟨↑t, 1⟩
  let g := GaussianInt.gcd pGi zGi
  (g.re, g.im)

-- Algorithm D3: Lift base representation (a, b) of p to p^e
def powerOfGaussian (a b : Int) (e : Nat) : SqPair :=
  let z      : GaussianInt := ⟨a, b⟩
  let result : GaussianInt := GaussianInt.fastPow z e
  (result.re, result.im)

-- Algorithm D: Combine D1, D2, D3 to compute (a, b) with a² + b² = p^e for p ≡ 1 (mod 4)
def powerOfOneMod4 (p e : Nat) : SqPair :=
  let t              := sqrtMinusOneMod p
  let (baseA, baseB) := repPrime p t
  powerOfGaussian baseA baseB e

-- Algorithm E: Combine two representations using Brahmagupta-Fibonacci identity
def combine (x y : SqPair) : SqPair :=
  let (a, b) := x
  let (c, d) := y
  (a * c - b * d,  a * d + b * c)
-- primeFactorization returns (prime, exponent) pairs for n
def primeFactorization (n : Nat) : List (Nat × Nat) :=
  let flat   := factorsList n
  let primes := sortedDedup flat
  primes.map fun p => (p, countOccurrences p flat)

-- reprPrimePower computes (a, b) for p^e
def reprPrimePower (p e : Nat) : SqPair :=
  if p == 2 then
    powerOfTwo e
  else if p % 4 == 3 then
    powerOfThreeMod4 p e
  else
    powerOfOneMod4 p e

-- Main: Find (x, y) with x² + y² = n using Algorithms A-E, or return none
def findSumOfTwoSquares (n : Nat) : Option SqPair :=
  if n == 0 then some (0, 0)
  else if ¬ isSolvable n then none
  else
    let factors := primeFactorization n
    let reps := factors.map fun (p, e) => reprPrimePower p e
    let result := reps.foldl combine (1, 0)
    some result

-- Verify that the pair (x, y) satisfies x² + y² = n
def verifySqPair (n : Nat) (pair : SqPair) : Bool :=
  let (x, y) := pair
  x * x + y * y == (n : Int)

-- showResult is a helper function to display the result of findSumOfTwoSquares in a readable format
def showResult (n : Nat) : String :=
  match findSumOfTwoSquares n with
  | none        => s!"{n} is NOT a sum of two squares."
  | some (x, y) =>
    let valid := verifySqPair n (x, y)
    s!"{n} = {x}² + {y}²   (verified: {valid})"

#eval showResult 65
#eval showResult 2
#eval showResult 25
#eval showResult 3
#eval showResult 50
#eval showResult 28
#eval showResult 10001
#eval showResult 1
#eval showResult 0
#eval (List.range 31).map fun n => (n, showResult n)
