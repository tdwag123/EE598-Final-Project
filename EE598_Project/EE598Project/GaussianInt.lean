import Mathlib.Tactic

import Mathlib.Tactic

/-- A Gaussian integer `re + im * I` where `re im : ℤ`. -/
structure GaussianInt where
  re : Int
  im : Int
  deriving Repr, DecidableEq

namespace GaussianInt

instance : Zero GaussianInt := ⟨⟨0, 0⟩⟩
instance : One  GaussianInt := ⟨⟨1, 0⟩⟩

/-- Embed an integer into `ℤ[i]`. -/
def ofInt (n : Int) : GaussianInt := ⟨n, 0⟩

instance : ToString GaussianInt where
  toString z :=
    if z.im == 0      then s!"{z.re}"
    else if z.im == 1 then s!"{z.re} + i"
    else if z.im > 0  then s!"{z.re} + {z.im}i"
    else if z.im == -1 then s!"{z.re} - i"
    else s!"{z.re} - {(-z.im)}i"

instance : Add GaussianInt := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Neg GaussianInt := ⟨fun z   => ⟨-z.re, -z.im⟩⟩
instance : Sub GaussianInt := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩

instance : Mul GaussianInt := ⟨fun z w =>
  ⟨z.re * w.re - z.im * w.im,
   z.re * w.im + z.im * w.re⟩⟩

/-- Complex conjugate in `ℤ[i]`. -/
def conj (z : GaussianInt) : GaussianInt := ⟨z.re, -z.im⟩
/-- Gaussian norm `a² + b²`. -/
def norm (z : GaussianInt) : Int := z.re * z.re + z.im * z.im
/-- Gaussian norm as a natural number. -/
def normNat (z : GaussianInt) : Nat := (norm z).toNat

/-- Round `a/b` to the nearest integer (half-up). -/
def roundNearest (a b : Int) : Int :=
  Int.ediv (2 * a + b) (2 * b)

/-- Divide a by b in ℤ[i], rounding to nearest integer. -/
def gaussianDiv (a b : GaussianInt) : GaussianInt :=
  let num := a * b.conj
  let den := b.norm
  ⟨roundNearest num.re den, roundNearest num.im den⟩

/-- Euclidean remainder in `ℤ[i]`. -/
def gaussianMod (a b : GaussianInt) : GaussianInt :=
  let q := gaussianDiv a b
  a - q * b

/-- Euclidean GCD in `ℤ[i]`. -/
partial def gcd (a b : GaussianInt) : GaussianInt :=
  if b == 0 then a
  else gcd b (gaussianMod a b)

/-- Tail-recursive helper for binary exponentiation. -/
private def fastPowAux (z : GaussianInt) (n : Nat) (acc : GaussianInt) : GaussianInt :=
  if hn : n = 0 then acc
  else
    let acc' := if n % 2 == 1 then acc * z else acc
    fastPowAux (z * z) (n / 2) acc'
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by norm_num)

/-- Compute `z^n` in `ℤ[i]`. -/
def fastPow (z : GaussianInt) (n : Nat) : GaussianInt :=
  fastPowAux z n 1

instance : HPow GaussianInt Nat GaussianInt := ⟨fastPow⟩

end GaussianInt
