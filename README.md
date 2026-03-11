# EE598 Final Project — Sum of Two Squares in Lean 4

## Goal

This project formalizes a **constructive algorithm** for the classical *sum of two squares* problem in Lean 4: given a natural number $n$, either produce integers $x, y$ satisfying $x^2 + y^2 = n$, or certify that no such representation exists.

The implementation follows Fermat's theorem: a positive integer $n$ is a sum of two squares if and only if every prime factor $p \equiv 3 \pmod{4}$ appears to an even power in the prime factorization of $n$. The constructive direction is realized through a pipeline that

1. trial-divides $n$ to obtain its prime factorization,
2. checks solvability via the mod-4 criterion,
3. represents each prime power $p^e$ as a sum of two squares using Gaussian-integer GCD (for $p \equiv 1 \pmod 4$) or elementary formulas (for $p = 2$ and $p \equiv 3 \pmod 4$),
4. combines representations with the Brahmagupta–Fibonacci identity.

Correctness is verified in Lean: a **soundness theorem** states that whenever the algorithm returns a pair $(x, y)$, the equation $x^2 + y^2 = n$ holds; a **completeness theorem** ties the solvability check to Mathlib's `padicValNat` criterion.

---

## Project Structure

```
EE598_Project/EE598Project/
├── GaussianInt.lean       -- ℤ[i] arithmetic (ring operations, GCD, fast power)
├── SumOfTwoSquares.lean   -- main algorithm (factorization → representation → combination)
├── Proof.lean             -- formal correctness proofs
└── Basic.lean             -- top-level re-export
```

---

## Main Definitions

### `GaussianInt.lean`

| Name | Description |
|------|-------------|
| `GaussianInt` | Structure `{ re im : ℤ }` representing a Gaussian integer $a + bi$. Instances are provided for `Zero`, `One`, `Add`, `Sub`, `Neg`, `Mul`, `HPow`. |
| `GaussianInt.norm` | The Gaussian norm $N(a+bi) = a^2 + b^2 : \mathbb{Z}$. Multiplicative: $N(zw) = N(z)N(w)$. |
| `GaussianInt.conj` | Complex conjugate $\overline{a+bi} = a - bi$. Used in the division formula. |
| `GaussianInt.roundNearest` | Rounds the integer ratio $a/b$ to the nearest integer via $\lfloor(2a+b)/(2b)\rfloor$. Guarantees the rounding error is at most $1/2$. |
| `GaussianInt.gaussianDiv` | Euclidean quotient in $\mathbb{Z}[i]$: divides $a$ by $b$ by multiplying by $\bar{b}$, dividing by $N(b)$, and rounding each component. |
| `GaussianInt.gaussianMod` | Euclidean remainder: $a \bmod b = a - \lfloor a/b \rceil \cdot b$. The norm of the remainder is strictly less than the norm of $b$. |
| `GaussianInt.gcd` | Euclidean GCD in $\mathbb{Z}[i]$ by repeated remainder. Terminates because `norm` is a strict descent measure. |
| `GaussianInt.fastPow` | Binary (square-and-multiply) exponentiation $z^n$ in $O(\log n)$ multiplications. |

### `SumOfTwoSquares.lean`

| Name | Description |
|------|-------------|
| `SqPair` | Type alias `ℤ × ℤ` for a pair of integers representing a sum-of-two-squares decomposition. |
| `modPow a b m` | Computes $a^b \bmod m$ by binary exponentiation, used to find square roots mod $p$. |
| `factorsList n` | Returns the prime factorization of $n$ as a flat list with repetition (e.g., `12 → [2,2,3]`). Uses trial division with a fuel bound for termination. |
| `sortedDedup` | Removes consecutive duplicates from a sorted list; used to enumerate distinct prime factors. |
| `countOccurrences p lst` | Counts how many times `p` appears in `lst`; equals `padicValNat p n` when `lst = factorsList n`. |
| `isSolvable n` | Returns `true` iff $n$ passes Fermat's mod-4 criterion: no prime $p \equiv 3 \pmod 4$ divides $n$ to an odd power. |
| `powerOfTwo e` | Computes $(a,b)$ with $a^2+b^2 = 2^e$ by the recurrence $(a_{e+1},b_{e+1}) = (a_e - b_e,\, a_e + b_e)$. |
| `powerOfThreeMod4 p e` | Computes $(p^{e/2},\, 0)$ for prime $p \equiv 3 \pmod 4$ with $e$ even. Valid because $p^{e/2}$ squares to $p^e$ and the imaginary part is $0$. |
| `findQuadraticNonResidue p` | Finds a generator $a$ such that $a^{(p-1)/2} \equiv -1 \pmod p$ by brute-force search starting from $2$. |
| `sqrtMinusOneMod p` | Computes $t$ with $t^2 \equiv -1 \pmod p$ for prime $p \equiv 1 \pmod 4$ using the formula $t = a^{(p-1)/4} \bmod p$. |
| `repPrime p t` | Represents prime $p \equiv 1 \pmod 4$ as $a^2 + b^2$ by computing $\gcd_{\mathbb{Z}[i]}(p,\, t+i)$ and returning its real and imaginary parts. |
| `powerOfGaussian a b e` | Lifts a base representation $(a,b)$ of $p$ to one of $p^e$ by computing $(a+bi)^e$ in $\mathbb{Z}[i]$ via `fastPow`. |
| `powerOfOneMod4 p e` | Combines `sqrtMinusOneMod`, `repPrime`, and `powerOfGaussian` to produce $(a,b)$ with $a^2+b^2 = p^e$ for $p \equiv 1 \pmod 4$. |
| `combine x y` | Brahmagupta–Fibonacci identity: `combine (a,b) (c,d) = (ac−bd, ad+bc)`, satisfying $N(\text{combine}(x,y)) = N(x) \cdot N(y)$. |
| `reprPrimePower p e` | Dispatches to `powerOfTwo`, `powerOfThreeMod4`, or `powerOfOneMod4` based on the residue of $p$ mod $4$. |
| `findSumOfTwoSquares n` | **Main entry point.** Returns `some (x, y)` with $x^2+y^2 = n$ if solvable, `none` otherwise. |
| `verifySqPair n pair` | Checks $x^2 + y^2 = n$ computationally; used for sanity-checking `#eval` output. |

### `Proof.lean`

| Name | Description |
|------|-------------|
| `sqPairNorm p` | Norm of a `SqPair`: $p.1^2 + p.2^2 : \mathbb{Z}$. Mirrors `GaussianInt.norm` for the proof side. |

---

## Main Theorems

| Name | Statement | Status |
|------|-----------|--------|
| `combine_norm` | `sqPairNorm (combine (a,b) (c,d)) = sqPairNorm (a,b) * sqPairNorm (c,d)` — the Brahmagupta–Fibonacci identity. | Proved |
| `foldl_combine_norm` | The norm of a left-fold by `combine` equals the product of the individual norms: `sqPairNorm (l.foldl combine acc) = sqPairNorm acc * (l.map sqPairNorm).prod`. | Proved |
| `powerOfTwo_norm` | `sqPairNorm (powerOfTwo e) = 2 ^ e` for all `e : ℕ`. | Proved (by induction) |
| `powerOfThreeMod4_norm` | `sqPairNorm (powerOfThreeMod4 p e) = p ^ e` whenever `e % 2 = 0`. | Proved |
| `powerOfOneMod4_norm` | `sqPairNorm (powerOfOneMod4 p e) = p ^ e` for prime $p \equiv 1 \pmod 4$. | `sorry` — depends on GCD correctness |
| `reprPrimePower_norm` | `sqPairNorm (reprPrimePower p e) = p ^ e` for any prime $p$ and exponent $e$. | `sorry` — awaits `powerOfOneMod4_norm` |
| `primeFactorization_prod` | The product $\prod_{(p,e)} p^e$ over `primeFactorization n` equals $n$ in $\mathbb{Z}$. | `sorry` — requires trial-division correctness |
| `findSumOfTwoSquares_sound` | **Soundness.** If `findSumOfTwoSquares n = some (x, y)`, then $x \cdot x + y \cdot y = n$. | **Proved** (modulo the three `sorry`s above) |
| `countOccurrences_eq_count` | `countOccurrences p l = l.count p` — bridging the custom counter to Lean's `List.count`. | Proved |
| `mem_sortedDedup_iff` | `p ∈ sortedDedup l ↔ p ∈ l` — membership is preserved by deduplication. | Proved |
| `isSolvable_iff_padicVal` | `isSolvable n = true ↔ ∀ q prime, q % 4 = 3 → Even (padicValNat q n)`. | `sorry` — requires `factorsList` ↔ `padicValNat` |
| `findSumOfTwoSquares_complete` | **Completeness.** `isSolvable n = true ↔ ∃ x y : ℤ, x*x + y*y = n`. | Proved (conditional on `isSolvable_iff_padicVal` and the Mathlib axiom) |

> **Note on axioms.** The Mathlib theorem `Nat.Prime.sq_add_sq` (characterization via `padicValNat`) is axiomatized as `Nat.eq_sq_add_sq_iff'` because importing `Mathlib.NumberTheory.Zsqrtd.GaussianInt` would conflict with our custom `GaussianInt` structure.

---

## References

1. **Fermat's theorem on sums of two squares** — Any prime $p \equiv 1 \pmod 4$ (and $p = 2$) is a sum of two squares; a positive integer is a sum of two squares iff all prime factors $p \equiv 3 \pmod 4$ appear with even exponent.
   *C.-F. Gauss, Disquisitiones Arithmeticae, 1801.*

2. **Brahmagupta–Fibonacci identity** — $(a^2+b^2)(c^2+d^2) = (ac-bd)^2 + (ad+bc)^2$.
   *Brahmagupta, Brahmasphutasiddhanta, 628 CE; Fibonacci, Liber Quadratorum, 1225.*

3. **Gaussian integers and Euclidean domains** — $\mathbb{Z}[i]$ is a Euclidean domain with norm $N(a+bi) = a^2+b^2$; the GCD algorithm terminates because the norm strictly decreases.
   *I. Niven, H. S. Zuckerman, H. L. Montgomery, An Introduction to the Theory of Numbers, 5th ed., Wiley, 1991.*

4. **Square roots of $-1$ modulo $p$** — For prime $p \equiv 1 \pmod 4$, any quadratic non-residue $a$ satisfies $a^{(p-1)/4} \equiv \pm i \pmod p$.
   *H. Cohen, A Course in Computational Algebraic Number Theory, Springer, 1993.*

5. **Lean 4 and Mathlib** — The `Mathlib.NumberTheory.SumTwoSquares` module contains a machine-checked proof of Fermat's theorem. Our project uses the `padicValNat` characterization from that module as an axiom.
   *The Mathlib Community, Mathlib4, https://leanprover-community.github.io/mathlib4_docs/.*

6. **Lean 4 language reference** — *L. de Moura, S. Ullrich, The Lean 4 Theorem Prover and Programming Language, CADE 2021.*

---

## Future Work

- **Complete the `sorry`d proofs.**
  - Prove `powerOfOneMod4_norm` by showing that the Gaussian GCD of $(p, t+i)$ yields a generator of norm $p$, then that `fastPow` raises the norm correctly.
  - Prove `primeFactorization_prod` by connecting the trial-division `factorsList` to Mathlib's `Nat.factors` or `Nat.factorization`.
  - Prove `isSolvable_iff_padicVal` by the `countOccurrences_eq_count` bridge lemma already established.

- **Remove the axiom.** Replace the axiomatized `Nat.eq_sq_add_sq_iff'` with a direct import or re-statement that avoids the `Zsqrtd.GaussianInt` namespace clash, e.g., by renaming our structure.

- **Formal `GaussianInt` ring instance.** Register `GaussianInt` as a `CommRing` (and ultimately a `EuclideanDomain`) in Mathlib's type-class hierarchy, enabling full algebraic reasoning.

- **Certified `factorsList`.** Prove that `factorsList n` returns exactly the prime factors of $n$ with the correct multiplicities, making all downstream arithmetic proofs unconditional.

- **Lean tactic.** Expose `findSumOfTwoSquares` as a decision procedure inside a `decide`-style tactic, so goals of the form `∃ x y, x^2 + y^2 = n` can be closed automatically for concrete $n$.

- **Generalization.** Extend the framework to related Diophantine families, such as sums of three or four squares (Legendre/Lagrange theorems), or norms in other quadratic rings $\mathbb{Z}[\sqrt{-d}]$.

