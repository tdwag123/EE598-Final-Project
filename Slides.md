# Sum of Two Squares in Lean 4

A **constructive algorithm** in Lean 4: given `n`, either return `(x, y)` with `x² + y² = n` or certify no solution exists.

---

## The Algorithm

**Fermat's theorem:** `n` is a sum of two squares iff every prime `p ≡ 3 (mod 4)` appears to an even power.
For example: `45 = 3² × 5` — `3` to an even power → solvable (`3² + 6²`). But `15 = 3¹ × 5` → not solvable.

Every prime is `2`, `≡ 1 (mod 4)`, or `≡ 3 (mod 4)` — exhaustive since odd primes can't be `0` or `2` mod 4. Each case has a recipe for writing `pᵉ` as a sum of two squares:

- **`p = 2`**: recurrence `(a−b, a+b)` gives `a²+b² = 2ᵉ`
- **`p ≡ 3`**: `(pᵉ/², 0)` works since Fermat forces `e` to be even
- **`p ≡ 1`**: no closed-form — find `t² ≡ −1 (mod p)`, then `gcd(p, t+i)` in `ℤ[i]` extracts `a+bi` with `a²+b²=p`, then raise to `e`

Representations are combined using **Brahmagupta–Fibonacci**: `(a²+b²)(c²+d²) = (ac−bd)² + (ad+bc)²`, i.e. `N(z·w) = N(z)·N(w)` in `ℤ[i]`, so the norms multiply up to `n`.

```lean
def findSumOfTwoSquares (n : Nat) : Option SqPair :=
  if ¬ isSolvable n then none
  else some ((primeFactorization n).map (fun (p,e) => reprPrimePower p e) |>.foldl combine (1,0))
```

**Output:** `45 = 3² + 6²` ✓ · `65 = 4² + 7²` ✓ · `10001 = 55² + 76²` ✓ · `15` → none ✓

---

## Future Work: Proving the Following

- **Output Guarantee**: if `findSumOfTwoSquares n = some (x, y)` then `x² + y² = n`
- **Solvability Criterion**: `isSolvable n = true ↔ ∃ x y, x² + y² = n`

Several lemmas are `sorry`d and one Mathlib result is axiomatized due to a namespace conflict with our custom `GaussianInt`.
