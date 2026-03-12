# Sum of Two Squares in Lean 4

A **constructive algorithm** in Lean 4: given `n`, either return `(x, y)` with `x² + y² = n` or certify no solution exists.

---

## The Algorithm

**Fermat's theorem:** `n` is a sum of two squares iff every prime `p ≡ 3 (mod 4)` appears to an even power.
For example: `45 = 3² × 5` — `3` to an even power → solvable (`3² + 6²`). But `15 = 3¹ × 5` → not solvable.

Every prime is `2`, `≡ 1 (mod 4)`, or `≡ 3 (mod 4)` — exhaustive since odd primes can't be `0` or `2` mod 4. Each case has a recipe for writing `pᵉ` as a sum of two squares:

- **`p = 2`**: start from `(1,0)` and repeatedly apply `(a,b) → (a−b, a+b)`, which doubles the norm each step:
  `(1,0), (1,1), (0,2), (−2,2), ...` with norms `2⁰=1, 2¹=2, 2²=4, 2³=8, ...`
- **`p ≡ 3`**: `isSolvable` already guarantees `e` is even — if it weren't, no solution exists and we return `none`. So write `e = 2k` and the representation is just `(pᵏ, 0)`, since `(pᵏ)² + 0² = p²ᵏ = pᵉ`.
- **`p ≡ 1`**: `p` factors in `ℤ[i]` as `p = (a+bi)(a−bi)`. To find `a` and `b`:
  1. **Find `t` with `t² ≡ −1 (mod p)`**, exists because `p ≡ 1 (mod 4)`. E.g. `p=5`: `2²=4≡−1`, so `t=2`.
  2. **GCD in `ℤ[i]`**: `p | (t+i)(t−i)` in `ℤ[i]`, but `p` divides neither factor alone, so `gcd(p, t+i)` extracts the shared factor `a+bi`. Its norm `a²+b² = p`. E.g. `gcd(5, 2+i) = 2+i`, and `2²+1²=5`
  3. **Raise to power `e`**: compute `(a+bi)ᵉ` in `ℤ[i]` via exponentiation, norm multiplicativity gives `N((a+bi)ᵉ) = pᵉ`.

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

Several lemmas are `sorry`d and one Mathlib result is axiomatized due to a namespace conflict with our custom `GaussianInt`. This proof work has been done with help from Claude.
