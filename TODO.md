Phase 1 — Infrastructure
- Set up Lean project structure and GitHub repo

- Add basic number‑theory utilities (integer sqrt, divisors, etc.)

- Implement a simple isSumOfTwoSquares : Int → Bool using the mod‑4 condition

Phase 2 — Gaussian Integer Arithmetic
- Define Gaussian integers ℤ[i] as a structure

- Implement addition, multiplication, and norm

- Implement Euclidean division in ℤ[i]

- Implement gaussianGCD : ℤ[i] → ℤ[i] → ℤ[i]

- Prove correctness of the Gaussian GCD

Phase 3 — Prime Representation
- Implement algorithm to find a,b such that p = a^2 + b^2 for primes p ≡ 1 mod 4

- Handle p = 2

- Handle p ≡ 3 mod 4 with even exponent

Phase 4 — Combine Representations
- Implement the sum‑of‑two‑squares identity

- Fold prime‑power representations into a representation of n

- Prove correctness

Phase 5 — Tactic
- Implement a tactic sos that solves goals of the form ∃ x y, x^2 + y^2 = n

- Add pretty‑printing of solutions

- Add tests in Test/

Phase 6 — Extensions (optional)
- Support ax^2 + by^2 = c via scaling

- Explore quadratic forms and norm equations

- Benchmark and document tactic performance
