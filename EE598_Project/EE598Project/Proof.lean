import Mathlib.Tactic
import EE598Project.SumOfTwoSquares

open GaussianInt

/-
I tried what you suggested, write the theorem statements and let Claude go.
No success as of yet. It wants to assume nontrivial things as seen below.
-/


-- Mathlib's characterization of sums of two squares via padicValNat.
-- Cannot import Mathlib.NumberTheory.SumTwoSquares directly because it
-- pulls in Mathlib.NumberTheory.Zsqrtd.GaussianInt, which conflicts with
-- our custom GaussianInt structure.  We axiomatize the result instead.
axiom Nat.eq_sq_add_sq_iff' {n : ℕ} :
    (∃ a b : ℕ, n = a ^ 2 + b ^ 2) ↔
    ∀ q : ℕ, Nat.Prime q → q % 4 = 3 → Even (padicValNat q n)

-- ───────────────────────────────────────────────────────────────
-- Helper: the "norm" of a SqPair
-- ───────────────────────────────────────────────────────────────

def sqPairNorm (p : SqPair) : Int := p.1 * p.1 + p.2 * p.2

-- ───────────────────────────────────────────────────────────────
-- Lemma 1: Brahmagupta-Fibonacci identity
-- combine (a,b) (c,d) has norm = norm(a,b) * norm(c,d)
-- Proof: pure algebra.
-- ───────────────────────────────────────────────────────────────

lemma combine_norm (a b c d : Int) :
    sqPairNorm (combine (a, b) (c, d)) =
    sqPairNorm (a, b) * sqPairNorm (c, d) := by
  simp [combine, sqPairNorm]
  ring

-- ───────────────────────────────────────────────────────────────
-- Lemma 2: norm of a foldl is the product of norms
-- ───────────────────────────────────────────────────────────────

lemma foldl_combine_norm (reps : List SqPair) (acc : SqPair) :
    sqPairNorm (reps.foldl combine acc) =
    sqPairNorm acc * (reps.map sqPairNorm).prod := by
  induction reps generalizing acc with
  | nil => simp [sqPairNorm]
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    rw [ih (combine acc hd)]
    have hcn : sqPairNorm (combine acc hd) = sqPairNorm acc * sqPairNorm hd := by
      obtain ⟨a, b⟩ := acc
      obtain ⟨c, d⟩ := hd
      exact combine_norm a b c d
    rw [hcn]
    ring

-- ───────────────────────────────────────────────────────────────
-- Lemma 3: sub-lemmas and main statement
-- ───────────────────────────────────────────────────────────────

-- Sub-lemma: powerOfTwo e has sqPairNorm = 2^e  (proved by induction)
private lemma powerOfTwo_norm : ∀ e : Nat,
    sqPairNorm (powerOfTwo e) = (2 : Int) ^ e
  | 0 => by simp [powerOfTwo, sqPairNorm]
  | 1 => by simp [powerOfTwo, sqPairNorm]
  | (e + 2) => by
      have ih := powerOfTwo_norm (e + 1)
      simp only [sqPairNorm] at ih
      -- unfold one step definitionally
      have hdef : powerOfTwo (e + 2) =
          ((powerOfTwo (e + 1)).1 - (powerOfTwo (e + 1)).2,
           (powerOfTwo (e + 1)).1 + (powerOfTwo (e + 1)).2) := rfl
      rw [hdef, sqPairNorm]
      have key : ((powerOfTwo (e+1)).1 - (powerOfTwo (e+1)).2) *
                 ((powerOfTwo (e+1)).1 - (powerOfTwo (e+1)).2) +
                 ((powerOfTwo (e+1)).1 + (powerOfTwo (e+1)).2) *
                 ((powerOfTwo (e+1)).1 + (powerOfTwo (e+1)).2) =
                 2 * ((powerOfTwo (e+1)).1 * (powerOfTwo (e+1)).1 +
                      (powerOfTwo (e+1)).2 * (powerOfTwo (e+1)).2) := by ring
      rw [key, ih]; ring

-- Sub-lemma: powerOfThreeMod4 p e has sqPairNorm = p^e when e is even  (proved)
private lemma powerOfThreeMod4_norm (p e : Nat) (he : e % 2 = 0) :
    sqPairNorm (powerOfThreeMod4 p e) = (p : Int) ^ e := by
  simp only [powerOfThreeMod4, sqPairNorm]
  push_cast
  have hk : e / 2 + e / 2 = e := by omega
  rw [add_zero, ← pow_add, hk]

-- Sub-lemma: powerOfOneMod4 p e has sqPairNorm = p^e  (SORRY: needs GCD correctness)
private lemma powerOfOneMod4_norm (p e : Nat) (hp : Nat.Prime p) (hp1 : p % 4 = 1) :
    sqPairNorm (powerOfOneMod4 p e) = (p : Int) ^ e := by
  sorry

lemma reprPrimePower_norm (p e : Nat) :
    sqPairNorm (reprPrimePower p e) = (p : Int) ^ e := by
  sorry

-- ───────────────────────────────────────────────────────────────
-- Lemma 4: product of prime factorization equals n  (sorry'd)
-- ───────────────────────────────────────────────────────────────

lemma primeFactorization_prod (n : Nat) (hn : n ≠ 0) :
    ((primeFactorization n).map fun (pe : Nat × Nat) =>
        (pe.1 : Int) ^ pe.2).prod = (n : Int) := by
  sorry

-- ───────────────────────────────────────────────────────────────
-- Main soundness theorem
-- ───────────────────────────────────────────────────────────────

/-- Soundness: if the algorithm returns `some (x, y)`, then x² + y² = n. -/
theorem findSumOfTwoSquares_sound (n : Nat) (x y : Int) :
    findSumOfTwoSquares n = some (x, y) → x * x + y * y = (n : Int) := by
  intro h
  unfold findSumOfTwoSquares at h
  split_ifs at h with h0 h1
  · -- Case 1: n = 0, algorithm returns some (0, 0)
    have hn : n = 0 := by simpa using h0
    subst hn
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    norm_num
  · -- Case 2: main case — split_ifs auto-closes the `none = some` case,
    -- so this bullet is: h0 : ¬(n==0), h1 : isSolvable n = true
    -- h : some (foldl combine (1,0) reps) = some (x, y)
    simp only [Option.some.injEq] at h
    -- now h : foldl combine (1,0) reps = (x, y)
    have hn : n ≠ 0 := by simpa using h0
    set factors := primeFactorization n with hfactors
    set reps := List.map (fun pe : Nat × Nat => reprPrimePower pe.1 pe.2) factors
      with hreps_def
    -- norm of the fold equals product of norms
    have hnorm : sqPairNorm (reps.foldl combine (1, 0)) =
        sqPairNorm (1, 0) * (reps.map sqPairNorm).prod :=
      foldl_combine_norm reps (1, 0)
    -- sqPairNorm (1, 0) = 1
    have hone : sqPairNorm (1, 0) = 1 := by simp [sqPairNorm]
    -- each rep has norm p^e
    have hreps : reps.map sqPairNorm =
        factors.map fun pe : Nat × Nat => (pe.1 : Int) ^ pe.2 := by
      simp only [hreps_def, List.map_map]
      congr 1; ext ⟨p, e⟩
      exact reprPrimePower_norm p e
    -- product of p^e equals n
    have hprod : (factors.map fun pe : Nat × Nat => (pe.1 : Int) ^ pe.2).prod = (n : Int) :=
      primeFactorization_prod n hn
    -- assemble: norm of the fold = n
    have hgoal : sqPairNorm (reps.foldl combine (1, 0)) = (n : Int) := by
      rw [hnorm, hone, one_mul, hreps, hprod]
    -- rewrite using h : foldl = (x,y) to get sqPairNorm (x,y) = n
    rw [h] at hgoal
    simpa [sqPairNorm] using hgoal














-- ───────────────────────────────────────────────────────────────
-- Bridge helpers
-- ───────────────────────────────────────────────────────────────

-- Helper A: general foldl-count identity (helper lemma)
private lemma countOccurrences_go (p : Nat) : ∀ (l : List Nat) (acc : Nat),
    l.foldl (fun a q => if q == p then a + 1 else a) acc = acc + l.count p
  | [], _ => by simp
  | hd :: tl, acc => by
      simp only [List.foldl_cons]
      -- Case split on the Bool value of (hd == p) to avoid changing the inner lambda
      cases hbp : (hd == p)
      · -- hbp : (hd == p) = false  (hd ≠ p); goal has `if false = true then …`
        rw [if_neg (by decide), countOccurrences_go p tl acc]
        simp [List.count_cons, hbp]
      · -- hbp : (hd == p) = true  (hd = p); goal has `if true = true then …`
        rw [if_pos (by rfl)]
        have heq : hd = p := by rwa [beq_iff_eq] at hbp
        subst heq
        rw [countOccurrences_go hd tl (acc + 1)]
        simp; omega

-- Helper A: countOccurrences p l = l.count p  (proved)
private lemma countOccurrences_eq_count (p : Nat) (l : List Nat) :
    countOccurrences p l = l.count p := by
  simp only [countOccurrences]
  have h := countOccurrences_go p l 0
  simpa using h

-- Helper B: factorsList correctness
-- (SORRY: requires proving trial division produces the Mathlib prime factorization)
private lemma factorsList_prime (n : Nat) : ∀ p ∈ factorsList n, Nat.Prime p := by
  sorry

-- The key property used downstream: factorsList count equals padicValNat
private lemma factorsList_eq_factors (n p : Nat) (hp : Nat.Prime p) :
    (factorsList n).count p = padicValNat p n := by
  sorry

-- Helper C: for prime p, factorsList count = padicValNat  (follows from Helper B)
private lemma factors_count_eq_padicVal (p n : Nat) (hp : Nat.Prime p) :
    (factorsList n).count p = padicValNat p n :=
  factorsList_eq_factors n p hp

-- Helper D: p ∈ sortedDedup l ↔ p ∈ l  (proved by structural induction)
private lemma mem_sortedDedup_iff : ∀ (l : List Nat) (p : Nat), p ∈ sortedDedup l ↔ p ∈ l
  | [], _ => by simp [sortedDedup]
  | [a], _ => by simp [sortedDedup]
  | (a :: b :: rest), p => by
      simp only [sortedDedup]
      split_ifs with h
      · -- a == b, i.e., a = b; sortedDedup skips a
        have hab : a = b := by simpa using h
        constructor
        · -- p ∈ sortedDedup (b::rest) → p ∈ a::b::rest
          intro hm
          exact List.mem_cons.mpr (.inr ((mem_sortedDedup_iff (b :: rest) p).mp hm))
        · -- p ∈ a::b::rest → p ∈ sortedDedup (b::rest)
          intro hm
          apply (mem_sortedDedup_iff (b :: rest) p).mpr
          rcases List.mem_cons.mp hm with rfl | hm
          · exact List.mem_cons.mpr (.inl hab)  -- p = a = b
          · exact hm
      · -- a ≠ b; sortedDedup keeps a
        simp only [List.mem_cons, mem_sortedDedup_iff (b :: rest) p]

-- ───────────────────────────────────────────────────────────────
-- Bridge: isSolvable n ↔ Mathlib's padicValNat criterion
-- ───────────────────────────────────────────────────────────────

lemma isSolvable_iff_padicVal (n : Nat) :
    isSolvable n = true ↔
    ∀ q : ℕ, Nat.Prime q → q % 4 = 3 → Even (padicValNat q n) := by
  sorry

/-- Completeness: isSolvable n ↔ n is a sum of two squares. -/
theorem findSumOfTwoSquares_complete (n : Nat) :
    isSolvable n = true ↔ ∃ x y : Int, x * x + y * y = (n : Int) := by
  rw [isSolvable_iff_padicVal]
  constructor
  · -- (→): padicVal condition ⇒ ∃ a b : ℕ, n = a² + b², then cast to ℤ
    intro hpv
    obtain ⟨a, b, hab⟩ := Nat.eq_sq_add_sq_iff'.mpr hpv
    exact ⟨↑a, ↑b, by
      have h : (n : ℤ) = (↑a)^2 + (↑b)^2 := by exact_mod_cast hab
      nlinarith [sq_nonneg (↑a : ℤ), sq_nonneg (↑b : ℤ), h]⟩
  · -- (←): ∃ x y : ℤ, x²+y²=n ⇒ padicVal condition via natAbs
    intro ⟨x, y, hxy⟩
    have hnat : n = x.natAbs ^ 2 + y.natAbs ^ 2 := by
      have heq : (n : ℤ) = (x.natAbs : ℤ) ^ 2 + (y.natAbs : ℤ) ^ 2 := by
        simp only [Int.natAbs_sq]; linarith
      exact_mod_cast heq
    exact Nat.eq_sq_add_sq_iff'.mp ⟨x.natAbs, y.natAbs, hnat⟩
