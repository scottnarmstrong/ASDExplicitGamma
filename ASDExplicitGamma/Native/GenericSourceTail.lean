module

public import ASDExplicitGamma.Native.GenericSourceMeans

/-! Complete the generic source's weak-tail charge. The growth estimate and tail allocation bound
the entire post-prefix history by a quadratic-exponential profile; this file
proves the exact polynomial-geometric majorant used for that charge. -/
@[expose] public section

namespace ASDExplicitGamma.Native

theorem native_source_geom_quadratic_summable :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 2 * (9 / 10 : ℝ) ^ k) := by
  have h0 : Summable (fun k : ℕ => (9 / 10 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h1 : Summable (fun k : ℕ => (k : ℝ) * (9 / 10 : ℝ) ^ k) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one 1
      (by norm_num : ‖(9 / 10 : ℝ)‖ < 1))
  have h2 : Summable (fun k : ℕ => (k : ℝ) ^ 2 * (9 / 10 : ℝ) ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one 2
      (by norm_num : ‖(9 / 10 : ℝ)‖ < 1)
  have hsum : Summable (fun k : ℕ =>
      (9 / 10 : ℝ) ^ k + 2 * ((k : ℝ) * (9 / 10 : ℝ) ^ k) +
        (k : ℝ) ^ 2 * (9 / 10 : ℝ) ^ k) :=
    (h0.add (h1.mul_left 2)).add h2
  have heq : (fun k : ℕ => ((k : ℝ) + 1) ^ 2 * (9 / 10 : ℝ) ^ k) =
      (fun k : ℕ => (9 / 10 : ℝ) ^ k +
        2 * ((k : ℝ) * (9 / 10 : ℝ) ^ k) +
        (k : ℝ) ^ 2 * (9 / 10 : ℝ) ^ k) := by
    funext k
    ring
  rw [heq]
  exact hsum

private theorem native_source_geom_quadratic_sum :
    ∑' k : ℕ, ((k : ℝ) + 1) ^ 2 * (9 / 10 : ℝ) ^ k = 1900 := by
  have h0 : Summable (fun k : ℕ => (9 / 10 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h1 : Summable (fun k : ℕ => (k : ℝ) * (9 / 10 : ℝ) ^ k) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one 1
      (by norm_num : ‖(9 / 10 : ℝ)‖ < 1))
  have h2 : Summable (fun k : ℕ => (k : ℝ) ^ 2 * (9 / 10 : ℝ) ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one 2
      (by norm_num : ‖(9 / 10 : ℝ)‖ < 1)
  have hsum : Summable (fun k : ℕ =>
      (9 / 10 : ℝ) ^ k + 2 * ((k : ℝ) * (9 / 10 : ℝ) ^ k) +
        (k : ℝ) ^ 2 * (9 / 10 : ℝ) ^ k) :=
    (h0.add (h1.mul_left 2)).add h2
  calc
    _ = ∑' k : ℕ, ((9 / 10 : ℝ) ^ k +
        2 * ((k : ℝ) * (9 / 10 : ℝ) ^ k) +
        (k : ℝ) ^ 2 * (9 / 10 : ℝ) ^ k) := by
      apply tsum_congr
      intro k
      ring
    _ = (∑' k : ℕ, (9 / 10 : ℝ) ^ k) +
        (∑' k : ℕ, 2 * ((k : ℝ) * (9 / 10 : ℝ) ^ k)) +
        (∑' k : ℕ, (k : ℝ) ^ 2 * (9 / 10 : ℝ) ^ k) := by
      rw [(h0.add (h1.mul_left 2)).tsum_add h2, h0.tsum_add (h1.mul_left 2)]
    _ = 1900 := by
      rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num), tsum_mul_left,
        tsum_coe_mul_geometric_of_norm_lt_one (by norm_num),
        tsum_sq_mul_geometric_of_norm_lt_one (by norm_num)]
      norm_num

/-- The full post-`N` quadratic geometric tail used in the raw-frame
comparison is bounded by its retained outward coefficient. -/
theorem native_source_polynomial_tail_le (N : ℕ) :
    ∑' k : ℕ, ((N + 2 + k : ℕ) : ℝ) ^ 2 *
        (9 / 10 : ℝ) ^ (N + 1 + k) ≤
      ((N + 2 : ℕ) : ℝ) ^ 4 * (9 / 10 : ℝ) ^ (N + 1) *
        (((Nat.factorial 4 : ℕ) : ℝ) * 10 ^ 5) := by
  let n : ℝ := ((N + 2 : ℕ) : ℝ)
  let q : ℝ := 9 / 10
  have hn2 : 4 ≤ n ^ 2 := by
    have hnNat : 2 ≤ N + 2 := by omega
    have hn : (2 : ℝ) ≤ n := by
      dsimp [n]
      exact_mod_cast hnNat
    nlinarith [sq_nonneg (n - 2)]
  have hpolyTerm (k : ℕ) :
      ((N + 2 + k : ℕ) : ℝ) ^ 2 * q ^ k ≤
        n ^ 2 * (((k : ℝ) + 1) ^ 2 * q ^ k) := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hlin : ((N + 2 + k : ℕ) : ℝ) ≤ n * ((k : ℝ) + 1) := by
      dsimp [n]
      norm_cast
      have hprod : 0 ≤ ((N : ℝ) + 1) * (k : ℝ) :=
        mul_nonneg (by positivity) (Nat.cast_nonneg k)
      nlinarith [hprod]
    have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
      ((N + 2 + k : ℕ) : ℝ)) hlin 2
    calc
      _ ≤ (n * ((k : ℝ) + 1)) ^ 2 * q ^ k :=
        mul_le_mul_of_nonneg_right hsq (pow_nonneg (by norm_num [q] : 0 ≤ q) k)
      _ = _ := by ring
  have hpolySummable : Summable (fun k : ℕ =>
      ((N + 2 + k : ℕ) : ℝ) ^ 2 * q ^ k) := by
    apply Summable.of_nonneg_of_le (fun k => mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num [q]) _))
      hpolyTerm
    simpa [q, n, mul_comm] using
      (native_source_geom_quadratic_summable.mul_left (((N + 2 : ℕ) : ℝ) ^ 2))
  have hpolyBound :
      ∑' k : ℕ, ((N + 2 + k : ℕ) : ℝ) ^ 2 * q ^ k ≤ n ^ 2 * 1900 := by
    calc
      _ ≤ ∑' k : ℕ, n ^ 2 * (((k : ℝ) + 1) ^ 2 * q ^ k) :=
        hpolySummable.tsum_le_tsum hpolyTerm
          (native_source_geom_quadratic_summable.mul_left (n ^ 2))
      _ = n ^ 2 * 1900 := by
        rw [tsum_mul_left, show q = (9 / 10 : ℝ) by rfl,
          native_source_geom_quadratic_sum]
  have htailEq :
      (∑' k : ℕ, ((N + 2 + k : ℕ) : ℝ) ^ 2 * q ^ (N + 1 + k)) =
        q ^ (N + 1) *
          (∑' k : ℕ, ((N + 2 + k : ℕ) : ℝ) ^ 2 * q ^ k) := by
    calc
      _ = ∑' k : ℕ, q ^ (N + 1) *
          (((N + 2 + k : ℕ) : ℝ) ^ 2 * q ^ k) := by
        apply tsum_congr
        intro k
        rw [pow_add]
        ring
      _ = _ := tsum_mul_left
  have hcoef : n ^ 2 * 1900 ≤
      n ^ 4 * (((Nat.factorial 4 : ℕ) : ℝ) * 10 ^ 5) := by
    have hquad : 4 * n ^ 2 ≤ n ^ 4 := by
      calc
        4 * n ^ 2 ≤ n ^ 2 * n ^ 2 := mul_le_mul_of_nonneg_right hn2 (sq_nonneg n)
        _ = n ^ 4 := by ring
    have hconst : (1900 : ℝ) ≤ (((Nat.factorial 4 : ℕ) : ℝ) * 10 ^ 5) * 4 := by
      norm_num [Nat.factorial]
    calc
      n ^ 2 * 1900 ≤ n ^ 2 * ((((Nat.factorial 4 : ℕ) : ℝ) * 10 ^ 5) * 4) :=
        mul_le_mul_of_nonneg_left hconst (sq_nonneg n)
      _ = (((Nat.factorial 4 : ℕ) : ℝ) * 10 ^ 5) * (4 * n ^ 2) := by ring
      _ ≤ (((Nat.factorial 4 : ℕ) : ℝ) * 10 ^ 5) * n ^ 4 :=
        mul_le_mul_of_nonneg_left hquad (by positivity)
      _ = n ^ 4 * (((Nat.factorial 4 : ℕ) : ℝ) * 10 ^ 5) := by ring
  have hqnonneg : 0 ≤ q := by norm_num [q]
  calc
    _ = q ^ (N + 1) *
        (∑' k : ℕ, ((N + 2 + k : ℕ) : ℝ) ^ 2 * q ^ k) := htailEq
    _ ≤ q ^ (N + 1) * (n ^ 2 * 1900) :=
      mul_le_mul_of_nonneg_left hpolyBound (pow_nonneg hqnonneg _)
    _ ≤ q ^ (N + 1) *
        (n ^ 4 * (((Nat.factorial 4 : ℕ) : ℝ) * 10 ^ 5)) :=
      mul_le_mul_of_nonneg_left hcoef (pow_nonneg hqnonneg _)
    _ = ((N + 2 : ℕ) : ℝ) ^ 4 * (9 / 10 : ℝ) ^ (N + 1) *
        (((Nat.factorial 4 : ℕ) : ℝ) * 10 ^ 5) := by
      dsimp [q, n]
      ring

/-- The full raw-profile tail. The hypotheses are precisely the
quadratic growth comparison and the retained ratio gate `q·3^(6γ)≤.9`; no
finite truncation is dropped. -/
noncomputable def nativeSourceRawWeightedTail
    (q : ℝ) (H N : ℕ) (rawFrame : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, q ^ (N + 1 + k) * rawFrame (H + (N + 1 + k))

theorem native_source_raw_weighted_tail_le
    (q growth : ℝ) (H N : ℕ) (rawFrame : ℕ → ℝ)
    (hq : 0 ≤ q) (hgrowth : 0 ≤ growth) (hratio : q * growth ≤ 9 / 10)
    (hbase : 0 ≤ rawFrame H)
    (hframeNonneg : ∀ j, 0 ≤ rawFrame (H + j))
    (hframe : ∀ j, rawFrame (H + j) ≤
      rawFrame H * ((j + 1 : ℕ) : ℝ) ^ 2 * growth ^ j) :
    nativeSourceRawWeightedTail q H N rawFrame ≤
      rawFrame H * ((N + 2 : ℕ) : ℝ) ^ 4 * (9 / 10 : ℝ) ^ (N + 1) *
        (((Nat.factorial 4 : ℕ) : ℝ) * 10 ^ 5) := by
  have hmajorSummable : Summable (fun k : ℕ =>
      rawFrame H * ((N + 2 + k : ℕ) : ℝ) ^ 2 *
        (9 / 10 : ℝ) ^ (N + 1 + k)) := by
    have hPoly : Summable (fun k : ℕ =>
        ((N + 2 + k : ℕ) : ℝ) ^ 2 * (9 / 10 : ℝ) ^ (N + 1 + k)) := by
      have hPolyBase := native_source_geom_quadratic_summable
      have hPolyShift : Summable (fun k : ℕ =>
          ((N + 2 + k : ℕ) : ℝ) ^ 2 * (9 / 10 : ℝ) ^ k) := by
        apply Summable.of_nonneg_of_le
          (fun k => mul_nonneg (sq_nonneg _) (by norm_num))
          (fun k => ?_)
          (hPolyBase.mul_left (((N + 2 : ℕ) : ℝ) ^ 2))
        have hn : (2 : ℝ) ≤ ((N + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ N + 2)
        have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        have hlin : ((N + 2 + k : ℕ) : ℝ) ≤
            ((N + 2 : ℕ) : ℝ) * ((k : ℝ) + 1) := by
          norm_cast
          have hprod : 0 ≤ (((N + 2 : ℕ) : ℝ) - 1) * (k : ℝ) :=
            mul_nonneg (by linarith) hk
          nlinarith [hprod]
        have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
          ((N + 2 + k : ℕ) : ℝ)) hlin 2
        calc
          _ ≤ (((N + 2 : ℕ) : ℝ) * ((k : ℝ) + 1)) ^ 2 *
              (9 / 10 : ℝ) ^ k :=
            mul_le_mul_of_nonneg_right hsq
              (pow_nonneg (by norm_num : 0 ≤ (9 / 10 : ℝ)) k)
          _ = _ := by ring
      have heq : (fun k : ℕ =>
          ((N + 2 + k : ℕ) : ℝ) ^ 2 * (9 / 10 : ℝ) ^ (N + 1 + k)) =
        (fun k : ℕ => (9 / 10 : ℝ) ^ (N + 1) *
          (((N + 2 + k : ℕ) : ℝ) ^ 2 * (9 / 10 : ℝ) ^ k)) := by
        funext k
        rw [pow_add]
        ring
      rw [heq]
      exact hPolyShift.mul_left _
    simpa only [mul_assoc] using hPoly.mul_left (rawFrame H)
  have hterm (k : ℕ) :
      q ^ (N + 1 + k) * rawFrame (H + (N + 1 + k)) ≤
        rawFrame H * ((N + 2 + k : ℕ) : ℝ) ^ 2 *
          (9 / 10 : ℝ) ^ (N + 1 + k) := by
    let j : ℕ := N + 1 + k
    have hjCast : ((j + 1 : ℕ) : ℝ) = ((N + 2 + k : ℕ) : ℝ) := by
      dsimp [j]
      congr 1
      omega
    have hpow : (q * growth) ^ j ≤ (9 / 10 : ℝ) ^ j :=
      pow_le_pow_left₀ (mul_nonneg hq hgrowth) hratio j
    have hframej := hframe j
    calc
      _ ≤ q ^ j * (rawFrame H * ((j + 1 : ℕ) : ℝ) ^ 2 * growth ^ j) :=
        mul_le_mul_of_nonneg_left hframej (pow_nonneg hq _)
      _ = rawFrame H * ((N + 2 + k : ℕ) : ℝ) ^ 2 * (q * growth) ^ j := by
        rw [hjCast]
        rw [mul_pow]
        ring
      _ ≤ rawFrame H * ((N + 2 + k : ℕ) : ℝ) ^ 2 * (9 / 10 : ℝ) ^ j :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg hbase (sq_nonneg _))
      _ = _ := by dsimp [j]
  have htailSummable : Summable (fun k : ℕ =>
      q ^ (N + 1 + k) * rawFrame (H + (N + 1 + k))) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg hq _) (hframeNonneg _)) hterm hmajorSummable
  have hsum := htailSummable.tsum_le_tsum hterm hmajorSummable
  have hsumAssoc : (fun k : ℕ =>
      rawFrame H * ((N + 2 + k : ℕ) : ℝ) ^ 2 *
        (9 / 10 : ℝ) ^ (N + 1 + k)) =
      (fun k : ℕ => rawFrame H *
        (((N + 2 + k : ℕ) : ℝ) ^ 2 * (9 / 10 : ℝ) ^ (N + 1 + k))) := by
    funext k
    ring
  rw [hsumAssoc, tsum_mul_left] at hsum
  have hpoly := native_source_polynomial_tail_le N
  unfold nativeSourceRawWeightedTail
  calc
    _ ≤ rawFrame H *
        (∑' k : ℕ, ((N + 2 + k : ℕ) : ℝ) ^ 2 *
          (9 / 10 : ℝ) ^ (N + 1 + k)) := hsum
    _ ≤ rawFrame H * (((N + 2 : ℕ) : ℝ) ^ 4 * (9 / 10 : ℝ) ^ (N + 1) *
        (((Nat.factorial 4 : ℕ) : ℝ) * 10 ^ 5)) :=
      mul_le_mul_of_nonneg_left hpoly hbase
    _ = _ := by ring

end ASDExplicitGamma.Native
