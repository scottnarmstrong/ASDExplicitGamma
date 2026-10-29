module

public import ASDExplicitGamma.Gaussian.Q3ModelCovariance
public import ASDExplicitGamma.Statements.ShellVarianceSum
public import ASDExplicitGamma.Numerics.Scalar.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.BigOperators.Intervals

/-! # The quarter-corridor Gaussian shell clocks -/

@[expose] public section

open Algsuperdiff.Section3

namespace ASDExplicitGamma.Gaussian

/-- The physical kernel amplitude has precisely the frozen shell variance. -/
theorem q3ModelAmplitude_sq (M : ABKModel 2) (h : ℝ) (i : ℤ) :
    q3ModelAmplitude M h i ^ 2 = h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (i : ℝ)) := by
  rw [q3ModelAmplitude, mul_pow]
  congr 1
  have he := Real.rpow_mul (x := 3) (by norm_num) (M.gamma * (i : ℝ)) 2
  rw [Real.rpow_two] at he
  calc
    _ = (3 : ℝ) ^ ((M.gamma * (i : ℝ)) * 2) := he.symm
    _ = _ := by congr 1; ring

/-- The source's simple variance clock uses only gamma>0 and the proved log(3)<11/10. -/
theorem four_shell_variance_ratio_le {γ : ℝ} (hγ : 0 < γ) :
    4 * (1 - (3 : ℝ) ^ (-(2 * γ))) ≤ 9 * γ := by
  have he := Real.add_one_le_exp (-(2 * γ) * Real.log 3)
  have hlog := mul_le_mul_of_nonneg_left Numerics.Scalar.log_three_small.2.le hγ.le
  have halg {e l g : ℝ} (hg : 0 ≤ g) (he : 1 - 2 * g * l ≤ e)
      (hl : g * l ≤ g * (11 / 10)) : 4 * (1 - e) ≤ 9 * g := by
    linarith only [he, hl, hg]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  rw [mul_comm (Real.log 3)]
  apply halg (l := Real.log 3) (g := γ) hγ.le
  · convert he using 1
    ring
  · exact hlog

/-- The named protected lower corridor gives the corresponding bound, uniformly over all shell labels. -/
theorem q3_shell_variance_div_frame_sq_le (M : ABKModel 2) (h σ : ℝ) (j i : ℤ)
    (hσ : 0 < σ) (hlower : shellVarianceSum h M.gamma j / 4 ≤ σ ^ 2) :
    q3ModelAmplitude M h i ^ 2 / σ ^ 2 ≤
      9 * M.gamma * (3 : ℝ) ^ (2 * M.gamma * ((i : ℝ) - j)) := by
  let δ := 1 - (3 : ℝ) ^ (-(2 * M.gamma))
  have hγ := M.shellPrefix.gamma_pos
  have hδ : 0 < δ := by
    apply sub_pos.mpr
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos (mul_pos (by norm_num) hγ))
  have hm : h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) ≤ σ ^ 2 * (δ * 4) := by
    apply (div_le_iff₀ (mul_pos hδ (by norm_num : (0 : ℝ) < 4))).mp
    simpa only [shellVarianceSum, div_div, δ] using hlower
  have he : (3 : ℝ) ^ (2 * M.gamma * (i : ℝ)) =
      (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) * (3 : ℝ) ^ (2 * M.gamma * ((i : ℝ) - j)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hd := four_shell_variance_ratio_le hγ
  change 4 * δ ≤ 9 * M.gamma at hd
  apply (div_le_iff₀ (sq_pos_of_pos hσ)).mpr
  rw [q3ModelAmplitude_sq, he, ← mul_assoc]
  calc
    _ ≤ (σ ^ 2 * (δ * 4)) * (3 : ℝ) ^ (2 * M.gamma * ((i : ℝ) - j)) :=
      mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (by norm_num) _)
    _ = (4 * δ) * (σ ^ 2 * (3 : ℝ) ^ (2 * M.gamma * ((i : ℝ) - j))) := by ring
    _ ≤ (9 * M.gamma) * (σ ^ 2 * (3 : ℝ) ^ (2 * M.gamma * ((i : ℝ) - j))) :=
      mul_le_mul_of_nonneg_right hd (by positivity)
    _ = _ := by ring

/-- The fine spatial kernel costs form a geometric tail, uniformly in the root depth. -/
theorem q3_fine_spatial_clock_le (j n : ℤ) (hjn : j ≤ n) :
    ∑ k ∈ Finset.Ioc j n, min ((3 : ℝ) ^ (k - n)) 1 ≤ 3 / 2 := by
  have hgeom (r : ℕ) : ∑ t ∈ Finset.range r, (1 / 3 : ℝ) ^ t ≤ 3 / 2 := by
    have hid : (1 - (1 / 3 : ℝ)) * (∑ t ∈ Finset.range r, (1 / 3 : ℝ) ^ t) =
        1 - (1 / 3 : ℝ) ^ r := by
      induction r with
      | zero => simp
      | succ r ih =>
          rw [Finset.sum_range_succ, pow_succ]
          rw [mul_add, ih]
          ring
    have hp : 0 ≤ (1 / 3 : ℝ) ^ r := pow_nonneg (by norm_num) _
    nlinarith only [hid, hp]
  have hr : ((n - j).toNat : ℤ) = n - j := Int.toNat_of_nonneg (sub_nonneg.mpr hjn)
  have hsum : (∑ k ∈ Finset.Ioc j n, (3 : ℝ) ^ (k - n)) =
      ∑ t ∈ Finset.range (n - j).toNat, (1 / 3 : ℝ) ^ t := by
    rw [Int.Ioc_eq_finset_map, Finset.sum_map]
    rw [← Finset.sum_range_reflect]
    simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]
    apply Finset.sum_congr rfl
    intro t ht
    have ht' : t < (n - j).toNat := Finset.mem_range.mp ht
    have he : (j + 1 + (((n - j).toNat - 1 - t : ℕ) : ℤ)) - n = -(t : ℤ) := by
      rw [← hr]
      omega
    rw [he]
    simp [zpow_neg, zpow_natCast, one_div]
  have hterm (k : ℤ) (hk : k ∈ Finset.Ioc j n) :
      min ((3 : ℝ) ^ (k - n)) 1 = (3 : ℝ) ^ (k - n) := by
    rw [min_eq_left]
    exact zpow_le_one_of_nonpos₀ (by norm_num) (by simp only [Finset.mem_Ioc] at hk; omega)
  rw [Finset.sum_congr rfl hterm, hsum]
  exact hgeom _

/-- Above the observation scale, each shell costs at most one; together with the fine tail this
gives the full spatial operator clock. -/
theorem q3_spatial_clock_sum_le (j n N : ℤ) (hjn : j ≤ n) (hnN : n ≤ N) :
    ∑ k ∈ Finset.Ioc j N, min ((3 : ℝ) ^ (k - n)) 1 ≤ (N - n : ℝ) + 3 / 2 := by
  have hsplit : Finset.Ioc j N = Finset.Ioc j n ∪ Finset.Ioc n N := by
    ext k
    simp only [Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdis : Disjoint (Finset.Ioc j n) (Finset.Ioc n N) := by
    apply Finset.disjoint_left.mpr
    intro k hk₁ hk₂
    simp only [Finset.mem_Ioc] at hk₁ hk₂
    omega
  rw [hsplit, Finset.sum_union hdis]
  have hf := q3_fine_spatial_clock_le j n hjn
  have hc : (∑ k ∈ Finset.Ioc n N, min ((3 : ℝ) ^ (k - n)) 1) ≤ (N - n : ℝ) := by
    calc
      _ = ∑ k ∈ Finset.Ioc n N, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_Ioc] at hk
        rw [min_eq_right]
        have he : 0 ≤ k - n := by omega
        rw [← Int.toNat_of_nonneg he, zpow_natCast]
        exact one_le_pow₀ (by norm_num)
      _ = (Finset.Ioc n N).card := by simp
      _ ≤ (N - n : ℝ) := by
        have hcard : ((Finset.Ioc n N).card : ℝ) = (N - n : ℝ) := by
          exact_mod_cast Int.card_Ioc_of_le n N hnN
        rw [← hcard]
  linarith

/-- Summing the protected per-shell clocks bounds the full variance of a finite later band. -/
theorem q3_shell_variance_sum_div_frame_sq_le (M : ABKModel 2) (h σ : ℝ) (j N : ℤ)
    (hσ : 0 < σ) (hlower : shellVarianceSum h M.gamma j / 4 ≤ σ ^ 2) (hjN : j ≤ N) :
    (∑ i ∈ Finset.Ioc j N, q3ModelAmplitude M h i ^ 2 / σ ^ 2) ≤
      9 * M.gamma * (N - j : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ)) := by
  have hγ := M.shellPrefix.gamma_pos
  let C : ℝ := 9 * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ))
  have hterm (i : ℤ) (hi : i ∈ Finset.Ioc j N) :
      q3ModelAmplitude M h i ^ 2 / σ ^ 2 ≤ C := by
    have hclock := q3_shell_variance_div_frame_sq_le M h σ j i hσ hlower
    have he : 2 * M.gamma * ((i : ℝ) - j) ≤ 2 * M.gamma * ((N : ℝ) - j) := by
      simp only [Finset.mem_Ioc] at hi
      have hiReal : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi.2
      nlinarith [hγ.le, hiReal]
    have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) he
    dsimp [C]
    calc
      _ ≤ 9 * M.gamma * (3 : ℝ) ^ (2 * M.gamma * ((i : ℝ) - j)) := hclock
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
  calc
    _ ≤ ∑ i ∈ Finset.Ioc j N, C := Finset.sum_le_sum fun i hi => hterm i hi
    _ = ((Finset.Ioc j N).card : ℝ) * C := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = (N - j : ℝ) * C := by
      have hcard : ((Finset.Ioc j N).card : ℝ) = (N - j : ℝ) := by
        exact_mod_cast Int.card_Ioc_of_le j N hjN
      rw [hcard]
    _ = 9 * M.gamma * (N - j : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ)) := by
      dsimp [C]
      ring

end ASDExplicitGamma.Gaussian
