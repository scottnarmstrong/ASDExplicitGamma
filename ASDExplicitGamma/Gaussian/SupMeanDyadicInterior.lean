module

public import ASDExplicitGamma.Gaussian.SupMeanDyadicConvergence

/-! Every actual dyadic center has a positive physical ball inside its observation square. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian

/-- The half-cell margin retains both endpoints of the finite center grid. -/
theorem supMean_half_cell_margin (N i s : ℝ) (hN : 0 < N) (hi0 : 0 ≤ i) (hi1 : i+1 ≤ N) (hs : 0 ≤ s) :
    |s*((i+1/2)/N-1/2)| ≤ s/2-s/(2*N) := by
  have hlo : (1/2:ℝ)/N ≤ (i+1/2)/N := div_le_div_of_nonneg_right (by linarith only [hi0]) hN.le
  have hhi : (i+1/2)/N ≤ (N-1/2)/N := div_le_div_of_nonneg_right (by linarith only [hi1]) hN.le
  have he : (N-1/2)/N = 1-(1/2:ℝ)/N := by field_simp
  rw [he] at hhi
  rw [abs_mul,abs_of_nonneg hs]
  have hb : |(i+1/2)/N-1/2| ≤ (1/2:ℝ)-(1/2)/N :=
    abs_le.mpr ⟨by linarith only [hlo],by linarith only [hhi]⟩
  exact (mul_le_mul_of_nonneg_left hb hs).trans_eq (by ring)

/-- The actual dyadic center has its literal half-cell coordinate margin. -/
theorem supMean_dyadic_center_margin (c : Fin 2 → ℝ) (s : ℝ) (hs : 0 ≤ s)
    (n : ℕ) (i : SupMeanDyadicIndex n) (d : Fin 2) :
    |supMeanDyadicCenter c s n i d-c d| ≤ s/2-s/(2*(2:ℝ)^n) := by
  have hi1 : ((i d).val:ℝ)+1 ≤ (2:ℝ)^n := by exact_mod_cast (i d).isLt
  have he : supMeanDyadicCenter c s n i d-c d = s*((((i d).val:ℝ)+1/2)/(2:ℝ)^n-1/2) := by
    unfold supMeanDyadicCenter
    ring
  rw [he]
  exact supMean_half_cell_margin _ _ s (by positivity) (Nat.cast_nonneg _) hi1 hs

/-- No boundary regularity convention is needed to recover the jets used by
the dense-center supremum: every such jet is at a genuine interior point. -/
theorem supMean_dyadic_center_ball_subset (c : Fin 2 → ℝ) (s : ℝ) (hs : 0 < s)
    (n : ℕ) (i : SupMeanDyadicIndex n) :
    Metric.closedBall (supMeanDyadicCenter c s n i) (s/(2*(2:ℝ)^n)) ⊆ supMeanClosedSquare c s := by
  intro y hy d
  have hr : 0 ≤ s/(2*(2:ℝ)^n) := by positivity
  have hn : ‖y-supMeanDyadicCenter c s n i‖ ≤ s/(2*(2:ℝ)^n) := by
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hy
  have hd := (pi_norm_le_iff_of_nonneg hr).mp hn d
  have hc := supMean_dyadic_center_margin c s hs.le n i d
  have hd' : |y d-supMeanDyadicCenter c s n i d| ≤ s/(2*(2:ℝ)^n) := by
    simpa only [Pi.sub_apply,Real.norm_eq_abs] using hd
  have ht : |y d-c d| ≤ |y d-supMeanDyadicCenter c s n i d|+|supMeanDyadicCenter c s n i d-c d| :=
    abs_sub_le _ _ _
  linarith only [ht,hd',hc]

end ASDExplicitGamma.Gaussian
