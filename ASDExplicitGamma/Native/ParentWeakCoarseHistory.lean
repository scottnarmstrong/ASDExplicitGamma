module

public import ASDExplicitGamma.Native.ParentWeakCoarseKernel

/-! A coarse theta-linear actual history cap for rare payments only. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- A deliberately coarse source delta cap; the leading panel retains its
exact primitive slope and is not replaced by this diagnostic allowance. -/
theorem parent_weak_source_delta_cap (height r : ℕ) (hh : height ≤ 16) (hr : r ≤ 5) :
    parentBoundaryCommonSourceDelta gammaZero height r ≤ 10^14 := by
  let A2 := parentBoundaryCommonSourceSpatialClock gammaZero height r 2
  let A4 := parentBoundaryCommonSourceSpatialClock gammaZero height r 4
  let U := parentBoundaryCommonRawBase gammaZero height r
  let V := 32474*gammaZero
  let F := parentBoundaryCommonRawFactor gammaZero height r
  let S := parentBoundaryCommonSourceVariance gammaZero height
  let X := parentBoundaryCommonKernelGeometric A2 A4 gammaZero 8 U V
  let Y := parentBoundaryCommonKernelGeometric A2 A4 gammaZero 6 1 0
  let a := (26/25:ℝ)*(3683/2500:ℝ)^2*F
  let b := (26*48:ℝ)*S*(3683/2500:ℝ)^3
  have hraw := parent_weak_source_raw_caps height r hh hr
  have hcl2 := parent_weak_source_clock_caps height r 2 hh
  have hcl4 := parent_weak_source_clock_caps height r 4 hh
  have hU0 : 0 ≤ U := by dsimp only [U]; unfold parentBoundaryCommonRawBase; norm_num [gammaZero]; positivity
  have hV0 : 0 ≤ V := by norm_num [V,gammaZero]
  have hX : 0 ≤ X ∧ X ≤ 4000000000 := parent_weak_kernel_geometric_cap hcl2.2 hcl4.2 le_rfl hU0 hraw.2.1 hV0 hraw.2.2
  have hY : 0 ≤ Y ∧ Y ≤ 4000000000 := parent_weak_kernel_geometric_cap hcl2.2 hcl4.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have ha : a ≤ 100 := (mul_le_mul_of_nonneg_left hraw.1 (by norm_num : (0:ℝ)≤(26/25)*(3683/2500)^2)).trans (by norm_num)
  have hb : b ≤ 10000 := by
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcl2.1 (by norm_num : (0:ℝ)≤26*48))
      (by norm_num : (0:ℝ)≤(3683/2500)^3)).trans (by norm_num)
  have ha0 : 0 ≤ a := by dsimp only [a,F]; unfold parentBoundaryCommonRawFactor; positivity
  have hb0 : 0 ≤ b := by
    dsimp only [b,S]
    unfold parentBoundaryCommonSourceVariance nativeSourceShellClock
    norm_num [gammaZero]
    positivity
  have hsum : a*X+b*Y ≤ (10:ℝ)^14 :=
    (add_le_add (mul_le_mul ha hX.2 hX.1 (by norm_num : (0:ℝ)≤100))
      (mul_le_mul hb hY.2 hY.1 (by norm_num : (0:ℝ)≤10000))).trans (by norm_num)
  have hsum0 : 0 ≤ a*X+b*Y := add_nonneg (mul_nonneg ha0 hX.1) (mul_nonneg hb0 hY.1)
  change (1-inverseHistoryDiscount)*(a*X+b*Y) ≤ _
  exact (mul_le_mul (sub_le_self _ inverse_history_discount_range.1.le) hsum hsum0 zero_le_one).trans_eq (one_mul _)

/-- Uniform endpoint HH cap, preserving the literal source envelope and
original3e-46 reserve. It is used only after multiplying by a rare factor. -/
theorem parent_weak_source_history_cap (height r : ℕ) (hh : height ≤ 16) (hr : r ≤ 5)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    parentHistorySourceEnvelope height r t ≤ 10^16 := by
  let D := parentBoundaryCommonSourceDelta gammaZero height r
  let S := parentBoundaryCommonSourceVariance gammaZero height
  let H0 := (3:ℝ)^((3:ℝ)*(r:ℝ)/20)
  let K := (3:ℝ)^((1:ℝ)/4)*Real.sqrt (3683/2500:ℝ)+
    (105:ℝ)^((1:ℝ)/8)*Real.sqrt (3/10^46:ℝ)
  have hd0 : 0 ≤ D := parent_boundary_common_source_delta_nonneg gammaZero (by norm_num [gammaZero]) le_rfl height r
  have hd : D ≤ 10^14 := parent_weak_source_delta_cap height r hh hr
  have hs : S ≤ 1 := (parent_weak_source_clock_caps height r 2 hh).1
  have hs0 : 0 ≤ S := by dsimp only [S]; unfold parentBoundaryCommonSourceVariance nativeSourceShellClock; norm_num [gammaZero]; positivity
  have hrR : (r:ℝ)≤5 := by exact_mod_cast hr
  have hh0 : H0 ≤ 3 := by
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
      (by linarith only [hrR] : (3:ℝ)*(r:ℝ)/20 ≤ 1)).trans_eq (Real.rpow_one _)
  have hroot : Real.sqrt (H0+t*D) ≤ 20000000 := Real.sqrt_le_iff.mpr
    ⟨by norm_num,(add_le_add hh0 ((mul_le_mul_of_nonneg_right ht1 hd0).trans_eq (one_mul _) |>.trans hd)).trans (by norm_num)⟩
  have htS : t*S ≤ 1 := (mul_le_mul ht1 hs hs0 zero_le_one).trans_eq (one_mul _)
  have hvarroot : Real.sqrt (2*t*S) ≤ 2 := Real.sqrt_le_iff.mpr
    ⟨by norm_num, by
      calc 2*t*S = 2*(t*S) := by ring
           _ ≤ 2 := by simpa only [mul_one] using mul_le_mul_of_nonneg_left htS (by norm_num : (0:ℝ)≤2)
           _ ≤ 2^2 := by norm_num⟩
  have hp3 : (3:ℝ)^((1:ℝ)/4) ≤ 3 := (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num : (1:ℝ)/4≤1)).trans_eq (Real.rpow_one _)
  have hp105 : (105:ℝ)^((1:ℝ)/8) ≤ 105 := (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num : (1:ℝ)/8≤1)).trans_eq (Real.rpow_one _)
  have hb : Real.sqrt (3683/2500:ℝ) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have heps : Real.sqrt (3/10^46:ℝ) ≤ 1 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have hK : K ≤ 111 := (add_le_add (mul_le_mul hp3 hb (Real.sqrt_nonneg _) (by norm_num : (0:ℝ)≤3))
    (mul_le_mul hp105 heps (Real.sqrt_nonneg _) (by norm_num : (0:ℝ)≤105))).trans (by norm_num)
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  have hsum : Real.sqrt (H0+t*D)+Real.sqrt (2*t*S)*K ≤ 20000000+2*111 :=
    add_le_add hroot (mul_le_mul hvarroot hK hK0 (by norm_num : (0:ℝ)≤2))
  change (Real.sqrt (H0+t*D)+Real.sqrt (2*t*S)*K)^2 ≤ _
  exact (pow_le_pow_left₀ (by positivity) hsum 2).trans (by norm_num)

/-- Actual-law L2 history with one theta, uniformly for every protected
source square and all sixteen parent bands. No norm cap is a premise. -/
theorem parent_weak_actual_history_L2
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (P : TriadicCube 2) (n : ℤ) (r : ℕ) (hr : r ≤ 5) (hP : P.scale=n-(r:ℤ))
    (hstate : nativeInductionState M h n) (height : ℕ) (hheight : 1 ≤ height) (hh16 : height ≤ 16)
    (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    MemLp (fun ω => (parentBoundaryBandMaxTraceHistory M n height P t ω).toReal) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    eLpNorm (fun ω => (parentBoundaryBandMaxTraceHistory M n height P t ω).toReal) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (theta M*(10:ℝ)^16) := by
  have hh := parent_history_physical_endpoint_L2 M h hM hg P n r hr hP hstate height hheight hpast t ht.1 ht.2
  have hcap := parent_weak_source_history_cap height r hh16 hr t ht.1 ht.2
  have he := parent_history_toReal_norm (Cutoff.cutoffSampleLaw M).toMeasure
    (parentBoundaryBandMaxTraceHistory M n height P t)
    (ae_of_all _ (fun ω => (parent_history_sample_finite M P n height t ω).1.ne)) 2
  rw [←he] at hh
  have hfinal := hh.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hcap (cold_theta_pos M).le))
  exact ⟨hfinal.trans_lt ENNReal.ofReal_lt_top,hfinal⟩

end
end ASDExplicitGamma.Native
