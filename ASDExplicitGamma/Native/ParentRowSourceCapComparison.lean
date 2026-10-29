module

public import ASDExplicitGamma.Native.ParentRowErrorExpectation
public import ASDExplicitGamma.Native.ParentRowFiniteBudgets
public import ASDExplicitGamma.Native.ParentRowHistoryPanel
public import ASDExplicitGamma.Native.ParentRowOscillationPanel
public import ASDExplicitGamma.Native.ParentRowMultiplierPanel

/-! Source cap comparison before the finite-shell quadratic contraction. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Variational Main Triadic Algsuperdiff.Section3 Numerics.Native
noncomputable section

/-- Increasing only the common weak allowance preserves the full correlated
source cap; no amplitude sign or reciprocal-energy estimate is assumed. -/
theorem parent_row_source_cap_weak_mono
    (M : ABKModel 2) (n : ℤ) (height r : ℕ) (t b : ℝ) (L : {l : ℝ // 0<l})
    (X : ℝ) (hX : theta M*parentRowWeakAllowance height t≤X) :
    let k := parentBoundaryPotentialSourceClock (originCube 2 n) r b L
    parentRowSourceMixedCap M n height r t b L≤
      k^2*((3683/2500:ℝ)*X)+(2*k)*(Real.sqrt X*Real.sqrt (X*b^2))+
        (2*k)*(Real.sqrt X*Real.sqrt (parentRowReciprocalCap n height r t b L)) := by
  intro k
  have hk : 0≤k := parent_boundary_potential_source_clock_nonneg (originCube 2 n) r b L
  have h2k : 0≤2*k := mul_nonneg (by norm_num) hk
  have hj := mul_le_mul (Real.sqrt_le_sqrt hX)
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hX (sq_nonneg b)))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX (by norm_num : (0:ℝ)≤3683/2500)) (sq_nonneg k))
    (mul_le_mul_of_nonneg_left hj h2k))
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hX) (Real.sqrt_nonneg _)) h2k)

/-- The reciprocal cap contracts as the exact sum of its two oscillation
energies; both sign-specific fields remain distinct. -/
theorem parent_row_band_reciprocal_cap
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (j : Fin 16) (t : ℝ) :
    let f := fun k => (parentRowFields j).getD k 0
    let H := parentRowPanelHistory j t
    let A := 1+2*H+Real.sqrt (2*H)
    Real.sqrt (∑ i : Fin (j.val+1),parentRowReciprocalCap n (j.val+1) 5 t
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
      (q3ModelLength (n+((i.val+1:ℕ):ℤ))))≤
      Real.sqrt (theta M)*Real.sqrt (((3683/2500:ℝ)+1)^2*(f 4)^2+(3683/2500:ℝ)*A*(f 5)^2) := by
  intro f H A
  have hp := parent_row_band_oscillation_panel M h hg n hstate j true
  have hm := parent_row_band_oscillation_panel M h hg n hstate j false
  simp only [ite_true] at hp
  simp only [Bool.false_eq_true,ite_false] at hm
  have hA : 0≤A := add_nonneg (add_nonneg (by norm_num)
    (mul_nonneg (by norm_num) (sq_nonneg _))) (Real.sqrt_nonneg _)
  rw [←Real.sqrt_mul (cold_theta_pos M).le]
  apply Real.sqrt_le_sqrt
  unfold parentRowReciprocalCap
  simp_rw [parent_row_history_panel_eq]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
  exact (add_le_add
    (mul_le_mul_of_nonneg_left hp (sq_nonneg ((3683/2500:ℝ)+1)))
    (mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num : (0:ℝ)≤3683/2500) hA))).trans_eq (by ring)

/-- The deterministic reciprocal cap is nonnegative before shell aggregation. -/
theorem parent_row_reciprocal_cap_nonneg (n : ℤ) (height r : ℕ) (t b : ℝ)
    (L : {l : ℝ // 0<l}) : 0≤parentRowReciprocalCap n height r t b L := by
  have hA : 0≤1+2*parentHistorySourceEnvelope height r t+
      Real.sqrt (2*parentHistorySourceEnvelope height r t) :=
    add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num) (sq_nonneg _))) (Real.sqrt_nonneg _)
  exact add_nonneg (mul_nonneg (sq_nonneg _)
    (descendantsAverage_nonneg _ _ _ (fun _ _ => sq_nonneg _)))
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤3683/2500) hA)
      (descendantsAverage_nonneg _ _ _ (fun _ _ => sq_nonneg _)))

/-- The whole source quadratic/mixed block fits the exact source-panel
coefficients; only the separately owned scalar weak-field comparison is an
in-node input. -/
theorem parent_row_band_source_cap
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (j : Fin 16) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (hw : parentRowWeakAllowance (j.val+1) t ≤
      (parentRowFields j).getD 15 0+(parentRowFields j).getD 12 0*t) :
    let f := fun k => (parentRowFields j).getD k 0
    let X := f 15+f 12*t
    let H := parentRowPanelHistory j t
    let A := 1+2*H+Real.sqrt (2*H)
    let R := Real.sqrt (((3683/2500:ℝ)+1)^2*(f 4)^2+(3683/2500:ℝ)*A*(f 5)^2)
    (∑ i : Fin (j.val+1),parentRowSourceMixedCap M n (j.val+1) 5 t
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
      (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) ≤
      theta M*((f 2)^2*((3683/2500:ℝ)*X)+2*f 2*(X*Real.sqrt (f 0))+2*f 2*(Real.sqrt X*R)) := by
  intro f X H A R
  let b := fun i : Fin (j.val+1) => q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ)
  let L := fun i : Fin (j.val+1) => q3ModelLength (n+((i.val+1:ℕ):ℤ))
  let k := fun i => parentBoundaryPotentialSourceClock (originCube 2 n) 5 (b i) (L i)
  let e := fun i => parentRowReciprocalCap n (j.val+1) 5 t (b i) (L i)
  have hw0 := parent_row_weak_allowance_nonneg (j.val+1) t ht.1
  have hX : 0≤X := hw0.trans hw
  have hactual : theta M*parentRowWeakAllowance (j.val+1) t≤X :=
    ((mul_le_mul_of_nonneg_right (cold_theta_le_one M hg) hw0).trans_eq (one_mul _)).trans hw
  have hb : Real.sqrt (∑ i,b i^2)≤Real.sqrt (theta M)*Real.sqrt (f 0) := by
    rw [←Real.sqrt_mul (cold_theta_pos M).le]
    exact Real.sqrt_le_sqrt (parent_row_actual_variance M h hg n hstate j)
  have hpay := parent_row_source_sum_budget k b e (theta M) (f 2) (Real.sqrt (f 0)) R X
    (cold_theta_pos M).le (nativeList_getD_nonneg _ (parent_row_fields_valid j).2 2) hX
    (fun i => parent_row_reciprocal_cap_nonneg n (j.val+1) 5 t (b i) (L i))
    (parent_row_band_source_panel M h hg n hstate j) hb
    (parent_row_band_reciprocal_cap M h hg n hstate j t)
  exact (Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin (j.val+1)))) =>
    parent_row_source_cap_weak_mono M n (j.val+1) 5 t (b i) (L i) X hactual)).trans hpay

end
end ASDExplicitGamma.Native
