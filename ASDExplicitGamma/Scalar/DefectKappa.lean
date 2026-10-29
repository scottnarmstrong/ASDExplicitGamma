module

public import ASDExplicitGamma.Scalar.DefectPosHaarFields
public import ASDExplicitGamma.Scalar.NewResolventDefectFormula

/-! The weak-face column constant is at most `|b| A` once the mesh radius is at most `L/3^6`. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization ASDExplicitGamma.Triadic ASDExplicitGamma.Native

theorem colKappa_le (Q : TriadicCube 2) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (hr : diagMeshRadius Q m ≤ L.1 / 729) :
    colKappa Q m b L ≤ |b| * defectA := by
  unfold colKappa oldSignedSourceMultiplier defectA
  have hL := L.2
  set r := diagMeshRadius Q m with hrdef
  have hr0 : 0 ≤ r := (diagMeshRadius_pos Q m).le
  set l := L.1
  have e1 : Real.sqrt ((156 / 5) * b ^ 2 / l ^ 2) = Real.sqrt (156 / 5) * |b| / l := by
    have : (156 / 5) * b ^ 2 / l ^ 2 = (156 / 5) * (b / l) ^ 2 := by ring
    rw [this, Real.sqrt_mul (by norm_num), Real.sqrt_sq_eq_abs, abs_div, abs_of_pos hL]
    ring
  have e2 : Real.sqrt ((46488 / 25) * b ^ 2 / l ^ 4) = Real.sqrt (46488 / 25) * |b| / l ^ 2 := by
    have : (46488 / 25) * b ^ 2 / l ^ 4 = (46488 / 25) * (b / l ^ 2) ^ 2 := by ring
    rw [this, Real.sqrt_mul (by norm_num), Real.sqrt_sq_eq_abs, abs_div, abs_of_pos (pow_pos hL 2)]
    ring
  rw [e1, e2, Real.sqrt_sq_eq_abs]
  have ht : r / l ≤ 1 / 729 := by rw [div_le_iff₀ hL]; linarith
  have ht0 : 0 ≤ r / l := by positivity
  have h1 : r * (36 / 25) * (Real.sqrt (156 / 5) * |b| / l) ≤
      (36 / 25) * (Real.sqrt (156 / 5) * (1 / 729)) * |b| := by
    have : r * (36 / 25) * (Real.sqrt (156 / 5) * |b| / l) =
        (36 / 25) * Real.sqrt (156 / 5) * |b| * (r / l) := by ring
    rw [this]
    have hc : 0 ≤ (36 / 25) * Real.sqrt (156 / 5) * |b| := by positivity
    calc _ ≤ (36 / 25) * Real.sqrt (156 / 5) * |b| * (1 / 729) := mul_le_mul_of_nonneg_left ht hc
      _ = _ := by ring
  have h2 : r ^ 2 * (57 / 200) * (Real.sqrt (46488 / 25) * |b| / l ^ 2) ≤
      (57 / 200) * (Real.sqrt (46488 / 25) * (1 / 531441)) * |b| := by
    have : r ^ 2 * (57 / 200) * (Real.sqrt (46488 / 25) * |b| / l ^ 2) =
        (57 / 200) * Real.sqrt (46488 / 25) * |b| * (r / l) ^ 2 := by
      field_simp
    rw [this]
    have hc : 0 ≤ (57 / 200) * Real.sqrt (46488 / 25) * |b| := by positivity
    have : (r / l) ^ 2 ≤ 1 / 531441 := by
      calc (r / l) ^ 2 ≤ (1 / 729) ^ 2 := pow_le_pow_left₀ ht0 ht 2
        _ = _ := by norm_num
    calc _ ≤ (57 / 200) * Real.sqrt (46488 / 25) * |b| * (1 / 531441) :=
          mul_le_mul_of_nonneg_left this hc
      _ = _ := by ring
  nlinarith [h1, h2]

theorem colKappa_sq_le (Q : TriadicCube 2) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (hr : diagMeshRadius Q m ≤ L.1 / 729) :
    colKappa Q m b L ^ 2 ≤ defectA ^ 2 * b ^ 2 := by
  have h := colKappa_le Q m b L hr
  have h0 : 0 ≤ colKappa Q m b L := by
    unfold colKappa oldSignedSourceMultiplier
    have := (diagMeshRadius_pos Q m).le
    positivity
  calc colKappa Q m b L ^ 2 ≤ (|b| * defectA) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = _ := by rw [mul_pow, sq_abs]; ring

end ASDExplicitGamma.Scalar
