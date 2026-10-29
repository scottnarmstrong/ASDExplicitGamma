module

public import ASDExplicitGamma.Native.ParentRowPhysicalScales
public import ASDExplicitGamma.Native.OldSignedQ1OscillationCaps

/-! Whole-band oscillation energies with the exact second mesh moment. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- The complete band gradient energy uses the same exact A2 field. -/
theorem parent_row_band_gradient_energy
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (j : Fin 16) :
    (∑ i : Fin (j.val+1),(cubeScaleFactor (originCube 2 n)/3^5)^2*
      mainFlatSigmaSq (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
        (q3ModelLength (n+((i.val+1:ℕ):ℤ))))≤
      theta M*((156/5:ℝ)*(parentRowFields j).getD 1 0) := by
  have hh := mul_le_mul_of_nonneg_left
    (parent_row_mesh_second_bound M h hg n hstate j) (by norm_num : (0:ℝ)≤156/5)
  have he : (156/5:ℝ)*parentRowMeshMoment M h n (j.val+1) 1=
      ∑ i : Fin (j.val+1),(cubeScaleFactor (originCube 2 n)/3^5)^2*
        mainFlatSigmaSq (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
          (q3ModelLength (n+((i.val+1:ℕ):ℤ))) := by
    unfold parentRowMeshMoment
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold mainFlatSigmaSq
    ring
  rw [he] at hh
  exact hh.trans_eq (by ring)

/-- Both signs of the actual complete band oscillation admit the source
coefficient, with no loss depending on the number of shells. -/
theorem parent_row_band_oscillation_energy
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (j : Fin 16) (plus : Bool) :
    let Q := originCube 2 n
    let c : ℝ := if plus then 1+Real.sqrt 2 else 1
    (∑ i : Fin (j.val+1),descendantsAverage Q 5 (fun U =>
      oldSignedFlatOscillationSize Q U
        (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
        (q3ModelLength (n+((i.val+1:ℕ):ℤ))) plus^2))≤
      theta M*((c*(11/25:ℝ))^2*((156/5:ℝ)*(parentRowFields j).getD 1 0)) := by
  intro Q c
  let S := fun i : Fin (j.val+1) => mainFlatSigmaSq
    (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
    (q3ModelLength (n+((i.val+1:ℕ):ℤ)))
  have hS (i) : 0≤S i := by dsimp only [S,mainFlatSigmaSq]; positivity
  have hpoint (i : Fin (j.val+1)) :
      descendantsAverage Q 5 (fun U => oldSignedFlatOscillationSize Q U
        (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
        (q3ModelLength (n+((i.val+1:ℕ):ℤ))) plus^2)≤
      (c*planarC0)^2*((cubeScaleFactor Q/3^5)^2*S i) := by
    cases plus
    · simpa only [c,S,Bool.false_eq_true,ite_false,one_mul,one_pow,mul_pow,mul_assoc,mul_left_comm,mul_comm] using
        old_signed_flat_minus_partition_oscillation_cap Q 5
          (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
          (q3ModelLength (n+((i.val+1:ℕ):ℤ)))
    · simpa only [c,S,ite_true,mul_pow,mul_assoc,mul_left_comm,mul_comm] using
        old_signed_flat_plus_partition_oscillation_cap Q 5
          (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
          (q3ModelLength (n+((i.val+1:ℕ):ℤ)))
  have hsum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hpoint i)
  rw [←Finset.mul_sum] at hsum
  have hc0 : 0≤c := by cases plus <;> dsimp only [c] <;> positivity
  have hc : (c*planarC0)^2≤(c*(11/25:ℝ))^2 :=
    pow_le_pow_left₀ (mul_nonneg hc0 (Real.sqrt_nonneg _))
      (mul_le_mul_of_nonneg_left old_signed_q1_planarC0_le hc0) 2
  have hp := mul_le_mul hc (parent_row_band_gradient_energy M h hg n hstate j)
    (Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (hS i))) (sq_nonneg _)
  exact hsum.trans (hp.trans_eq (by ring))

end
end ASDExplicitGamma.Native
