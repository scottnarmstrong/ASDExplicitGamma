module

public import ASDExplicitGamma.Triadic.HaarNormTriangle
public import ASDExplicitGamma.Triadic.PlanarSobolev

/-! Scalar sign and planar quarter-turn invariance of the exact Haar energies. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped BigOperators
noncomputable section

 theorem cubeIncrement_neg (Q : TriadicCube 2) (n : ℕ) (f : Vec 2 → ℝ) :
    cubeIncrement Q n (fun x => -f x) = fun x => -cubeIncrement Q n f x := by
  have hp (j : ℕ) : cubeProjection Q j (fun x => -f x) = fun x => -cubeProjection Q j f x := by
    simpa only [neg_one_mul] using projection_smul Q j f (-1)
  cases n with
  | zero => exact hp 0
  | succ n =>
      simp only [cubeIncrement, hp]
      funext x
      ring

 theorem energy_neg (Q : TriadicCube 2) (f : Vec 2 → ℝ) : energy Q (fun x => -f x) = energy Q f := by
  rw [energy_eq_integral_sq, energy_eq_integral_sq]
  simp only [neg_sq]

 theorem primalEnergy_neg (Q : TriadicCube 2) (q : ℝ) (f : Vec 2 → ℝ) : primalEnergy Q q (fun x => -f x) = primalEnergy Q q f := by
  simp only [primalEnergy, cubeIncrement_neg, energy_neg]

 theorem vectorPositiveHaarNorm_quarterTurn (Q : TriadicCube 2) (F : Vec 2 → Fin 2 → ℝ) :
    vectorPositiveHaarNorm Q (fun x => planarQuarterTurn (F x)) = vectorPositiveHaarNorm Q F := by
  unfold vectorPositiveHaarNorm vectorPositiveHaarEnergy
  congr 1
  simp only [Fin.sum_univ_two, planarQuarterTurn, ite_true, show (1:Fin 2)≠0 by decide, ite_false, primalEnergy_neg]
  ring

 theorem positive_series_quarterTurn (Q : TriadicCube 2) (F : Vec 2 → Fin 2 → ℝ)
    (hP : ∀ i, Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) (fun x => F x i)))) :
    ∀ i, Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) (fun x => planarQuarterTurn (F x) i))) := by
  intro i
  fin_cases i
  · change Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) (fun x => -F x 1)))
    simp_rw [cubeIncrement_neg, energy_neg]
    exact hP 1
  · change Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) (fun x => F x 0)))
    exact hP 0

 theorem vectorL2_le_vectorPositiveHaar {d m : ℕ} (Q : TriadicCube d) (F : Vec d → Fin m → ℝ)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hP : ∀ i, Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) (fun x => F x i)))) :
    Real.sqrt (∑ i, energy Q (fun x => F x i)) ≤ vectorPositiveHaarNorm Q F := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  have hq : 1 < Real.sqrt 3 := by nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg (3:ℝ)]
  have hpH : Summable (fun n => (Real.sqrt 3)^(n+1)*hilbertEnergy Q (hilbertCubeIncrement Q (n+1) (fun x => F x i))) := by
    simpa only [hilbertCubeIncrement_real, hilbertEnergy_real] using hP i
  have hid := (hilbert_sensitivity_tail_of_weight Q hq (hF i) hpH).2.1
  rw [hilbertPrimalEnergy_real, hilbertEnergy_real] at hid
  rw [hid]
  exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hq.le)
    (tsum_nonneg fun n => mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (hilbertEnergy_nonneg Q _)))

end
end ASDExplicitGamma.Triadic
