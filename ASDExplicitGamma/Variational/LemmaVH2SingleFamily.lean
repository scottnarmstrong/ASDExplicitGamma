module

public import ASDExplicitGamma.Variational.LemmaVH2SingleCaps
public import ASDExplicitGamma.Variational.LemmaVH2Combination
public import ASDExplicitGamma.Triadic.PlanarDirectionScalar

/-! The canonical covariance-defect direction, embedded as a one-direction family. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open scoped BigOperators
noncomputable section

local instance lemmaVH2SingleFamilyFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

 def q3CovarianceDefectFamily (Q : TriadicCube 2) (L : ℝ) (l : ℕ) : PlanarW2Infinity Q :=
  if l=0 then q3CovarianceDefectWitness Q L (cubeCenter Q) else PlanarW2Infinity.zero Q

 def singleDirectionCoefficient (s : Finset ℕ) (c : ℕ → ℝ) : ℝ := if 0 ∈ s then c 0 else 0

 theorem singleDirectionCoefficient_abs_le (s : Finset ℕ) (c : ℕ → ℝ) :
    |singleDirectionCoefficient s c| ≤ Real.sqrt (∑ l ∈ s, c l^2) := by
  unfold singleDirectionCoefficient
  split_ifs with h0
  · have hs : c 0^2 ≤ ∑ l ∈ s, c l^2 := Finset.single_le_sum (fun l _ => sq_nonneg (c l)) h0
    simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hs
  · simpa only [abs_zero] using Real.sqrt_nonneg (∑ l ∈ s, c l^2)

 theorem q3CovarianceDefectFamily_combination_value (Q : TriadicCube 2) (L : ℝ) (s : Finset ℕ) (c : ℕ → ℝ) :
    (PlanarW2Infinity.linearCombination (q3CovarianceDefectFamily Q L) s c).value =
      singleDirectionCoefficient s c • (q3CovarianceDefectWitness Q L (cubeCenter Q)).value := by
  simp only [PlanarW2Infinity.linearCombination, q3CovarianceDefectFamily, apply_ite, PlanarW2Infinity.zero]
  simp only [smul_zero]
  rw [Finset.sum_ite_eq']
  unfold singleDirectionCoefficient
  split_ifs <;> simp only [zero_smul]

 theorem lemmaVH2_row_bound_smul (Q : TriadicCube 2) (j : ℕ) (η : PlanarW2Infinity Q)
    (p : Vec 2) (u : H10Function (openCubeSet Q)) (a : ℝ) {A G H : ℝ}
    (hA : 0 ≤ A) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hval : ∀ᵐ x ∂normalizedCubeMeasure Q, |η.value.toFun x| ≤ A)
    (hgrad : ∀ᵐ x ∂normalizedCubeMeasure Q, planarEuclideanNorm (planarW1Value η.gradient x) ≤ G)
    (hhess : ∀ᵐ x ∂normalizedCubeMeasure Q, planarFrobeniusNorm (planarW1Derivative η.gradient x) ≤ H) :
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    let I := diagInterpolant Q j
    (∀ R ∈ descendantsAtDepth Q j, ∀ i, Summable (fun k => (Real.sqrt 3)^(k+1)*energy R
      (cubeIncrement R (k+1) (fun x => lemmaVPlanarRowField I (a • η.value) v x i)))) ∧
    Real.sqrt (lemmaVTiledPositiveEnergy Q j (lemmaVPlanarRowField I (a • η.value) v)) ≤
      lemmaVH2RowConstant (diagMeshRadius Q j) A G H* |a| *Real.sqrt (lemmaVTiledWeakEnergy Q j v.grad) := by
  intro v I
  have hv : ∀ᵐ x ∂normalizedCubeMeasure Q, |(η.smul a).value.toFun x| ≤ A* |a| := by
    filter_upwards [hval] with x hx
    simpa only [PlanarW2Infinity.smul, H1Function.smul_toFun, abs_mul, mul_comm] using mul_le_mul_of_nonneg_left hx (abs_nonneg a)
  have hg : ∀ᵐ x ∂normalizedCubeMeasure Q, planarEuclideanNorm (planarW1Value (η.smul a).gradient x) ≤ G* |a| := by
    filter_upwards [hgrad] with x hx
    change planarEuclideanNorm (fun i => a*planarW1Value η.gradient x i) ≤ _
    rw [planarEuclideanNorm_const_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hx (abs_nonneg a)
  have hh : ∀ᵐ x ∂normalizedCubeMeasure Q, planarFrobeniusNorm (planarW1Derivative (η.smul a).gradient x) ≤ H* |a| := by
    filter_upwards [hhess] with x hx
    change planarFrobeniusNorm (fun i j => a*planarW1Derivative η.gradient x i j) ≤ _
    rw [planarFrobeniusNorm_const_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hx (abs_nonneg a)
  have hb := lemmaVH2_row_bound Q j (η.smul a) p u (mul_nonneg hA (abs_nonneg a))
    (mul_nonneg hG (abs_nonneg a)) (mul_nonneg hH (abs_nonneg a)) hv hg hh
  simpa only [lemmaVH2RowConstant_scale, PlanarW2Infinity.smul] using hb

end
end ASDExplicitGamma.Variational
