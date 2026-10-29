module

public import ASDExplicitGamma.Native.ParentBoundaryCommonCenterHilbertSeries

/-! The complete physical-frame common-center Hilbert--Schmidt coefficient. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Model Response Triadic Variational Scalar Inverse
open scoped BigOperators
noncomputable section

/-- The source A-column coefficient: value uses the common parent radius,
while derivative columns use the actual observation mesh. -/
def parentBoundaryCommonRowCoefficient (P Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (j : ℕ) : ℝ :=
  Real.sqrt (b^2*((78/5:ℝ)/2)*(cubeScaleFactor P/L.val)^2) +
    diagMeshRadius Q j*(36/25)*Real.sqrt ((156/5)*b^2/L.val^2) +
    (diagMeshRadius Q j)^2*(57/200)*Real.sqrt ((46488/25)*b^2/L.val^4)

/-- Every actual covariance row scales quadratically with the inverse
starting frame, including the whole spatial average. -/
theorem parent_boundary_common_row_energy_scale
    (P Q : TriadicCube 2) (b σ : ℝ) (L : {l : ℝ // 0 < l}) (m : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet Q)) (l : whiteBasisIndex) :
    parentBoundaryCommonRowEnergy P Q b σ L m p u l =
      (σ⁻¹)^2*parentBoundaryCommonRowEnergy P Q b 1 L m p u l := by
  have hη : parentBoundaryCommonBasisMultiplier P Q b σ L l =
      (σ⁻¹:ℝ) • parentBoundaryCommonBasisMultiplier P Q b 1 L l := by
    simp [parentBoundaryCommonBasisMultiplier]
  unfold parentBoundaryCommonRowEnergy
  simp only [hη,pureFluxPlanarRowField_smul]
  have he (U : TriadicCube 2) (v : H1Function (openCubeSet Q)) :
      vectorPositiveHaarEnergy U (fun x => σ⁻¹ • lemmaVPlanarRowField (diagInterpolant Q m)
        (parentBoundaryCommonBasisMultiplier P Q b 1 L l) v x) =
      (σ⁻¹)^2*vectorPositiveHaarEnergy U (lemmaVPlanarRowField (diagInterpolant Q m)
        (parentBoundaryCommonBasisMultiplier P Q b 1 L l) v) := by
    unfold vectorPositiveHaarEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [Pi.smul_apply,smul_eq_mul] using sensitivity_primalEnergy_smul U (Real.sqrt 3)
      (fun x => lemmaVPlanarRowField (diagInterpolant Q m)
        (parentBoundaryCommonBasisMultiplier P Q b 1 L l) v x i) σ⁻¹
  simp_rw [he]
  exact descendantsAverage_mul_left _ _ _ _

/-- The full covariance basis is summable and has the exact common-center
Hilbert--Schmidt source coefficient. No finite-cutoff covariance surrogate is
substituted for the complete positive Haar and covariance sums. -/
theorem parent_boundary_common_row_trace_bound
    (P Q : TriadicCube 2) (hQP : cubeSet Q ⊆ cubeSet P) (b σ : ℝ)
    (L : {l : ℝ // 0 < l}) (m : ℕ) (p : Vec 2) (u : H10Function (openCubeSet Q)) :
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    Summable (parentBoundaryCommonRowEnergy P Q b σ L m p u) ∧
      Real.sqrt (∑' l,parentBoundaryCommonRowEnergy P Q b σ L m p u l) ≤
        |σ⁻¹| *parentBoundaryCommonRowCoefficient P Q b L m*
          Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) := by
  intro v
  let R := parentBoundaryCommonRowEnergy P Q b σ L m p u
  let C := |σ⁻¹| *parentBoundaryCommonRowCoefficient P Q b L m*
    Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad)
  have hcoef : 0 ≤ parentBoundaryCommonRowCoefficient P Q b L m := by
    have hm := (diagMeshRadius_pos Q m).le
    dsimp [parentBoundaryCommonRowCoefficient]
    positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hR (l : whiteBasisIndex) : 0 ≤ R l := by
    unfold R parentBoundaryCommonRowEnergy descendantsAverage
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun U hU => vectorPositiveHaarEnergy_nonneg U _)
  have hfinite (s : Finset whiteBasisIndex) : ∑ l ∈ s,R l ≤ C^2 := by
    have hs : (∑ l ∈ s,R l)=(σ⁻¹)^2*∑ l ∈ s,parentBoundaryCommonRowEnergy P Q b 1 L m p u l := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun l hl => parent_boundary_common_row_energy_scale P Q b σ L m p u l)
    have hbase := parent_boundary_common_hilbert_trace_finset P Q hQP b L m p u s
    have hroot : Real.sqrt (∑ l ∈ s,R l) ≤ C := by
      rw [hs,Real.sqrt_mul (sq_nonneg (σ⁻¹)),Real.sqrt_sq_eq_abs]
      exact (mul_le_mul_of_nonneg_left hbase (abs_nonneg (σ⁻¹))).trans_eq (by
        dsimp [C,parentBoundaryCommonRowCoefficient]
        ring)
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 2
    rw [Real.sq_sqrt (Finset.sum_nonneg fun l hl => hR l)] at hsq
    exact hsq
  have hsum : Summable R := summable_of_sum_le hR hfinite
  have htotal : ∑' l,R l ≤ C^2 := Real.tsum_le_of_sum_le hR hfinite
  exact ⟨hsum,Real.sqrt_le_iff.mpr ⟨hC,htotal⟩⟩

end
end ASDExplicitGamma.Native
