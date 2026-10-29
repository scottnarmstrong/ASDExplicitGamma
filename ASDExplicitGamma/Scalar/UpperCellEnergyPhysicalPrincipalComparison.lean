module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalAllEvent
public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalPrincipalGauge
public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalIndependence

/-! The all-event comparison inserted at the actual random principal load. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Variational Algsuperdiff.Section3
noncomputable section

/-- Exact normalized physical OLD matrix in the true scalar frame. -/
theorem upper_cell_physical_old_framed_matrix
    (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    coarseBlockMatrix (openCubeSet Q)
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n:ℝ)
        (oldCutoffSkewCoefficient n Q ω)) =
      frameMatrix (Annealed.sigmaBar M n:ℝ) (coarseBlockMatrix (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu n ω).toFun) := by
  rw [upper_cell_physical_old_coarse_matrix]
  obtain ⟨Lam,hEll⟩ := cutoff_isEllipticFieldOn_cube M n ω Q
  exact Cold.cold_coarse_frame M.nu_pos hEll (Annealed.sigmaBar M n).property

/-- The scalar magnitude is exactly the squared block-load norm. -/
theorem upper_cell_physical_load_magnitude_sq
    (M : ABKModel 2) (n terminal : ℤ) (c : ℝ) {e : Vec 2}
    (he : Book.Ch02.vecNorm e = 1) (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    (upperCellPhysicalLoadMagnitude M n terminal c e Q ω)^2 =
    blockVecDot (e,upperCellPhysicalPotentialMean M n terminal c e Q ω)
      (e,upperCellPhysicalPotentialMean M n terminal c e Q ω) := by
  have he2 : vecDot e e = 1 := by
    have hh := Book.Ch02.vecNorm_sq_eq_vecNormSq e
    rw [he] at hh
    simpa only [one_pow,vecNormSq] using hh.symm
  rw [upperCellPhysicalLoadMagnitude,Real.sq_sqrt (by positivity)]
  change _ = vecDot e e + _
  rw [he2]
  simp only [vecDot,pow_two]

/-- The measurable principal energy is bounded by the actual OLD quadratic
plus the literal sensitivity integrand. Only the defining physical load
representation is a premise; the comparison has no estimate assumption. -/
theorem upper_cell_physical_principal_comparison
    (M : ABKModel 2) (n : ℤ) (height : ℕ) {e : Vec 2} (he : Book.Ch02.vecNorm e = 1)
    (F : Cutoff.CutoffSample 2 → HilbertBlockL2 (openCubeSet (originCube 2 (n-14))))
    (hF : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∃ hω : MemBlockL2 (openCubeSet (originCube 2 (n-14)))
        (bandLoad M n (n+height) (Annealed.sigmaBar M n:ℝ) e ω),
        F ω = toHilbertBlockL2OfBlockField hω) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let Q := originCube 2 (n-14)
      let sigma := (Annealed.sigmaBar M n:ℝ)
      let k := oldCutoffSkewCoefficient (n+height) Q ω
      let B := (scalarFrameRealization Q M.nu sigma M.nu_pos (Annealed.sigmaBar M n).property k).energyBilin
      let S := scalarProjectionResidual Q M.nu sigma M.nu_pos (Annealed.sigmaBar M n).property k
        (upperCellResetMeanField Q (F ω))
      let P := (e,upperCellPhysicalPotentialMean M n (n+height) sigma⁻¹ e Q ω)
      let A := 1+2*(lagTraceHistory M n 14 ω).toReal+Real.sqrt (2*(lagTraceHistory M n 14 ω).toReal)
      let D := upperCellPhysicalEnvelope M n height (cubeCenter Q) ω
      let L := upperCellPhysicalLoadMagnitude M n (n+height) sigma⁻¹ e Q ω
      B S S ≤ blockVecDot P (blockMatVecMul (frameMatrix sigma
        (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun)) P)+
        6*A^2*D*(1+2*D+4*D^2)*L^2 := by
  filter_upwards [upper_cell_physical_principal_gauge M n (n+height)
    (Annealed.sigmaBar M n:ℝ) (Annealed.sigmaBar M n).property e (originCube 2 (n-14)) F hF] with ω hg
  dsimp only at hg ⊢
  rw [hg,upper_cell_physical_load_magnitude_sq M n (n+height) _ he]
  have hc := upper_cell_physical_all_event_comparison M n 14 height ω
    (e,upperCellPhysicalPotentialMean M n (n+height) (Annealed.sigmaBar M n:ℝ)⁻¹ e
      (originCube 2 (n-14)) ω)
  dsimp only at hc
  rw [upper_cell_physical_old_framed_matrix] at hc
  exact hc

end
end ASDExplicitGamma.Scalar
