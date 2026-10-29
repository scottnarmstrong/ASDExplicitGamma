module

public import ASDExplicitGamma.Native.OldSignedRemainderCovarianceVector
public import ASDExplicitGamma.Native.OldSignedRowProductMembership

/-! Actual cellwise L2 and positive-Haar membership of the complete
covariance fields. All fields retain their parent boundary problems. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

/-- Restricting the actual parent kernel gives all scalar covariance
membership needed for the exact cellwise weak/positive pairing. -/
theorem old_signed_scalar_covariance_cell_membership (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q) (b : ℝ) (L : {l : ℝ // 0 < l})
    (plus : Bool) (a : Fin 2 × Fin 2) :
    MemLp (oldSignedRemainderScalarCovariance Q b L plus a) 2 (normalizedCubeMeasure U) ∧
    Summable (fun k => (Real.sqrt 3)^(k+1)*energy U
      (cubeIncrement U (k+1) (oldSignedRemainderScalarCovariance Q b L plus a))) :=
  old_signed_row_h1_product_membership U _ (old_signed_white_section_contDiff b L)
    ((oldSignedRemainderKernel Q b L plus a).restrict hU (isOpen_openCubeSet Q).measurableSet)

/-- Both rotated covariance coordinates are genuinely L2 and positive
Haar on each cell, with no summability premise hidden in beta. -/
theorem old_signed_covariance_cell_membership (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q) (b : ℝ) (L : {l : ℝ // 0 < l})
    (plus : Bool) (i k : Fin 2) :
    MemLp (fun x => oldSignedRemainderCovarianceField Q b L plus i x k) 2 (normalizedCubeMeasure U) ∧
    Summable (fun j => (Real.sqrt 3)^(j+1)*energy U
      (cubeIncrement U (j+1) (fun x => oldSignedRemainderCovarianceField Q b L plus i x k))) := by
  fin_cases k
  · have hs := old_signed_scalar_covariance_cell_membership Q U hU b L plus (i,1)
    have hn : MemLp (fun x => -oldSignedRemainderScalarCovariance Q b L plus (i,1) x)
        2 (normalizedCubeMeasure U) ∧
        Summable (fun j => (Real.sqrt 3)^(j+1)*energy U (cubeIncrement U (j+1)
          (fun x => -oldSignedRemainderScalarCovariance Q b L plus (i,1) x))) := by
      refine ⟨hs.1.neg,?_⟩
      simp_rw [cubeIncrement_neg,energy_neg]
      exact hs.2
    simpa [oldSignedRemainderCovarianceField,planarQuarterTurn] using hn
  · simpa [oldSignedRemainderCovarianceField,planarQuarterTurn] using
      old_signed_scalar_covariance_cell_membership Q U hU b L plus (i,0)

end
end ASDExplicitGamma.Native
