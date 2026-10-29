module

public import ASDExplicitGamma.Native.ParentBoundaryBandProfiles
public import ASDExplicitGamma.Native.GenericSourceBandHistory
public import ASDExplicitGamma.Native.OldSignedSourceDepthBank

/-! Actual local inverse depth-block banks for the simultaneous band on
every paid source-cell population. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Scalar Gaussian Main Triadic Variational Inverse
open scoped ENNReal
noncomputable section

/-- The actual depth-block positive remainder on the same band law. -/
def parentBoundaryBandDepthRemainder (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (U : TriadicCube 2) (j : ℕ) : Cutoff.CutoffSample 2 → ℝ :=
  inverseBankDepthBlockRemainder .localInverse (descendantsAtDepth U j)
    M n (n+(height:ℤ)) (fun _ => Real.sqrt t) j

/-- The complete bank applies to every source-cell descendant population,
with the original allowance and no extra moment premise. -/
theorem parent_boundary_band_depth_block_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht : t≤1)
    (r : ℕ) (hr : r≤5) (U : TriadicCube 2) (hU : U.scale=n-(r:ℤ)) (j : ℕ) :
    InverseBankDepthBlockConclusion M .localInverse (descendantsAtDepth U j)
      n (n+(height:ℤ)) (fun _ => Real.sqrt t) j := by
  have hscale : ∀ V∈descendantsAtDepth U j,V.scale≤n-(j:ℤ) ∧ (n-(j:ℤ))-V.scale≤5 := by
    intro V hV
    have hh := scale_eq_sub_of_mem_descendantsAtDepth hV
    rw [hU] at hh
    omega
  have hcard : (descendantsAtDepth U j).card≤6*9^(45+j) := by
    rw [descendantsAtDepth_card,show (3^2:ℕ)=9 by norm_num]
    exact (pow_le_pow_right₀ (by norm_num : (1:ℕ)≤9) (by omega : j≤45+j)).trans (by omega)
  exact inverse_bank_depth_block M h hM hg .localInverse _ n (n+(height:ℤ)) (by omega) _
    (fun _ _ => ⟨Real.sqrt_nonneg t,Real.sqrt_le_one.mpr ht⟩) j hscale hcard hpast
    (bank_inverse_mean_inputs_of_states M h hM hg n hpast).2

/-- A finite physical depth block is exactly the normalized inverse maximum
on the same source cell; all descendants retain sigma_n. -/
theorem parent_boundary_band_cell_depth_max_eq
    (M : ABKModel 2) (n : ℤ) (height r : ℕ) (t : ℝ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 n) r)
    (omega : Cutoff.CutoffSample 2) (j : ℕ) :
    bankFiniteRootResponseMax (descendantsAtDepth U j) M n (n+(height:ℤ))
      (fun _ => Real.sqrt t) omega=
      ENNReal.ofReal (lemmaVInverseDepthMax U (parentBoundaryBandFrameField M n height t omega) j) := by
  let a := parentBoundaryBandFrameField M n height t omega
  have hs := (Annealed.sigmaBar_characterization M n).1
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet (originCube 2 n)) M.nu (Annealed.sigmaBar M n) M.nu_pos hs
    (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t omega))
  have hm := bank_finite_max_ofReal (descendantsAtDepth U j) (descendantsAtDepth_nonempty U j)
    (fun V => rootInverseResponse M V n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)
  change bankFiniteRootResponseMax (descendantsAtDepth U j) M n (n+(height:ℤ))
    (fun _ => Real.sqrt t) omega = _ at hm
  rw [hm]
  apply congrArg ENNReal.ofReal
  unfold lemmaVInverseDepthMax
  apply Book.Ch02.finsetSupReal_congr
  intro V hV
  have hVQ := mem_descendantsAtDepth_add hU hV
  rw [inverse_history_lowerRight V a (hEll.mono (measurableSet_openCubeSet V)
    (openCubeSet_subset_of_mem_descendantsAtDepth hVQ))]
  dsimp only [a,parentBoundaryBandFrameField]
  rw [native_source_band_coarse_matrix_frame M n height t omega hVQ]
  simp only [frameMatrix]
  rw [inverse_history_matrixNorm_smul _ _ hs.le]
  rfl

/-- The actual source-cell inverse maximum has the complete baseline-plus-
rare split, without an inverse bound or finiteness premise. -/
theorem parent_boundary_band_cell_inverse_split
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht : t≤1)
    (r : ℕ) (hr : r≤5) (U : TriadicCube 2)
    (hU : U∈descendantsAtDepth (originCube 2 n) r) (j : ℕ) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      lemmaVInverseDepthMax U (parentBoundaryBandFrameField M n height t omega) j≤
        (inverseBankCap .localInverse:ℝ)*bankDepthFrame M j+
          parentBoundaryBandDepthRemainder M n height t U j omega := by
  have hb := parent_boundary_band_depth_block_bank M h hM hg n height hpast t ht r hr U
    (by simpa only [originCube] using scale_eq_sub_of_mem_descendantsAtDepth hU) j
  have hc : 0≤(inverseBankCap .localInverse:ℝ)*bankDepthFrame M j :=
    mul_nonneg (by norm_num [inverseBankCap]) (bankDepthFrame_pos M j).le
  filter_upwards [hb.block_le] with omega ho
  rw [parent_boundary_band_cell_depth_max_eq M n height r t U hU omega j] at ho
  rw [←ENNReal.ofReal_add hc (hb.remainder_nonneg omega)] at ho
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg hc (hb.remainder_nonneg omega))).mp ho

end
end ASDExplicitGamma.Native
