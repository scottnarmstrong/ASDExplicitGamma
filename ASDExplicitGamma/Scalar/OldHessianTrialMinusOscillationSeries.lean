module

public import ASDExplicitGamma.Scalar.OldHessianTrialMinusOscillation
public import ASDExplicitGamma.Native.OldSignedSpatialSeriesBound
public import ASDExplicitGamma.Scalar.OldHessianTrialFlatHistoryMoments
public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedHistoryAdapter

/-! Complete physical minus oscillation receiver energies, before expectation. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- All original white modes and both loads of the centered reciprocal
receiver converge on each cell, with constant-one joint oscillation cost. -/
theorem old_hessian_minus_oscillation_cell_series (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (U : OldSignedCellIndex Q fine) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let E := fun p => vectorWeakHaarEnergy U.val
      (oldHessianMinusOscillationColumn Q fine nu sigma hnu hsigma k b L p U)
    Summable E ∧ (∑' p,E p)≤(oldSignedInverseHistory U.val a*oldSignedResponseHistory U.val a)*
      oldSignedFlatOscillationSize Q U.val b L false^2 := by
  intro a E
  let V := fun p : whiteBasisIndex×Fin 2 => oldSignedBlockPositiveNorm U.val
    (fun x => oldSignedFlatInput Q b L false p.1 p.2 x-
      oldSignedBlockMean U.val (oldSignedFlatInput Q b L false p.1 p.2))^2
  have hVs : Summable V := (summable_prod_of_nonneg (fun _ => sq_nonneg _)).2
    ⟨fun _ => Summable.of_finite,by
      simpa only [V,tsum_fintype,Pi.sub_def] using
        old_signed_flat_oscillation_budget_series Q fine b L false U.val U.property⟩
  have hv : (∑' p,V p)=oldSignedFlatOscillationSize Q U.val b L false^2 := by
    rw [oldSignedFlatOscillationSize,Real.sq_sqrt
      (tsum_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))]
    rw [hVs.tsum_prod]
    simp only [V,tsum_fintype,Pi.sub_def]
  have hB : 0≤oldSignedInverseHistory U.val a :=
    lemmaVInverseHistory_nonneg U.val a (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hC : 0≤oldSignedInverseHistory U.val a*oldSignedResponseHistory U.val a :=
    mul_nonneg hB ENNReal.toReal_nonneg
  have hs := hVs.mul_left (oldSignedInverseHistory U.val a*oldSignedResponseHistory U.val a)
  have he p : E p≤(oldSignedInverseHistory U.val a*oldSignedResponseHistory U.val a)*V p :=
    old_hessian_minus_oscillation_column_energy Q fine nu sigma hnu hsigma k b L p U
  have hEs := hs.of_nonneg_of_le (fun _ => vectorWeakHaarEnergy_nonneg _ _) he
  refine ⟨hEs,(hEs.tsum_le_tsum he hs).trans_eq ?_⟩
  rw [tsum_mul_left,hv]

/-- Complete spatial receiver energy on the unchanged fine partition. -/
def oldHessianMinusOscillationSpatialEnergy (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (p : whiteBasisIndex×Fin 2) : ℝ :=
  oldSignedCellAverage Q fine (fun U => vectorWeakHaarEnergy U.val
    (oldHessianMinusOscillationColumn Q fine nu sigma hnu hsigma k b L p U))

/-- The actual correlated grouped bank and cell matrix history bound every
mode of the literal physical reciprocal oscillation receiver. -/
theorem old_hessian_actual_minus_oscillation_series
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let E := oldHessianMinusOscillationSpatialEnergy (originCube 2 (m+129)) 134
        M.nu (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1
        (oldHessianOldOpenCoefficient (m+129) m ω) b L
      Summable E ∧ (∑' p,E p)≤oldHessianGroupedBank M m ω*oldHessianFlatMatrixEnergy M m b L ω := by
  filter_upwards [old_hessian_actual_fine_histories_le_bank M h hM hg N hpast m hm] with ω hω
  let Q := originCube 2 (m+129)
  let k := oldHessianOldOpenCoefficient (m+129) m ω
  let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m) k
  have hglobal := hω 5 (by norm_num)
  have hc (U : OldSignedCellIndex Q 134) := old_hessian_minus_oscillation_cell_series Q 134
    M.nu (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1 k b L U
  have hb (U : OldSignedCellIndex Q 134) : oldSignedInverseHistory U.val a≤oldHessianGroupedBank M m ω :=
    (old_hessian_fine_history_le Q 134 M.nu (Annealed.sigmaBar M m) k U.val U.property).trans hglobal
  have hcell (U : OldSignedCellIndex Q 134) := old_hessian_cell_matrix_history_bounds M m U.val ω
  have hh := old_signed_cell_average_series_upper Q 134
    (fun p U => vectorWeakHaarEnergy U.val (oldHessianMinusOscillationColumn Q 134
      M.nu (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1 k b L p U))
    (fun U => (oldSignedInverseHistory U.val a*oldSignedResponseHistory U.val a)*
      oldSignedFlatOscillationSize Q U.val b L false^2) (fun U => (hc U).1) (fun U => (hc U).2)
  refine ⟨hh.1,hh.2.trans ?_⟩
  change _≤oldHessianGroupedBank M m ω*oldSignedCellAverage Q 134 _
  rw [←old_signed_cell_average_mul]
  apply old_signed_cell_average_mono
  intro U
  have hp := mul_le_mul (hb U) (hcell U).1 ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  exact (mul_le_mul_of_nonneg_right hp (sq_nonneg _)).trans_eq (mul_assoc _ _ _)

end
end ASDExplicitGamma.Scalar
