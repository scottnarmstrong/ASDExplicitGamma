module

public import ASDExplicitGamma.Scalar.OldHessianTrialMinusAffineReceiver
public import ASDExplicitGamma.Scalar.OldHessianTrialCellDirectionalJoin
public import ASDExplicitGamma.Scalar.OldHessianTrialMinusMeanBank
public import ASDExplicitGamma.Scalar.OldHessianTrialCellSeriesExtraction
public import ASDExplicitGamma.Native.OldSignedFlatDirectionalProxy

/-! Actual original minus affine proxy, with deterministic varying loads retained. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The actual mean-field proxy used in the original minus feedback is
below the same complete uniform-load envelope paid by Xi/2. -/
theorem old_hessian_actual_minus_directional_proxy
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      oldSignedCellAverage (originCube 2 (m+129)) 134 (fun U => oldSignedFlatDirectionalMeanProxy
        (originCube 2 (m+129)) U.val (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
          (oldHessianOldOpenCoefficient (m+129) m ω)) b L false)≤
        oldHessianMinusAffineReceiverEnvelope M m b L ω := by
  let Q := originCube 2 (m+129)
  let q := oldHessianMinusMeanColumn Q 134 b L
  let θ := fun (p : whiteBasisIndex×Fin 2) (U : OldSignedCellIndex Q 134) ω =>
    oldHessianCellDirectionalTheta M m U.val (q p U) ω
  have hbank := old_hessian_minus_mean_bank Q 134 b L
  have hs := old_hessian_cell_directional_weighted_series M h hM hg N hpast m hm q hbank.1
  have hall := ae_all_iff.mpr (fun p : whiteBasisIndex×Fin 2 => ae_all_iff.mpr
    (fun U : OldSignedCellIndex Q 134 => old_hessian_actual_cell_directional_proxy_join M h hM hg N hpast m hm U.val U.property (q p U)))
  filter_upwards [hs.1,hall] with ω hsum hω
  let k := oldHessianOldOpenCoefficient (m+129) m ω
  let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m) k
  let P := fun (p : whiteBasisIndex×Fin 2) (U : OldSignedCellIndex Q 134) => oldSignedDirectionalProxy U.val
    (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
      (oldSignedCellCoefficient Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)) (q p U)
  have hn p U : 0≤θ p U ω := old_hessian_cell_directional_theta_nonneg M m U.val U.property _ ω
  have hθcell U : Summable (fun p => θ p U ω) :=
    old_hessian_cell_series_of_average Q 134 (fun p U => θ p U ω) hn hsum U
  have hP0 p U : 0≤P p U := (old_signed_directional_proxy_nonneg_le U.val M.nu (Annealed.sigmaBar M m)
    M.nu_pos (Annealed.sigmaBar_characterization M m).1 _ (q p U)).1
  have hPcell U : Summable (fun p => P p U) := (hθcell U).of_nonneg_of_le (fun p => hP0 p U) (fun p => hω p U)
  have hcap (U : OldSignedCellIndex Q 134) : oldSignedFlatDirectionalMeanProxy Q U.val a b L false≤∑' p,θ p U ω := by
    rw [←old_signed_flat_directional_proxy_cell_eq Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property) M.nu (Annealed.sigmaBar M m) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 k b L false]
    have he : oldSignedFlatDirectionalMeanProxy Q U.val
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
          (oldSignedCellCoefficient Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)) b L false=∑' p,P p U := by
      rw [(hPcell U).tsum_prod]
      simp only [tsum_fintype,oldSignedFlatDirectionalMeanProxy,oldSignedFlatInput,Bool.false_eq_true,ite_false,P,q,oldHessianMinusMeanColumn]
    rw [he]
    exact (hPcell U).tsum_le_tsum (fun p => hω p U) (hθcell U)
  have hh := old_signed_cell_average_mono Q 134 hcap
  exact hh.trans_eq (old_signed_cell_average_series Q 134 (fun p U => θ p U ω) hθcell).2.symm

end
end ASDExplicitGamma.Scalar
