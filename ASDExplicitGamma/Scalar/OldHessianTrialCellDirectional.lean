module

public import ASDExplicitGamma.Scalar.OldHessianTrialCellTrace
public import ASDExplicitGamma.Scalar.OldHessianTrialCoarseTraceSeries
public import ASDExplicitGamma.Scalar.OldHessianTrialRestrictedFrame
public import ASDExplicitGamma.Scalar.OldHessianTrialDirectionalTrace
public import ASDExplicitGamma.Native.OldSignedDirectionalProxyCongr

/-! Fine-cell directional laws, uniform before deterministic load weighting. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Literal directional depth trace inside one actual fine source cell. -/
def oldHessianCellDepthDirectional (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2)
    (j : ℕ) (e : Vec 2) (ω : Cutoff.CutoffSample 2) : ℝ :=
  vecDot e (matVecMul (oldSignedPairedDepthMatrix U j
    (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
      (oldHessianOldOpenCoefficient (m+129) m ω))) e)

/-- Uniform physical positivity and full-trace domination on every fine
source cell, without a pathwise half-trace claim. -/
theorem old_hessian_cell_directional_bounds (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 (m+129)) 134)
    (j : ℕ) (e : Vec 2) (ω : Cutoff.CutoffSample 2) :
    0≤oldHessianCellDepthDirectional M m U j e ω ∧
      oldHessianCellDepthDirectional M m U j e ω≤oldHessianCellDepthTrace M m U j ω*vecNormSq e := by
  let Q := originCube 2 (m+129)
  let k := oldHessianOldOpenCoefficient (m+129) m ω
  have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
  let kU := oldSignedCellCoefficient Q U hsub k
  have he := old_signed_cell_frame_coefficient_ae Q U hsub M.nu (Annealed.sigmaBar M m) k
  have hn := old_signed_paired_depth_quadratic_nonneg U j M.nu (Annealed.sigmaBar M m) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 kU e
  have hb := old_signed_directional_depth_trace_bound U j M.nu (Annealed.sigmaBar M m) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 kU e
  dsimp only at hn hb
  rw [old_signed_paired_depth_matrix_congr U j _ _ he] at hn hb
  rw [old_hessian_descendant_trace_congr U j _ _ he,
    old_hessian_restricted_trace_sequence M (m+129) m U hsub] at hb
  exact ⟨hn,hb⟩

/-- Every actual fine-cell directional depth trace has its own exact
half-trace expectation; the cell location is kept throughout the proof. -/
theorem old_hessian_cell_directional_mean (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 (m+129)) 134)
    (j : ℕ) (e : Vec 2) :
    Integrable (oldHessianCellDepthDirectional M m U j e) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,oldHessianCellDepthDirectional M m U j e ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
        (1/2:ℝ)*inSourceMeanActual M m (5+j) 0*vecNormSq e := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let F := fun (V : TriadicCube 2) (ω : Cutoff.CutoffSample 2) => vecDot e
    (matVecMul (oldSignedCoarseDirectionalMatrix V (Model.partialInsertedCoefficient M m 0 ω).toFun
      (Annealed.sigmaBar M m)) e)
  have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
  have hscale : U.scale=m-5 := by
    have hs := scale_eq_sub_of_mem_descendantsAtDepth hU
    change U.scale=m+129-134 at hs
    omega
  have hF (V : TriadicCube 2) : Integrable (F V) μ :=
    old_signed_directional_sample_integrable M m 0 (by norm_num) V (Annealed.sigmaBar M m) e
  have he : oldHessianCellDepthDirectional M m U j e=
      (fun ω => descendantsAverage U j (fun V => F V ω)) := by
    funext ω
    unfold oldHessianCellDepthDirectional
    rw [old_hessian_restricted_physical_directional_matrix M (m+129) m U hsub,
      vecDot_matVecMul_descendantsAverageMat]
  have hi : Integrable (fun ω => descendantsAverage U j (fun V => F V ω)) μ := by
    unfold descendantsAverage
    exact (integrable_finsetSum _ (fun V _ => hF V)).const_mul _
  refine ⟨he.symm ▸ hi,?_⟩
  have hhalf := old_signed_descendant_directional_mean M m U j 0 (by norm_num)
    (Annealed.sigmaBar M m) e
  have htrace : (fun ω => descendantsAverage U j (fun V => traceDefect (cubeSet V)
      (Model.partialInsertedCoefficient M m 0 ω).toFun (Annealed.sigmaBar M m)))=
      oldHessianCellDepthTrace M m U j := by
    funext ω
    change descendantsAverage U j (fun V => rawCubeFourLoadTrace M m V 0 ω)=
      oldSignedCellAverage U j (fun V => rawCubeFourLoadTrace M m V.val 0 ω)
    rw [old_signed_cell_average_eq_descendantsAverage U j (fun V => rawCubeFourLoadTrace M m V 0 ω)]
  have hphys : (∫ ω,oldHessianCellDepthDirectional M m U j e ω ∂μ)=
      (1/2:ℝ)*(∫ ω,oldHessianCellDepthTrace M m U j ω ∂μ)*vecNormSq e := by
    unfold oldHessianCellDepthDirectional
    simp_rw [old_hessian_restricted_physical_directional_matrix M (m+129) m U hsub]
    rw [hhalf,htrace]
  rw [hphys,(old_hessian_cell_depth_trace_mean M m U hscale j).2]

end
end ASDExplicitGamma.Scalar
