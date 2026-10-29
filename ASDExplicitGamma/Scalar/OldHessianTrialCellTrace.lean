module

public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalTraceMoments
public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedThetaTrace
public import ASDExplicitGamma.Scalar.OldHessianTrialWeakRareBudget

/-! Uniform actual trace laws on every fine source cell, before weighting. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Actual depth trace on an arbitrary source cell, retaining its location. -/
def oldHessianCellDepthTrace (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2) (j : ℕ)
    (ω : Cutoff.CutoffSample 2) : ℝ := rawWeakTraceSequence M m U 0 ω j

/-- Every fine cell has the same exact completed source mean at each
additional depth, with integrability proved by the actual trace law. -/
theorem old_hessian_cell_depth_trace_mean (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (hU : U.scale=m-5) (j : ℕ) :
    Integrable (oldHessianCellDepthTrace M m U j) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,oldHessianCellDepthTrace M m U j ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
        inSourceMeanActual M m (5+j) 0 := by
  refine ⟨old_signed_source_trace_integrable M m U 0 (by norm_num) j,?_⟩
  unfold oldHessianCellDepthTrace
  rw [old_signed_source_trace_mean_eq_depth M m U 0 (by norm_num) j,hU]
  have hs : m-5-(j:ℤ)=m-((5+j:ℕ):ℤ) := by omega
  rw [hs,inSourceMeanActual,modelTraceHeatAverage]
  rfl

/-- Uniform L2 profile for the trace on each actual fine source cell. It
is available before a deterministic cell weight is introduced. -/
theorem old_hessian_cell_depth_trace_profile
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N)
    (U : TriadicCube 2) (hU : U.scale=m-5) (j : ℕ) :
    eLpNorm (oldHessianCellDepthTrace M m U j) 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (rawWeakTraceProfileEnvelope M j) := by
  let I := SquareCells U j
  let C := rawWeakTraceProfileEnvelope M j
  let d : ℝ := (descendantsAtDepth U j).card
  have hd : 0<d := by
    dsimp [d]
    exact_mod_cast Finset.card_pos.mpr (descendantsAtDepth_nonempty U j)
  have hC : 0≤C := old_hessian_raw_profile_nonneg M j
  have hcell (V : I) : eLpNorm (rawCubeFourLoadTrace M m V.val 0) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal C := by
    apply old_signed_source_cell_trace_L2 M h hM hg m 5 j (by norm_num) 0 (by norm_num)
      (fun l hl => hpast l (hl.trans_lt hm)) V.val
    have hs := scale_eq_sub_of_mem_descendantsAtDepth V.property
    rw [hU] at hs
    omega
  have hh := finite_density_sum_Lp (Cutoff.cutoffSampleLaw M).toMeasure 2
    (by norm_num) (fun V : I => rawCubeFourLoadTrace M m V.val 0)
    (fun _ => d⁻¹) (fun _ => C) (fun _ => inv_nonneg.mpr hd.le) (fun _ => hC) hcell
  have hcard : Fintype.card I=(descendantsAtDepth U j).card := by simp [I,SquareCells]
  have hsum : (∑ _V : I,d⁻¹*C)=C := by
    simp only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul]
    change d*(d⁻¹*C)=C
    rw [←mul_assoc,mul_inv_cancel₀ hd.ne',one_mul]
  have he : oldHessianCellDepthTrace M m U j=
      (fun ω => ∑ V : I,d⁻¹*rawCubeFourLoadTrace M m V.val 0 ω) := by
    funext ω
    exact Finset.mul_sum _ _ _
  rw [he]
  rwa [hsum] at hh

end
end ASDExplicitGamma.Scalar
