module

public import ASDExplicitGamma.Native.OldSignedActualDirectionalRare
public import ASDExplicitGamma.Inverse.RareSum

/-! Raw-trace moments on arbitrary descendant source cells, in the fixed
completed frame and the actual partially inserted law. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Inverse Gaussian Cold Algsuperdiff.Section3 Numerics.Inverse
open scoped ENNReal
noncomputable section

/-- Every translated cell at the specified source depth inherits the exact
raw-trace L2 envelope. Translation changes neither the frame nor the law. -/
theorem old_signed_source_cell_trace_L2
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (r j : ℕ) (hr : r ≤ 5)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hstates : ∀ l ≤ n,nativeInductionState M h l)
    (Q : TriadicCube 2) (hQ : Q.scale=n-(r:ℤ)-(j:ℤ)) :
    eLpNorm (rawCubeFourLoadTrace M n Q t) 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M*(invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j)) := by
  have hp := (raw_rare_sum_expansion_source M h hM hg n r hr t ht
    (fun d => hstates _ (by omega))).1 j
  have he : rawTraceTransportBandObservable M n r t j=
      rawDepthFourLoadTrace M n (n-(r:ℤ)-(j:ℤ)) t := by
    funext ω
    rw [rawTraceTransportBandObservable,raw_depth_four_load_trace_eq_model_observable,
      raw_trace_transport_band_scalar_eq_inserted_helper M n r j hr t ht ω]
  rw [he] at hp
  have htrans : rawCubeFourLoadTrace M n Q t =
      rawDepthFourLoadTrace M n (n-(r:ℤ)-(j:ℤ)) t ∘
        (fun ω => triadicCubeShift Q +ᵥ ω) := by
    funext ω
    rw [raw_cube_four_load_trace_eq_translated_origin_helper M n Q t ω,hQ]
    rfl
  have hm : AEStronglyMeasurable (rawDepthFourLoadTrace M n (n-(r:ℤ)-(j:ℤ)) t)
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    (old_signed_trace_sample_integrable M n t ht (originCube 2 (n-(r:ℤ)-(j:ℤ)))
      (Annealed.sigmaBar M n)).aestronglyMeasurable
  rw [htrans,eLpNorm_comp_measurePreserving hm
    (Algsuperdiff.Probability.Stationary.measurePreserving_const_vadd
      (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (triadicCubeShift Q))]
  simpa only [ENNReal.ofReal_ofNat] using hp

/-- The same profile holds for the actual descendant average of any source
cell at an OLD refinement offset. No independence of its descendants is used. -/
theorem old_signed_source_cell_trace_sequence_L2
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (r : ℕ) (hr : r ≤ 5)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hstates : ∀ l ≤ n,nativeInductionState M h l)
    (Q : TriadicCube 2) (hQ : Q.scale=n-(r:ℤ)) (j : ℕ) :
    eLpNorm (fun ω => rawWeakTraceSequence M n Q t ω j) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M*(invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j)) := by
  let I := SquareCells Q j
  let C := theta M*(invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j)
  let d : ℝ := (descendantsAtDepth Q j).card
  have hd : 0<d := by
    dsimp [d]
    exact_mod_cast Finset.card_pos.mpr (descendantsAtDepth_nonempty Q j)
  have htheta : 0 ≤ theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hMrat : 0 ≤ invTraceM := by rw [invTrace_coefficient.1]; positivity
  have hM0 : 0 ≤ (invTraceM:ℝ) := by exact_mod_cast hMrat
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcell (U : I) : eLpNorm (rawCubeFourLoadTrace M n U.val t) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal C := by
    apply old_signed_source_cell_trace_L2 M h hM hg n r j hr t ht hstates U.val
    rw [scale_eq_sub_of_mem_descendantsAtDepth U.property,hQ]
  have hh := finite_density_sum_Lp (Cutoff.cutoffSampleLaw M).toMeasure 2
    (by norm_num) (fun U : I => rawCubeFourLoadTrace M n U.val t)
    (fun _ => d⁻¹) (fun _ => C) (fun _ => inv_nonneg.mpr hd.le) (fun _ => hC) hcell
  have hcard : Fintype.card I=(descendantsAtDepth Q j).card := by simp [I,SquareCells]
  have hsum : (∑ _U : I,d⁻¹*C)=C := by
    simp only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul]
    change d*(d⁻¹*C)=C
    rw [←mul_assoc,mul_inv_cancel₀ hd.ne',one_mul]
  have he : (fun ω => rawWeakTraceSequence M n Q t ω j)=
      (fun ω => ∑ U : I,d⁻¹*rawCubeFourLoadTrace M n U.val t ω) := by
    funext ω
    exact Finset.mul_sum _ _ _
  rw [he]
  rwa [hsum] at hh

end
end ASDExplicitGamma.Native
