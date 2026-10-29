module

public import ASDExplicitGamma.Inverse.AssemblyMeanOscillation

/-! Actual good-parent derivative gates discharge all contained-cube mean caps. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Triadic ASDExplicitGamma.Gaussian ASDExplicitGamma.Variational
open Algsuperdiff.Section3.Provider Algsuperdiff.Section3.Provider.Multiscale
open scoped ENNReal
noncomputable section

/-- Every descendant's normalized wave average differs from its parent's
by at most twice the actual derivative gate. -/
theorem assembly_good_parent_descendant_mean_bound (M : ABKModel 2)
    {Q R : TriadicCube 2} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    (m J : ℤ) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M resetAllOrderTau (waveGateEta .allOrder) Q) :
    let n := Q.scale+40
    let h := laterBandW2 Q n J (sourceBandWeights m weights) ω
    let σ := (Annealed.sigmaBar M n:ℝ)
    |cubeAverage R (h.restrict hR).value.toFun/σ| ≤
      |cubeAverage Q h.value.toFun/σ|+2*(10*waveGateEta .allOrder) := by
  dsimp only
  let n := Q.scale+40
  let h := laterBandW2 Q n J (sourceBandWeights m weights) ω
  let σ := (Annealed.sigmaBar M n:ℝ)
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M n).1
  have hdiff := assembly_descendant_mean_difference Q h hR
  have hD := good_cell_later_band_Dsharp M Q resetAllOrderTau (waveGateEta .allOrder)
    (wave_gate_eta_pos .allOrder).le ω hgood J (sourceBandWeights m weights)
    (source_band_weights_bounds n m J weights hw)
  have havg : |cubeAverage R (h.restrict hR).value.toFun| ≤
      |cubeAverage Q h.value.toFun|+2*(σ*(10*waveGateEta .allOrder)) := by
    calc
      _ = |cubeAverage Q h.value.toFun+
          (cubeAverage R (h.restrict hR).value.toFun-cubeAverage Q h.value.toFun)| := by
        congr 1
        ring
      _ ≤ |cubeAverage Q h.value.toFun|+
          |cubeAverage R (h.restrict hR).value.toFun-cubeAverage Q h.value.toFun| := abs_add_le _ _
      _ ≤ _ := add_le_add le_rfl (hdiff.trans (mul_le_mul_of_nonneg_left hD (by norm_num)))
  rw [abs_div,abs_div,abs_of_pos hσ]
  apply (div_le_div_of_nonneg_right havg hσ.le).trans_eq
  field_simp
  ring

/-- The active simplex cap with every contained-cube mean premise
supplied by the actual good-parent derivative event. -/
theorem assembly_active_triangle_trace_parent_mean (M : ABKModel 2)
    {Q U : TriadicCube 2} {a : ℕ} (hU : U ∈ descendantsAtDepth Q a) (ha : a ≤ 2)
    (pi : Equiv.Perm (Fin 2)) (m J : ℤ) (hn : Q.scale+40 ≤ m) (hm : m ≤ J)
    (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M resetAllOrderTau (waveGateEta .allOrder) Q) :
    let n := Q.scale+40
    let σ := (Annealed.sigmaBar M n:ℝ)
    let h := laterBandW2 Q n J (sourceBandWeights m weights) ω
    let W := |cubeAverage Q h.value.toFun/σ|+2*(10*waveGateEta .allOrder)
    ENNReal.ofReal (Matrix.trace (toFullBlockMat (frameMatrix σ
      (coarseBlockMatrix (Whitney.KuhnCell.mk U pi).openCarrier
        (attenuatedCoefficient M m J weights ω))))/4) ≤
      ENNReal.ofReal (2*rootAssemblySensitivity*(1+W^2)*(1+2*Real.sqrt 3*resetAllOrderTau)) := by
  dsimp only
  apply assembly_active_triangle_trace_of_uniform_mean M hU ha pi m J hn hm weights hw ω hgood
  · exact add_nonneg (abs_nonneg _) (mul_nonneg (by norm_num)
      (mul_nonneg (by norm_num) (wave_gate_eta_pos .allOrder).le))
  · intro P
    exact assembly_good_parent_descendant_mean_bound M
      (triangle_root_cube_descendant_of_parent hU pi P) m J weights hw ω hgood

/-- A good parent's mean-square payment is bounded at almost every physical
point by the same actual later band, enabling the spatial density charge. -/
theorem assembly_good_parent_pointwise_mean_payment (M : ABKModel 2)
    (Q : TriadicCube 2) (m J : ℤ) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M resetAllOrderTau (waveGateEta .allOrder) Q) :
    let n := Q.scale+40
    let h := laterBandW2 Q n J (sourceBandWeights m weights) ω
    let σ := (Annealed.sigmaBar M n:ℝ)
    let δ := 10*waveGateEta .allOrder
    ∀ᵐ x ∂normalizedCubeMeasure Q,
      1+(|cubeAverage Q h.value.toFun/σ|+2*δ)^2 ≤
        1+32*δ^2+2*(h.value.toFun x/σ)^2 := by
  dsimp only
  let n := Q.scale+40
  let h := laterBandW2 Q n J (sourceBandWeights m weights) ω
  let σ := (Annealed.sigmaBar M n:ℝ)
  let δ := 10*waveGateEta .allOrder
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M n).1
  have hδ : 0 ≤ δ := mul_nonneg (by norm_num) (wave_gate_eta_pos .allOrder).le
  have hD := good_cell_later_band_Dsharp M Q resetAllOrderTau (waveGateEta .allOrder)
    (wave_gate_eta_pos .allOrder).le ω hgood J (sourceBandWeights m weights)
    (source_band_weights_bounds n m J weights hw)
  filter_upwards [assembly_parent_mean_oscillation Q h] with x hx
  have hx' : |h.value.toFun x-cubeAverage Q h.value.toFun| ≤ 2*(σ*δ) :=
    hx.trans (mul_le_mul_of_nonneg_left hD (by norm_num))
  have hμ : |cubeAverage Q h.value.toFun| ≤ |h.value.toFun x|+2*(σ*δ) := by
    calc
      _ = |h.value.toFun x-(h.value.toFun x-cubeAverage Q h.value.toFun)| := by congr 1; ring
      _ ≤ |h.value.toFun x|+|h.value.toFun x-cubeAverage Q h.value.toFun| := abs_sub _ _
      _ ≤ _ := add_le_add le_rfl hx'
  have hμ' : |cubeAverage Q h.value.toFun/σ| ≤ |h.value.toFun x/σ|+2*δ := by
    rw [abs_div,abs_div,abs_of_pos hσ]
    apply (div_le_div_of_nonneg_right hμ hσ.le).trans_eq
    field_simp
  have hW : |cubeAverage Q h.value.toFun/σ|+2*δ ≤ |h.value.toFun x/σ|+4*δ := by
    linarith only [hμ']
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ |cubeAverage Q h.value.toFun/σ|+2*δ) hW 2
  have habs : |h.value.toFun x/σ|^2=(h.value.toFun x/σ)^2 := sq_abs _
  have hh := sq_nonneg (|h.value.toFun x/σ|-4*δ)
  dsimp only [δ,h,σ,n] at hs hh habs ⊢
  nlinarith only [hs,hh,habs]

end
end ASDExplicitGamma.Inverse
