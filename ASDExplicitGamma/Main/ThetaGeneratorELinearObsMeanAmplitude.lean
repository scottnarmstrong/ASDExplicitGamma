module

public import ASDExplicitGamma.Main.ThetaGeneratorELinearProxyTranslate
public import ASDExplicitGamma.Main.ThetaGeneratorELinearCellExpectation

/-! Annealed payment of the directional mean proxy of an arbitrary source cell
`U` of scale `m-5` inside an arbitrary observer root `Q`, from the cell's own
frame field. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

/-- The directional mean proxy of the cell's own frame field. -/
def mainELinearObsMeanProxy_Th
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q U : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (plus : Bool) (ω : CutoffSample 2) : ℝ :=
  oldSignedFlatDirectionalMeanProxy Q U
    (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
      (mainInsertionSkewCoefficient m t U ω)) b L plus

theorem mainELinearObsMeanProxy_nonneg_Th
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q U : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (plus : Bool) (ω : CutoffSample 2) :
    0 ≤ mainELinearObsMeanProxy_Th M m t Q U b L plus ω := by
  unfold mainELinearObsMeanProxy_Th oldSignedFlatDirectionalMeanProxy
  apply tsum_nonneg
  intro n
  apply Finset.sum_nonneg
  intro i _
  exact (old_signed_directional_proxy_nonneg_le U M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 (mainInsertionSkewCoefficient m t U ω) _).1

theorem main_e_linear_obs_mean_proxy_payment_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (Q : TriadicCube 2) (d : ℕ) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q d) (hscale : U.scale = m - 5)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let xi := mainEnvelopeXi
      ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2)
      M.gamma (theta M * mainSourceInversePrefix) (theta M) t
    Integrable (mainELinearObsMeanProxy_Th M m t Q U b L plus) μ ∧
    (∫ ω, mainELinearObsMeanProxy_Th M m t Q U b L plus ω ∂μ) ≤
      xi / 2 * oldSignedFlatMeanSize Q U b L plus ^ 2 ∧
    Integrable (fun ω => Real.sqrt (mainELinearObsMeanProxy_Th M m t Q U b L plus ω)) μ ∧
    (∫ ω, Real.sqrt (mainELinearObsMeanProxy_Th M m t Q U b L plus ω) ∂μ) ≤
      Real.sqrt (xi / 2) * oldSignedFlatMeanSize Q U b L plus := by
  intro μ xi
  let mu := fun i c => oldSignedBlockMean U (oldSignedFlatInput Q b L plus i c)
  let E : whiteBasisIndex → Fin 2 → Vec 2 :=
    fun i c => if plus then (mu i c).2 else (mu i c).1
  have he (i : whiteBasisIndex) (c : Fin 2) : vecNormSq (E i c) = blockVecDot (mu i c) (mu i c) := by
    cases plus
    · simp [E, mu, oldSignedBlockMean, oldSignedFlatInput, oldSignedFlatMinusBlock,
        cubeAverage_const, blockVecDot, vecDot, vecNormSq]
    · simp [E, mu, oldSignedBlockMean, oldSignedFlatInput, oldSignedFlatPlusBlock,
        cubeAverage_const, blockVecDot, vecDot, vecNormSq]
  have hs : Summable (fun i => ∑ c : Fin 2, vecNormSq (E i c)) := by
    simp_rw [he]
    exact old_signed_flat_mean_budget_series Q d b L plus U hU
  have hpay := main_e_linear_obs_proxy_modes_payment_Th M h hM hγ N hpast m hm t ht U hscale E hs
  have hnorm : oldSignedFlatMeanSize Q U b L plus ^ 2 = ∑' i, ∑ c : Fin 2, vecNormSq (E i c) := by
    simp_rw [he]
    exact Real.sq_sqrt (tsum_nonneg (fun i => Finset.sum_nonneg (fun c _ =>
      add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _))))
  have hfun : mainELinearObsMeanProxy_Th M m t Q U b L plus = fun ω => ∑' i, ∑ c : Fin 2,
      oldSignedDirectionalProxy U (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) (E i c) := by
    funext ω
    unfold mainELinearObsMeanProxy_Th oldSignedFlatDirectionalMeanProxy
    apply tsum_congr
    intro i
    apply Finset.sum_congr rfl
    intro c _
    cases plus <;> rfl
  have hnn := mainELinearObsMeanProxy_nonneg_Th M m t Q U b L plus
  rw [hfun] at hnn ⊢
  have hsq := main_sqrt_expectation_ae_Th μ _ hpay.1 (Filter.Eventually.of_forall hnn)
  rw [← hnorm] at hpay
  refine ⟨hpay.1, hpay.2, hsq.1, hsq.2.trans ?_⟩
  have hx0 : 0 ≤ oldSignedFlatMeanSize Q U b L plus := Real.sqrt_nonneg _
  calc Real.sqrt (∫ ω, ∑' i, ∑ c : Fin 2, oldSignedDirectionalProxy U
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (mainInsertionSkewCoefficient m t U ω)) (E i c) ∂μ)
      ≤ Real.sqrt (xi / 2 * oldSignedFlatMeanSize Q U b L plus ^ 2) := Real.sqrt_le_sqrt hpay.2
    _ = _ := by
      rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hx0]

end

end ASDExplicitGamma.Main
