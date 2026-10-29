module

public import ASDExplicitGamma.Main.ELinearObsPathwise
public import ASDExplicitGamma.Main.ThetaGeneratorELinearObsMeanAmplitude
public import ASDExplicitGamma.Main.ELinearCauchy

/-! Observer-root exact split of the pathwise `L` group majorant into the
leading part (cell frame fields) and the parent-gap weighted part. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

/-- Leading `L`-type part of one cell term, from the cell's own frame field. -/
def mainELinearObsLCellTerm_Th
    (M : ABKModel 2) (m : ℤ) (t b : ℝ) (L : {l : ℝ // 0 < l})
    (Q U : TriadicCube 2) (ω : CutoffSample 2) : ℝ :=
  let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
    (mainInsertionSkewCoefficient m t U ω)
  2 * Real.sqrt (mainELinearObsMeanProxy_Th M m t Q U b L true ω) *
      oldSignedFlatOscillationSize Q U b L true +
    oldSignedInverseHistory U a * oldSignedFlatOscillationSize Q U b L true ^ 2 +
    2 * Real.sqrt (2 * oldSignedCorrectorHistory U a) *
      (oldSignedFlatL2Size Q U b L false * oldSignedFlatOscillationSize Q U b L false) +
    oldSignedResponseHistory U a * oldSignedFlatOscillationSize Q U b L false ^ 2 +
    2 * Real.sqrt 2 * oldSignedDerivativeKappa (cubeScaleFactor U) b L.1 *
      (Real.sqrt (mainELinearObsMeanProxy_Th M m t Q U b L false ω) +
        (Real.sqrt (oldSignedInverseHistory U a * oldSignedResponseHistory U a) + 1) *
          oldSignedFlatOscillationSize Q U b L false)

/-- Parent-gap weighted part of one cell term (half-gain plus constant). -/
def mainELinearObsGCellTerm_Th
    (M : ABKModel 2) (m : ℤ) (t b : ℝ) (L : {l : ℝ // 0 < l})
    (Q U : TriadicCube 2) (ω : CutoffSample 2) : ℝ :=
  let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
    (mainInsertionSkewCoefficient m t U ω)
  let G := oldSignedReciprocalErrorSize Q U M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 (mainELinearObsCoefficient Q m t ω)
  2 * oldSignedDerivativeKappa (cubeScaleFactor U) b L.1 * G *
      (Real.sqrt (mainELinearObsMeanProxy_Th M m t Q U b L true ω) +
        (1 / 2 + inverseHistoryDiscount) * oldSignedInverseHistory U a *
          oldSignedFlatOscillationSize Q U b L true) +
    2 * oldSignedDerivativeKappa (cubeScaleFactor U) b L.1 * G *
      (Real.sqrt (mainELinearObsMeanProxy_Th M m t Q U b L false ω) +
        (Real.sqrt (oldSignedInverseHistory U a * oldSignedResponseHistory U a) + 1) *
          oldSignedFlatOscillationSize Q U b L false)

def mainELinearObsLAverageTerm_Th
    (M : ABKModel 2) (Q : TriadicCube 2) (d : ℕ) (m : ℤ) (t b : ℝ)
    (L : {l : ℝ // 0 < l}) (ω : CutoffSample 2) : ℝ :=
  finAvg (descendantsAtDepth Q d) (fun U => mainELinearObsLCellTerm_Th M m t b L Q U ω)

def mainELinearObsGAverageTerm_Th
    (M : ABKModel 2) (Q : TriadicCube 2) (d : ℕ) (m : ℤ) (t b : ℝ)
    (L : {l : ℝ // 0 < l}) (ω : CutoffSample 2) : ℝ :=
  finAvg (descendantsAtDepth Q d) (fun U => mainELinearObsGCellTerm_Th M m t b L Q U ω)

theorem main_e_linear_obs_group_split_Th
    (M : ABKModel 2) (Q : TriadicCube 2) (d : ℕ) (m : ℤ) (t b : ℝ)
    (L : {l : ℝ // 0 < l}) (ω : CutoffSample 2) :
    mainELinearObsGroup M Q d m t b L ω ≤
      mainELinearObsLAverageTerm_Th M Q d m t b L ω +
        mainELinearObsGAverageTerm_Th M Q d m t b L ω := by
  refine (main_e_linear_obs_group_pathwise_bound M Q d m t b L ω).trans (le_of_eq ?_)
  unfold mainELinearFlatMajorant mainELinearPlusFeedbackHalfGainMajorant
    mainELinearMinusFeedbackMajorant mainELinearObsLAverageTerm_Th mainELinearObsGAverageTerm_Th
  simp only []
  unfold descendantsAverage
  dsimp only
  exact finAvg_split_aux _ _ _ _ _ _ (fun U hU => by
    have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    have hb : oldSignedInverseHistory U (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mainELinearObsCoefficient Q m t ω)) =
        oldSignedInverseHistory U (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) ∧
      oldSignedResponseHistory U (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mainELinearObsCoefficient Q m t ω)) =
        oldSignedResponseHistory U (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) ∧
      oldSignedCorrectorHistory U (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mainELinearObsCoefficient Q m t ω)) =
        oldSignedCorrectorHistory U (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) :=
      main_e_linear_obs_histories_bridge M Q m t ω U hsub
    have hp : ∀ e, oldSignedDirectionalProxy U (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mainELinearObsCoefficient Q m t ω)) e =
        oldSignedDirectionalProxy U (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) e :=
      fun e => main_e_linear_obs_proxy_bridge M Q m t ω U hsub e
    have hpr (plus : Bool) : oldSignedFlatDirectionalMeanProxy Q U
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mainELinearObsCoefficient Q m t ω)) b L plus =
        oldSignedFlatDirectionalMeanProxy Q U (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) b L plus := by
      unfold oldSignedFlatDirectionalMeanProxy
      simp only [hp]
    unfold mainELinearObsLCellTerm_Th mainELinearObsGCellTerm_Th mainELinearObsMeanProxy_Th
    obtain ⟨h1, h2, h3⟩ := hb
    simp only [hpr, h1, h2, h3]
    ring)

end

end ASDExplicitGamma.Main
