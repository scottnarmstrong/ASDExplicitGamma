module

public import ASDExplicitGamma.Gaussian.WaveGateElementaryTail
public import ASDExplicitGamma.Gaussian.WaveGateUnionCost

/-! The actual enlarged finite wave-failure event on the original shell sequence law. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory
noncomputable section

/-- Four fine-block corners, the full planar buffer volume, and precisely the
parent plus two generations. Centers may be any deterministic translates. -/
abbrev WavePlanarElementaryIndex :=
  Fin 4 × ((Fin (3^40) × Fin (3^40)) × (Fin 1 ⊕ (Fin 9 ⊕ Fin 81)))

/-- The geometry has exactly the source number of elementary events. -/
theorem wave_planar_elementary_card : Fintype.card WavePlanarElementaryIndex = wavePlanarEventCount := by
  norm_num [WavePlanarElementaryIndex,wavePlanarEventCount]

/-- The enlarged event is the literal union of derivative threshold failures,
all at the same fresh shell and in the same old buffered true frame. -/
def waveGateEnlargedFailure (M : ABKModel 2) (j Λ : ℤ) (η : ℝ)
    (c : WavePlanarElementaryIndex → Vec 2) (s : WavePlanarElementaryIndex → ℝ) :
    Set (ℤ → ShellField 2) :=
  {F | ∃ i, η*(3:ℝ)^(-(Λ:ℝ)/8) <
    waveGateDerivativeSize (c i) (s i) (Annealed.sigmaBar M (j+40):ℝ) (F (j+40+Λ))}

/-- No event measurability is smuggled into the marginal transfer: the general
outer-measure map inequality suffices on the original probability space. -/
theorem wave_shell_preimage_measure_le (M : ABKModel 2) (k : ℤ) (E : Set (ShellField 2)) :
    M.P.toMeasure.real ((fun F : ℤ → ShellField 2 => F k) ⁻¹' E) ≤
      (ShellField.shellMarginalLaw M.P k).toMeasure.real E := by
  apply ENNReal.toReal_mono (by finiteness)
  exact Measure.le_map_apply (ShellField.measurable_shellCoordinate k).aemeasurable E

/-- The finite source event union pays its full count and leaves exactly the
rate-1200 bound. All analytic Gaussian inputs and mean/variance normalizations
are proved internally; only the literal numerical scalar gates are supplied. -/
theorem wave_gate_enlarged_tail_of_gates (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (j Λ : ℤ) (hj : shellVarianceSum h M.gamma (j+40)/4 ≤ (Annealed.sigmaBar M (j+40):ℝ)^2) (hΛ : 1 ≤ Λ)
    (η : ℝ) (hη : 0 < η) (hg : M.gamma ≤ 1/64)
    (hm : M.gamma ≤ η^2*3^80/(12*waveBufferMean^2))
    (ht : M.gamma ≤ η^2*3^80/(60*waveBufferEll^2*(1200+(6+(11/5:ℝ)*40)/5)))
    (c : WavePlanarElementaryIndex → Vec 2) (s : WavePlanarElementaryIndex → ℝ)
    (hs : ∀ i, 0 < s i) (hside : ∀ i, s i ≤ (3:ℝ)^j) :
    M.P.toMeasure.real (waveGateEnlargedFailure M j Λ η c s) ≤
      Real.exp (-1200*(3:ℝ)^((3/2:ℝ)*(Λ:ℝ))) := by
  let E (i : WavePlanarElementaryIndex) : Set (ShellField 2) :=
    {F | η*(3:ℝ)^(-(Λ:ℝ)/8) < waveGateDerivativeSize (c i) (s i)
      (Annealed.sigmaBar M (j+40):ℝ) F}
  let z := (3:ℝ)^((3/2:ℝ)*(Λ:ℝ))
  let A := ((6+(11/5:ℝ)*40)/5)*z
  have hcard : (Fintype.card WavePlanarElementaryIndex:ℝ) ≤ Real.exp A := by
    rw [wave_planar_elementary_card]
    exact wave_planar_union_cost Λ hΛ
  have hE (i : WavePlanarElementaryIndex) :
      (ShellField.shellMarginalLaw M.P (j+40+Λ)).toMeasure.real (E i) ≤ Real.exp (-(A+1200*z)) := by
    have hh := wave_gate_elementary_tail M h hM j Λ hj hΛ η hη hg hm ht (c i) (s i) (hs i) (hside i)
    convert hh using 1
    congr 1
    dsimp only [A,z]
    ring
  have hh := wave_finite_union_tail (ShellField.shellMarginalLaw M.P (j+40+Λ)).toMeasure E A (1200*z) hcard hE
  have hp := wave_shell_preimage_measure_le M (j+40+Λ) (⋃ i, E i)
  have hpre : M.P.toMeasure.real (waveGateEnlargedFailure M j Λ η c s) ≤
      (ShellField.shellMarginalLaw M.P (j+40+Λ)).toMeasure.real (⋃ i, E i) := by
    simpa only [waveGateEnlargedFailure, Set.preimage_iUnion, Set.iUnion_ofPred,
      Set.preimage_ofPred_eq, E] using! hp
  simpa only [z,neg_mul] using! hpre.trans hh

end
end ASDExplicitGamma.Gaussian
