module

public import ASDExplicitGamma.Gaussian.WaveGateEnlargedFailure

/-! # GA-WAVE-GATE

The enlarged event has exactly four block corners, the full 3^80 buffer
population, and parent plus two generations. Every center is deterministic;
all positive sides are at most the old fine side 3^j. Repeated parent events
in the two-generation extension are allowed by this universal population.
The only earlier scalar input is the quarter lower corridor at j+40.
The shell and fixed true frame are respectively j+40+Lambda and sigmaBar(j+40).
The protected source label n_* may be any j+40≤n_*<n_ind: no frame at n_*
is introduced, and no scalar estimate at a terminal/reference label is used.
-/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory
noncomputable section

/-- The three source tuples retain their distinct threshold parameters. -/
inductive WaveGateTuple where
  | full
  | inverse
  | allOrder

/-- Exact eta from the named source tuple; no tuple is substituted for another. -/
def waveGateEta : WaveGateTuple → ℝ
  | .full => Numerics.Wave.fullEta
  | .inverse => Numerics.Wave.inverseEta
  | .allOrder => Numerics.Wave.allOrderEta

theorem wave_gate_eta_pos (t : WaveGateTuple) : 0 < waveGateEta t := by
  cases t <;> norm_num [waveGateEta,Numerics.Wave.fullEta,Numerics.Wave.fullTau,
    Numerics.Wave.inverseEta,Numerics.Wave.inverseTau,Numerics.Wave.allOrderEta,Numerics.Wave.allOrderTau]

/-- Each exact certificate supplies both analytic scalar gates and the exponent range. -/
theorem wave_gate_tuple_margins (t : WaveGateTuple) (γ : ℝ) (hγ : γ ≤ gammaZero) :
    γ ≤ (waveGateEta t)^2*3^80/(12*waveBufferMean^2) ∧
    γ ≤ (waveGateEta t)^2*3^80/(60*waveBufferEll^2*(1200+(6+(11/5:ℝ)*40)/5)) ∧ γ ≤ 1/64 := by
  have get (η : ℝ) (hm : γ < η^2*3^80/(12*waveBufferMean^2))
      (ht : γ < η^2*3^80/(60*waveBufferEll^2*(1200+(6+11*40/5)/5))) (hg : γ < 1/64) :
      γ ≤ η^2*3^80/(12*waveBufferMean^2) ∧
      γ ≤ η^2*3^80/(60*waveBufferEll^2*(1200+(6+(11/5:ℝ)*40)/5)) ∧ γ ≤ 1/64 := by
    exact ⟨hm.le,by convert ht.le using 1; norm_num,hg.le⟩
  cases t with
  | full =>
    obtain ⟨hm,ht,hg⟩ := wave_full_numeric_gate γ hγ
    exact get _ hm ht hg
  | inverse =>
    obtain ⟨hm,ht,hg⟩ := wave_inverse_numeric_gate γ hγ
    exact get _ hm ht hg
  | allOrder =>
    obtain ⟨hm,ht,hg⟩ := wave_allorder_numeric_gate γ hγ
    exact get _ hm ht hg

/-- The source rate-1200 enlarged planar wave gate for all three exact tuples.
Only the named old-label lower corridor is required from the native state. -/
theorem q3_wave_gate (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (t : WaveGateTuple) (j Λ : ℤ) (hΛ : 1 ≤ Λ)
    (hLower : shellVarianceSum h M.gamma (j+40)/4 ≤ (Annealed.sigmaBar M (j+40):ℝ)^2)
    (c : WavePlanarElementaryIndex → Vec 2) (s : WavePlanarElementaryIndex → ℝ)
    (hs : ∀ i, 0 < s i) (hside : ∀ i, s i ≤ (3:ℝ)^j) :
    M.P.toMeasure.real (waveGateEnlargedFailure M j Λ (waveGateEta t) c s) ≤
      Real.exp (-1200*(3:ℝ)^((3/2:ℝ)*(Λ:ℝ))) := by
  obtain ⟨hm,ht,hg⟩ := wave_gate_tuple_margins t M.gamma hγ
  exact wave_gate_enlarged_tail_of_gates M h hM j Λ hLower hΛ (waveGateEta t)
    (wave_gate_eta_pos t) hg hm ht c s hs hside

end
end ASDExplicitGamma.Gaussian
