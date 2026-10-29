module

public import ASDExplicitGamma.Scalar.DefectTwoSlot
public import ASDExplicitGamma.Scalar.NewResolventDefectFormula
public import ASDExplicitGamma.Scalar.ChaosHilbertEnvelope
public import ASDExplicitGamma.Gaussian.ModelHeatLaw

/-! SC-NEW-RESOLVENT-DEFECT: the two-slot assembly with the source constants. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open MeasureTheory ProbabilityTheory ASDExplicitGamma.Gaussian Homogenization Filter Topology
  ASDExplicitGamma.Variational
open scoped ENNReal

/-- Continuity of the parity pairing along a convergent sequence of sources: the abstract
step `D_n → D∞` once `s_n → s∞` in the pair space (`J` the parity, `N` the NEW inverse). -/
theorem pairing_tendsto {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (J N : Z →L[ℝ] Z) {s : ℕ → Z} {s0 : Z} (h : Tendsto s atTop (𝓝 s0)) :
    Tendsto (fun n => @inner ℝ Z _ (J (s n)) (N (s n))) atTop
      (𝓝 (@inner ℝ Z _ (J s0) (N s0))) :=
  ((J.continuous.tendsto _).comp h).inner ((N.continuous.tendsto _).comp h)

end ASDExplicitGamma.Scalar
