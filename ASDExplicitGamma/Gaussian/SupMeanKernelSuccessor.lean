module

public import ASDExplicitGamma.Gaussian.SupMeanKernelCrossIntegral
public import ASDExplicitGamma.Gaussian.WaveGateConstants

/-! Exact isotropic derivative traces of the actual q3 convolution jets. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model
open scoped BigOperators RealInnerProductSpace
noncomputable section

/-- The ordinary next spatial kernel index, up to the third weak derivative. -/
def supMeanKernelJetSuccessor (o : Q3SpatialJet) (d : Fin 2) : H3Index :=
  h3Next (supMeanKernelJetIndex o) d (by
    cases o with
    | value => norm_num [supMeanKernelJetIndex, Q3SpatialJet.count]
    | first i => fin_cases i <;> norm_num [supMeanKernelJetIndex, Q3SpatialJet.count]
    | second i j => fin_cases i <;> fin_cases j <;> norm_num [supMeanKernelJetIndex, Q3SpatialJet.count])

/-- Different coordinate successors of the same jet are genuinely orthogonal. -/
theorem supMean_kernel_successor_orthogonal (β : ℝ) (L : {l : ℝ // 0 < l})
    (o : Q3SpatialJet) (x : Vec 2) :
    ⟪q3Section β L (supMeanKernelJetSuccessor o 0) x,
      q3Section β L (supMeanKernelJetSuccessor o 1) x⟫ = 0 := by
  apply supMean_kernel_cross_orthogonal
  cases o with
  | value => norm_num [supMeanKernelJetSuccessor, supMeanKernelJetIndex, h3Next, Q3SpatialJet.count]
  | first i =>
      fin_cases i <;> norm_num [supMeanKernelJetSuccessor, supMeanKernelJetIndex, h3Next, Q3SpatialJet.count]
      decide
  | second i j => fin_cases i <;> fin_cases j <;>
      norm_num [supMeanKernelJetSuccessor, supMeanKernelJetIndex, h3Next, Q3SpatialJet.count] <;> decide

/-- One spatial coordinate accounts for exactly half the full Hessian trace. -/
theorem supMean_kernel_first_successor_trace (β : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (d : Fin 2) :
    (∑ i : Fin 2, ‖Real.sqrt 2 • q3Section β L (supMeanKernelJetSuccessor (.first i) d) x‖^2) =
      (waveTau2/2)*(β^2/L.val^4) := by
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Fin.sum_univ_two, gaussQ3Section_norm_sq]
  fin_cases d <;>
    norm_num [supMeanKernelJetSuccessor, supMeanKernelJetIndex, h3Next, Q3SpatialJet.count,
      q3DerivativeMoment, waveTau2, waveMu2, waveR1, waveR2] <;>
    field_simp [L.property.ne'] <;> ring

/-- The same isotropic half-trace identity holds for the third weak kernel;
no pathwise third derivative of the frozen C2 shell is assumed. -/
theorem supMean_kernel_second_successor_trace (β : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (d : Fin 2) :
    (∑ i : Fin 2 × Fin 2,
      ‖Real.sqrt 2 • q3Section β L (supMeanKernelJetSuccessor (.second i.1 i.2) d) x‖^2) =
        (waveTau3/2)*(β^2/L.val^6) := by
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Fintype.sum_prod_type, Fin.sum_univ_two, gaussQ3Section_norm_sq]
  fin_cases d <;>
    norm_num [supMeanKernelJetSuccessor, supMeanKernelJetIndex, h3Next, Q3SpatialJet.count,
      q3DerivativeMoment, waveTau3, waveMu3, waveR1, waveR2, waveR3] <;>
    field_simp [L.property.ne'] <;> ring

end
end ASDExplicitGamma.Gaussian
