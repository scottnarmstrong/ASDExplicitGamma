module

public import ASDExplicitGamma.Inverse.PositiveRootAssembly
public import ASDExplicitGamma.Inverse.RootErrorMoments

/-! The fixed-row actual positive pointwise root theorem. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3
noncomputable section

/-- IN-POINTWISE-ROOT: the actual attenuated full-UV root response in the
true completed-m frame, with one measurable positive source E_l and both
source moment alternatives at every real 2<=p<=256. All response estimates
use only strictly earlier ordinary states and the named source H3 mean. -/
theorem q3_pointwise_root (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (m J : ℤ)
    (hQ : Q.scale ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (r : RootRow) (hpast : ∀ n < m, nativeInductionState M h n)
    (hmean : ClippedInverseMeanInput M m r) :
    PointwiseRootConclusion M Q m J weights r := by
  refine ⟨positive_root_error_measurable M Q r,
    q3_positive_root_assembly M h hM hg Q m J hQ hm weights hw r hpast hmean,?_⟩
  have hH0 : 333 ≤ rootH0 r := by cases r <;> norm_num [rootH0]
  have hprotected : ∀ k ≤ Q.scale-(rootH0 r:ℤ)+40, nativeInductionState M h k := by
    intro k hk
    exact hpast k (by omega)
  intro p hp hp256
  exact positive_root_error_Lp M h hM hg Q r hprotected p hp hp256

end
end ASDExplicitGamma.Inverse
