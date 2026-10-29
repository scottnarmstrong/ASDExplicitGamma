module

public import ASDExplicitGamma.Joint.StepAssembly
public import ASDExplicitGamma.Joint.UpperScalarN
public import ASDExplicitGamma.Native.StepNode
public import ASDExplicitGamma.Main.OrdinaryReturn

/-! GATE-STEP assembly. The conclusion is the exact statement of
`induction_step`. The two open producers enter only as the named hypotheses of
`gate_step_of_lower_scalar_and_theta`: JO-LOWER-SCALAR-N and MA-THETA-CONTINUATION. -/

@[expose] public section

namespace ASDExplicitGamma.Joint

open Algsuperdiff.Section3
open scoped ENNReal

/-- The JO-LOWER-SCALAR-N conclusion at the target label `N`. -/
def LowerScalarConclusion (M : ABKModel 2) (h : ℝ) (N : ℤ) : Prop :=
  M.nu ≤ (Annealed.sigmaBar M N : ℝ) ∧
    (31 / 50) * shellVarianceSum h M.gamma N + (19 / 50) * M.nu ^ 2 ≤
      (Annealed.sigmaBar M N : ℝ) ^ 2

/-- Conditional GATE-STEP: the statement of `induction_step`, with JO-LOWER-SCALAR-N and the
real-valued MA-THETA-CONTINUATION return as the only named hypotheses. -/
theorem gate_step_of_lower_scalar_and_theta (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hprev : ∀ n : ℤ, n < N → nativeInductionState M h n)
    (hLower : LowerScalarConclusion M h N)
    (hθ : ASDExplicitGamma.Main.MaThetaReturnReal M h N) :
    nativeInductionState M h N := by
  obtain ⟨hStrong, hRoot, hHist, hMean⟩ := ASDExplicitGamma.Native.nativeStep_node
    M h hM hγ N hprev
  have hOrd := ASDExplicitGamma.Main.jo_ordinary_mean M h N hθ hprev
  have hUpper := upper_scalar_n M h hM hγ N hprev
  exact step_assembly_of_components M h N hOrd hStrong hRoot hHist hMean hLower hUpper

end ASDExplicitGamma.Joint
