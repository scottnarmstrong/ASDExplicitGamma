module

public import ASDExplicitGamma.Inverse.BridgeGlobalBank
public import ASDExplicitGamma.Inverse.BridgeObserverRoots
public import ASDExplicitGamma.Inverse.ParentGapPairedTrace
public import ASDExplicitGamma.Inverse.ParentGapObserverMembership
public import Algsuperdiff.Section3.Provider.ErrorComparison.CubeMonotonicity

/-! Structural parent-cube membership and its OLD-frame inverse-history cap. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
  Algsuperdiff.Section3.Provider.ErrorComparison
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Scalar
open ASDExplicitGamma.Response ASDExplicitGamma.Variational

attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Every discounted parent inverse depth is bounded by the exported
complete observer history `B*`, in the same actual OLD frame. -/
theorem mixed_bridge_parent_depth_discount_le_bstar
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (j : ℕ) :
    Scalar.inverseHistoryDiscount ^ j *
        lemmaVInverseDepthMax (originCube 2 m)
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mixedBridgeResponseCoefficient m t ω)) j ≤
      mixedBridgeBstar M m t ω := by
  let Q := originCube 2 m
  let a := (Model.partialInsertedCoefficient M m t ω).toFun
  let σ : ℝ := Annealed.sigmaBar M m
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  have hframe := mixed_bridge_frame_inverse_depth_eq_sigma_actual
    M m t ω ht j
  have hEll := partialInserted_parent_cube_elliptic M m t ω ht
  have hEll' : IsEllipticFieldOn M.nu
      (((2 : ℝ) * 2 * (Model.partialInsertedEntryBound M (m + 40) m ω) ^ 2 +
        M.nu ^ 2) / M.nu)
      (openCubeSet Q) a := by
    simpa only [Q, a] using hEll
  have hdepth := actual_inverse_depth_discount_bound Q a hEll' σ hσ.le j
  have hroot := rawFiniteInverseHistoryMax_lower_of_mem
    (mixedBridgeObserverSourceRoots m)
    (mixed_bridge_parent_cube_mem_observer m) a σ
  calc
    Scalar.inverseHistoryDiscount ^ j *
        lemmaVInverseDepthMax Q
          (responseFramePlanarCoefficientField M.nu σ
            (mixedBridgeResponseCoefficient m t ω)) j =
        Scalar.inverseHistoryDiscount ^ j *
          (σ * lemmaVInverseDepthMax Q a j) := by rw [hframe]
    _ ≤ σ * lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ)) := hdepth
    _ ≤ rawFiniteInverseHistoryMax (mixedBridgeObserverSourceRoots m) a σ := hroot
    _ = mixedBridgeBstar M m t ω := by
      symm
      exact mixedBridgeBstar_eq_raw_history_max M m t ω

end ASDExplicitGamma.Inverse
