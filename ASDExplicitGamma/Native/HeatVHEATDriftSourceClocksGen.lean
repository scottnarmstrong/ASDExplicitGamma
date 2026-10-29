module

public import ASDExplicitGamma.Native.HeatVHEATDriftSourceClocks

/-! The `ns`-shell generalization of the source shell clocks: `e_ns = (9/2) gamma 3^(2 gamma ns)`. -/

@[expose] public section


namespace ASDExplicitGamma.Native
open Homogenization Gaussian Response Scalar Variational Inverse Triadic Algsuperdiff.Section3
noncomputable section

variable (ns : ℕ)

/-- The exact physical variance clock in the OLD true frame. -/
def heatVHEATDriftVarianceGen (M : ABKModel 2) (h : ℝ) (n : ℤ) (d : Fin ns) : ℝ :=
  (q3ModelAmplitude M h (n+((d.val+1:ℕ):ℤ)))^2/(Annealed.sigmaBar M n:ℝ)^2

/-- The common source e_9; the OLD label and observation label remain distinct. -/
def heatVHEATDriftEGen (M : ABKModel 2) : ℝ :=
  (9/2:ℝ)*M.gamma*(3:ℝ)^(2*M.gamma*(ns:ℝ))

/-- Exact deterministic mixed-shear coefficient at a refined observation child. -/
def heatVHEATDriftKappaGen (n : ℤ) (d : Fin ns) : ℝ :=
  let Q := originCube 2 (n-1)
  let L := q3ModelLength (n+((d.val+1:ℕ):ℤ))
  lemmaVH2kn (cubeScaleFactor Q/L.1)
    (diagMeshRadius Q (pureFluxBankSourceDepth (d.val+2))/L.1)

/-- Exact covariance-remainder coefficient from the same translated source row. -/
def heatVHEATDriftMuGen (d : Fin ns) : ℝ :=
  pureFluxCovarianceMu (pureFluxCovarianceA 0 (d.val+1)) (pureFluxCovarianceB 0 (d.val+1))

/-- The actual finite shell sums, before any refined certificate is substituted. -/
def heatVHEATDriftKActualGen (n : ℤ) : ℝ := ∑ d : Fin ns,(heatVHEATDriftKappaGen ns) n d

/-- The actual finite covariance-remainder sum. -/
def heatVHEATDriftCActualGen : ℝ := ∑ d : Fin ns,(heatVHEATDriftMuGen ns) d

/-- Each physical fresh-shell variance is below the same e_9 on the
completed OLD state. No variance estimate is a premise. -/
theorem heatVHEATDrift_source_variance_le_Gen
    (M : ABKModel 2) (h : ℝ) (n : ℤ) (hstate : nativeInductionState M h n) (d : Fin ns) :
    0 ≤ (heatVHEATDriftVarianceGen ns) M h n d ∧ (heatVHEATDriftVarianceGen ns) M h n d ≤ (heatVHEATDriftEGen ns) M := by
  constructor
  · exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  · have hv := native_source_shell_variance_le_clock M h n (d.val+1) (d.val+1) hstate le_rfl
    have hs : ((d.val+1:ℕ):ℝ) ≤ ns := by exact_mod_cast (show d.val+1≤ns by have := d.isLt; omega)
    have hg := M.shellPrefix.gamma_pos.le
    have hp : (3:ℝ)^(2*M.gamma*((d.val+1:ℕ):ℝ)) ≤ (3:ℝ)^(2*M.gamma*(ns:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        ((mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num : (0:ℝ)≤2) hg)))
    have hc := mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num : (0:ℝ)≤9/2) hg)
    change (heatVHEATDriftVarianceGen ns) M h n d ≤ _ at hv
    exact hv.trans hc

end
end ASDExplicitGamma.Native
