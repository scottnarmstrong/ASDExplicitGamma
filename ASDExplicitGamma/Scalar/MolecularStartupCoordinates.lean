module

public import ASDExplicitGamma.Scalar.MolecularNativeBox

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Algsuperdiff.Section3

/-- At every molecular startup label, the actual five frozen observables
satisfy their carried caps. The numerical comparisons are consumed from
NU-NA-MOLECULAR-STARTUP in the true completed-label frame. -/
theorem molecular_startup_coordinates (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero) (n : ℤ)
    (hx : shellVarianceSum h M.gamma n / M.nu ^ 2 ≤ theta M / 400) :
    ordinaryMean M n ≤ ENNReal.ofReal (3 / 50 * theta M) ∧
    strong20 M n ≤ ENNReal.ofReal (2379 / 2500 * theta M) ∧
    root20 M n ≤ ENNReal.ofReal (2013 / 10000 * theta M) ∧
    buffer40History M n ≤ ENNReal.ofReal (61 / 10 * theta M) ∧
    bufferMean M n ≤ ENNReal.ofReal (8 / 25 * theta M) := by
  have hB : 0 ≤ shellVarianceSum h M.gamma n :=
    ge_of_tendsto (Model.cutoffPartialStream_variance_tendsto M h n)
      (Filter.Eventually.of_forall fun N => (Model.cutoffPartialVariance M h n N).coe_nonneg)
  have hg0 : 0 < gammaZero := by norm_num [gammaZero]
  have ht : 0 < theta M := div_pos M.shellPrefix.gamma_pos hg0
  have ht1 : theta M ≤ 1 := (div_le_one hg0).mpr hγ
  have hc := Numerics.Native.native_molecular_startup_gate
    (shellVarianceSum h M.gamma n / M.nu ^ 2) (theta M)
    (div_nonneg hB (sq_nonneg M.nu)) ht ht1 hx
  have he : Numerics.Native.startupHistoryConstant = molecularHistoryFactor := by
    simp only [Numerics.Native.startupHistoryConstant, molecularHistoryFactor, neg_div]
  rw [he] at hc
  exact ⟨(ordinaryMean_molecular M h hM n).trans (ENNReal.ofReal_le_ofReal hc.2.2.2.1.le),
    (strong20_molecular M h hM n).trans (ENNReal.ofReal_le_ofReal hc.2.1.le),
    (root20_molecular M h hM n).trans (ENNReal.ofReal_le_ofReal hc.1.le),
    (buffer40History_molecular M h hM n).trans (ENNReal.ofReal_le_ofReal hc.2.2.1.le),
    (bufferMean_molecular M h hM n).trans (ENNReal.ofReal_le_ofReal hc.2.2.2.2.le)⟩

end ASDExplicitGamma.Scalar
