module

public import ASDExplicitGamma.Native.OldSignedSourceLocalProxy

/-! Complete deterministic covariance-mode contraction of the actual source
proxy, with correlations and the directional half-trace budget retained. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Inverse Algsuperdiff.Section3
noncomputable section

/-- Summing actual source proxies over a square-summable deterministic load
family preserves the sharp expected directional budget. -/
theorem old_signed_source_directional_modes_payment
    {I : Type*} [Countable I]
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (r : ℕ) (hr : r ≤ 5)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hstates : ∀ l ≤ n,nativeInductionState M h l)
    (E : I → Fin 2 → Vec 2) (hE : Summable (fun i => ∑ c : Fin 2,vecNormSq (E i c))) :
    let a := fun ω => responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
      (oldSignedCellCoefficient (originCube 2 n) U
        (openCubeSet_subset_of_mem_descendantsAtDepth hU) (oldSignedPartialResponseCoefficient n 1 t ω))
    Integrable (fun ω => ∑' i,∑ c : Fin 2,oldSignedDirectionalProxy U (a ω) (E i c))
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,∑' i,∑ c : Fin 2,oldSignedDirectionalProxy U (a ω) (E i c)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ((1-inverseHistoryDiscount^2)*
        ∑' j : ℕ,inverseHistoryDiscount^(2*j)*oldSignedSourceHistoryBudget M n U t j)*
          (∑' i,∑ c : Fin 2,vecNormSq (E i c)) := by
  classical
  intro a
  let B := (1-inverseHistoryDiscount^2)*
    ∑' j : ℕ,inverseHistoryDiscount^(2*j)*oldSignedSourceHistoryBudget M n U t j
  let p := fun i ω => ∑ c : Fin 2,oldSignedDirectionalProxy U (a ω) (E i c)
  have hp (i : I) (c : Fin 2) :=
    old_signed_source_local_proxy_payment M h hM hg n r hr U hU t ht hstates (E i c)
  have hn (ω : Cutoff.CutoffSample 2) (i : I) (c : Fin 2) :=
    old_signed_directional_proxy_nonneg_le U M.nu (Annealed.sigmaBar M n)
      M.nu_pos (Annealed.sigmaBar_characterization M n).1
      (oldSignedCellCoefficient (originCube 2 n) U
        (openCubeSet_subset_of_mem_descendantsAtDepth hU) (oldSignedPartialResponseCoefficient n 1 t ω)) (E i c)
  have hpi (i : I) : Integrable (p i) (Cutoff.cutoffSampleLaw M).toMeasure :=
    integrable_finsetSum _ (fun c _ => (hp i c).1)
  have hpn (i : I) (ω : Cutoff.CutoffSample 2) : 0 ≤ p i ω :=
    Finset.sum_nonneg (fun c _ => (hn ω i c).1)
  have hps (ω : Cutoff.CutoffSample 2) : Summable (fun i => p i ω) := by
    let H := rawWeakTraceProxy (lemmaVInverseDepthMax U (a ω))
      (fun j => descendantsAverage U j (fun V => traceDefect (openCubeSet V) (a ω) 1))
    apply Summable.of_nonneg_of_le (fun i => hpn i ω) _ (hE.mul_left H)
    intro i
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun c _ => (hn ω i c).2)
  have hbound (i : I) : (∫ ω,p i ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      B*(∑ c : Fin 2,vecNormSq (E i c)) := by
    rw [integral_finsetSum _ (fun c _ => (hp i c).1),Finset.mul_sum]
    exact Finset.sum_le_sum (fun c _ => (hp i c).2)
  have hh := old_signed_nonnegative_series_integral (Cutoff.cutoffSampleLaw M).toMeasure p
    (fun i => B*(∑ c : Fin 2,vecNormSq (E i c))) hpi hpn hps (hE.mul_left B) hbound
  rw [tsum_mul_left] at hh
  exact hh

end
end ASDExplicitGamma.Native
