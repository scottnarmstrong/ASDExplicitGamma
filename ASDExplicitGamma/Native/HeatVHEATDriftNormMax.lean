module

public import ASDExplicitGamma.Native.HeatRemainderAverageNorm

/-! Intrinsic actual heat norms. Finiteness is established on the extended
carrier before taking any real value; no positive padding of X is used. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The exact finite maximum of actual child L20 norms, kept extended. This
is a common trace norm; the distinct rare factors are never maximized. -/
def heatVHEATDriftXExtended {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset I) (T : I → Ω → ℝ) : ℝ≥0∞ :=
  s.sup (fun i => eLpNorm (T i) 20 μ)

/-- A proved raw profile makes the intrinsic X finite and controls the
actual spatial average by that same X. All child correlations remain. -/
theorem heatVHEATDrift_intrinsic_trace_caps
    {Ω I : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset I) (w : I → ℝ) (hw : ∀ i∈s,0 ≤ w i) (hw1 : ∑ i∈s,w i=1)
    (T : I → Ω → ℝ) (hT : ∀ i∈s,AEStronglyMeasurable (T i) μ)
    (F : ℝ) (hraw : ∀ i∈s,eLpNorm (T i) 128 μ ≤ ENNReal.ofReal F) :
    heatVHEATDriftXExtended μ s T < ⊤ ∧
    (∀ i∈s,eLpNorm (T i) 20 μ ≤ ENNReal.ofReal (heatVHEATDriftXExtended μ s T).toReal) ∧
    eLpNorm (fun ω => ∑ i∈s,w i*T i ω) 20 μ ≤
      ENNReal.ofReal (heatVHEATDriftXExtended μ s T).toReal ∧
    eLpNorm (fun ω => ∑ i∈s,w i*T i ω) 128 μ ≤ ENNReal.ofReal F := by
  let X := heatVHEATDriftXExtended μ s T
  have hs : X ≤ ENNReal.ofReal F := by
    apply Finset.sup_le
    intro i hi
    exact (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (20:ℝ≥0∞)≤128)).trans (hraw i hi)
  have hx : X < ⊤ := hs.trans_lt ENNReal.ofReal_lt_top
  have hc (i : I) (hi : i∈s) : eLpNorm (T i) 20 μ ≤ ENNReal.ofReal X.toReal := by
    rw [ENNReal.ofReal_toReal hx.ne]
    exact Finset.le_sup (f := fun i => eLpNorm (T i) 20 μ) hi
  have hA : AEStronglyMeasurable (fun ω => ∑ i∈s,w i*T i ω) μ :=
    Finset.aestronglyMeasurable_fun_sum _ (fun i hi => (hT i hi).const_mul _)
  have h20 := heat_remainder_average_prime_cap μ s w hw hw1 T hT 20 (by norm_num)
    (ENNReal.ofReal X.toReal) (fun i hi => by
      simpa only [eLpNorm_eq_eLpNorm' (by norm_num : (20:ℝ≥0∞)≠0) (by norm_num) (hT i hi),
        ENNReal.toReal_ofNat] using hc i hi)
  have h128 := heat_remainder_average_prime_cap μ s w hw hw1 T hT 128 (by norm_num)
    (ENNReal.ofReal F) (fun i hi => by
      simpa only [eLpNorm_eq_eLpNorm' (by norm_num : (128:ℝ≥0∞)≠0) (by norm_num) (hT i hi),
        ENNReal.toReal_ofNat] using hraw i hi)
  refine ⟨hx,hc,?_,?_⟩
  · simpa only [eLpNorm_eq_eLpNorm' (by norm_num : (20:ℝ≥0∞)≠0) (by norm_num) hA,
      ENNReal.toReal_ofNat] using h20
  · simpa only [eLpNorm_eq_eLpNorm' (by norm_num : (128:ℝ≥0∞)≠0) (by norm_num) hA,
      ENNReal.toReal_ofNat] using h128

end
end ASDExplicitGamma.Native
