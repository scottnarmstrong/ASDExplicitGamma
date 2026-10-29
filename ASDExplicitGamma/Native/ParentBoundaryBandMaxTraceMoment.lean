module

public import ASDExplicitGamma.Native.ParentBoundaryBandMaxTraceLaw
public import ASDExplicitGamma.Native.ParentBoundaryBandTraceLp
public import ASDExplicitGamma.Native.ParentBoundaryBandDepthSeries
public import ASDExplicitGamma.Native.OldSignedMaxHistoryMoment

/-! Honest probability moments of the actual band maximum history,
with the exact order20 population cost and the complete infinite depth sum. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The actual source-cell population pays exactly 9^(j/20), with no
independence and no extra comparison-depth population factor. -/
theorem parent_boundary_band_depth_max_L20
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma≤gammaZero)
    (n : ℤ) (height r : ℕ) (U : TriadicCube 2) (hU : U.scale=n-(r:ℤ))
    (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht : t≤1) (j : ℕ) :
    eLpNorm (parentBoundaryBandTraceDepthMax M n height U t j) 20
      (Cutoff.cutoffSampleLaw M).toMeasure≤
      ((9:ℝ≥0∞)^j)^(1/20:ℝ)*ENNReal.ofReal (parentBoundaryBandTraceCap M height (r+j)) := by
  let f := fun V omega => ENNReal.ofReal (traceDefect (cubeSet V)
    (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega) (Annealed.sigmaBar M n))
  have hf (V) : Measurable (f V) := by
    have he : parentBoundaryBandTraceDepthMax M n height V t 0=f V := by
      funext omega
      simp only [parentBoundaryBandTraceDepthMax,historyFiniteMax,descendantsAtDepth_zero,Finset.sup_singleton,f]
    rw [←he]
    exact parent_boundary_band_trace_depth_max_measurable M n height V t 0
  have hcell (V) (hV : V∈descendantsAtDepth U j) :
      eLpNorm (f V) 20 (Cutoff.cutoffSampleLaw M).toMeasure≤
        ENNReal.ofReal (parentBoundaryBandTraceCap M height (r+j)) := by
    change eLpNorm (ENNReal.ofReal ∘ (fun omega => traceDefect (cubeSet V)
      (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega) (Annealed.sigmaBar M n))) 20 _≤_
    rw [eLpNorm_ofReal _ (Filter.Eventually.of_forall (parent_boundary_band_trace_nonneg M n height t V))]
    apply parent_boundary_band_cell_trace_Lp M h hM hg n height (r+j) V _ hpast t ht 20 (by norm_num)
    rw [scale_eq_sub_of_mem_descendantsAtDepth hV,hU]
    push_cast
    ring
  have hh := history_finite_max_L20 (Cutoff.cutoffSampleLaw M).toMeasure (descendantsAtDepth U j)
    f hf (ENNReal.ofReal (parentBoundaryBandTraceCap M height (r+j))) hcell
  have hc : ((descendantsAtDepth U j).card:ℝ≥0∞)=(9:ℝ≥0∞)^j := by
    rw [descendantsAtDepth_card]
    norm_num
  change eLpNorm (parentBoundaryBandTraceDepthMax M n height U t j) 20 _≤_ at hh
  simpa only [hc] using hh

/-- The complete actual maximum-history profile is summable throughout
our source gamma range. The full trace bank is used only for moments here. -/
theorem parent_boundary_band_max_trace_cap_summable
    (M : ABKModel 2) (hg : M.gamma≤gammaZero) (height r : ℕ) :
    Summable (fun j : ℕ => coldHistoryBeta^j*parentBoundaryBandTraceCap M height (r+j)) := by
  let q := coldHistoryBeta*(3:ℝ)^(4*M.gamma)
  have hq0 : 0≤q := mul_nonneg coldHistoryBeta_pos.le (Real.rpow_nonneg (by norm_num) _)
  have hqe : q=(3:ℝ)^(-(3/20:ℝ)+4*M.gamma) := by
    have hb : coldHistoryBeta=(3:ℝ)^(-(3/20:ℝ)) := by simpa using cold_native_beta_power 1
    rw [show q=coldHistoryBeta*(3:ℝ)^(4*M.gamma) from rfl,hb,←Real.rpow_add (by norm_num : (0:ℝ)<3)]
  have hq1 : q<1 := by
    rw [hqe]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ)<3)
    have hh : M.gamma≤17/50000 := hg
    linarith only [hh]
  have hqn : ‖q‖<1 := by rwa [Real.norm_of_nonneg hq0]
  have hs0 := summable_geometric_of_norm_lt_one hqn
  have hs1 : Summable (fun j : ℕ => (j:ℝ)*q^j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hqn
  let A := (1009309/500000:ℝ)+M.gamma*(32474*((height:ℝ)+(r:ℝ)+1)+11483216)
  let B := 32474*M.gamma
  let C := 4*(3:ℝ)^((2*(height:ℝ)+4*(r:ℝ)+4)*M.gamma)
  apply (((hs0.mul_left A).add (hs1.mul_left B)).mul_left C).congr
  intro j
  rw [parent_boundary_band_trace_cap_factor]
  have he : (3:ℝ)^(4*M.gamma*(j:ℝ))=((3:ℝ)^(4*M.gamma))^j := by
    rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
  rw [he]
  dsimp only [A,B,C,q]
  rw [mul_pow]
  ring

/-- The complete raw maximum-history moment cap, used only to establish
actual integrability before sharpening the evolving panel envelope. -/
def parentBoundaryBandMaxTraceCap (M : ABKModel 2) (height r : ℕ) : ℝ :=
  (1-inverseHistoryDiscount)*∑' j : ℕ,coldHistoryBeta^j*parentBoundaryBandTraceCap M height (r+j)

/-- The genuine complete simultaneous-band maximum history has a finite
order20 moment. All population and response inputs are discharged. -/
theorem parent_boundary_band_max_trace_L20
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma≤gammaZero)
    (n : ℤ) (height r : ℕ) (U : TriadicCube 2) (hU : U.scale=n-(r:ℤ))
    (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht : t≤1) :
    eLpNorm (parentBoundaryBandMaxTraceHistory M n height U t) 20
      (Cutoff.cutoffSampleLaw M).toMeasure≤ENNReal.ofReal (parentBoundaryBandMaxTraceCap M height r) := by
  let mu := (Cutoff.cutoffSampleLaw M).toMeasure
  let F := fun j : ℕ => fun omega => ENNReal.ofReal (inverseHistoryDiscount^j)*
    parentBoundaryBandTraceDepthMax M n height U t j omega
  have hm (j : ℕ) : Measurable (F j) :=
    (parent_boundary_band_trace_depth_max_measurable M n height U t j).const_mul _
  have hb (j : ℕ) : eLpNorm (F j) 20 mu≤
      ENNReal.ofReal (coldHistoryBeta^j*parentBoundaryBandTraceCap M height (r+j)) := by
    change eLpNorm (fun omega => ENNReal.ofReal (inverseHistoryDiscount^j)*
      parentBoundaryBandTraceDepthMax M n height U t j omega) 20 mu≤_
    rw [history_constant_mul_L20 mu _ _ (parent_boundary_band_trace_depth_max_measurable M n height U t j)]
    have hd := parent_boundary_band_depth_max_L20 M h hM hg n height r U hU hpast t ht j
    apply (mul_le_mul_of_nonneg_left hd (by positivity)).trans_eq
    rw [←mul_assoc,old_signed_max_history_population_weight,
      ←ENNReal.ofReal_mul (pow_nonneg coldHistoryBeta_pos.le j)]
  have hsum := (ENNReal.tsum_le_tsum hb).trans_eq
    (ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (pow_nonneg coldHistoryBeta_pos.le j)
      (parent_boundary_band_trace_cap_nonneg M height (r+j)))
        (parent_boundary_band_max_trace_cap_summable M hg height r)).symm
  change eLpNorm (fun omega => ENNReal.ofReal (1-inverseHistoryDiscount)*∑' j : ℕ,F j omega) 20 mu≤_
  rw [history_constant_mul_L20 mu _ _ (Measurable.tsum hm)]
  exact (mul_le_mul_of_nonneg_left ((history_ennreal_tsum_L20 mu F hm).trans hsum)
    (by positivity)).trans_eq (ENNReal.ofReal_mul (sub_nonneg.mpr inverse_history_discount_range.2.le)).symm

end
end ASDExplicitGamma.Native
