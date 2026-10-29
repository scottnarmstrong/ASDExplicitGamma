module

public import ASDExplicitGamma.Cold.TwentiethMomentNorm
public import Mathlib.MeasureTheory.Order.Lattice
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! # The exact finite-union cost for nonnegative depthwise trace maxima -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- Actual maximum over all cells in one finite spatial generation. -/
def coldFiniteMaximum {Ω ι : Type*} [Fintype ι] [Nonempty ι] (X : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω)

/-- Every actual source cell is bounded by its generation maximum. -/
theorem le_coldFiniteMaximum {Ω ι : Type*} [Fintype ι] [Nonempty ι]
    (X : ι → Ω → ℝ) (ω : Ω) (i : ι) : X i ω ≤ coldFiniteMaximum X ω :=
  Finset.le_sup' (fun i => X i ω) (Finset.mem_univ i)

/-- The generation maximum is an actual cell value, without a relaxation. -/
theorem coldFiniteMaximum_eq_some {Ω ι : Type*} [Fintype ι] [Nonempty ι]
    (X : ι → Ω → ℝ) (ω : Ω) : ∃ i, coldFiniteMaximum X ω = X i ω := by
  obtain ⟨i,_,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => X i ω)
  exact ⟨i,he⟩

/-- The twentieth power of a nonnegative maximum is bounded by the spatial sum. -/
theorem coldFiniteMaximum_pow_le_sum {Ω ι : Type*} [Fintype ι] [Nonempty ι]
    (X : ι → Ω → ℝ) (ω : Ω) :
    (coldFiniteMaximum X ω)^20 ≤ ∑ i, (X i ω)^20 := by
  obtain ⟨i,hi⟩ := coldFiniteMaximum_eq_some X ω
  rw [hi]
  exact Finset.single_le_sum (f := fun j => X j ω^20) (fun j _ => by positivity) (Finset.mem_univ i)

/-- Measurability of the literal finite maximum. -/
theorem measurable_coldFiniteMaximum {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    {X : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i)) : Measurable (coldFiniteMaximum X) := by
  have h := Finset.measurable_sup' Finset.univ_nonempty (fun i _ => hX i)
  convert h using 1
  funext ω
  exact (Finset.sup'_apply _ _ _).symm

/-- Finite maxima of nonnegative L20 cell traces remain in L20. -/
theorem memLp_coldFiniteMaximum {Ω ι : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [Fintype ι] [Nonempty ι] {X : ι → Ω → ℝ} (hX : ∀ i, MemLp (X i) 20 ℙ)
    (hMeas : ∀ i, Measurable (X i)) : MemLp (coldFiniteMaximum X) 20 ℙ := by
  classical
  have hsum := memLp_finsetSum Finset.univ (fun i _ => (hX i).norm)
  apply hsum.mono' (measurable_coldFiniteMaximum hMeas).aestronglyMeasurable
  filter_upwards with ω
  obtain ⟨i,hi⟩ := coldFiniteMaximum_eq_some X ω
  rw [hi]
  exact Finset.single_le_sum (f := fun j => ‖X j ω‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)

/-- The union cost for arbitrary dependent source cells is exactly `N^(1/20)`. -/
theorem coldFiniteMaximum_lpNorm_le {Ω ι : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsFiniteMeasure ℙ] [Fintype ι] [Nonempty ι] {X : ι → Ω → ℝ} {M : ℝ}
    (hX : ∀ i, MemLp (X i) 20 ℙ) (hMeas : ∀ i, Measurable (X i))
    (hM : 0 ≤ M) (hcap : ∀ i, lpNorm (X i) 20 ℙ ≤ M) :
    lpNorm (coldFiniteMaximum X) 20 ℙ ≤ (Fintype.card ι:ℝ)^((1:ℝ)/20)*M := by
  have hmax := memLp_coldFiniteMaximum hX hMeas
  have hmi : Integrable (fun ω => (coldFiniteMaximum X ω)^20) ℙ := by
    have h := hmax.integrable_norm_pow (p := 20) (by norm_num)
    simpa only [Real.norm_eq_abs,show (20:ℕ)=2*10 by norm_num,pow_mul,sq_abs] using h
  have hi (i : ι) : Integrable (fun ω => X i ω^20) ℙ := by
    have h := (hX i).integrable_norm_pow (p := 20) (by norm_num)
    simpa only [Real.norm_eq_abs,show (20:ℕ)=2*10 by norm_num,pow_mul,sq_abs] using h
  have h := integral_mono_ae hmi (integrable_finsetSum Finset.univ (fun i _ => hi i))
    (Filter.Eventually.of_forall (coldFiniteMaximum_pow_le_sum X))
  rw [integral_finsetSum _ (fun i _ => hi i)] at h
  have hc := Finset.sum_le_sum (s := Finset.univ) (fun i _ => cold_integral_twentieth_le (hX i) (hcap i))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hc
  rw [← cold_lpNorm_twenty_pow hmax] at h
  have hb : (lpNorm (coldFiniteMaximum X) 20 ℙ)^20 ≤ (Fintype.card ι:ℝ)*M^20 := h.trans hc
  have he : ((Fintype.card ι:ℝ)^((1:ℝ)/20)*M)^20 = (Fintype.card ι:ℝ)*M^20 := by
    rw [mul_pow,← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    norm_num
  apply (pow_le_pow_iff_left₀ lpNorm_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hM)
    (by norm_num : (20:ℕ) ≠ 0)).mp
  rwa [he]

end ASDExplicitGamma.Cold
