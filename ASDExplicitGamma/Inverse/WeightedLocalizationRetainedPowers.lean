module

public import ASDExplicitGamma.Inverse.WeightedLocalizationProfile
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Retaining each source power and each of the three resolution offsets in PE. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

/-- Positive finite sums admit the source's termwise square-root envelope. -/
theorem localization_sqrt_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    Real.sqrt (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Real.sqrt (f i) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _), ?_⟩
  have hh := Finset.sum_sq_le_sq_sum_of_nonneg (s := s) (f := fun i => Real.sqrt (f i))
    (fun i _ => Real.sqrt_nonneg _)
  have he : (∑ i ∈ s, Real.sqrt (f i) ^ 2) = ∑ i ∈ s, f i :=
    Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hf i hi))
  rwa [he] at hh

/-- Square roots of retained PE powers retain half of each individual exponent. -/
theorem localization_sqrt_power_envelope {ι : Type*} (s : Finset ι) (c nu : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (R : ℝ) :
    Real.sqrt (∑ i ∈ s, c i * (3 : ℝ) ^ (-nu i * R)) ≤
      ∑ i ∈ s, Real.sqrt (c i) * (3 : ℝ) ^ (-nu i * R / 2) := by
  apply (localization_sqrt_sum_le s _ (fun i hi => mul_nonneg (hc i hi)
    (Real.rpow_nonneg (by norm_num) _))).trans_eq
  apply Finset.sum_congr rfl
  intro i hi
  have he : Real.sqrt ((3 : ℝ) ^ (-nu i * R)) = (3 : ℝ) ^ (-nu i * R / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  rw [Real.sqrt_mul (hc i hi), he]

/-- All three active resolutions are paid exactly by 1+3^nu+3^(2nu). -/
theorem localization_resolution_power_sum (nu x : ℝ) :
    (∑ e : Fin 3, (3 : ℝ) ^ (-nu * (x + 1 - (e : ℝ)))) =
      (1 + (3 : ℝ) ^ nu + (3 : ℝ) ^ (2 * nu)) * (3 : ℝ) ^ (-nu * (x + 1)) := by
  have he (e : Fin 3) : (3 : ℝ) ^ (-nu * (x + 1 - (e : ℝ))) =
      (3 : ℝ) ^ (nu * (e : ℝ)) * (3 : ℝ) ^ (-nu * (x + 1)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  simp_rw [he]
  rw [← Finset.sum_mul]
  congr 1
  norm_num [Fin.sum_univ_succ, mul_comm nu 2]
  ring

/-- The three resolutions of the square-root error retain exactly the half-power offsets. -/
theorem localization_resolution_sqrt_power_sum (nu x : ℝ) :
    (∑ e : Fin 3, (3 : ℝ) ^ (-nu * (x + 1 - (e : ℝ)) / 2)) =
      (1 + (3 : ℝ) ^ (nu / 2) + (3 : ℝ) ^ nu) * (3 : ℝ) ^ (-nu * (x + 1) / 2) := by
  have hh := localization_resolution_power_sum (nu / 2) x
  have h1 : 2 * (nu / 2) = nu := by ring
  have h2 : -(nu / 2) * (x + 1) = -nu * (x + 1) / 2 := by ring
  rw [h1, h2] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  ring

end ASDExplicitGamma.Inverse
