module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.Real.Sqrt

/-! Finite-average Cauchy-Schwarz and the abstract linear combination used to
close the `L`-type profile. -/

@[expose] public section

namespace ASDExplicitGamma.Main

/-- The finite uniform average. -/
noncomputable def finAvg {ι : Type*} (S : Finset ι) (f : ι → ℝ) : ℝ :=
  ((S.card : ℝ)⁻¹) * ∑ i ∈ S, f i

theorem finAvg_mul_le {ι : Type*} (S : Finset ι) (u w : ι → ℝ) :
    finAvg S (fun i => u i * w i) ≤
      Real.sqrt (finAvg S (fun i => u i ^ 2)) *
        Real.sqrt (finAvg S (fun i => w i ^ 2)) := by
  unfold finAvg
  set c : ℝ := (S.card : ℝ)⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  rw [Real.sqrt_mul hc0, Real.sqrt_mul hc0]
  have h := Real.sum_mul_le_sqrt_mul_sqrt S u w
  have hcc : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc0
  calc c * ∑ i ∈ S, u i * w i ≤ c * (Real.sqrt (∑ i ∈ S, u i ^ 2) *
        Real.sqrt (∑ i ∈ S, w i ^ 2)) := mul_le_mul_of_nonneg_left h hc0
    _ = (Real.sqrt c * Real.sqrt c) * (Real.sqrt (∑ i ∈ S, u i ^ 2) *
        Real.sqrt (∑ i ∈ S, w i ^ 2)) := by rw [hcc]
    _ = (Real.sqrt c * Real.sqrt (∑ i ∈ S, u i ^ 2)) *
        (Real.sqrt c * Real.sqrt (∑ i ∈ S, w i ^ 2)) := by ring

theorem finAvg_le_sqrt {ι : Type*} (S : Finset ι) (u : ι → ℝ) :
    finAvg S u ≤ Real.sqrt (finAvg S (fun i => u i ^ 2)) := by
  have h := finAvg_mul_le S u (fun _ => 1)
  have h1 : finAvg S (fun i => (1 : ℝ) ^ 2) ≤ 1 := by
    unfold finAvg
    simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
    by_cases h0 : (S.card : ℝ) = 0
    · simp [h0]
    · rw [inv_mul_cancel₀ h0]
  have : finAvg S (fun i => u i * 1) = finAvg S u := by simp [finAvg]
  rw [this] at h
  calc finAvg S u ≤ _ := h
    _ ≤ Real.sqrt (finAvg S (fun i => u i ^ 2)) * 1 :=
      mul_le_mul_of_nonneg_left (by simpa using Real.sqrt_le_sqrt h1) (Real.sqrt_nonneg _)
    _ = _ := mul_one _

theorem finAvg_add {ι : Type*} (S : Finset ι) (f g : ι → ℝ) :
    finAvg S (fun i => f i + g i) = finAvg S f + finAvg S g := by
  unfold finAvg
  rw [Finset.sum_add_distrib, mul_add]

theorem finAvg_mul_left {ι : Type*} (S : Finset ι) (c : ℝ) (f : ι → ℝ) :
    finAvg S (fun i => c * f i) = c * finAvg S f := by
  unfold finAvg
  rw [← Finset.mul_sum]
  ring

theorem finAvg_mono {ι : Type*} (S : Finset ι) (f g : ι → ℝ) (h : ∀ i ∈ S, f i ≤ g i) :
    finAvg S f ≤ finAvg S g := by
  unfold finAvg
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum h) (by positivity)

theorem finAvg_split_aux {ι : Type*} (S : Finset ι) (F P Mn Lc Gc : ι → ℝ)
    (h : ∀ i ∈ S, F i + 2 * P i + 2 * Mn i = Lc i + Gc i) :
    finAvg S F + 2 * finAvg S P + 2 * finAvg S Mn =
      finAvg S Lc + finAvg S Gc := by
  unfold finAvg
  have : ∑ i ∈ S, (F i + 2 * P i + 2 * Mn i) = ∑ i ∈ S, (Lc i + Gc i) :=
    Finset.sum_congr rfl h
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib] at this
  linear_combination ((S.card : ℝ)⁻¹) * this

/-- Closing the five-term profile by Cauchy-Schwarz over the cells. -/
theorem L_profile_abstract {ι : Type*} (S : Finset ι)
    (Ωp Ωm ℓ μp μm : ι → ℝ)
    (hΩp : ∀ i, 0 ≤ Ωp i) (hΩm : ∀ i, 0 ≤ Ωm i) (hℓ : ∀ i, 0 ≤ ℓ i)
    (hμp : ∀ i, 0 ≤ μp i) (hμm : ∀ i, 0 ≤ μm i)
    (op om y x : ℝ) (hop : 0 ≤ op) (hom : 0 ≤ om) (hy : 0 ≤ y) (hx : 0 ≤ x)
    (hOp : finAvg S (fun i => Ωp i ^ 2) ≤ op ^ 2)
    (hOm : finAvg S (fun i => Ωm i ^ 2) ≤ om ^ 2)
    (hl : finAvg S (fun i => ℓ i ^ 2) ≤ y ^ 2)
    (hmp : finAvg S (fun i => μp i ^ 2) ≤ x ^ 2)
    (hmm : finAvg S (fun i => μm i ^ 2) ≤ y ^ 2)
    (c1 c2 c3 c4 c5 s r : ℝ) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (h3 : 0 ≤ c3) (h4 : 0 ≤ c4)
    (h5 : 0 ≤ c5) (hs : 0 ≤ s) (hr : 0 ≤ r) :
    finAvg S (fun i => c1 * μp i * Ωp i + c2 * Ωp i ^ 2 + c3 * (ℓ i * Ωm i) +
        c4 * Ωm i ^ 2 + c5 * (s * μm i + r * Ωm i)) ≤
      c1 * x * op + c2 * op ^ 2 + c3 * (y * om) + c4 * om ^ 2 + c5 * (s * y + r * om) := by
  have sq_le (a b : ℝ) (hb : 0 ≤ b) (h : a ≤ b ^ 2) : Real.sqrt a ≤ b := by
    calc Real.sqrt a ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt h
      _ = b := Real.sqrt_sq hb
  have aΩp := sq_le _ _ hop hOp
  have aΩm := sq_le _ _ hom hOm
  have aℓ := sq_le _ _ hy hl
  have aμp := sq_le _ _ hx hmp
  have aμm := sq_le _ _ hy hmm
  have t1 : finAvg S (fun i => μp i * Ωp i) ≤ x * op :=
    (finAvg_mul_le S μp Ωp).trans (mul_le_mul aμp aΩp (Real.sqrt_nonneg _) hx)
  have t3 : finAvg S (fun i => ℓ i * Ωm i) ≤ y * om :=
    (finAvg_mul_le S ℓ Ωm).trans (mul_le_mul aℓ aΩm (Real.sqrt_nonneg _) hy)
  have t5a : finAvg S μm ≤ y := (finAvg_le_sqrt S μm).trans aμm
  have t5b : finAvg S Ωm ≤ om := (finAvg_le_sqrt S Ωm).trans aΩm
  have e : (fun i => c1 * μp i * Ωp i + c2 * Ωp i ^ 2 + c3 * (ℓ i * Ωm i) +
        c4 * Ωm i ^ 2 + c5 * (s * μm i + r * Ωm i)) =
      fun i => c1 * (μp i * Ωp i) + c2 * Ωp i ^ 2 + c3 * (ℓ i * Ωm i) +
        c4 * Ωm i ^ 2 + c5 * (s * μm i + r * Ωm i) := by
    funext i; ring
  rw [e]
  simp only [finAvg_add, finAvg_mul_left]
  have := mul_le_mul_of_nonneg_left t1 h1
  have := mul_le_mul_of_nonneg_left hOp h2
  have := mul_le_mul_of_nonneg_left t3 h3
  have := mul_le_mul_of_nonneg_left hOm h4
  have := mul_le_mul_of_nonneg_left t5a hs
  have := mul_le_mul_of_nonneg_left t5b hr
  nlinarith [mul_le_mul_of_nonneg_left t1 h1, mul_le_mul_of_nonneg_left hOp h2,
    mul_le_mul_of_nonneg_left t3 h3, mul_le_mul_of_nonneg_left hOm h4,
    mul_le_mul_of_nonneg_left t5a hs, mul_le_mul_of_nonneg_left t5b hr,
    mul_nonneg h5 (sub_nonneg.mpr (add_le_add (mul_le_mul_of_nonneg_left t5a hs)
      (mul_le_mul_of_nonneg_left t5b hr)))]

end ASDExplicitGamma.Main
