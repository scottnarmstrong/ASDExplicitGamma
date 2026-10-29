module

public import ASDExplicitGamma.Gaussian.NonnegativeFatou
public import ASDExplicitGamma.Scalar.DefectTruncation

/-! Two-slot version of the uniform-in-truncation moment bound: the energy is
`H = H^F + H^G`, the sum of the flux-slot and potential-slot tiled positive-Haar energies. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open MeasureTheory ProbabilityTheory ASDExplicitGamma.Gaussian Homogenization Filter Topology
  ASDExplicitGamma.Variational
open scoped ENNReal

/-- Moments of a jointly measurable nonnegative `H` on `ν ⊗ γ` from fibre bounds. -/
theorem moments_of_fibres {𝒪 : Type*} [MeasurableSpace 𝒪] (ν : Measure 𝒪)
    [IsProbabilityMeasure ν] (H : 𝒪 × (ℕ → ℝ) → ℝ) (hHm : Measurable H)
    (Λ : 𝒪 → ℝ) (hΛm : Measurable Λ) (hΛi : Integrable Λ ν) (hΛ0 : ∀ o, 0 ≤ Λ o)
    (κ2 : ℝ) (hκ2 : 0 ≤ κ2) (E1 Lq : ℝ) (hLq : 0 ≤ Lq)
    (hΛ1 : ∫ o, Λ o ∂ν ≤ E1)
    (hΛq : eLpNorm Λ (ENNReal.ofReal (128 / 127)) ν ≤ ENNReal.ofReal Lq)
    (hint_fib : ∀ o, ∫ z, H (o, z) ∂standardGaussianInfinitePi ≤ κ2 * Λ o)
    (hnorm_fib : ∀ o, eLpNorm (fun z => H (o, z)) (ENNReal.ofReal (128 / 127))
      standardGaussianInfinitePi ≤
      ENNReal.ofReal ((1 + Real.sqrt 15) ^ (2 / (128 : ℝ)) * (κ2 * Λ o))) :
    Integrable H (ν.prod standardGaussianInfinitePi) ∧
      eLpNorm H (ENNReal.ofReal (128 / 127)) (ν.prod standardGaussianInfinitePi) ≤
        ENNReal.ofReal ((1 + Real.sqrt 15) ^ (2 / (128 : ℝ)) * κ2 * Lq) ∧
      ∫ p, H p ∂(ν.prod standardGaussianInfinitePi) ≤ κ2 * E1 := by
  set γ := standardGaussianInfinitePi
  set Cp : ℝ := (1 + Real.sqrt 15) ^ (2 / (128 : ℝ)) with hCp
  have hCp0 : 0 ≤ Cp := by positivity
  have hq0 : ENNReal.ofReal (128 / 127) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; norm_num
  have hqtop : ENNReal.ofReal (128 / 127) ≠ ∞ := ENNReal.ofReal_ne_top
  have hqr : (ENNReal.ofReal (128 / 127)).toReal = 128 / 127 :=
    ENNReal.toReal_ofReal (by norm_num)
  have hprod := eLpNorm_prod_le ν γ (fun o z => H (o, z)) hHm _ hq0 hqtop
    (fun o => ENNReal.ofReal (Cp * (κ2 * Λ o))) hnorm_fib
  -- the right side is the norm of Cp*κ2*Λ
  have hmeasΛ' : Measurable (fun o => Cp * (κ2 * Λ o)) := measurable_const.mul (measurable_const.mul hΛm)
  have hrhs : (∫⁻ o, ENNReal.ofReal (Cp * (κ2 * Λ o)) ^ (ENNReal.ofReal (128 / 127)).toReal ∂ν) ^
      (1 / (ENNReal.ofReal (128 / 127)).toReal) ≤ ENNReal.ofReal (Cp * κ2 * Lq) := by
    have hn := eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop
      (μ := ν) (f := fun o => (Cp * κ2) * Λ o) (measurable_const.mul hΛm).aestronglyMeasurable
    have e1 : (∫⁻ o, ENNReal.ofReal (Cp * (κ2 * Λ o)) ^ (ENNReal.ofReal (128 / 127)).toReal ∂ν) =
        ∫⁻ o, ‖(Cp * κ2) * Λ o‖ₑ ^ (ENNReal.ofReal (128 / 127)).toReal ∂ν := by
      refine lintegral_congr fun o => ?_
      rw [Real.enorm_of_nonneg (by have := hΛ0 o; positivity)]
      ring_nf
    rw [e1, ← hn]
    have h2 : eLpNorm (fun o => (Cp * κ2) * Λ o) (ENNReal.ofReal (128 / 127)) ν =
        ‖Cp * κ2‖ₑ * eLpNorm Λ (ENNReal.ofReal (128 / 127)) ν := by
      have h := eLpNorm_const_smul (μ := ν) (p := ENNReal.ofReal (128 / 127)) (Cp * κ2) Λ
      exact h
    rw [h2, Real.enorm_of_nonneg (by positivity)]
    calc ENNReal.ofReal (Cp * κ2) * eLpNorm Λ (ENNReal.ofReal (128 / 127)) ν
        ≤ ENNReal.ofReal (Cp * κ2) * ENNReal.ofReal Lq := mul_le_mul' le_rfl hΛq
      _ = ENNReal.ofReal (Cp * κ2 * Lq) := (ENNReal.ofReal_mul (by positivity)).symm
  have hHq : eLpNorm H (ENNReal.ofReal (128 / 127)) (ν.prod γ) ≤ ENNReal.ofReal (Cp * κ2 * Lq) :=
    hprod.trans hrhs
  have hHaes : AEStronglyMeasurable H (ν.prod γ) := hHm.aestronglyMeasurable
  have hHmem : MemLp H (ENNReal.ofReal (128 / 127)) (ν.prod γ) :=
    memLp_iff.mpr (lt_of_le_of_lt hHq ENNReal.ofReal_lt_top)
  have hHint : Integrable H (ν.prod γ) :=
    hHmem.integrable (by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num))
  have hEH : ∫ p, H p ∂(ν.prod γ) ≤ κ2 * E1 := by
    rw [integral_prod _ hHint]
    calc ∫ o, ∫ z, H (o, z) ∂γ ∂ν ≤ ∫ o, κ2 * Λ o ∂ν := by
          refine integral_mono hHint.integral_prod_left ?_ hint_fib
          exact hΛi.const_mul κ2
      _ = κ2 * ∫ o, Λ o ∂ν := integral_const_mul _ _
      _ ≤ κ2 * E1 := mul_le_mul_of_nonneg_left hΛ1 hκ2
  exact ⟨hHint, hHq, hEH⟩


/-- Fibre data of one slot on the infinite Gaussian product. -/
theorem slot_fibre (Q : TriadicCube 2) (m : ℕ) {n : ℕ}
    (B : Fin n → Fin n → TiledHaarField Q m) (hB : ∀ i j, B i j = B j i) (K : ℝ)
    (hK : tiledPositiveEnergy Q m (∑ i, B i i) +
        2 * ∑ i, ∑ j, tiledPositiveEnergy Q m (B i j) ≤ K) :
    let H : (ℕ → ℝ) → ℝ := fun z => tiledPositiveEnergy Q m
      (psdDefectSource B (fun i : Fin n => z i))
    Measurable H ∧ Integrable H standardGaussianInfinitePi ∧
      ∫ z, H z ∂standardGaussianInfinitePi ≤ K ∧
      eLpNorm H (ENNReal.ofReal (128 / 127)) standardGaussianInfinitePi ≤
        ENNReal.ofReal ((1 + Real.sqrt 15) ^ (2 / (128 : ℝ)) * K) := by
  intro H
  obtain ⟨hint, hle, hnorm⟩ := fibre_bounds Q m B hB K hK
  let f : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    tiledPositiveEnergy Q m (psdDefectSource B (fun i => y i))
  have hfm : Measurable f := tiled_defect_measurable Q m B
  have hH : H = fun z => f (gaussianFirstCoordinates n z) := rfl
  have hmap := map_gaussian_first_coordinates n
  have hHm : Measurable H := by
    rw [hH]; exact hfm.comp (gaussian_first_coordinates_measurable n)
  refine ⟨hHm, ?_, ?_, ?_⟩
  · rw [hH]
    have : Integrable f (standardGaussianInfinitePi.map (gaussianFirstCoordinates n)) := by
      rw [hmap]; exact hint
    exact (integrable_map_measure hfm.aestronglyMeasurable
      (gaussian_first_coordinates_measurable n).aemeasurable).1 this
  · rw [hH, integral_gaussian_first_coordinates_comp n f hfm]; exact hle
  · have e : eLpNorm H (ENNReal.ofReal (128 / 127)) standardGaussianInfinitePi =
        eLpNorm f (ENNReal.ofReal (128 / 127)) (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
      rw [← hmap]
      exact (eLpNorm_map_measure hfm.aestronglyMeasurable
        (gaussian_first_coordinates_measurable n).aemeasurable).symm
    rw [e]; exact hnorm

/-- Two-slot moments: `H = H^F + H^G` with Wick bounds `κ2 Λ^F`, `κ2 Λ^G` and budget on
`Λ = Λ^F + Λ^G`. -/
theorem two_slot_moments {𝒪 : Type*} [MeasurableSpace 𝒪] (ν : Measure 𝒪)
    [IsProbabilityMeasure ν] (Q : TriadicCube 2) (m : ℕ) {n : ℕ}
    (BF BG : 𝒪 → Fin n → Fin n → TiledHaarField Q m)
    (hBF : ∀ o i j, BF o i j = BF o j i) (hBG : ∀ o i j, BG o i j = BG o j i)
    (hFmeas : Measurable (fun p : 𝒪 × (ℕ → ℝ) =>
      tiledPositiveEnergy Q m (psdDefectSource (BF p.1) (fun i : Fin n => p.2 i))))
    (hGmeas : Measurable (fun p : 𝒪 × (ℕ → ℝ) =>
      tiledPositiveEnergy Q m (psdDefectSource (BG p.1) (fun i : Fin n => p.2 i))))
    (ΛF ΛG : 𝒪 → ℝ) (hΛFm : Measurable ΛF) (hΛGm : Measurable ΛG)
    (hΛFi : Integrable ΛF ν) (hΛGi : Integrable ΛG ν)
    (hΛF0 : ∀ o, 0 ≤ ΛF o) (hΛG0 : ∀ o, 0 ≤ ΛG o)
    (κ2 : ℝ) (hκ2 : 0 ≤ κ2)
    (hwickF : ∀ o, tiledPositiveEnergy Q m (∑ i, BF o i i) +
        2 * ∑ i, ∑ j, tiledPositiveEnergy Q m (BF o i j) ≤ κ2 * ΛF o)
    (hwickG : ∀ o, tiledPositiveEnergy Q m (∑ i, BG o i i) +
        2 * ∑ i, ∑ j, tiledPositiveEnergy Q m (BG o i j) ≤ κ2 * ΛG o)
    (E1 Lq : ℝ) (hLq : 0 ≤ Lq)
    (hΛ1 : ∫ o, (ΛF o + ΛG o) ∂ν ≤ E1)
    (hΛq : eLpNorm (fun o => ΛF o + ΛG o) (ENNReal.ofReal (128 / 127)) ν ≤ ENNReal.ofReal Lq) :
    let H : 𝒪 × (ℕ → ℝ) → ℝ := fun p =>
      tiledPositiveEnergy Q m (psdDefectSource (BF p.1) (fun i : Fin n => p.2 i)) +
      tiledPositiveEnergy Q m (psdDefectSource (BG p.1) (fun i : Fin n => p.2 i))
    Integrable H (ν.prod standardGaussianInfinitePi) ∧
      eLpNorm H (ENNReal.ofReal (128 / 127)) (ν.prod standardGaussianInfinitePi) ≤
        ENNReal.ofReal ((1 + Real.sqrt 15) ^ (2 / (128 : ℝ)) * κ2 * Lq) ∧
      ∫ p, H p ∂(ν.prod standardGaussianInfinitePi) ≤ κ2 * E1 := by
  intro H
  set Cp : ℝ := (1 + Real.sqrt 15) ^ (2 / (128 : ℝ)) with hCp
  have hCp0 : 0 ≤ Cp := by positivity
  refine moments_of_fibres ν H (hFmeas.add hGmeas) (fun o => ΛF o + ΛG o)
    (hΛFm.add hΛGm) (hΛFi.add hΛGi) (fun o => add_nonneg (hΛF0 o) (hΛG0 o)) κ2 hκ2 E1 Lq hLq
    hΛ1 hΛq ?_ ?_
  · intro o
    obtain ⟨hmF, hiF, hlF, -⟩ := slot_fibre Q m (BF o) (hBF o) _ (hwickF o)
    obtain ⟨hmG, hiG, hlG, -⟩ := slot_fibre Q m (BG o) (hBG o) _ (hwickG o)
    change ∫ z, (tiledPositiveEnergy Q m (psdDefectSource (BF o) (fun i : Fin n => z i)) +
      tiledPositiveEnergy Q m (psdDefectSource (BG o) (fun i : Fin n => z i)))
        ∂standardGaussianInfinitePi ≤ _
    rw [integral_add hiF hiG]
    linarith
  · intro o
    obtain ⟨hmF, hiF, hlF, hnF⟩ := slot_fibre Q m (BF o) (hBF o) _ (hwickF o)
    obtain ⟨hmG, hiG, hlG, hnG⟩ := slot_fibre Q m (BG o) (hBG o) _ (hwickG o)
    have h := eLpNorm_add_le
      (f := fun z => tiledPositiveEnergy Q m (psdDefectSource (BF o) (fun i : Fin n => z i)))
      (g := fun z => tiledPositiveEnergy Q m (psdDefectSource (BG o) (fun i : Fin n => z i)))
      (p := ENNReal.ofReal (128 / 127)) (μ := standardGaussianInfinitePi)
      (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num))
    change eLpNorm (fun z => tiledPositiveEnergy Q m (psdDefectSource (BF o) (fun i : Fin n => z i)) +
      tiledPositiveEnergy Q m (psdDefectSource (BG o) (fun i : Fin n => z i)))
        (ENNReal.ofReal (128 / 127)) standardGaussianInfinitePi ≤ _
    refine h.trans ?_
    refine (add_le_add hnF hnG).trans ?_
    rw [← ENNReal.ofReal_add (by have := hΛF0 o; positivity) (by have := hΛG0 o; positivity)]
    apply le_of_eq
    congr 1
    ring


/-- Coupled two-slot bound on a sample space carrying `(old, z)` with law `ν ⊗ γ`. -/
theorem two_slot_coupled_bound {Ω 𝒪 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒪]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure 𝒪) [IsProbabilityMeasure ν]
    (o : Ω → 𝒪) (z : Ω → ℕ → ℝ) (ho : Measurable o) (hz : Measurable z)
    (hcouple : μ.map (fun ω => (o ω, z ω)) = ν.prod standardGaussianInfinitePi)
    (Q : TriadicCube 2) (m : ℕ) {n : ℕ}
    (BF BG : 𝒪 → Fin n → Fin n → TiledHaarField Q m)
    (hBF : ∀ o i j, BF o i j = BF o j i) (hBG : ∀ o i j, BG o i j = BG o j i)
    (hFmeas : Measurable (fun p : 𝒪 × (ℕ → ℝ) =>
      tiledPositiveEnergy Q m (psdDefectSource (BF p.1) (fun i : Fin n => p.2 i))))
    (hGmeas : Measurable (fun p : 𝒪 × (ℕ → ℝ) =>
      tiledPositiveEnergy Q m (psdDefectSource (BG p.1) (fun i : Fin n => p.2 i))))
    (ΛF ΛG : 𝒪 → ℝ) (hΛFm : Measurable ΛF) (hΛGm : Measurable ΛG)
    (hΛFi : Integrable ΛF ν) (hΛGi : Integrable ΛG ν)
    (hΛF0 : ∀ o, 0 ≤ ΛF o) (hΛG0 : ∀ o, 0 ≤ ΛG o) (κ2 : ℝ) (hκ2 : 0 ≤ κ2)
    (hwickF : ∀ o, tiledPositiveEnergy Q m (∑ i, BF o i i) +
        2 * ∑ i, ∑ j, tiledPositiveEnergy Q m (BF o i j) ≤ κ2 * ΛF o)
    (hwickG : ∀ o, tiledPositiveEnergy Q m (∑ i, BG o i i) +
        2 * ∑ i, ∑ j, tiledPositiveEnergy Q m (BG o i j) ≤ κ2 * ΛG o)
    (Bs R : Ω → ℝ) (hRm : Measurable R) (b ε E1 Lq : ℝ)
    (hb : 0 ≤ b) (hε : 0 ≤ ε) (hLq : 0 ≤ Lq)
    (hBR : ∀ ω, Bs ω ≤ b + R ω) (hR0 : ∀ ω, 0 ≤ R ω)
    (hΛ1 : ∫ o, (ΛF o + ΛG o) ∂ν ≤ E1)
    (hΛq : eLpNorm (fun o => ΛF o + ΛG o) (ENNReal.ofReal (128 / 127)) ν ≤ ENNReal.ofReal Lq)
    (hR : eLpNorm R 128 μ ≤ ENNReal.ofReal ε)
    (hBH : Integrable (fun ω => Bs ω *
      (tiledPositiveEnergy Q m (psdDefectSource (BF (o ω)) (fun i : Fin n => z ω i)) +
       tiledPositiveEnergy Q m (psdDefectSource (BG (o ω)) (fun i : Fin n => z ω i)))) μ) :
    ∫ ω, Bs ω * (tiledPositiveEnergy Q m
        (psdDefectSource (BF (o ω)) (fun i : Fin n => z ω i)) +
      tiledPositiveEnergy Q m
        (psdDefectSource (BG (o ω)) (fun i : Fin n => z ω i))) ∂μ ≤
      κ2 * (b * E1 + ε * ((1 + Real.sqrt 15) ^ (2 / (128 : ℝ)) * Lq)) := by
  set Cp : ℝ := (1 + Real.sqrt 15) ^ (2 / (128 : ℝ)) with hCp
  have hCp0 : 0 ≤ Cp := by positivity
  obtain ⟨hHint, hHq, hEH⟩ := two_slot_moments ν Q m BF BG hBF hBG hFmeas hGmeas ΛF ΛG
    hΛFm hΛGm hΛFi hΛGi hΛF0 hΛG0 κ2 hκ2 hwickF hwickG E1 Lq hLq hΛ1 hΛq
  let Ht : 𝒪 × (ℕ → ℝ) → ℝ := fun p =>
    tiledPositiveEnergy Q m (psdDefectSource (BF p.1) (fun i : Fin n => p.2 i)) +
    tiledPositiveEnergy Q m (psdDefectSource (BG p.1) (fun i : Fin n => p.2 i))
  let H : Ω → ℝ := fun ω => Ht (o ω, z ω)
  have hpair : Measurable (fun ω => (o ω, z ω)) := ho.prodMk hz
  have hHtm : Measurable Ht := hFmeas.add hGmeas
  have hHm : Measurable H := hHtm.comp hpair
  have hH0 : ∀ ω, 0 ≤ H ω := fun ω =>
    add_nonneg (lemmaVTiledPositiveEnergy_nonneg Q m _) (lemmaVTiledPositiveEnergy_nonneg Q m _)
  have hHq' : eLpNorm H (ENNReal.ofReal (128 / 127)) μ ≤ ENNReal.ofReal (Cp * κ2 * Lq) := by
    have e := eLpNorm_map_measure (μ := μ) (f := fun ω => (o ω, z ω))
      (p := ENNReal.ofReal (128 / 127)) (g := Ht) hHtm.aestronglyMeasurable hpair.aemeasurable
    rw [hcouple] at e
    exact e.symm.le.trans hHq
  have hHint' : Integrable H μ := by
    have := (integrable_map_measure hHtm.aestronglyMeasurable hpair.aemeasurable).1
      (by rw [hcouple]; exact hHint)
    exact this
  have hEH' : ∫ ω, H ω ∂μ ≤ κ2 * E1 := by
    have e := integral_map hpair.aemeasurable hHtm.aestronglyMeasurable (μ := μ)
    rw [hcouple] at e
    calc ∫ ω, H ω ∂μ = ∫ p, Ht p ∂(ν.prod standardGaussianInfinitePi) := e.symm
      _ ≤ _ := hEH
  have hfin := defect_bank_holder (μ := μ) (Bs := Bs) (R := R) (H := H)
    (b := b) (ε := ε) (g := Cp * κ2 * Lq) (Eh := κ2 * E1) hRm hHm hBR hR0 hH0 hε
    (by positivity) hR hHq' hHint' hBH hEH' hb
  calc _ ≤ b * (κ2 * E1) + ε * (Cp * κ2 * Lq) := hfin
    _ = _ := by ring

/-- Two-slot assembly from pieces: pathwise `D_n ≤ Dc · B* · (H^F_n + H^G_n)`. -/
theorem two_slot_of_pieces {Ω 𝒪 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒪]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure 𝒪) [IsProbabilityMeasure ν]
    (o : Ω → 𝒪) (z : Ω → ℕ → ℝ) (ho : Measurable o) (hz : Measurable z)
    (hcouple : μ.map (fun ω => (o ω, z ω)) = ν.prod standardGaussianInfinitePi)
    (Q : TriadicCube 2) (m : ℕ)
    (BF BG : ∀ n : ℕ, 𝒪 → Fin n → Fin n → TiledHaarField Q m)
    (hBF : ∀ n o i j, BF n o i j = BF n o j i) (hBG : ∀ n o i j, BG n o i j = BG n o j i)
    (hFmeas : ∀ n, Measurable (fun p : 𝒪 × (ℕ → ℝ) =>
      tiledPositiveEnergy Q m (psdDefectSource (BF n p.1) (fun i : Fin n => p.2 i))))
    (hGmeas : ∀ n, Measurable (fun p : 𝒪 × (ℕ → ℝ) =>
      tiledPositiveEnergy Q m (psdDefectSource (BG n p.1) (fun i : Fin n => p.2 i))))
    (ΛF ΛG : ℕ → 𝒪 → ℝ) (hΛFm : ∀ n, Measurable (ΛF n)) (hΛGm : ∀ n, Measurable (ΛG n))
    (hΛFi : ∀ n, Integrable (ΛF n) ν) (hΛGi : ∀ n, Integrable (ΛG n) ν)
    (hΛF0 : ∀ n o, 0 ≤ ΛF n o) (hΛG0 : ∀ n o, 0 ≤ ΛG n o) (κ2 : ℝ) (hκ2 : 0 ≤ κ2)
    (hwickF : ∀ n o, tiledPositiveEnergy Q m (∑ i, BF n o i i) +
        2 * ∑ i, ∑ j, tiledPositiveEnergy Q m (BF n o i j) ≤ κ2 * ΛF n o)
    (hwickG : ∀ n o, tiledPositiveEnergy Q m (∑ i, BG n o i i) +
        2 * ∑ i, ∑ j, tiledPositiveEnergy Q m (BG n o i j) ≤ κ2 * ΛG n o)
    (Bs R : Ω → ℝ) (hRm : Measurable R) (b ε E1 Lq : ℝ)
    (hb : 0 ≤ b) (hε : 0 ≤ ε) (hLq : 0 ≤ Lq)
    (hBs0 : ∀ ω, 0 ≤ Bs ω) (hBR : ∀ ω, Bs ω ≤ b + R ω) (hR0 : ∀ ω, 0 ≤ R ω)
    (hΛ1 : ∀ n, ∫ o, (ΛF n o + ΛG n o) ∂ν ≤ E1)
    (hΛq : ∀ n, eLpNorm (fun o => ΛF n o + ΛG n o) (ENNReal.ofReal (128 / 127)) ν ≤
      ENNReal.ofReal Lq)
    (hR : eLpNorm R 128 μ ≤ ENNReal.ofReal ε)
    (hBH : ∀ n, Integrable (fun ω => Bs ω *
      (tiledPositiveEnergy Q m (psdDefectSource (BF n (o ω)) (fun i : Fin n => z ω i)) +
       tiledPositiveEnergy Q m (psdDefectSource (BG n (o ω)) (fun i : Fin n => z ω i)))) μ)
    (Dc : ℝ) (hDc : 0 ≤ Dc) (Dn : ℕ → Ω → ℝ) (Dinf : Ω → ℝ)
    (hDnm : ∀ n, Measurable (Dn n)) (hDinfm : Measurable Dinf)
    (hpath : ∀ n ω, Dn n ω ≤ Dc * (Bs ω *
      (tiledPositiveEnergy Q m (psdDefectSource (BF n (o ω)) (fun i : Fin n => z ω i)) +
       tiledPositiveEnergy Q m (psdDefectSource (BG n (o ω)) (fun i : Fin n => z ω i)))))
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => Dn n ω) atTop (𝓝 (Dinf ω))) :
    Integrable (fun ω => max (Dinf ω) 0) μ ∧
      ∫ ω, max (Dinf ω) 0 ∂μ ≤
        Dc * (κ2 * (b * E1 + ε * ((1 + Real.sqrt 15) ^ (2 / (128 : ℝ)) * Lq))) := by
  set C := κ2 * (b * E1 + ε * ((1 + Real.sqrt 15) ^ (2 / (128 : ℝ)) * Lq)) with hC
  let G : ℕ → Ω → ℝ := fun n ω => Bs ω *
    (tiledPositiveEnergy Q m (psdDefectSource (BF n (o ω)) (fun i : Fin n => z ω i)) +
     tiledPositiveEnergy Q m (psdDefectSource (BG n (o ω)) (fun i : Fin n => z ω i)))
  have hG0 : ∀ n ω, 0 ≤ G n ω := fun n ω =>
    mul_nonneg (hBs0 ω) (add_nonneg (lemmaVTiledPositiveEnergy_nonneg Q m _)
      (lemmaVTiledPositiveEnergy_nonneg Q m _))
  have hGb : ∀ n, ∫ ω, G n ω ∂μ ≤ C := fun n =>
    two_slot_coupled_bound μ ν o z ho hz hcouple Q m (BF n) (BG n) (hBF n) (hBG n)
      (hFmeas n) (hGmeas n) (ΛF n) (ΛG n) (hΛFm n) (hΛGm n) (hΛFi n) (hΛGi n) (hΛF0 n)
      (hΛG0 n) κ2 hκ2 (hwickF n) (hwickG n) Bs R hRm b ε E1 Lq hb hε hLq hBR hR0 (hΛ1 n)
      (hΛq n) hR (hBH n)
  have hf0 : ∀ n, 0 ≤ᵐ[μ] fun ω => max (Dn n ω) 0 :=
    fun n => Filter.Eventually.of_forall fun ω => le_max_right _ _
  have hfint : ∀ n, Integrable (fun ω => max (Dn n ω) 0) μ := by
    intro n
    refine Integrable.mono' ((hBH n).const_mul Dc) ((hDnm n).max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (hpath n ω) (mul_nonneg hDc (hG0 n ω))
  have hfb : ∀ n, ∫ ω, max (Dn n ω) 0 ∂μ ≤ Dc * C := by
    intro n
    calc ∫ ω, max (Dn n ω) 0 ∂μ ≤ ∫ ω, Dc * G n ω ∂μ :=
          integral_mono (hfint n) ((hBH n).const_mul Dc) fun ω =>
            max_le (hpath n ω) (mul_nonneg hDc (hG0 n ω))
      _ = Dc * ∫ ω, G n ω ∂μ := integral_const_mul _ _
      _ ≤ Dc * C := mul_le_mul_of_nonneg_left (hGb n) hDc
  have hlim' : ∀ᵐ ω ∂μ, Tendsto (fun n => max (Dn n ω) 0) atTop (𝓝 (max (Dinf ω) 0)) := by
    filter_upwards [hlim] with ω hω
    exact hω.max tendsto_const_nhds
  exact Gaussian.integrable_integral_le_of_ae_tendsto_nonneg μ hfint hf0
    (hDinfm.max measurable_const).aestronglyMeasurable hlim' hfb

end ASDExplicitGamma.Scalar
