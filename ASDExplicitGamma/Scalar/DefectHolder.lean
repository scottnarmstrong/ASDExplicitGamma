module

public import ASDExplicitGamma.Scalar.DefectTwoSlot

/-! Integrability of `B* H_n` by Hölder from the chaos moments of the two-slot Wick energy. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Gaussian Filter
open scoped BigOperators ENNReal Topology

noncomputable section

theorem two_slot_hBH {Ω 𝒪 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒪]
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
    (Bs : Ω → ℝ) (E1 Lq : ℝ) (hLq : 0 ≤ Lq)
    (hΛ1 : ∫ o, (ΛF o + ΛG o) ∂ν ≤ E1)
    (hΛq : eLpNorm (fun o => ΛF o + ΛG o) (ENNReal.ofReal (128 / 127)) ν ≤ ENNReal.ofReal Lq)
    (hBmem : MemLp Bs 128 μ) :
    Integrable (fun ω => Bs ω *
      (tiledPositiveEnergy Q m (psdDefectSource (BF (o ω)) (fun i : Fin n => z ω i)) +
       tiledPositiveEnergy Q m (psdDefectSource (BG (o ω)) (fun i : Fin n => z ω i)))) μ := by
  obtain ⟨hHint, hHq, hEH⟩ := two_slot_moments ν Q m BF BG hBF hBG hFmeas hGmeas ΛF ΛG
    hΛFm hΛGm hΛFi hΛGi hΛF0 hΛG0 κ2 hκ2 hwickF hwickG E1 Lq hLq hΛ1 hΛq
  let Ht : 𝒪 × (ℕ → ℝ) → ℝ := fun p =>
    tiledPositiveEnergy Q m (psdDefectSource (BF p.1) (fun i : Fin n => p.2 i)) +
    tiledPositiveEnergy Q m (psdDefectSource (BG p.1) (fun i : Fin n => p.2 i))
  let H : Ω → ℝ := fun ω => Ht (o ω, z ω)
  have hpair : Measurable (fun ω => (o ω, z ω)) := ho.prodMk hz
  have hHtm : Measurable Ht := hFmeas.add hGmeas
  have hHm : Measurable H := hHtm.comp hpair
  have hHq' : eLpNorm H (ENNReal.ofReal (128 / 127)) μ < ⊤ := by
    have e := eLpNorm_map_measure (μ := μ) (f := fun ω => (o ω, z ω))
      (p := ENNReal.ofReal (128 / 127)) (g := Ht) hHtm.aestronglyMeasurable hpair.aemeasurable
    rw [hcouple] at e
    have e' : eLpNorm H (ENNReal.ofReal (128 / 127)) μ =
        eLpNorm Ht (ENNReal.ofReal (128 / 127)) (ν.prod standardGaussianInfinitePi) := e.symm
    rw [e']
    exact lt_of_le_of_lt hHq ENNReal.ofReal_lt_top
  have hYmem : MemLp H (ENNReal.ofReal (128 / 127 : ℝ)) μ := by
    rw [memLp_iff]
    exact hHq'
  have hconj : (128 : ℝ).HolderConjugate (128 / 127 : ℝ) := by
    rw [Real.holderConjugate_iff_eq_conjExponent (by norm_num : (1 : ℝ) < 128)]
    norm_num
  letI : ENNReal.HolderTriple 128 (ENNReal.ofReal (128 / 127 : ℝ)) 1 := by
    simpa using hconj.ennrealOfReal
  letI : ENNReal.HolderTriple (ENNReal.ofReal 128)
      (ENNReal.ofReal (128 / 127 : ℝ)) 1 := hconj.ennrealOfReal
  exact hBmem.integrable_mul hYmem

end

end ASDExplicitGamma.Scalar
