module

public import ASDExplicitGamma.Inverse.RawMomentChain
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! One-sided integration of the nonnegative p=20 moment root. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory Set
open scoped Topology

/-- A one-sided differential inequality for the twentieth moment suffices to
control its twentieth root. The proof regularizes by `ε` and therefore also
covers times at which the moment vanishes. -/
theorem raw_p20_moment_root_sub_le_integral {f df U : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1))
    (hf0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ f t)
    (hdf : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt f (df t) t)
    (hU0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ U t)
    (hU : IntegrableOn U (Icc 0 1))
    (hb : ∀ t ∈ Ioo (0 : ℝ) 1,
      df t ≤ 20 * f t ^ ((19 : ℝ) / 20) * U t)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    f t ^ ((20 : ℝ)⁻¹) - f s ^ ((20 : ℝ)⁻¹) ≤ ∫ r in s..t, U r := by
  have hp : 1 < (20 : ℝ) := by norm_num
  have hq : 0 < (20 : ℝ)⁻¹ := inv_pos.mpr (by norm_num)
  have he (ε : ℝ) (hε : 0 < ε) :
      (f t + ε) ^ (20 : ℝ)⁻¹ - (f s + ε) ^ (20 : ℝ)⁻¹ ≤ ∫ r in s..t, U r := by
    let g : ℝ → ℝ := fun r => (f r + ε) ^ (20 : ℝ)⁻¹
    let dg : ℝ → ℝ := fun r => (20 : ℝ)⁻¹ * (f r + ε) ^ ((20 : ℝ)⁻¹ - 1) * df r
    have hsub : Icc s t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hs ht
    apply intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hst
      (g := g) (g' := dg) ?_ ?_ (hU.mono_set hsub) ?_
    · exact (hf.mono hsub |>.add continuousOn_const).rpow_const
        (fun r hr => Or.inl
          (add_pos_of_nonneg_of_pos (hf0 r (hsub hr)) hε).ne')
    · intro r hr
      convert (((hdf r ⟨hs.trans_lt hr.1, hr.2.trans_le ht⟩).add_const ε).rpow_const
        (p := (20 : ℝ)⁻¹)
        (Or.inl (add_pos_of_nonneg_of_pos
          (hf0 r (hsub ⟨hr.1.le, hr.2.le⟩)) hε).ne')).hasDerivWithinAt
          (s := Ioi r) using 1
      dsimp only [g, dg]
      ring
    · intro r hr
      have hmem : r ∈ Icc (0 : ℝ) 1 := hsub ⟨hr.1.le, hr.2.le⟩
      have ha : 0 ≤ f r := hf0 r hmem
      have hexp : 0 ≤ 1 - (20 : ℝ)⁻¹ := by norm_num
      have hpow : f r ^ (1 - (20 : ℝ)⁻¹) ≤ (f r + ε) ^ (1 - (20 : ℝ)⁻¹) :=
        Real.rpow_le_rpow ha (by linarith) hexp
      have hprod : (f r + ε) ^ ((20 : ℝ)⁻¹ - 1) *
          f r ^ (1 - (20 : ℝ)⁻¹) ≤ 1 := by
        calc
          _ ≤ (f r + ε) ^ ((20 : ℝ)⁻¹ - 1) *
              (f r + ε) ^ (1 - (20 : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left hpow
              (Real.rpow_nonneg (by linarith : 0 ≤ f r + ε) _)
          _ = 1 := by
            have hbase : 0 < f r + ε := add_pos_of_nonneg_of_pos ha hε
            rw [← Real.rpow_add hbase]
            norm_num
      have hc : 0 ≤ (20 : ℝ)⁻¹ * (f r + ε) ^ ((20 : ℝ)⁻¹ - 1) := by positivity
      have hscaled := mul_le_mul_of_nonneg_left (hb r ⟨hs.trans_lt hr.1, hr.2.trans_le ht⟩) hc
      have hcoef : (20 : ℝ)⁻¹ * (f r + ε) ^ ((20 : ℝ)⁻¹ - 1) *
          (20 : ℝ) * f r ^ (1 - (20 : ℝ)⁻¹) =
          (f r + ε) ^ ((20 : ℝ)⁻¹ - 1) * f r ^ (1 - (20 : ℝ)⁻¹) := by
        field_simp
      have hprodU := mul_le_mul_of_nonneg_right hprod (hU0 r hmem)
      dsimp only [dg]
      rw [show ((19 : ℝ) / 20) = 1 - (20 : ℝ)⁻¹ by norm_num] at hscaled
      calc
        _ ≤ (20 : ℝ)⁻¹ * (f r + ε) ^ ((20 : ℝ)⁻¹ - 1) *
            (20 * f r ^ (1 - (20 : ℝ)⁻¹) * U r) := hscaled
        _ = ((20 : ℝ)⁻¹ * (f r + ε) ^ ((20 : ℝ)⁻¹ - 1) *
            (20 : ℝ) * f r ^ (1 - (20 : ℝ)⁻¹)) * U r := by ring
        _ = ((f r + ε) ^ ((20 : ℝ)⁻¹ - 1) *
            f r ^ (1 - (20 : ℝ)⁻¹)) * U r := by rw [hcoef]
        _ ≤ U r := by nlinarith only [hprodU]
  have hc (r : ℝ) : ContinuousAt (fun ε : ℝ => (f r + ε) ^ (20 : ℝ)⁻¹) 0 :=
    (continuousAt_const.add continuousAt_id).rpow_const (Or.inr hq.le)
  have hlim := (hc t).tendsto.sub (hc s).tendsto
  simp only [add_zero] at hlim
  apply le_of_tendsto (hlim.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds))
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact he ε hε

end ASDExplicitGamma.Inverse
