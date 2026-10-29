module

public import ASDExplicitGamma.Native.HeatConfiguredBillIntegral
public import ASDExplicitGamma.Native.HeatVHEATThetaFixedEps
public import ASDExplicitGamma.Native.HeatRemainderMoments
public import ASDExplicitGamma.Native.HeatInitialRefinedNumeric

/-! Theta-scaled individual source bill: with the trace cap `θ·old.x`, the drift `e' ≤ θ·old.e`
and the fixed rare reserve, the integrated bill is paid by the endpoint row with the
subdiagonal and force entries carrying the factors `θ` and `θ^k`. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native MeasureTheory
open scoped ENNReal
noncomputable section

theorem heat_configured_individual_bill_integral_theta_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (index : Fin 153) (R T : Ω → ℝ)
    (hR : AEStronglyMeasurable R μ) (hT : AEStronglyMeasurable T μ)
    (hR0 : ∀ z,0 ≤ R z) (hT0 : ∀ z,0 ≤ T z)
    (k : ℕ) (hk : 1 ≤ k) (hk20 : k ≤ 20)
    (τ e' : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (he' : 0 ≤ e')
    (hee : e' ≤ τ * ((nativeOld (nativeConfiguredSystem index).gap).e : ℝ))
    (hRc : eLpNorm' R 128 μ ≤ ENNReal.ofReal (nativeEps:ℝ))
    (h20 : eLpNorm' T 20 μ ≤
      ENNReal.ofReal (τ * ((nativeOld (nativeConfiguredSystem index).gap).x:ℝ)))
    (h128 : eLpNorm' T 128 μ ≤ ENNReal.ofReal ((nativeOld (nativeConfiguredSystem index).gap).f:ℝ)) :
    let height := (nativeConfiguredSystem index).gap
    let old := nativeOld height
    let c : ℝ := 1975/1000+2*((k-1:ℕ):ℝ)*(1565/1000)
    let d : ℝ := 2*(height:ℝ)+4*((k:ℝ)-1)*((height:ℝ)+521/1000)
    let row := nativeIndividualRow height k old
    Integrable (fun z => heatIndividualSourceBill k e' d (521/1000) c nativeB (T z) (R z)) μ ∧
    (∫ z,heatIndividualSourceBill k e' d (521/1000) c nativeB (T z) (R z) ∂μ) ≤
      (nativeA:ℝ)*τ*(row.1:ℝ)*(∫ z,T z^(k-1) ∂μ)+
        (row.2.1:ℝ)*(∫ z,T z^k ∂μ)+((nativeA:ℝ)*τ)^k*(row.2.2:ℝ) := by
  intro height old c d row
  obtain ⟨he, hx, hf, hroot1, hroot2⟩ := heat_configured_individual_old_valid index
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hkm : 0 ≤ (k:ℝ)-1 := sub_nonneg.mpr hkR
  have hxR : (0:ℝ) < (old.x:ℝ) := by exact_mod_cast hx
  have hfR : (0:ℝ) ≤ (old.f:ℝ) := by exact_mod_cast hf
  have hτx : 0 < τ * (old.x:ℝ) := mul_pos hτ hxR
  have hprev := heat_individual_power_integrable μ T hT hT0 (τ * (old.x:ℝ)) h20 (k-1) (by omega)
  have hcur := heat_individual_power_integrable μ T hT hT0 (τ * (old.x:ℝ)) h20 k hk20
  have hroot : ∀ j : Fin 2, nativeRootValid ((old.f/old.x)^(5*(j.val+1))) 27 = true := by
    intro j
    fin_cases j
    · exact hroot1
    · exact hroot2
  -- rare moments with the theta-scaled trace cap
  have hrare : ∀ (j : Fin 2) (l : ℕ), l ≤ 20 → k - 1 ≤ l → l ≤ k →
      Integrable (fun z => R z^(j.val+1)*T z^l) μ ∧
        (∫ z,R z^(j.val+1)*T z^l ∂μ) ≤
          τ^(k-1) * (nativeRareJ old.x old.f (j.val+1) l : ℝ) := by
    intro j l hl hl1 hl2
    have hm := heat_remainder_rare_moment_le_J μ R T hR hT hR0 hT0 j l hl
      (nativeEps:ℝ) (τ * (old.x:ℝ)) (old.f:ℝ) (by norm_num [nativeEps]) hτx hfR hRc h20 h128
    refine ⟨hm.1, hm.2.trans ?_⟩
    have hs := nativeHeatVHEATJ_fixedEps_scaled_le τ (nativeEps:ℝ) (old.x:ℝ) (old.f:ℝ) (j.val+1) k l
      hτ hτ1 (by norm_num [nativeEps]) hxR hfR (by omega) hk hk20 hl1 hl2
    have hr := heat_individual_rareJ_le old.x old.f hx hf (j.val+1) l hl (hroot j)
    exact hs.trans (mul_le_mul_of_nonneg_left hr (pow_nonneg hτ.le _))
  have h1p := hrare (0:Fin 2) (k-1) (by omega) le_rfl (by omega)
  have h1 := hrare (0:Fin 2) k hk20 (by omega) le_rfl
  have h2p := hrare (1:Fin 2) (k-1) (by omega) le_rfl (by omega)
  have h2 := hrare (1:Fin 2) k hk20 (by omega) le_rfl
  norm_num only [Fin.val_zero,Fin.val_one,pow_one] at h1p h1 h2p h2
  have hb := heat_individual_source_bill_integral_le μ k e' d (521/1000) c nativeB T R
    he' (by dsimp [d]; positivity) (by norm_num)
    (by dsimp [c]; positivity) (by norm_num [nativeB]) hprev hcur _ _ _ _ h1p h1 h2p h2
  refine ⟨hb.1, hb.2.trans ?_⟩
  -- coefficient comparison
  obtain ⟨ha, hb2, hc3⟩ := heat_individual_row_coefficients height k old
  dsimp only [row]
  have hPnn : 0 ≤ ∫ z,T z^(k-1) ∂μ := integral_nonneg fun z => pow_nonneg (hT0 z) _
  have hCnn : 0 ≤ ∫ z,T z^k ∂μ := integral_nonneg fun z => pow_nonneg (hT0 z) _
  set P := ∫ z,T z^(k-1) ∂μ
  set C := ∫ z,T z^k ∂μ
  have hold0 : (0:ℝ) ≤ (old.e:ℝ) := by exact_mod_cast he
  have hτ1' : τ * τ ^ (k-1) = τ ^ k := by rw [← pow_succ']; congr 1; omega
  set A1 : ℝ := (d*(nativeB:ℝ)+4*(2*(521/1000)*(nativeB:ℝ)+c*(nativeB:ℝ)^2)) with hA1
  set A2 : ℝ := (2*(521/1000)*(nativeB:ℝ)+c*(nativeB:ℝ)^2) with hA2
  have hdn : 0 ≤ d := by dsimp [d]; positivity
  have hcn : 0 ≤ c := by dsimp [c]; positivity
  have hBn : (0:ℝ) ≤ nativeB := by norm_num [nativeB]
  have hA1n : 0 ≤ A1 := by dsimp [A1]; positivity
  have hA2n : 0 ≤ A2 := by dsimp [A2]; positivity
  -- the three coefficient facts in the form needed
  have ha' : (k:ℝ) * old.e * A1 ≤ (nativeA:ℝ) * row.1 := by
    have := ha
    dsimp only [row, A1, d, c, height, old] at this ⊢
    push_cast at this ⊢
    linarith
  have hb2' : (k:ℝ) * old.e * A2 ≤ row.2.1 := by
    have := hb2
    dsimp only [row, A2, c, height, old] at this ⊢
    push_cast at this ⊢
    linarith
  set K3 : ℝ := d * (nativeRareJ old.x old.f 1 (k-1) : ℝ) +
      (2*(521/1000)+2*(nativeB:ℝ)*c)*(4*(nativeRareJ old.x old.f 1 (k-1) : ℝ)+(nativeRareJ old.x old.f 1 k : ℝ))+
      c*(4*(nativeRareJ old.x old.f 2 (k-1) : ℝ)+(nativeRareJ old.x old.f 2 k : ℝ)) with hK3
  have hc3' : (k:ℝ) * old.e * K3 ≤ (nativeA:ℝ)^k * row.2.2 := by
    have := hc3
    dsimp only [row, K3, d, c, height, old] at this ⊢
    push_cast at this ⊢
    linarith
  have hJnn : ∀ j l : ℕ, (0:ℝ) ≤ (nativeRareJ old.x old.f j l : ℝ) := by
    intro j l
    have hin : (0:ℚ) ≤ nativeEps^j*old.x^l*(if l=20 then nativeRootUp ((old.f/old.x)^(5*j)) 27 else 1) := by
      have h0 : (0:ℚ) ≤ nativeEps := by norm_num [nativeEps]
      have h2 : (0:ℚ) ≤ (if l=20 then nativeRootUp ((old.f/old.x)^(5*j)) 27 else 1) := by
        split_ifs
        · exact nativeHeatRootUp_nonneg _ _
        · norm_num
      exact mul_nonneg (mul_nonneg (pow_nonneg h0 _) (pow_nonneg hx.le _)) h2
    have := nativeUp_ge (nativeEps^j*old.x^l*(if l=20 then nativeRootUp ((old.f/old.x)^(5*j)) 27 else 1))
    have h3 : (0:ℚ) ≤ nativeRareJ old.x old.f j l := by
      unfold nativeRareJ; exact hin.trans this
    exact_mod_cast h3
  have hK3n : 0 ≤ K3 := by
    have := hJnn 1 (k-1); have := hJnn 1 k; have := hJnn 2 (k-1); have := hJnn 2 k
    dsimp only [K3]
    have hc2 : (0:ℝ) ≤ 2*(521/1000)+2*(nativeB:ℝ)*c := by positivity
    positivity
  have hkk : (0:ℝ) ≤ (k:ℝ) := by positivity
  have e1 : (k:ℝ) * e' ≤ (k:ℝ) * (τ * old.e) := mul_le_mul_of_nonneg_left hee hkk
  have hτk1 : 0 ≤ τ ^ (k-1) := pow_nonneg hτ.le _
  have t1 : (k:ℝ) * e' * A1 * P ≤ (nativeA:ℝ) * τ * row.1 * P := by
    have : (k:ℝ) * e' * A1 ≤ τ * ((k:ℝ) * old.e * A1) := by
      calc (k:ℝ) * e' * A1 ≤ (k:ℝ) * (τ * old.e) * A1 := mul_le_mul_of_nonneg_right e1 hA1n
        _ = τ * ((k:ℝ) * old.e * A1) := by ring
    have h2 := mul_le_mul_of_nonneg_left ha' hτ.le
    exact mul_le_mul_of_nonneg_right (this.trans (h2.trans_eq (by ring))) hPnn
  have t2 : (k:ℝ) * e' * A2 * C ≤ row.2.1 * C := by
    have : (k:ℝ) * e' * A2 ≤ (k:ℝ) * old.e * A2 := by
      have hee1 : e' ≤ old.e := hee.trans (mul_le_of_le_one_left hold0 hτ1)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hee1 hkk) hA2n
    exact mul_le_mul_of_nonneg_right (this.trans hb2') hCnn
  have t3 : (k:ℝ) * e' * (τ ^ (k-1) * K3) ≤ ((nativeA:ℝ) * τ) ^ k * row.2.2 := by
    have : (k:ℝ) * e' * (τ ^ (k-1) * K3) ≤ (k:ℝ) * (τ * old.e) * (τ ^ (k-1) * K3) :=
      mul_le_mul_of_nonneg_right e1 (mul_nonneg hτk1 hK3n)
    calc _ ≤ _ := this
      _ = τ ^ k * ((k:ℝ) * old.e * K3) := by rw [← hτ1']; ring
      _ ≤ τ ^ k * ((nativeA:ℝ)^k * row.2.2) := mul_le_mul_of_nonneg_left hc3' (pow_nonneg hτ.le _)
      _ = _ := by rw [mul_pow]; ring
  have hexp : (k:ℝ) * e' * (A1 * P + A2 * C + d * (τ ^ (k-1) * (nativeRareJ old.x old.f 1 (k-1) : ℝ)) +
      (2*(521/1000)+2*(nativeB:ℝ)*c) * (4 * (τ ^ (k-1) * (nativeRareJ old.x old.f 1 (k-1) : ℝ)) +
        τ ^ (k-1) * (nativeRareJ old.x old.f 1 k : ℝ)) +
      c * (4 * (τ ^ (k-1) * (nativeRareJ old.x old.f 2 (k-1) : ℝ)) +
        τ ^ (k-1) * (nativeRareJ old.x old.f 2 k : ℝ))) =
      (k:ℝ) * e' * A1 * P + (k:ℝ) * e' * A2 * C + (k:ℝ) * e' * (τ ^ (k-1) * K3) := by
    simp only [K3]; ring
  linarith [t1, t2, t3, hexp]

end
end ASDExplicitGamma.Native
