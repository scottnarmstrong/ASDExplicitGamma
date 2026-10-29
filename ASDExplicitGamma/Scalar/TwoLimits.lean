module

public import ASDExplicitGamma.Scalar.LocalizedParent
public import ASDExplicitGamma.Scalar.NoLoss
public import ASDExplicitGamma.Scalar.StreamLimit
public import ASDExplicitGamma.Statements.GammaZero

/-! The parent-scale limit and the two tolerance removals in the no-loss
argument. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Algsuperdiff.Section3 Filter
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Corrector
noncomputable section

/-- For fixed positive Young and stream tolerances, the actual stationary cell
trial bounds the genuine long-block scalar ratio. -/
theorem no_loss_tolerance_bound (M : ABKModel 2) (n N : ℤ) (_hnN : n < N)
    (σ τ δ : ℝ) (hσ : 0 < σ)
    (hσeq : σ = (Annealed.sigmaBar M n : ℝ)) (hτ : 0 < τ) (hδ : 0 < δ)
    (hν : 0 < M.nu) (e : Vec 2) (he : vecDot e e = 1)
    (C : CutoffSample 2 → Vec 2 → BlockVec 2)
    (hC : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ScalarVariation (openCubeSet (originCube 2 (n-14))) (C ω))
    (hE : Integrable (cutoffTrialEnergy M N σ (originCube 2 (n-14))
      (bandTrialField M n N σ e C)) (Cutoff.cutoffSampleLaw M).toMeasure) :
    (Annealed.sigmaBar M N : ℝ) / (Annealed.sigmaBar M n : ℝ) ≤
      (1+τ) * (∫ ω, cutoffTrialEnergy M N σ (originCube 2 (n-14))
        (bandTrialField M n N σ e C) ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) +
      (1+τ⁻¹)*(σ/M.nu)*δ := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let q : ℤ := n-14
  let Γ : ℝ := ∫ ω, cutoffTrialEnergy M N σ (originCube 2 q)
    (bandTrialField M n N σ e C) ω ∂μ
  let b : ℝ := (1+τ⁻¹)*(σ/M.nu)
  obtain ⟨S,D,hSm,hS,hSmooth,hAnti,hDiv,hDm,hD,hgap,L,K,hErr⟩ :=
    exists_localStreamApprox_cube_error_eventually M n N σ⁻¹ e hδ
  let Kq : ℕ := (max (0:ℤ) q).toNat
  have hqK : q ≤ (Kq:ℤ) := by
    have hmax : 0 ≤ max (0:ℤ) q := le_max_left _ _
    simp [Kq, Int.toNat_of_nonneg hmax]
  have hσbar : 0 < σ := by positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hKevent : ∀ᶠ k : ℕ in atTop, K ≤ k :=
    eventually_atTop.2 ⟨K, fun _ hk => hk⟩
  have hKqevent : ∀ᶠ k : ℕ in atTop, Kq ≤ k :=
    eventually_atTop.2 ⟨Kq, fun _ hk => hk⟩
  have hentryEvent : ∀ᶠ k : ℕ in atTop,
      (Homogenization.Book.Ch04.annealedBlockMatrixAtScale
        (Cutoff.coefficientCutoffLaw M N) (k:ℤ)).upperLeft 0 0 ≤
        (Annealed.sigmaBar M n : ℝ) * ((1+τ)*Γ+b*δ) := by
    filter_upwards [hKevent, hKqevent] with k hkK hkq
    have hqk : q ≤ (k:ℤ) := by
      exact hqK.trans (by exact_mod_cast hkq)
    have hparent := localized_parent_bound M n N q (k:ℤ) σ τ hσ hτ e he C hC hE
      S D L hSm hS hDm hD hSmooth hAnti hDiv hqk
    have herr := hErr k hkK
    have hcap := add_le_add_right (mul_le_mul_of_nonneg_left herr hb)
      ((1+τ)*Γ)
    have hbound : σ⁻¹ * (Homogenization.Book.Ch04.annealedBlockMatrixAtScale
        (Cutoff.coefficientCutoffLaw M N) (k:ℤ)).upperLeft 0 0 ≤
        (1+τ)*Γ+b*δ := by
      calc
        σ⁻¹ * (Homogenization.Book.Ch04.annealedBlockMatrixAtScale
            (Cutoff.coefficientCutoffLaw M N) (k:ℤ)).upperLeft 0 0 ≤
            (1+τ)*Γ+b*(∫ ω, cubeLpNorm (originCube 2 (k:ℤ)) 2
              (fun x => HilbertVec.ofVec
                (localStreamApprox (originCube 2 (k:ℤ)) L S D ω x) -
                  realize (cutoffBandFlux M n N σ⁻¹ e) ω x) ^ (2:ℝ)
              ∂μ) := by
          simpa [q, Γ, b, μ] using hparent
        _ ≤ (1+τ)*Γ+b*δ := by
          nlinarith [hcap]
    have hdiv :
        (Homogenization.Book.Ch04.annealedBlockMatrixAtScale
          (Cutoff.coefficientCutoffLaw M N) (k:ℤ)).upperLeft 0 0 / σ ≤
          (1+τ)*Γ+b*δ := by
      simpa [div_eq_mul_inv, mul_comm] using hbound
    have hraw := (div_le_iff₀ hσ).1 hdiv
    simpa [Γ, μ, b, q, hσeq, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hraw
  exact sigmaBar_ratio_le_of_annealed_top_entry_eventually_le M n N
    ((1+τ)*Γ+b*δ) hentryEvent

/-- No-loss estimate: a positive compatible source cell trial controls the
genuine long-block scalar ratio with no loss. The large-parent limit is taken
first; the stream error and Young tolerances are then removed. -/
theorem no_loss_long_block (M : ABKModel 2) (h : ℝ)
    (_hM : PlanarQ3Gaussian M h) (_hγ : M.gamma ≤ gammaZero)
    (n N : ℤ) (hnN : n < N) (hν : 0 < M.nu)
    (Ebound : ℝ)
    (e : Vec 2) (he : vecDot e e = 1)
    (C : CutoffSample 2 → Vec 2 → BlockVec 2)
    (hC : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ScalarVariation (openCubeSet (originCube 2 (n-14))) (C ω))
    (hE : Integrable (cutoffTrialEnergy M N (Annealed.sigmaBar M n : ℝ)
      (originCube 2 (n-14))
      (bandTrialField M n N (Annealed.sigmaBar M n : ℝ) e C))
      (Cutoff.cutoffSampleLaw M).toMeasure)
    (hTrialBound : (∫ ω, cutoffTrialEnergy M N (Annealed.sigmaBar M n : ℝ)
      (originCube 2 (n-14))
      (bandTrialField M n N (Annealed.sigmaBar M n : ℝ) e C) ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ Ebound) :
    (Annealed.sigmaBar M N : ℝ) / (Annealed.sigmaBar M n : ℝ) ≤ Ebound := by
  let σ : ℝ := Annealed.sigmaBar M n
  let Γ : ℝ := ∫ ω, cutoffTrialEnergy M N σ (originCube 2 (n-14))
    (bandTrialField M n N σ e C) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure
  let ratio : ℝ := (Annealed.sigmaBar M N : ℝ)/(Annealed.sigmaBar M n : ℝ)
  have hσ : 0 < σ := by exact (Annealed.sigmaBar M n).property
  have hΓ : 0 ≤ Γ := by
    apply integral_nonneg
    intro ω
    exact cutoffTrialEnergy_nonneg M N σ hσ (originCube 2 (n-14))
      (bandTrialField M n N σ e C) ω
  have hremoveδ : ∀ τ : ℝ, 0 < τ → ratio ≤ (1+τ)*Γ := by
    intro τ hτ
    have hbτ : 0 < (1+τ⁻¹)*(σ/M.nu) := by positivity
    by_contra hnot
    have hgap : 0 < ratio-(1+τ)*Γ := sub_pos.mpr (lt_of_not_ge hnot)
    let δ : ℝ := (ratio-(1+τ)*Γ)/(2*((1+τ⁻¹)*(σ/M.nu)))
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    have hbound := no_loss_tolerance_bound M n N hnN σ τ δ hσ (by rfl) hτ hδ hν e he C
      (by simpa using hC)
      (by simpa [σ] using hE)
    have hprod : (1+τ⁻¹)*(σ/M.nu)*δ = (ratio-(1+τ)*Γ)/2 := by
      dsimp [δ]
      field_simp [ne_of_gt hbτ]
    have hbound' : ratio ≤ (1+τ)*Γ+(1+τ⁻¹)*(σ/M.nu)*δ := by
      simpa [ratio, Γ, σ] using hbound
    nlinarith [hbound', hprod]
  have hratioΓ : ratio ≤ Γ := by
    by_contra hnot
    have hgap : 0 < ratio-Γ := sub_pos.mpr (lt_of_not_ge hnot)
    by_cases hΓzero : Γ = 0
    · have h := hremoveδ 1 (by norm_num)
      simp [hΓzero] at h
      linarith
    · have hΓpos : 0 < Γ := lt_of_le_of_ne hΓ (Ne.symm hΓzero)
      let τ : ℝ := (ratio-Γ)/(2*Γ)
      have hτ : 0 < τ := by dsimp [τ]; positivity
      have h := hremoveδ τ hτ
      have hprod : τ*Γ = (ratio-Γ)/2 := by
        dsimp [τ]
        field_simp [ne_of_gt hΓpos]
      dsimp [ratio] at h
      nlinarith [h, hprod]
  have hΓE : Γ ≤ Ebound := by simpa [Γ, σ] using hTrialBound
  exact hratioΓ.trans hΓE

end
end ASDExplicitGamma.Scalar
