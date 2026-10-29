module

public import ASDExplicitGamma.Scalar.SignalInterval
public import ASDExplicitGamma.Scalar.MolecularUpperFiveFour
public import ASDExplicitGamma.Numerics.Scalar.Frames

/-! The target-label upper corridor from the exact long-block trial output. -/

@[expose] public section

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Model

namespace ASDExplicitGamma.Scalar

private theorem shellVarianceSum_nonneg (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (m : ℤ) :
    0 ≤ shellVarianceSum h M.gamma m := by
  have henergy : 0 ≤ ∫ ω, cutoffProjectedEnergy M planarBasis0 m m ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure :=
    integral_nonneg fun ω => cutoffProjectedEnergy_nonneg M planarBasis0 m m ω
  rw [integral_cutoffProjectedEnergy M h hM planarBasis0_unit m m] at henergy
  linarith

private theorem upper_step_from_trial (ν Bn BN σn σN z : ℝ)
    (hσn : 0 < σn) (hσN : 0 ≤ σN)
    (hupper : σn ^ 2 ≤ ν ^ 2 + (13 / 8 : ℝ) * Bn)
    (htrial : σN ≤ σn * (1 + z + (681 / 10000 : ℝ)))
    (hz : z = (BN - Bn) / (2 * σn ^ 2))
    (hzlo : (37 / 250 : ℝ) < z) (hzhi : z < (9 / 10 : ℝ)) :
    σN ^ 2 ≤ ν ^ 2 + (13 / 8 : ℝ) * BN := by
  have hbarrier := ASDExplicitGamma.Numerics.Scalar.upper_barrier_positive z
    (le_of_lt hzlo) (le_of_lt hzhi)
  have hfactor : (1 + z + (681 / 10000 : ℝ)) ^ 2 ≤
      1 + (13 / 4 : ℝ) * z := by
    nlinarith only [hbarrier]
  have htrialSq := (sq_le_sq₀ hσN
    (mul_nonneg hσn.le (by positivity))).mpr htrial
  have hscaled : σN ^ 2 ≤ σn ^ 2 * (1 + (13 / 4 : ℝ) * z) := by
    calc
      σN ^ 2 ≤ (σn * (1 + z + (681 / 10000 : ℝ))) ^ 2 := htrialSq
      _ = σn ^ 2 * (1 + z + (681 / 10000 : ℝ)) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfactor (sq_nonneg σn)
  have hidentity : σn ^ 2 * (1 + (13 / 4 : ℝ) * z) =
      σn ^ 2 + (13 / 8 : ℝ) * (BN - Bn) := by
    rw [hz]
    field_simp [ne_of_gt (sq_pos_of_pos hσn)]
    ring
  rw [hidentity] at hscaled
  nlinarith only [hscaled, hupper]

/-- The target-label upper corridor follows from the exact long-block ratio.
The long-block conclusion uses the certified endpoint error `681/10000`; its
cell-energy and source-row producers remain separate inputs. -/
theorem scalar_upper_step_of_longblock_trial
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hstate : ∀ k < N, nativeInductionState M h k)
    (htrial :
      (Annealed.sigmaBar M N : ℝ) ≤
        (Annealed.sigmaBar M
          (N - ⌊(17 / 50 : ℝ) / M.gamma⌋ : ℤ) : ℝ) *
          (1 +
            (shellVarianceSum h M.gamma N -
              shellVarianceSum h M.gamma
                (N - ⌊(17 / 50 : ℝ) / M.gamma⌋ : ℤ)) /
              (2 * (Annealed.sigmaBar M
                (N - ⌊(17 / 50 : ℝ) / M.gamma⌋ : ℤ) : ℝ) ^ 2) +
            (681 / 10000 : ℝ))) :
    (Annealed.sigmaBar M N : ℝ) ^ 2 ≤
      M.nu ^ 2 + (13 / 8 : ℝ) * shellVarianceSum h M.gamma N := by
  have hγpos := M.shellPrefix.gamma_pos
  have hγsmall : M.gamma ≤ (17 / 50000 : ℝ) := by
    simpa [gammaZero] using hγ
  let L : ℤ := ⌊(17 / 50 : ℝ) / M.gamma⌋
  let n : ℤ := N - L
  let Bn : ℝ := shellVarianceSum h M.gamma n
  let BN : ℝ := shellVarianceSum h M.gamma N
  let z : ℝ := (BN - Bn) / (2 * (Annealed.sigmaBar M n : ℝ) ^ 2)
  have hLpos : 0 < L := by
    dsimp [L]
    have hfloor := ASDExplicitGamma.Numerics.Scalar.frame_floor_bounds
      M.gamma hγpos hγsmall
    have hprod : 0 < M.gamma *
        ((⌊(17 / 50 : ℝ) / M.gamma⌋ : ℤ) : ℝ) :=
      lt_trans (by norm_num) hfloor.1
    have hcast : (0 : ℝ) <
        ((⌊(17 / 50 : ℝ) / M.gamma⌋ : ℤ) : ℝ) :=
      (mul_pos_iff_of_pos_left hγpos).mp hprod
    exact_mod_cast hcast
  have hnN : n < N := by
    dsimp [n]
    omega
  have hnplus : n + L = N := by
    dsimp [n]
    omega
  have hstateN : nativeInductionState M h n := hstate n hnN
  have hBNnonneg : 0 ≤ BN := by
    dsimp [BN]
    exact shellVarianceSum_nonneg M h hM N
  have hBnnonneg : 0 ≤ Bn := by
    dsimp [Bn]
    exact shellVarianceSum_nonneg M h hM n
  have htrial' : (Annealed.sigmaBar M N : ℝ) ≤
      (Annealed.sigmaBar M n : ℝ) * (1 + z + (681 / 10000 : ℝ)) := by
    simpa [n, L, Bn, BN, z, add_assoc] using htrial
  by_cases hsmallN : BN ≤ M.nu ^ 2
  · have hmol := sigmaBar_sq_le_molecular_five_four M h hM N hsmallN
    have hresult : (Annealed.sigmaBar M N : ℝ) ^ 2 ≤
        M.nu ^ 2 + (13 / 8 : ℝ) * BN := by
      dsimp [BN] at hmol hBNnonneg ⊢
      nlinarith only [hmol, hBNnonneg]
    exact hresult
  · have hBNpos : M.nu ^ 2 < BN := lt_of_not_ge hsmallN
    have hsignalInput : M.nu ^ 2 < shellVarianceSum h M.gamma (n + L) := by
      simpa [BN] using (hnplus ▸ hBNpos)
    have hnFloor : n + ⌊(17 / 50 : ℝ) / M.gamma⌋ = N := by
      simpa [L] using hnplus
    have hsignal' := sigmaBar_signal_interval M h n hγpos hγsmall
      hstateN (by simpa [L] using hsignalInput)
    have hsignal : (37 / 250 : ℝ) < z ∧ z < (9 / 10 : ℝ) := by
      simpa [z, Bn, BN, hnFloor] using hsignal'
    by_cases hsmalln : Bn ≤ M.nu ^ 2
    · have hmol := sigmaBar_sq_le_molecular_five_four M h hM n hsmalln
      have hupper : (Annealed.sigmaBar M n : ℝ) ^ 2 ≤
          M.nu ^ 2 + (13 / 8 : ℝ) * Bn := by
        dsimp [Bn] at hmol hBnnonneg ⊢
        nlinarith only [hmol, hBnnonneg]
      have hσn : 0 < (Annealed.sigmaBar M n : ℝ) :=
        M.nu_pos.trans_le (nu_le_sigmaBar M n)
      exact upper_step_from_trial M.nu Bn BN
        (Annealed.sigmaBar M n : ℝ) (Annealed.sigmaBar M N : ℝ) z
        hσn (Annealed.sigmaBar M N).property.le hupper htrial' (by rfl)
        hsignal.1 hsignal.2
    · have hlarge : M.nu ^ 2 < Bn := lt_of_not_ge hsmalln
      obtain ⟨_, _, _, _, _, _, _, hupper⟩ := hstateN
      have hσn : 0 < (Annealed.sigmaBar M n : ℝ) :=
        M.nu_pos.trans_le (nu_le_sigmaBar M n)
      exact upper_step_from_trial M.nu Bn BN
        (Annealed.sigmaBar M n : ℝ) (Annealed.sigmaBar M N : ℝ) z
        hσn (Annealed.sigmaBar M N).property.le hupper htrial' (by rfl)
        hsignal.1 hsignal.2

end ASDExplicitGamma.Scalar
