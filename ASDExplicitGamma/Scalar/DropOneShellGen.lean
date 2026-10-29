module

public import ASDExplicitGamma.Scalar.DropFinal

/-! SC-ONE-SHELL-RECIPROCAL-DROP: the exact one-shell decrement on the source sequences,
conditional only on the named NEW-resolvent quartic interface. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Set Filter Topology Algsuperdiff.Frozen.Assumptions
open Numerics.Mirror Numerics.Scalar

noncomputable section

/-- The remainder variable times the quartic coefficient is paid by the certified charge. -/
theorem drop_charge_arith_gen (Csh Chg : ℝ) (hC0 : 0 ≤ Csh)
    (hfac : Chg = Csh * (((11 / 5 : ℝ) * (17 / 50000)) / (1 - (11 / 5 : ℝ) * (17 / 50000)))) (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (B s2 : ℝ)
    (hB : 0 ≤ B) (hs2 : 0 < s2) (hlow : (31 / 50) * B ≤ s2) :
    Csh * (((3 : ℝ) ^ (2 * M.gamma) - 1) * B / s2) ≤
      Chg / (31 / 50) := by
  have hγ0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hg' : M.gamma ≤ 17 / 50000 := by simpa [gammaZero] using hg
  obtain ⟨hx0, hx1, hratio⟩ := one_shell_ratio_bounds M.gamma hγ0 hg'
  set x : ℝ := (11 / 5 : ℝ) * M.gamma with hx
  set x0 : ℝ := (11 / 5 : ℝ) * (17 / 50000) with hx0def
  have hxx0 : x ≤ x0 := mul_le_mul_of_nonneg_left hg' (by norm_num)
  have hx0lt : x0 < 1 := by norm_num [hx0def]
  have hmono : x / (1 - x) ≤ x0 / (1 - x0) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hv : ((3 : ℝ) ^ (2 * M.gamma) - 1) * B / s2 ≤ (50 / 31) * (x0 / (1 - x0)) := by
    have hpow0 : 0 ≤ (3 : ℝ) ^ (2 * M.gamma) - 1 := by
      have : (1 : ℝ) ≤ (3 : ℝ) ^ (2 * M.gamma) :=
        Real.one_le_rpow (by norm_num) (by linarith)
      linarith
    have hBs : B / s2 ≤ 50 / 31 := by
      rw [div_le_iff₀ hs2]; linarith
    calc ((3 : ℝ) ^ (2 * M.gamma) - 1) * B / s2
        = ((3 : ℝ) ^ (2 * M.gamma) - 1) * (B / s2) := by ring
      _ ≤ (x / (1 - x)) * (50 / 31) :=
          mul_le_mul (hratio) hBs (by positivity) (by
            have : 0 ≤ x / (1 - x) := div_nonneg hx0 (by linarith)
            exact this)
      _ ≤ (x0 / (1 - x0)) * (50 / 31) :=
          mul_le_mul_of_nonneg_right hmono (by norm_num)
      _ = (50 / 31) * (x0 / (1 - x0)) := by ring
  rw [hfac]
  calc Csh * (((3 : ℝ) ^ (2 * M.gamma) - 1) * B / s2)
      ≤ Csh * ((50 / 31) * (x0 / (1 - x0))) :=
        mul_le_mul_of_nonneg_left hv hC0
    _ = Csh * (x0 / (1 - x0)) / (31 / 50) := by
        field_simp

/-- SC-ONE-SHELL-RECIPROCAL-DROP at label `i < N`: the exact one-shell decrement, from the
NEW-resolvent quartic interface and the earlier native states. -/
theorem drop_one_shell_gen (Csh Chg G : ℝ) (hC0 : 0 ≤ Csh)
    (hfac : Chg = Csh * (((11 / 5 : ℝ) * (17 / 50000)) / (1 - (11 / 5 : ℝ) * (17 / 50000))))
    (hG : G = evalReal scalarRealEnv lowerBaseExpr - Chg / (31 / 50)) (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ) (hpast : ∀ l < N, nativeInductionState M h l)
    (i : ℤ) (hi : i < N) (e : Vec 2) (he : vecDot e e = 1)
    (Cq : ℝ) (hCq : Cq ≤ Csh) (hq : NewResolventQuarticBound M h i e Cq) :
    G *
        (shellVarianceSum h M.gamma (i + 1) - shellVarianceSum h M.gamma i) /
          (Annealed.sigmaBar M i : ℝ) ^ 3 ≤
      physicalInverseResponse M i (originCube 2 (i + 128)) e -
        physicalInverseResponse M (i + 1) (originCube 2 (i + 1 + 128)) e := by
  have hσ : 0 < (Annealed.sigmaBar M i : ℝ) := (Annealed.sigmaBar_characterization M i).1
  have hs := hpast i hi
  have hlow := hs.2.2.2.2.2.2.1
  obtain ⟨D, hD, hsplit⟩ := drop_increment_split M h hM hg N hpast i hi e he hσ
  have hvol : 0 < (volume (openCubeSet (originCube 2 (i + 129)))).toReal := by
    rw [volume_openCubeSet_toReal]; exact cubeVolume_pos _
  have hqb := hq hσ
  rw [drop_quartic_product_law M h hM i e hσ] at hqb
  have hBnn : 0 ≤ shellVarianceSum h M.gamma i := by
    have hγ0 : 0 < M.gamma := M.shellPrefix.gamma_pos
    have hlt : (3 : ℝ) ^ (-(2 * M.gamma)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    unfold shellVarianceSum
    exact div_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by norm_num) _)) (by linarith)
  set σ : ℝ := (Annealed.sigmaBar M i : ℝ) with hσdef
  set Bi := shellVarianceSum h M.gamma i with hBi
  have hBsucc : shellVarianceSum h M.gamma (i + 1) = (3 : ℝ) ^ (2 * M.gamma) * Bi :=
    shellVarianceSum_succ h M.gamma i
  set v : ℝ := ((q3ModelAmplitude M h (i + 1) / σ) ^ 2) with hvdef
  have hv : v = ((3 : ℝ) ^ (2 * M.gamma) - 1) * Bi / σ ^ 2 := by
    rw [hvdef, ← drop_v_eq_amp_sq M h i]
  have hv0 : 0 ≤ v := by rw [hvdef]; positivity
  have hΔ : (shellVarianceSum h M.gamma (i + 1) - Bi) / σ ^ 2 = v := by
    rw [hv, hBsucc]; ring
  have hs2 : (31 / 50) * Bi ≤ σ ^ 2 := by nlinarith [sq_nonneg M.nu]
  have hZ := drop_charge_arith_gen Csh Chg hC0 hfac M hg Bi (σ ^ 2) hBnn (by positivity) hs2
  rw [← hv] at hZ
  have hZ' : Cq * v ≤ Chg / (31 / 50) := by
    have hh : Cq * v ≤ Csh * v := mul_le_mul_of_nonneg_right hCq hv0
    linarith
  have hqv : (volume (openCubeSet (originCube 2 (i + 129)))).toReal⁻¹ *
      ∫ p, physicalParityQuarticObservable (originCube 2 (i + 129)) M.nu σ M.nu_pos hσ
        (physicalResponseRestriction (originCube 2 (i + 129)) (drop_hQ (i + 129))) e p
        ∂(physicalParityProductLaw M i) ≤ v ^ 2 * Cq := by
    rw [inv_mul_le_iff₀ hvol]
    exact hqb
  have hcoarse := drop_r_coarsen M i e
  have hlab : i + 1 + 128 = i + 129 := by ring
  rw [hlab]
  have hgain := hG
  have hsplit' := hsplit
  rw [hΔ] at hD
  -- σ (r1 - r') = D + Q
  have key : G * v ≤
      σ * (physicalInverseResponse M i (originCube 2 (i + 129)) e -
        physicalInverseResponse M (i + 1) (originCube 2 (i + 129)) e) := by
    have hnz : 0 ≤ v * (Chg / (31 / 50) -
        Cq * v) := mul_nonneg hv0 (by linarith)
    rw [hgain]
    nlinarith [hD, hsplit', hqv, hnz]
  have hdiv : G *
        (shellVarianceSum h M.gamma (i + 1) - Bi) / σ ^ 3 =
      G * v / σ := by
    rw [← hΔ]; field_simp
  rw [hdiv, div_le_iff₀ hσ]
  nlinarith [key, hcoarse, hσ]

end

end ASDExplicitGamma.Scalar
