module

public import ASDExplicitGamma.Statements.NativeInductionState
public import ASDExplicitGamma.Scalar.ColdReciprocalNormalization
public import ASDExplicitGamma.Scalar.MolecularStartupScale
public import ASDExplicitGamma.Scalar.ReciprocalMolecular
public import ASDExplicitGamma.Scalar.ReciprocalTrueFrame
public import ASDExplicitGamma.Scalar.StructuralContinuity
public import ASDExplicitGamma.Cold.NativeThetaScaling
public import ASDExplicitGamma.Numerics.Cold.Basic
public import ASDExplicitGamma.Scalar.ReciprocalInteger

/-! The lower corridor arithmetic of `LowerCorridor` with the reciprocal gain `G` as a
parameter: the certificate enters only through `12493/40000 ≤ G`. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization Algsuperdiff.Section3 ASDExplicitGamma.Numerics.Cold

theorem sigmaBar_reciprocal_telescope_gen (G : ℝ) (hG0 : 0 ≤ G) (M : ABKModel 2) (h D : ℝ)
    (e : Vec 2) (n0 N : ℤ)
    (hN : n0<N)
    (hdrop : ∀ i : ℤ, n0 ≤ i → i < N →
      G*(shellVarianceSum h M.gamma (i+1)-shellVarianceSum h M.gamma i)/
        (Annealed.sigmaBar M i : ℝ)^3 ≤
      physicalInverseResponse M i (originCube 2 (i+128)) e-
        physicalInverseResponse M (i+1) (originCube 2 (i+1+128)) e)
    (hlower : ∀ i : ℤ, n0 ≤ i → i ≤ N →
      1≤(Annealed.sigmaBar M i : ℝ)*physicalInverseResponse M i (originCube 2 (i+128)) e)
    (hupper : ∀ i : ℤ, n0 ≤ i → i < N →
      (Annealed.sigmaBar M i : ℝ)*physicalInverseResponse M i (originCube 2 (i+128)) e≤1+D/2)
    (hstart : physicalInverseResponse M n0 (originCube 2 (n0+128)) e≤M.nu⁻¹)
    (hfinal : ∀ i : ℤ, n0 ≤ i → i < N →
      (Annealed.sigmaBar M i : ℝ)≤(Annealed.sigmaBar M N : ℝ)) :
    M.nu^2+2*G/(1+3*D/2)*
      (shellVarianceSum h M.gamma N-shellVarianceSum h M.gamma n0)≤(Annealed.sigmaBar M N : ℝ)^2 := by
  apply reciprocal_telescope_int M.nu G D (fun i => (Annealed.sigmaBar M i : ℝ))
    (fun i => physicalInverseResponse M i (originCube 2 (i+128)) e)
    (shellVarianceSum h M.gamma) n0 N hN M.nu_pos hG0
  · intro i hi hiN
    exact (Annealed.sigmaBar M i).property
  · intro i hi hiN
    exact shellVarianceSum_monotone h M.gamma M.shellPrefix.gamma_pos (by omega)
  · exact hdrop
  · exact hlower
  · exact hupper
  · exact hstart
  · exact hfinal

theorem lower_reciprocal_coefficient_ge_gen (G : ℝ) (hG : 12493 / 40000 ≤ G) :
    (31 / 50 : ℝ) ≤
      2 * G / (1 + 3 * (coldD128Target : ℝ) / 2) := by
  have hDnonneg : 0 ≤ (coldD128Target : ℝ) := by
    norm_num [ASDExplicitGamma.Numerics.Cold.coldD128Target]
  have hDlt : (coldD128Target : ℝ) < 1 / 200 := by
    norm_num [ASDExplicitGamma.Numerics.Cold.coldD128Target]
  have hdenpos : 0 < 1 + 3 * (coldD128Target : ℝ) / 2 := by positivity
  have hdenlt : 1 + 3 * (coldD128Target : ℝ) / 2 <
      1 + 3 * (1 / 200 : ℝ) / 2 := by nlinarith
  have hmul : (31 / 50 : ℝ) *
      (1 + 3 * (coldD128Target : ℝ) / 2) ≤ 2 * G := by
    nlinarith [hG, hdenlt]
  exact (le_div_iff₀ hdenpos).2 hmul

/-- Conditional `SC-LOWER-CORRIDOR` assembly on the exact source sequences.
The only analytic producer premise is the named one-shell decrement; all
normalizations at earlier labels are obtained from their actual source state,
the cold response theorem, and the true-frame molecular cap. -/
theorem lower_corridor_of_one_shell_decrements_gen (G : ℝ) (hG : 12493 / 40000 ≤ G)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ) (e : Vec 2)
    (he : vecDot e e = 1)
    (hstate : ∀ i : ℤ, i < N → nativeInductionState M h i)
    (hdrop : ∀ i : ℤ, i < N →
      G * (shellVarianceSum h M.gamma (i + 1) - shellVarianceSum h M.gamma i) /
          (Annealed.sigmaBar M i : ℝ) ^ 3 ≤
        physicalInverseResponse M i (originCube 2 (i + 128)) e -
          physicalInverseResponse M (i + 1) (originCube 2 (i + 1 + 128)) e) :
    M.nu ≤ (Annealed.sigmaBar M N : ℝ) ∧
      (31 / 50) * shellVarianceSum h M.gamma N + (19 / 50) * M.nu ^ 2 ≤
        (Annealed.sigmaBar M N : ℝ) ^ 2 := by
  have hnuN : M.nu ≤ (Annealed.sigmaBar M N : ℝ) := nu_le_sigmaBar M N
  by_cases hsmallN : shellVarianceSum h M.gamma N ≤ M.nu ^ 2
  · have hsigpos : 0 ≤ (Annealed.sigmaBar M N : ℝ) :=
      M.nu_pos.le.trans hnuN
    have hsq : M.nu ^ 2 ≤ (Annealed.sigmaBar M N : ℝ) ^ 2 :=
      (sq_le_sq₀ M.nu_pos.le hsigpos).mpr hnuN
    refine ⟨hnuN, ?_⟩
    nlinarith
  · have hlargeN : M.nu ^ 2 ≤ shellVarianceSum h M.gamma N := le_of_not_ge hsmallN
    obtain ⟨K, hK⟩ := exists_startup_variance_halfLine M h
    let n0 : ℤ := min K (N - 1)
    have hn0lt : n0 < N := by
      dsimp [n0]
      omega
    have hn0K : n0 ≤ K := by
      dsimp [n0]
      exact min_le_left _ _
    have htheta := ASDExplicitGamma.Cold.cold_theta_le_one M hγ
    have hratio : shellVarianceSum h M.gamma n0 / M.nu ^ 2 ≤ 1 := by
      have hbase := hK n0 hn0K
      nlinarith
    have hsmall0 : shellVarianceSum h M.gamma n0 ≤ M.nu ^ 2 :=
      (div_le_one (sq_pos_of_pos M.nu_pos)).mp hratio
    have htel := sigmaBar_reciprocal_telescope_gen G (by linarith) M h
      (coldD128Target : ℝ) e n0 N hn0lt
      (by
        intro i hi0 hiN
        exact hdrop i hiN)
      (by
        intro i hi0 hiN
        by_cases hiEq : i = N
        · subst i
          exact sigmaBar_mul_physicalInverseResponse_ge_one M N
            (originCube 2 (N + 128)) e he
        · have hiLt : i < N := lt_of_le_of_ne hiN hiEq
          have hs := hstate i hiLt
          exact (cold_reciprocal_normalization M h hM hγ i
            hs.1 hs.2.1 hs.2.2.1 e he).2.1)
      (by
        intro i hi0 hiN
        have hs := hstate i hiN
        exact (cold_reciprocal_normalization M h hM hγ i
          hs.1 hs.2.1 hs.2.2.1 e he).2.2)
      (by
        exact physicalInverseResponse_le_inv_nu M n0
          (originCube 2 (n0 + 128)) e he)
      (by
        intro i hi0 hiN
        have hstruct := sigmaBar_structural_continuity M i (N - i) (by omega)
        have hlabels : i + (N - i) = N := by omega
        rw [hlabels] at hstruct
        have hsigpos : 0 < (Annealed.sigmaBar M i : ℝ) :=
          (Annealed.sigmaBar_characterization M i).1
        have hmul := (le_div_iff₀ hsigpos).mp hstruct.1
        simpa using hmul)
    let c : ℝ := 2 * G /
      (1 + 3 * (coldD128Target : ℝ) / 2)
    have htel' : M.nu ^ 2 + c *
        (shellVarianceSum h M.gamma N - shellVarianceSum h M.gamma n0) ≤
          (Annealed.sigmaBar M N : ℝ) ^ 2 := by
      simpa [c] using htel
    have hvarianceMonotone :=
      shellVarianceSum_monotone h M.gamma M.shellPrefix.gamma_pos
    have hbn0le : shellVarianceSum h M.gamma n0 ≤ shellVarianceSum h M.gamma N :=
      hvarianceMonotone (le_of_lt hn0lt)
    have hdiff : 0 ≤ shellVarianceSum h M.gamma N - M.nu ^ 2 :=
      sub_nonneg.mpr hlargeN
    have hdiffle : shellVarianceSum h M.gamma N - M.nu ^ 2 ≤
        shellVarianceSum h M.gamma N - shellVarianceSum h M.gamma n0 :=
      sub_le_sub_left hsmall0 _
    have hc := lower_reciprocal_coefficient_ge_gen G hG
    have hc0 : 0 ≤ c := by dsimp [c]; positivity
    have hgain : (31 / 50 : ℝ) *
        (shellVarianceSum h M.gamma N - M.nu ^ 2) ≤
        c * (shellVarianceSum h M.gamma N - shellVarianceSum h M.gamma n0) := by
      calc
        _ ≤ c * (shellVarianceSum h M.gamma N - M.nu ^ 2) :=
          mul_le_mul_of_nonneg_right hc hdiff
        _ ≤ _ := mul_le_mul_of_nonneg_left hdiffle hc0
    have hcorridor : (31 / 50) * shellVarianceSum h M.gamma N +
        (19 / 50) * M.nu ^ 2 ≤ (Annealed.sigmaBar M N : ℝ) ^ 2 := by
      have heq : (31 / 50 : ℝ) * shellVarianceSum h M.gamma N +
          (19 / 50 : ℝ) * M.nu ^ 2 = M.nu ^ 2 +
            (31 / 50 : ℝ) *
              (shellVarianceSum h M.gamma N - M.nu ^ 2) := by ring
      rw [heq]
      nlinarith [htel', hgain]
    exact ⟨hnuN, hcorridor⟩

end ASDExplicitGamma.Scalar
