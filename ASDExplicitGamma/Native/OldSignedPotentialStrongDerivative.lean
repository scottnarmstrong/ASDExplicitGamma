module

public import ASDExplicitGamma.Native.OldSignedPotentialPointDerivative
public import ASDExplicitGamma.Native.OldSignedStrongDifferentiation

/-! Strong L2 derivatives of the local potential differences. The exact
Helmholtz characters supply their gradients, including low frequencies. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Complex ASDExplicitGamma.Model
noncomputable section

/-- The spectral gradient of the potential as a bounded real-linear map. -/
def oldSignedSpectralPotentialDerivative (b : ℝ) (x : Vec 2) (j : Fin 2) :
    Vec 2 →L[ℝ] Lp ℂ 2 (q3SpectralMeasure b) :=
  (ContinuousLinearMap.proj 0).smulRight (oldSignedProjectedCharacter b x 0 j)+
    (ContinuousLinearMap.proj 1).smulRight (oldSignedProjectedCharacter b x 1 j)

/-- The candidate derivative has the actual pointwise gradient formula. -/
theorem old_signed_spectral_potential_derivative_coeFn (b : ℝ) (x v : Vec 2) (j : Fin 2) :
    (oldSignedSpectralPotentialDerivative b x j v : Q3FrequencyPlane → ℂ) =ᵐ[q3SpectralMeasure b]
      fun xi => oldSignedPotentialPointDerivative x j xi v := by
  change ((v 0:ℝ) • oldSignedProjectedCharacter b x 0 j+
    (v 1:ℝ) • oldSignedProjectedCharacter b x 1 j : Lp ℂ 2 (q3SpectralMeasure b)) =ᵐ[_] _
  filter_upwards [Lp.coeFn_add ((v 0:ℝ) • oldSignedProjectedCharacter b x 0 j)
    ((v 1:ℝ) • oldSignedProjectedCharacter b x 1 j),
    Lp.coeFn_smul (v 0:ℝ) (oldSignedProjectedCharacter b x 0 j),
    Lp.coeFn_smul (v 1:ℝ) (oldSignedProjectedCharacter b x 1 j),
    old_signed_projected_character_coeFn b x 0 j,
    old_signed_projected_character_coeFn b x 1 j] with xi ha h0 h1 hc0 hc1
  simp only [Pi.add_apply] at ha
  simp only [Pi.smul_apply] at h0 h1
  rw [ha,h0,h1,hc0,hc1]
  rfl

/-- The potential's strong spatial derivative is its complete Helmholtz
projection. The proof uses an actual constant L2 bound on its normalized
remainders, with no inverse-frequency integrability assumption. -/
theorem old_signed_spectral_potential_hasFDerivAt (b : ℝ) (x : Vec 2) (j : Fin 2) :
    HasFDerivAt (fun y => oldSignedSpectralPotential b y j)
      (oldSignedSpectralPotentialDerivative b x j) x := by
  let B : Lp ℝ 2 (q3SpectralMeasure b) :=
    (memLp_const (4:ℝ) : MemLp (fun _ : Q3FrequencyPlane => (4:ℝ)) 2 (q3SpectralMeasure b)).toLp _
  apply old_signed_hasFDerivAt_L2 (q3SpectralMeasure b)
    (fun y => oldSignedSpectralPotential b y j) (fun y => oldSignedPotentialValue y j) x
    (oldSignedSpectralPotentialDerivative b x j) (oldSignedPotentialPointDerivative x j) B
    (fun y => old_signed_spectral_potential_coeFn b y j)
    (fun v => old_signed_spectral_potential_derivative_coeFn b x v j)
    (Filter.Eventually.of_forall (old_signed_potential_point_hasFDerivAt x j))
  intro y
  have hB : (B : Q3FrequencyPlane → ℝ) =ᵐ[q3SpectralMeasure b] fun _ => (4:ℝ) :=
    (memLp_const (4:ℝ) : MemLp (fun _ : Q3FrequencyPlane => (4:ℝ)) 2 (q3SpectralMeasure b)).coeFn_toLp
  filter_upwards [hB] with xi hB
  have h0 : |(y-x) 0| ≤ ‖y-x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (y-x) 0
  have h1 : |(y-x) 1| ≤ ‖y-x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (y-x) 1
  have hinc := old_signed_potential_increment_norm x y j xi
  have hder := old_signed_potential_point_derivative_norm x (y-x) j xi
  rw [hB]
  norm_num only [Real.norm_ofNat]
  calc
    _ ≤ ‖oldSignedPotentialValue y j xi-oldSignedPotentialValue x j xi‖+
        ‖oldSignedPotentialPointDerivative x j xi (y-x)‖ := norm_sub_le _ _
    _ ≤ (|y 0-x 0|+|y 1-x 1|)+(|(y-x) 0|+|(y-x) 1|) := add_le_add hinc hder
    _ ≤ _ := by
      simp only [Pi.sub_apply] at h0 h1 ⊢
      linarith only [h0,h1]

end
end ASDExplicitGamma.Native
