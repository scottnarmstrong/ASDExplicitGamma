module

public import ASDExplicitGamma.Native.OldSignedProjectedStrongDerivative
public import ASDExplicitGamma.Native.OldSignedWhiteProjectedKernel

/-! The full Helmholtz trace recovers the original physical q3 mode, and
its divergence agrees with that mode's directional derivative. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Complex ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
noncomputable section

/-- Away from the spectral zero mode the projector has trace one. -/
theorem old_signed_helmholtz_trace_one (xi : Q3FrequencyPlane) (hxi : xi≠0) :
    oldSignedHelmholtzEntry xi 0 0+oldSignedHelmholtzEntry xi 1 1=1 := by
  have hn : ‖xi‖^2=xi.fst^2+xi.snd^2 := by
    simp only [WithLp.prod_norm_sq_eq_of_L2,Real.norm_eq_abs,sq_abs]
  have hd : xi.fst^2+xi.snd^2≠0 := by
    rw [←hn]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hxi)
  norm_num [oldSignedHelmholtzEntry,oldSignedFrequency]
  rw [←add_div,←pow_two,←pow_two,div_self hd]

/-- The complete projected-character trace is the unprojected character.
The absence of a zero-frequency atom is proved for the actual q3 measure. -/
theorem old_signed_projected_character_trace (b : ℝ) (x : Vec 2) :
    oldSignedProjectedCharacter b x 0 0+oldSignedProjectedCharacter b x 1 1=
      q3SpectralCharacter b (q3SpectralPoint x) := by
  have hne : ∀ᵐ xi ∂q3SpectralMeasure b, xi≠0 := by
    rw [ae_iff]
    simpa only [Set.compl_ofPred,Classical.not_not,Set.ofPred_eq_eq_singleton] using
      q3SpectralMeasure_singleton_zero b
  apply Lp.ext
  filter_upwards [hne,Lp.coeFn_add (oldSignedProjectedCharacter b x 0 0)
      (oldSignedProjectedCharacter b x 1 1),
    old_signed_projected_character_coeFn b x 0 0,
    old_signed_projected_character_coeFn b x 1 1,
    q3SpectralCharacter_coeFn b (q3SpectralPoint x)] with xi hne ha h0 h1 hc
  simp only [Pi.add_apply] at ha
  rw [ha,h0,h1,hc]
  simp only [oldSignedProjectedCharacterValue,q3SpectralPoint,WithLp.toLp_fst,WithLp.toLp_snd]
  rw [←add_mul,←Complex.ofReal_add,old_signed_helmholtz_trace_one xi hne,Complex.ofReal_one,one_mul]

/-- Taking the projected white-kernel trace recovers the same original q3
kernel, so its physical spatial derivative is fixed by the actual coefficient. -/
theorem old_signed_projected_white_kernel_trace (b : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2) :
    oldSignedProjectedWhiteKernel b L x 0 0+oldSignedProjectedWhiteKernel b L x 1 1=
      q3Section b L h3Zero (L.1 • x) := by
  have hreal (f : WhiteNoise) : oldSignedWhiteRealPart (oldSignedWhiteComplexify f)=f := by
    apply Lp.ext
    filter_upwards [old_signed_white_real_part_coeFn (oldSignedWhiteComplexify f),
      Complex.ofRealCLM.coeFn_compLpL f] with w hr hc
    change oldSignedWhiteComplexify f w = _ at hc
    rw [hr,hc]
    rfl
  unfold oldSignedProjectedWhiteKernel
  rw [←map_add,←map_add,old_signed_projected_character_trace,old_signed_spectral_white_character]
  exact hreal _

end
end ASDExplicitGamma.Native
