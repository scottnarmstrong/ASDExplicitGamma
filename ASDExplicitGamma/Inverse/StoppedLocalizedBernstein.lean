module

public import ASDExplicitGamma.Inverse.StoppedLocalizedIndependence
public import ASDExplicitGamma.Inverse.StoppedLocalizedMoments

/-! Weighted Bernstein for the actual coefficient-linked localized diameter field. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The source partial-block Bernstein bound for the actual q3 localized
field. Independence, boundedness, and rare second moments are derived here;
only the deterministic source weights and protected native past are supplied. -/
theorem q3_localized_partial_block_Lp {I : Type} [Fintype I]
    (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h) (hg : A.gamma ≤ gammaZero)
    (j : ℤ) (τ : ℝ) (hτ : 0 < τ) (t : WaveGateTuple) (q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000) (hfloor : Real.exp (-6000) ≤ q)
    (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ j+40, nativeInductionState A h k)
    (T : ℝ) (hT : 0 ≤ T) (hcut : 200*Real.exp (-T/4) ≤ 26*q)
    (M m : ℕ) (hm : 1 ≤ m) (p : ℝ) (hp : 2 ≤ p)
    (x : I → BlockSite) (hx : Function.Injective x)
    (a v : ℝ) (ha : 0 ≤ a) (hv : 0 ≤ v) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwmax : ∀ i, w i ≤ 9*a) (hwv : ∑ i, w i = v) :
    eLpNorm (fun ω => ∑ i, w i*((realLocalizedDiameterField
        (q3PlanarMarks A j τ (waveGateEta t)) M (3^M) (x i) ω)^m-
          ∫ ζ, (realLocalizedDiameterField (q3PlanarMarks A j τ (waveGateEta t)) M (3^M) (x i) ζ)^m
            ∂(Cutoff.cutoffSampleLaw A).toMeasure))
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw A).toMeasure ≤
    ENNReal.ofReal (4*Real.sqrt (p*21^2*((26*q)*rareMomentPolynomial (2*m) T)*(3:ℝ)^(2*M)*a*v)+
      4*p*21^2*4^m*(3:ℝ)^(M*(m+2))*a) := by
  let μ := (Cutoff.cutoffSampleLaw A).toMeasure
  let B := q3PlanarMarks A j τ (waveGateEta t)
  let F : I → Cutoff.CutoffSample 2 → ℝ := fun i ω => (realLocalizedDiameterField B M (3^M) (x i) ω)^m
  let c := fun i => localizationColor M (x i)
  have hB : PlanarMarkControl μ B q := q3_mark_control A h hA hg j τ hτ t q hraw hpast
  have hβ : 0 ≤ (26*q)*rareMomentPolynomial (2*m) T :=
    mul_nonneg (by positivity) (rare_moment_polynomial_nonneg (2*m) T hT)
  have hF : ∀ i, Measurable (F i) := fun i =>
    (real_localized_diameter_measurable B hB.local_measurable hB.positive_measurable M (3^M) (x i)).pow_const m
  have hbound (i : I) : ∀ᵐ ω ∂μ, 0 ≤ F i ω ∧ F i ω ≤ (4*(3:ℝ)^M)^m := by
    apply Filter.Eventually.of_forall
    intro ω
    obtain ⟨h0,h1⟩ := real_localized_diameter_bounds B M (3^M) (x i) ω
    have hN : (1:ℕ) ≤ 3^M := one_le_pow₀ (by norm_num : (1:ℕ) ≤ 3)
    have hnat : 2*3^M+1 ≤ 4*3^M := by omega
    have hreal : ((2*3^M+1:ℕ):ℝ) ≤ 4*(3:ℝ)^M := by exact_mod_cast hnat
    exact ⟨pow_nonneg h0 m,pow_le_pow_left₀ h0 (h1.trans hreal) m⟩
  have hvar (i : I) : moment (F i) 2 μ ≤ (26*q)*rareMomentPolynomial (2*m) T := by
    have hn : 2*m-1+1 = 2*m := by omega
    have hMom := real_diameter_nat_moment μ B q hB hq0 hq hfloor (x i) (2*m-1) T hT hcut
    simp only [hn] at hMom
    exact (localized_power_second_moment_le μ B q hB hq0 hq M (3^M) (x i) m hMom.1).trans hMom.2
  have hh := localization_partial_block_Lp μ F c
    (fun color => q3_localized_powers_colored_independent A h hA j τ (waveGateEta t) M m x hx color)
    hF m ((3:ℝ)^M) a v ((26*q)*rareMomentPolynomial (2*m) T) p (by positivity) ha hv hβ hp
    (by rw [localization_color_card]; norm_num only [Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat,le_refl])
    hbound hvar w hw hwmax hwv
  have hP2 : ((3:ℝ)^M)^2 = (3:ℝ)^(2*M) := by rw [← pow_mul,Nat.mul_comm M 2]
  have hPm : ((3:ℝ)^M)^(m+2) = (3:ℝ)^(M*(m+2)) := (pow_mul _ _ _).symm
  simpa only [hP2,hPm] using! hh

end
end ASDExplicitGamma.Inverse
