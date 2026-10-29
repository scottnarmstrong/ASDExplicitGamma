module

public import ASDExplicitGamma.Native.GenericSourceMeanHolder

/-! Integrating the positive OLD split in the sharp scalar source drift. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The mean keeps its own first moment, while the rare reserve uses the
independent L20 trace cap. Every product has explicit integrability. -/
theorem native_source_mean_drift_integral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T R G : Ω → ℝ) (hT : Integrable T μ) (hG : Integrable G μ)
    (hRm : AEStronglyMeasurable R μ) (hT0 : ∀ ω, 0 ≤ T ω) (hR0 : ∀ ω, 0 ≤ R ω)
    (b epsilon x e A K M : ℝ)
    (hb : 0 ≤ b) (hepsilon : 0 ≤ epsilon) (hx : 0 ≤ x)
    (he : 0 ≤ e) (hA : 0 ≤ A) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hRcap : eLpNorm' R 128 μ ≤ ENNReal.ofReal epsilon)
    (hTcap : eLpNorm' T 20 μ ≤ ENNReal.ofReal x)
    (hpoint : ∀ᵐ ω ∂μ, G ω ≤ e*(2*A*(b+R ω)+
      2*K*((b+R ω)*(T ω+4))+M*((b+R ω)^2*(T ω+4)))) :
    (∫ ω, G ω ∂μ) ≤
      e*((2*K*b+M*b^2)*(∫ ω, T ω ∂μ)+2*A*b+4*(2*K*b+M*b^2)+
        2*A*epsilon+(2*K+2*b*M)*(4*epsilon+epsilon*x)+M*(4*epsilon^2+epsilon^2*x)) := by
  have hrare := native_source_rare_mean_moments μ R T hRm hT.aestronglyMeasurable
    hR0 hT0 epsilon x hepsilon hx hRcap hTcap
  rcases hrare with ⟨⟨hR,hRle⟩,⟨hRT,hRTle⟩,⟨hR2,hR2le⟩,⟨hR2T,hR2Tle⟩⟩
  let c := 2*K*b+M*b^2
  let U := fun ω => c*T ω+(2*A*b+4*c)+(2*A+8*K+8*b*M)*R ω+
    (2*K+2*b*M)*(R ω*T ω)+4*M*(R ω)^2+M*((R ω)^2*T ω)
  have hU : Integrable U μ :=
    (((((hT.const_mul c).add (integrable_const _)).add (hR.const_mul _)).add
      (hRT.const_mul _)).add (hR2.const_mul _)).add (hR2T.const_mul _)
  have hGU : ∀ᵐ ω ∂μ, G ω ≤ e*U ω := by
    filter_upwards [hpoint] with ω hω
    convert hω using 1
    dsimp [U,c]
    ring
  have hI := integral_mono_ae hG (hU.const_mul e) hGU
  have hcoeff1 : 0 ≤ 2*A+8*K+8*b*M := by positivity
  have hcoeff2 : 0 ≤ 2*K+2*b*M := by positivity
  have hcoeff3 : 0 ≤ 4*M := by positivity
  have heval : (∫ ω, U ω ∂μ) = c*(∫ ω, T ω ∂μ)+(2*A*b+4*c)+
      (2*A+8*K+8*b*M)*(∫ ω, R ω ∂μ)+
      (2*K+2*b*M)*(∫ ω, R ω*T ω ∂μ)+4*M*(∫ ω, (R ω)^2 ∂μ)+
      M*(∫ ω, (R ω)^2*T ω ∂μ) := by
    have h0 := (hT.const_mul c).add (integrable_const (2*A*b+4*c))
    have h1 := h0.add (hR.const_mul (2*A+8*K+8*b*M))
    have h2 := h1.add (hRT.const_mul (2*K+2*b*M))
    have h3 := h2.add (hR2.const_mul (4*M))
    have e0 := integral_add (hT.const_mul c) (integrable_const (2*A*b+4*c))
    have e1 := integral_add h0 (hR.const_mul (2*A+8*K+8*b*M))
    have e2 := integral_add h1 (hRT.const_mul (2*K+2*b*M))
    have e3 := integral_add h2 (hR2.const_mul (4*M))
    have e4 := integral_add h3 (hR2T.const_mul M)
    simp only [Pi.add_apply] at e0 e1 e2 e3 e4
    dsimp only [U]
    rw [e4,e3,e2,e1,e0]
    simp only [integral_const_mul,integral_const,probReal_univ,one_smul]
  rw [integral_const_mul,heval] at hI
  have hbound := add_le_add (add_le_add (add_le_add (add_le_add (le_refl
    (c*(∫ ω, T ω ∂μ)+(2*A*b+4*c))) (mul_le_mul_of_nonneg_left hRle hcoeff1))
      (mul_le_mul_of_nonneg_left hRTle hcoeff2)) (mul_le_mul_of_nonneg_left hR2le hcoeff3))
      (mul_le_mul_of_nonneg_left hR2Tle hM)
  have hh := hI.trans (mul_le_mul_of_nonneg_left hbound he)
  convert hh using 1
  dsimp [c]
  ring

end
end ASDExplicitGamma.Native
