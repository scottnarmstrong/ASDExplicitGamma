module

public import ASDExplicitGamma.Gaussian.Q3ConvolutionRegularity
public import Mathlib.Topology.ContinuousMap.Compact

/-! # Continuous coefficient and first-derivative images of the physical q3 operator -/

@[expose] public section

open MeasureTheory Homogenization Set
open scoped Topology RealInnerProductSpace

namespace ASDExplicitGamma.Gaussian

section
variable (K : Set (Vec 2)) [CompactSpace K] (b : ℝ) (L : {l : ℝ // 0 < l})

/-- Convolution as a bounded linear map into continuous functions on the actual compact set. -/
noncomputable def q3ContinuousOperator (a : H3Index) : WhiteNoise →L[ℝ] C(K, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun (u : WhiteNoise) => ⟨fun x => q3Convolution b L a u x.1,
        (q3Convolution_continuous b L a u).comp continuous_subtype_val⟩
      map_add' := by
        intro u v
        ext x
        change ⟪u + v, q3Section b L a x.1⟫ = ⟪u, q3Section b L a x.1⟫ + ⟪v, q3Section b L a x.1⟫
        exact inner_add_left _ _ _
      map_smul' := by
        intro r u
        ext x
        change ⟪r • u, q3Section b L a x.1⟫ = r * ⟪u, q3Section b L a x.1⟫
        exact real_inner_smul_left _ _ _ }
    ‖q3Section b L a 0‖ (fun u => by
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      intro x
      change ‖⟪u, q3Section b L a x.1⟫‖ ≤ _
      have he : ‖q3Section b L a x.1‖ = ‖q3Section b L a 0‖ := by
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        rw [gaussQ3Section_norm_sq, gaussQ3Section_norm_sq]
      exact (norm_inner_le_norm _ _).trans_eq (by rw [he, mul_comm]))

theorem q3ContinuousOperator_apply (a : H3Index) (u : WhiteNoise) (x : K) :
    q3ContinuousOperator K b L a u x = q3Convolution b L a u x.1 := rfl

end

/-- Indices for the value and its two first partial derivatives. -/
def c1Index : Fin 3 → H3Index :=
  ![h3Zero, ⟨(1, 0), by norm_num⟩, ⟨(0, 1), by norm_num⟩]

/-- A first jet uses uniform norms of the value and the two genuine spatial partials. -/
abbrev C1Jet (K : Set (Vec 2)) := Fin 3 → C(K, ℝ)

noncomputable def q3C1JetOperator (K : Set (Vec 2)) [CompactSpace K]
    (b : ℝ) (L : {l : ℝ // 0 < l}) : WhiteNoise →L[ℝ] C1Jet K :=
  ContinuousLinearMap.pi fun i => q3ContinuousOperator K b L (c1Index i)

end ASDExplicitGamma.Gaussian
