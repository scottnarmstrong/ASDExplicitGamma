module

public import ASDExplicitGamma.Inverse.StoppedKuhnH1

/-! Sharp scalar payments of the actual finite-Kuhn interpolant. They agree
with the value and coordinate-gradient budgets of the stopped source meshes. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization
open Algsuperdiff.Section3.Provider.Affine Algsuperdiff.Section3.Provider.Whitney
noncomputable section

/-- Affine interpolation preserves a uniform vertex bound on the entire
closed simplex, without a count of its vertices. -/
theorem kuhn_interp_abs_bound (T : KuhnCell 2) (g : Vec 2 → ℝ) (M : ℝ)
    (hg : ∀ v : Fin 3, |g (T.vertex v)| ≤ M) {x : Vec 2} (hx : x ∈ T.closedCarrier) :
    |kuhnInterp T g x| ≤ M := by
  have hi : Convex ℝ (Set.Icc (-M) M) := convex_Icc (-M) M
  have hc : Convex ℝ ((kuhnInterpAffine T g) ⁻¹' Set.Icc (-M) M) :=
    hi.affine_preimage (kuhnInterpAffine T g)
  have hs : T.vertexSet ⊆ (kuhnInterpAffine T g) ⁻¹' Set.Icc (-M) M := by
    rintro y ⟨v,rfl⟩
    change kuhnInterp T g (T.vertex v) ∈ Set.Icc (-M) M
    rw [kuhnInterp_vertex]
    exact abs_le.mp (hg v)
  have hh := convexHull_min hs hc
  apply abs_le.mpr
  exact hh ((closedCarrier_eq_convexHull_vertexSet T) ▸ hx)

/-- The actual Kuhn coordinate slope costs two vertex amplitudes over the
physical mesh side. -/
theorem kuhn_slope_abs_bound (T : KuhnCell 2) (g : Vec 2 → ℝ) (M : ℝ)
    (hg : ∀ v : Fin 3, |g (T.vertex v)| ≤ M) (i : Fin 2) :
    |kuhnSlope T g i| ≤ 2*M/cubeScaleFactor T.supportCube := by
  have ho (k l : Fin 3) : |g (T.vertex k)-g (T.vertex l)| ≤ 2*M := by
    have hh := abs_sub_le (g (T.vertex k)) 0 (g (T.vertex l))
    simp only [sub_zero,zero_sub,abs_neg] at hh
    exact hh.trans (by linarith only [hg k,hg l])
  have hb (k l : Fin 3) :
      |(g (T.vertex k)-linearFn (0 : Vec 2) (T.vertex k))-
        (g (T.vertex l)-linearFn (0 : Vec 2) (T.vertex l))| ≤ 2*M := by
    simpa only [linearFn,vecDot_zero_left,sub_zero] using ho k l
  have ht := abs_kuhnSlope_sub_le_of_vertex_oscillation T g (0 : Vec 2) hb i
  simpa only [Pi.zero_apply,sub_zero] using ht

end
end ASDExplicitGamma.Inverse
