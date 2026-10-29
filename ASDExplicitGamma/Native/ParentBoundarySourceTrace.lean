module

public import ASDExplicitGamma.Native.ParentBoundarySourceFinite

/-! Complete parent-source trace, obtained from uniform finite-family
bounds rather than assuming convergence of its infinite Haar energy. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main ASDExplicitGamma.Variational
noncomputable section

/-- Physical parent/fine-cell source multiplier coefficient. -/
def parentBoundaryPotentialSourceClock (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
  Real.sqrt ((156/5:ℝ)*b^2/L.1^2)*
    Real.sqrt ((52/100:ℝ)^2*cubeScaleFactor Q^2+(662/1000:ℝ)^2*(cubeScaleFactor Q/3^depth)^2)+
  (372/1000:ℝ)*cubeScaleFactor Q*(cubeScaleFactor Q/3^depth)*
    Real.sqrt ((46488/25:ℝ)*b^2/L.1^4)

/-- The physical source coefficient is nonnegative. -/
theorem parent_boundary_potential_source_clock_nonneg (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) : 0≤parentBoundaryPotentialSourceClock Q depth b L := by
  unfold parentBoundaryPotentialSourceClock
  have hR := (Triadic.cubeScaleFactor_pos' Q).le
  positivity

/-- Every finite set of actual source modes has the sharp parent-boundary
energy estimate, with the SAME full broken weak-gradient profile. -/
theorem parent_boundary_potential_source_finset {ι : Type*}
    (e : HilbertBasis ι ℝ WhiteNoise) (s : Finset ι) (Q : TriadicCube 2)
    (depth : ℕ) (u : H10Function (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) :
    (∑ n ∈ s,parentBoundaryPotentialSourceMode e Q depth u b L n) ≤
      parentBoundaryPotentialSourceClock Q depth b L^2*lemmaVTiledWeakEnergy Q depth u.toH1Function.grad := by
  classical
  have he : (∑ n ∈ s,parentBoundaryPotentialSourceMode e Q depth u b L n) =
      descendantsAverage Q depth (fun U => hilbertPositiveHaarNorm U (Real.sqrt 3)
        (fun x => u.toH1Function x • mainQ3FiniteColumn e s b L x)^2) := by
    unfold parentBoundaryPotentialSourceMode
    rw [←Homogenization.descendantsAverage_sum]
    apply congrArg (fun z : ℝ => ((descendantsAtDepth Q depth).card : ℝ)⁻¹*z)
    exact Finset.sum_congr rfl (fun U hU => parent_boundary_source_finite_cell e s Q U depth hU u b L)
  have hh := parent_boundary_q3_finite_source e s Q depth u b L
  rw [←he] at hh
  have hW : 0≤lemmaVTiledWeakEnergy Q depth u.toH1Function.grad :=
    descendantsAverage_nonneg Q depth _ (fun U _ => vectorWeakHaarEnergy_nonneg U _)
  have h0 : 0≤∑ n ∈ s,parentBoundaryPotentialSourceMode e Q depth u b L n :=
    Finset.sum_nonneg (fun _ _ => descendantsAverage_nonneg Q depth _ (fun _ _ => sq_nonneg _))
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hh 2
  simpa only [Real.sq_sqrt h0,mul_pow,Real.sq_sqrt hW,parentBoundaryPotentialSourceClock] using hs

/-- The complete physical parent-source energy is genuinely summable and
obeys the sharp bound. No infinite-series convergence is a premise. -/
theorem parent_boundary_potential_source_trace {ι : Type*}
    (e : HilbertBasis ι ℝ WhiteNoise) (Q : TriadicCube 2) (depth : ℕ)
    (u : H10Function (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) :
    Summable (parentBoundaryPotentialSourceMode e Q depth u b L) ∧
    (∑' n,parentBoundaryPotentialSourceMode e Q depth u b L n) ≤
      parentBoundaryPotentialSourceClock Q depth b L^2*lemmaVTiledWeakEnergy Q depth u.toH1Function.grad := by
  have hn (n : ι) : 0≤parentBoundaryPotentialSourceMode e Q depth u b L n :=
    descendantsAverage_nonneg Q depth _ (fun _ _ => sq_nonneg _)
  have hh := fun s => parent_boundary_potential_source_finset e s Q depth u b L
  exact ⟨summable_of_sum_le hn hh,Real.tsum_le_of_sum_le hn hh⟩

end
end ASDExplicitGamma.Native
