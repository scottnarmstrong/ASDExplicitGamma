module

public import ASDExplicitGamma.Scalar.OldHessianTrialColumnProduct
public import ASDExplicitGamma.Scalar.OldHessianTrialPositiveRestriction

/-! The very same coarse Gaussian product restricted to the original fine
children. Both physical modes and spatial Haar depths stay complete. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Main Triadic Gaussian
noncomputable section

/-- Each literal column coordinate is in L2 and has finite complete positive
Haar energy. Singleton extraction discharges these regularity facts. -/
theorem old_hessian_column_coordinate_regular {I : Type*}
    (e : HilbertBasis I ℝ WhiteNoise) (b : ℝ) (L : {l : ℝ // 0<l})
    (Q : TriadicCube 2) (u : H10Function (openCubeSet Q)) (j : I) (i : Fin 2) :
    let f := fun x => u.toH1Function x*
      (fderiv ℝ (q3Convolution b L h3Zero (e j)) x) (basisVec i)
    MemLp f 2 (normalizedCubeMeasure Q) ∧
      Summable (fun k : ℕ => (Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) f)) := by
  classical
  intro f
  let s : Finset I := {j}
  let F := fun x => u.toH1Function x • mainQ3FiniteColumn e s b L x
  have hF : MemLp F 2 (normalizedCubeMeasure Q) :=
    (mainRankOneMultiplier Q _ (mainQ3FiniteColumn_contDiff e s b L)).product_memLp
      u.toH1Function.memL2_normalizedCubeMeasure
  have hP := (old_hessian_finite_column_product e s b L Q u).1
  let c : s × Fin 2 := (⟨j,Finset.mem_singleton_self j⟩,i)
  have he : (fun x => (F x).ofLp c)=f := by
    funext x
    rfl
  let pr : EuclideanSpace ℝ (s × Fin 2) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : s × Fin 2 => ℝ) c
  have hm := pr.comp_memLp' hF
  have hs := main_hilbert_coordinate_summable Q hF hP c
  change MemLp (fun x => (F x).ofLp c) 2 (normalizedCubeMeasure Q) at hm
  rw [he] at hm hs
  exact ⟨hm,hs⟩

/-- The actual product column is contractive on the nine fine children;
the field is restricted, never recomputed with a fine-cell potential. -/
theorem old_hessian_column_child_energy {I : Type*}
    (e : HilbertBasis I ℝ WhiteNoise) (b : ℝ) (L : {l : ℝ // 0<l})
    (Q : TriadicCube 2) (u : H10Function (openCubeSet Q)) (j : I) :
    descendantsAverage Q 1 (fun U => vectorPositiveHaarEnergy U (fun x i =>
      u.toH1Function x*(fderiv ℝ (q3Convolution b L h3Zero (e j)) x) (basisVec i))) ≤
      mainQ3DerivativeColumnEnergy e Q b L u j := by
  exact old_hessian_vector_positive_child_restriction Q _
    (fun i => (old_hessian_column_coordinate_regular e b L Q u j i).1)
    (fun i => (old_hessian_column_coordinate_regular e b L Q u j i).2)

/-- The complete fine-broken source product column has the genuine coarse
coefficient. Summability is explicit before comparing the infinite mode sums. -/
theorem old_hessian_column_broken_energy {I : Type*}
    (e : HilbertBasis I ℝ WhiteNoise) (b : ℝ) (L : {l : ℝ // 0<l})
    (Q : TriadicCube 2) (u : H10Function (openCubeSet Q)) :
    let E := fun j => descendantsAverage Q 1 (fun U => vectorPositiveHaarEnergy U (fun x i =>
      u.toH1Function x*(fderiv ℝ (q3Convolution b L h3Zero (e j)) x) (basisVec i)))
    Summable E ∧ (∑' j,E j)≤
      (oldSignedDerivativeKappa (cubeScaleFactor Q) (Real.sqrt 2*b) L.1*
        vectorWeakHaarNorm Q u.toH1Function.grad)^2 := by
  intro E
  have hn (j : I) : 0≤E j := descendantsAverage_nonneg Q 1 _
    (fun U _ => vectorPositiveHaarEnergy_nonneg U _)
  have hh := old_hessian_column_energy e b L Q u
  have hpoint (j : I) : E j≤mainQ3DerivativeColumnEnergy e Q b L u j :=
    old_hessian_column_child_energy e b L Q u j
  have hs : Summable E := hh.1.of_nonneg_of_le hn hpoint
  exact ⟨hs,(hs.tsum_le_tsum hpoint hh.1).trans hh.2⟩

end
end ASDExplicitGamma.Scalar
