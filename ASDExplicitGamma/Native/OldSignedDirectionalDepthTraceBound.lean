module

public import ASDExplicitGamma.Native.OldSignedDirectionalDepthPositivity

/-! Trace domination for the paired directional matrix. This gives the
pathwise rare-event payment without asserting a pathwise half-trace bound. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational
noncomputable section

/-- In two dimensions, a nonnegative quadratic form is bounded by its
trace times the squared load, by testing the perpendicular load. -/
theorem old_signed_nonnegative_quadratic_le_trace (A : Mat 2)
    (hA : ∀ e : Vec 2,0 ≤ vecDot e (matVecMul A e)) (e : Vec 2) :
    vecDot e (matVecMul A e) ≤ Matrix.trace A*vecNormSq e := by
  let eperp : Vec 2 := ![-e 1,e 0]
  have h := hA eperp
  have he : vecDot e (matVecMul A e)+vecDot eperp (matVecMul A eperp)=
      Matrix.trace A*vecNormSq e := by
    simp [vecDot,matVecMul,Matrix.trace_fin_two,vecNormSq,Fin.sum_univ_two,eperp]
    ring
  linarith only [h,he]

/-- The physical coarse majorant is bounded by its exact trace. This is
available samplewise; the sharper half factor is reserved for expectation. -/
theorem old_signed_directional_depth_trace_bound (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    let a := responseFramePlanarCoefficientField nu sigma k
    vecDot e (matVecMul (oldSignedPairedDepthMatrix Q depth a) e) ≤
      descendantsAverage Q depth (fun U => traceDefect (openCubeSet U) a 1)*vecNormSq e := by
  intro a
  have hh := old_signed_nonnegative_quadratic_le_trace (oldSignedPairedDepthMatrix Q depth a)
    (old_signed_paired_depth_quadratic_nonneg Q depth nu sigma hnu hsigma k) e
  rwa [old_signed_paired_depth_matrix_trace] at hh

end
end ASDExplicitGamma.Native
