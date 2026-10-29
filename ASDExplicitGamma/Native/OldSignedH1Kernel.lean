module

public import ASDExplicitGamma.Native.OldSignedLpKernel
public import ASDExplicitGamma.Native.OldSignedLpWeakGradient
public import Homogenization.Sobolev.H1.Algebra.H1Function

/-! Actual Hilbert H1 reconstruction of square-summable scalar H1 modes.
Weak derivatives are proved by continuous test pairing of the complete sums. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
noncomputable section

/-- Scalar H1 values embedded in their actual white basis direction. -/
def oldSignedH1ModeValue {d : ℕ} {E I : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {U : Set (Vec d)} (e : HilbertBasis I ℝ E) (u : I → H1Function U) (n : I) :
    Lp E 2 (volume.restrict U) :=
  oldSignedBasisLpEmbedding (volume.restrict U) e n ((u n).memL2.toLp (u n))

/-- Scalar H1 derivatives embedded in the same actual white basis direction. -/
def oldSignedH1ModeGradient {d : ℕ} {E I : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {U : Set (Vec d)} (e : HilbertBasis I ℝ E) (u : I → H1Function U) (n : I) (k : Fin d) :
    Lp E 2 (volume.restrict U) :=
  oldSignedBasisLpEmbedding (volume.restrict U) e n
    (((u n).grad_memL2 k).toLp (fun x => (u n).grad x k))

/-- Each genuine embedded H1 mode satisfies the literal weak identity,
including the actual Lp representatives. -/
theorem old_signed_h1_mode_weak_gradient {d : ℕ} {E I : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {U : Set (Vec d)} (e : HilbertBasis I ℝ E) (u : I → H1Function U) (n : I) (w : E) :
    HasWeakGradientOn U (fun x => inner ℝ w (oldSignedH1ModeValue e u n x))
      (fun x k => inner ℝ w (oldSignedH1ModeGradient e u n k x)) := by
  intro k phi hphi hcompact hsupport
  have hv : oldSignedH1ModeValue e u n =ᵐ[volume.restrict U] fun x => u n x • e n := by
    filter_upwards [old_signed_basis_lp_embedding_coeFn (volume.restrict U) e n
      ((u n).memL2.toLp (u n)),(u n).memL2.coeFn_toLp] with x hx hy
    exact hx.trans (congrArg (fun t : ℝ => t • e n) hy)
  have hg : oldSignedH1ModeGradient e u n k =ᵐ[volume.restrict U]
      fun x => (u n).grad x k • e n := by
    filter_upwards [old_signed_basis_lp_embedding_coeFn (volume.restrict U) e n
      (((u n).grad_memL2 k).toLp (fun x => (u n).grad x k)),
      ((u n).grad_memL2 k).coeFn_toLp] with x hx hy
    exact hx.trans (congrArg (fun t : ℝ => t • e n) hy)
  have he := ((inner ℝ w (e n)) • u n).hasWeakGradient k phi hphi hcompact hsupport
  calc
    _ = ∫ x in U,((inner ℝ w (e n)) • u n) x * (fderiv ℝ phi x) (basisVec k) := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [hx,real_inner_smul_right]
      simp only [H1Function.smul_toFun]
      ring
    _ = _ := he
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx,real_inner_smul_right]
      simp only [H1Function.smul_grad,Pi.smul_apply,smul_eq_mul]
      ring

/-- Reconstruction as an actual Hilbert-valued H1 function. No Poincare,
Haar or covariance estimate is part of the carrier or its hypotheses. -/
def oldSignedH1Kernel {d : ℕ} {E I : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {U : Set (Vec d)} (hU : IsOpen U) (e : HilbertBasis I ℝ E)
    (u : I → H1Function U)
    (hu : Summable (fun n => ‖(u n).memL2.toLp (u n)‖^2))
    (hdu : ∀ k,Summable (fun n => ‖((u n).grad_memL2 k).toLp (fun x => (u n).grad x k)‖^2)) :
    HilbertH1Function U E where
  toFun := oldSignedLpKernel (volume.restrict U) e (fun n => (u n).memL2.toLp (u n))
  grad x k := oldSignedLpKernel (volume.restrict U) e
    (fun n => ((u n).grad_memL2 k).toLp (fun x => (u n).grad x k)) x
  memL2 := Lp.memLp _
  gradMemL2 _ := Lp.memLp _
  hasWeakGradient w := old_signed_lp_sum_weak_gradient hU
    (oldSignedH1ModeValue e u) (oldSignedH1ModeGradient e u) _ _
    (old_signed_basis_lp_summable _ e _ hu).hasSum
    (fun k => (old_signed_basis_lp_summable _ e _ (hdu k)).hasSum)
    (old_signed_h1_mode_weak_gradient e u) w

end
end ASDExplicitGamma.Native
