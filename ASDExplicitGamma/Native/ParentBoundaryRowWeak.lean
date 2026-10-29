module

public import ASDExplicitGamma.Native.ParentBoundaryRowTesting
public import Homogenization.Book.Ch02.MultiscaleEllipticity

/-! Weak derivative of an actual complete-Hilbert covariance contraction. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
noncomputable section

/-- Each scalar Hilbert coordinate has the genuine product rule. -/
theorem parent_boundary_row_mode_weak {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube 2) (b : Vec 2 → E) (hb : ContDiff ℝ 1 b)
    (u : HilbertH1Function (openCubeSet Q) E) (z : E) :
    HasWeakGradientOn (openCubeSet Q)
      (fun x => inner ℝ z (b x)*inner ℝ z (u.toFun x))
      (fun x i => inner ℝ z (b x)*inner ℝ z (u.grad x i) +
        inner ℝ z ((fderiv ℝ b x) (basisVec i))*inner ℝ z (u.toFun x)) := by
  have hbc := parent_boundary_row_coordinate_contDiff b hb z
  have htop := contDiffOne_memLpTop_of_bounded_open_domain
    (isOpenBoundedConvexDomain_openCubeSet Q) hbc
  let v := h1_mul_contDiffOne_memLpTop (isOpenBoundedConvexDomain_openCubeSet Q)
    (Book.Ch02.openCubeSet_nonempty Q) (u.scalar z) hbc htop.1 htop.2
  have ht := v.hasWeakGradient
  change HasWeakGradientOn (openCubeSet Q)
    (fun x => inner ℝ z (b x)*inner ℝ z (u.toFun x))
    (fun x i => inner ℝ z (b x)*inner ℝ z (u.grad x i) +
      inner ℝ z (u.toFun x)*(fderiv ℝ (fun y => inner ℝ z (b y)) x) (basisVec i)) at ht
  simp_rw [parent_boundary_row_coordinate_derivative b hb z,mul_comm (inner ℝ z (u.toFun _))] at ht
  exact ht

/-- Passing the literal coordinate product rule through complete covariance
testing proves the actual Hilbert-row product rule. No weak derivative or
product estimate is assumed in the resulting conclusion. -/
theorem parent_boundary_row_product_weak {E I : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Countable I]
    (e : HilbertBasis I ℝ E) (Q : TriadicCube 2) (b : Vec 2 → E) (hb : ContDiff ℝ 1 b)
    (u : HilbertH1Function (openCubeSet Q) E) :
    HasWeakGradientOn (openCubeSet Q) (fun x => inner ℝ (b x) (u.toFun x))
      (fun x i => inner ℝ (b x) (u.grad x i) +
        inner ℝ ((fderiv ℝ b x) (basisVec i)) (u.toFun x)) := by
  intro i phi hphi hcompact hsupport
  let mu := volume.restrict (openCubeSet Q)
  let test := H1Function.ofContDiff (isOpen_openCubeSet Q) (hphi.of_le (by simp)) hcompact
  let db := fun x => (fderiv ℝ b x) (basisVec i)
  have hB : MemLp b ⊤ mu := parent_boundary_continuous_memLp_top_open Q b hb.continuous
  have hDB : MemLp db ⊤ mu := parent_boundary_continuous_memLp_top_open Q db
    ((hb.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hDtest : MemLp (fun x => (fderiv ℝ phi x) (basisVec i)) 2 mu := test.gradMemL2 i
  have hs0 := parent_boundary_bounded_row_test mu e b u.toFun _ hB u.memL2 hDtest
  have hs1 := parent_boundary_bounded_row_test mu e b (fun x => u.grad x i) phi
    hB (u.gradMemL2 i) test.memL2
  have hs2 := parent_boundary_bounded_row_test mu e db u.toFun phi hDB u.memL2 test.memL2
  have hmode (n : I) :
      (∫ x,(fderiv ℝ phi x) (basisVec i)*inner ℝ (e n) (b x)*inner ℝ (e n) (u.toFun x) ∂mu) =
      -((∫ x,phi x*inner ℝ (e n) (b x)*inner ℝ (e n) (u.grad x i) ∂mu) +
        ∫ x,phi x*inner ℝ (e n) (db x)*inner ℝ (e n) (u.toFun x) ∂mu) := by
    have ht := parent_boundary_row_mode_weak Q b hb u (e n) i phi hphi hcompact hsupport
    have hi1 : Integrable (fun x => phi x*inner ℝ (e n) (b x)*inner ℝ (e n) (u.grad x i)) mu := by
      have hm : MemLp (fun x => inner ℝ (e n) (b x)*inner ℝ (e n) (u.grad x i)) 2 mu :=
        ((innerSL ℝ (e n)).comp_memLp' hB).mul
          ((innerSL ℝ (e n)).comp_memLp' (u.gradMemL2 i))
      have hh := hm.integrable_mul test.memL2
      convert hh using 1
      funext x
      change _=(inner ℝ (e n) (b x)*inner ℝ (e n) (u.grad x i))*phi x
      ring
    have hi2 : Integrable (fun x => phi x*inner ℝ (e n) (db x)*inner ℝ (e n) (u.toFun x)) mu := by
      have hm : MemLp (fun x => inner ℝ (e n) (db x)*inner ℝ (e n) (u.toFun x)) 2 mu :=
        ((innerSL ℝ (e n)).comp_memLp' hDB).mul
          ((innerSL ℝ (e n)).comp_memLp' u.memL2)
      have hh := hm.integrable_mul test.memL2
      convert hh using 1
      funext x
      change _=(inner ℝ (e n) (db x)*inner ℝ (e n) (u.toFun x))*phi x
      ring
    have he : (∫ x,(inner ℝ (e n) (b x)*inner ℝ (e n) (u.grad x i)+
        inner ℝ (e n) (db x)*inner ℝ (e n) (u.toFun x))*phi x ∂mu) =
        (∫ x,phi x*inner ℝ (e n) (b x)*inner ℝ (e n) (u.grad x i) ∂mu) +
        ∫ x,phi x*inner ℝ (e n) (db x)*inner ℝ (e n) (u.toFun x) ∂mu := by
      rw [←integral_add hi1 hi2]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by ring)
    rw [he] at ht
    convert ht using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by ring)
  have hsum := hs0.congr_fun (fun n => (hmode n).symm)
  have hh := hsum.unique (hs1.add hs2).neg
  have hI1 : Integrable (fun x => phi x*inner ℝ (b x) (u.grad x i)) mu :=
    test.memL2.integrable_mul ((innerSL ℝ).memLp_of_bilin 2 hB (u.gradMemL2 i))
  have hI2 : Integrable (fun x => phi x*inner ℝ (db x) (u.toFun x)) mu :=
    test.memL2.integrable_mul ((innerSL ℝ).memLp_of_bilin 2 hDB u.memL2)
  have he : (∫ x,(inner ℝ (b x) (u.grad x i)+inner ℝ (db x) (u.toFun x))*phi x ∂mu) =
      (∫ x,phi x*inner ℝ (b x) (u.grad x i) ∂mu)+
        ∫ x,phi x*inner ℝ (db x) (u.toFun x) ∂mu := by
    rw [←integral_add hI1 hI2]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by ring)
  rw [he]
  convert hh using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => mul_comm _ _)

end
end ASDExplicitGamma.Native
