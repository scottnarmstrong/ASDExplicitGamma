module

public import ASDExplicitGamma.Native.OldSignedBasisLpEmbedding
public import ASDExplicitGamma.Triadic.HilbertHaarBasic
public import Homogenization.Sobolev.H1.BasicLemmas

/-! Continuous spatial L2 testing and weak derivatives of complete Hilbert
mode sums. These are literal weak derivative identities, without a regularity
or covariance estimate in the resulting Sobolev carrier. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
noncomputable section

/-- Spatial L2 pairing with a scalar test function and a Hilbert vector. -/
def oldSignedLpTest {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (mu : Measure X) (c : Lp ℝ 2 mu) (w : E) : Lp E 2 mu →L[ℝ] ℝ :=
  innerSL ℝ ((ContinuousLinearMap.toSpanSingleton ℝ w).compLpL 2 mu c)

/-- The continuous L2 test functional is the actual weak-test integral. -/
theorem old_signed_lp_test_integral {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (mu : Measure X) (c : Lp ℝ 2 mu) (w : E) (f : Lp E 2 mu) :
    oldSignedLpTest mu c w f=∫ x,c x * inner ℝ w (f x) ∂mu := by
  rw [oldSignedLpTest,innerSL_apply_apply,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ w).coeFn_compLpL c] with x hx
  rw [hx]
  simp only [ContinuousLinearMap.toSpanSingleton_apply,real_inner_smul_left]

/-- Complete L2 convergence of values and all derivatives preserves the
actual scalar-functional weak derivative identities. -/
theorem old_signed_lp_sum_weak_gradient {d : ℕ} {E I : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {U : Set (Vec d)} (hU : IsOpen U)
    (f : I → Lp E 2 (volume.restrict U))
    (g : I → Fin d → Lp E 2 (volume.restrict U))
    (F : Lp E 2 (volume.restrict U)) (G : Fin d → Lp E 2 (volume.restrict U))
    (hf : HasSum f F) (hg : ∀ k,HasSum (fun n => g n k) (G k))
    (hw : ∀ n w,HasWeakGradientOn U (fun x => inner ℝ w (f n x))
      (fun x k => inner ℝ w (g n k x))) (w : E) :
    HasWeakGradientOn U (fun x => inner ℝ w (F x))
      (fun x k => inner ℝ w (G k x)) := by
  intro k phi hphi hcompact hsupport
  let p := H1Function.ofContDiff hU (hphi.of_le (by simp)) hcompact
  let c : Lp ℝ 2 (volume.restrict U) := p.memL2.toLp phi
  let dc : Lp ℝ 2 (volume.restrict U) := (p.grad_memL2 k).toLp (fun x => (fderiv ℝ phi x) (basisVec k))
  have hc : c =ᵐ[volume.restrict U] phi := p.memL2.coeFn_toLp
  have hdc : dc =ᵐ[volume.restrict U] fun x => (fderiv ℝ phi x) (basisVec k) :=
    (p.grad_memL2 k).coeFn_toLp
  have ht (a : Lp E 2 (volume.restrict U)) :
      oldSignedLpTest (volume.restrict U) c w a=∫ x in U,inner ℝ w (a x)*phi x := by
    rw [old_signed_lp_test_integral]
    apply integral_congr_ae
    filter_upwards [hc] with x hx
    rw [hx,mul_comm]
  have hdt (a : Lp E 2 (volume.restrict U)) :
      oldSignedLpTest (volume.restrict U) dc w a=
        ∫ x in U,inner ℝ w (a x)*(fderiv ℝ phi x) (basisVec k) := by
    rw [old_signed_lp_test_integral]
    apply integral_congr_ae
    filter_upwards [hdc] with x hx
    rw [hx,mul_comm]
  have hs := hf.mapL (oldSignedLpTest (volume.restrict U) dc w)
  have hs' := ((hg k).mapL (oldSignedLpTest (volume.restrict U) c w)).neg
  have he : (fun n => oldSignedLpTest (volume.restrict U) dc w (f n))=
      (fun n => -oldSignedLpTest (volume.restrict U) c w (g n k)) := by
    funext n
    rw [hdt,ht]
    exact hw n w k phi hphi hcompact hsupport
  rw [he] at hs
  have hh := hs.unique hs'
  rwa [hdt,ht] at hh

end
end ASDExplicitGamma.Native
