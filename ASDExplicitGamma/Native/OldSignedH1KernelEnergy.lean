module

public import ASDExplicitGamma.Native.OldSignedH1Kernel
public import ASDExplicitGamma.Triadic.PoincareCell

/-! Exact normalized value and derivative energies of complete Hilbert H1
kernels, with square summability supplied by normalized scalar energies. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic ASDExplicitGamma.Gaussian
noncomputable section

/-- Unnormalized scalar spatial L2 energy differs from the source energy
by precisely the cube volume. -/
theorem old_signed_scalar_lp_energy (Q : TriadicCube 2) {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (volume.restrict (openCubeSet Q))) :
    ‖hf.toLp f‖^2=cubeVolume Q * energy Q f := by
  rw [l2_norm_sq,energy_eq_integral_sq,integral_normalized_eq_open]
  have hi : (∫ x in openCubeSet Q,‖hf.toLp f x‖^2)=∫ x in openCubeSet Q,f x^2 := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx,Real.norm_eq_abs,sq_abs]
  rw [hi,←mul_assoc,mul_inv_cancel₀ (ne_of_gt (cubeVolume_pos Q)),one_mul]

/-- Summability of actual normalized scalar energies supplies the L2
summability needed for the actual Hilbert H1 reconstruction. -/
theorem old_signed_h1_kernel_value_summable {I : Type*} (Q : TriadicCube 2)
    (u : I → H1Function (openCubeSet Q))
    (hu : Summable (fun n => energy Q (u n))) :
    Summable (fun n => ‖(u n).memL2.toLp (u n)‖^2) := by
  simp_rw [old_signed_scalar_lp_energy]
  exact hu.mul_left _

/-- Exact normalized energy of a complete spatial white-Hilbert kernel. -/
theorem old_signed_lp_kernel_normalized_energy {E I : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Countable I]
    (Q : TriadicCube 2) (e : HilbertBasis I ℝ E) (f : I → Vec 2 → ℝ)
    (hf : ∀ n,MemLp (f n) 2 (volume.restrict (openCubeSet Q)))
    (hs : Summable (fun n => energy Q (f n))) :
    hilbertEnergy Q (oldSignedLpKernel (volume.restrict (openCubeSet Q)) e
      (fun n => (hf n).toLp (f n)))=∑' n,energy Q (f n) := by
  have hnorm : Summable (fun n => ‖(hf n).toLp (f n)‖^2) := by
    simp_rw [old_signed_scalar_lp_energy]
    exact hs.mul_left _
  rw [hilbertEnergy,integral_normalized_eq_open,←l2_norm_sq,
    old_signed_lp_kernel_norm_sq _ e _ hnorm]
  simp_rw [old_signed_scalar_lp_energy]
  rw [tsum_mul_left,←mul_assoc,inv_mul_cancel₀ (ne_of_gt (cubeVolume_pos Q)),one_mul]

/-- The actual H1 kernel constructed directly from source-normalized scalar
value and derivative energies. -/
def oldSignedNormalizedH1Kernel {E I : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube 2) (e : HilbertBasis I ℝ E)
    (u : I → H1Function (openCubeSet Q))
    (hu : Summable (fun n => energy Q (u n)))
    (hdu : ∀ k,Summable (fun n => energy Q (fun x => (u n).grad x k))) :
    HilbertH1Function (openCubeSet Q) E :=
  oldSignedH1Kernel (isOpen_openCubeSet Q) e u
    (old_signed_h1_kernel_value_summable Q u hu)
    (fun k => by
      simp_rw [old_signed_scalar_lp_energy]
      exact (hdu k).mul_left _)

/-- Exact value energy of the reconstructed genuine Hilbert H1 kernel. -/
theorem old_signed_h1_kernel_energy {E I : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Countable I]
    (Q : TriadicCube 2) (e : HilbertBasis I ℝ E)
    (u : I → H1Function (openCubeSet Q))
    (hu : Summable (fun n => energy Q (u n)))
    (hdu : ∀ k,Summable (fun n => energy Q (fun x => (u n).grad x k))) :
    hilbertEnergy Q (oldSignedNormalizedH1Kernel Q e u hu hdu).toFun=∑' n,energy Q (u n) :=
  old_signed_lp_kernel_normalized_energy Q e (fun n => u n) (fun n => (u n).memL2) hu

/-- Exact derivative energy in each spatial coordinate, for the same
complete physical kernel. -/
theorem old_signed_h1_kernel_gradient_energy {E I : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Countable I]
    (Q : TriadicCube 2) (e : HilbertBasis I ℝ E)
    (u : I → H1Function (openCubeSet Q))
    (hu : Summable (fun n => energy Q (u n)))
    (hdu : ∀ k,Summable (fun n => energy Q (fun x => (u n).grad x k))) (k : Fin 2) :
    hilbertEnergy Q (fun x => (oldSignedNormalizedH1Kernel Q e u hu hdu).grad x k)=
      ∑' n,energy Q (fun x => (u n).grad x k) :=
  old_signed_lp_kernel_normalized_energy Q e _ (fun n => (u n).grad_memL2 k) (hdu k)

/-- Every actual white coefficient of the H1 kernel recovers the original
physical mode, rather than only an abstract isometric copy. -/
theorem old_signed_h1_kernel_coefficient {E I : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube 2) (e : HilbertBasis I ℝ E)
    (u : I → H1Function (openCubeSet Q))
    (hu : Summable (fun n => energy Q (u n)))
    (hdu : ∀ k,Summable (fun n => energy Q (fun x => (u n).grad x k))) (n : I) :
    (fun x => inner ℝ (e n) ((oldSignedNormalizedH1Kernel Q e u hu hdu).toFun x))
      =ᵐ[volume.restrict (openCubeSet Q)] u n := by
  let f := oldSignedLpKernel (volume.restrict (openCubeSet Q)) e
    (fun j => (u j).memL2.toLp (u j))
  have hc := (innerSL ℝ (e n)).coeFn_compLpL f
  rw [old_signed_lp_kernel_coefficient _ e _
    (old_signed_h1_kernel_value_summable Q u hu)] at hc
  exact hc.symm.trans (u n).memL2.coeFn_toLp

end
end ASDExplicitGamma.Native
