module

public import ASDExplicitGamma.Native.OldSignedPlusRemainderEnergy

/-! The actual harmonic flat field G(H e_i)-P_D(H e_i) and its exact
per-mode energy: the source Bflat before completing the white trace. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Main
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

/-- The actual harmonic flat field between the all-gradient and Dirichlet
projections of the same physical source load. -/
def oldSignedFlatHarmonicField (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) : Vec 2 → Vec 2 :=
  fun x => (fun k => mainFlatPlusCoordinate Q b L n (i,k) x)-
    (fun k => mainFlatMinusCoordinate Q b L n (i,k) x)

/-- Actual square integrability of the harmonic flat field. -/
theorem old_signed_flat_harmonic_memL2 (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    MemVectorL2 (openCubeSet Q) (oldSignedFlatHarmonicField Q b L n i) :=
  (old_signed_flat_plus_memL2 Q b L n i).sub (old_signed_flat_minus_memL2 Q b L n i)

/-- The flat difference is a genuine harmonic gradient. -/
theorem old_signed_flat_harmonic_spaces (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    IsPotentialOn (openCubeSet Q) (oldSignedFlatHarmonicField Q b L n i) ∧
      IsSolenoidalOn (openCubeSet Q) (oldSignedFlatHarmonicField Q b L n i) := by
  constructor
  · obtain ⟨u,hu⟩ := old_signed_flat_plus_potential Q b L n i
    obtain ⟨v,hv⟩ := old_signed_flat_minus_potential_zero_trace Q b L n i
    refine ⟨u-v.toH1Function,?_⟩
    rw [H1Function.sub_grad,hu,hv]
    rfl
  · have hh := old_signed_solenoidal_sub
      (old_signed_flat_remainders_memL2 Q b L n i).1
      (old_signed_flat_remainders_memL2 Q b L n i).2
      (old_signed_flat_plus_remainder_solenoidal Q b L n i)
      (old_signed_flat_minus_remainder_solenoidal Q b L n i)
    convert hh using 1
    funext x k
    simp only [oldSignedFlatHarmonicField,oldSignedFlatPlusRemainder,oldSignedFlatMinusRemainder,Pi.sub_apply]
    ring

/-- Actual two-load energy of the all-gradient flat modes. -/
def oldSignedFlatPlusModeEnergy (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) : ℝ :=
  ∑ i : Fin 2,∑ k : Fin 2,energy Q (fun x => mainFlatPlusCoordinate Q b L n (i,k) x)

/-- Actual two-load harmonic flat energy, the source Bflat mode summand. -/
def oldSignedFlatBoundaryModeEnergy (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) : ℝ :=
  ∑ i : Fin 2,∑ k : Fin 2,energy Q (fun x => oldSignedFlatHarmonicField Q b L n i x k)

/-- Per physical mode, all-gradient energy equals Dirichlet energy plus
harmonic boundary energy, by the actual H10/solenoidal orthogonality. -/
theorem old_signed_flat_boundary_mode_energy (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) :
    oldSignedFlatPlusModeEnergy Q b L n=oldSignedFlatDirichletModeEnergy Q b L n+
      oldSignedFlatBoundaryModeEnergy Q b L n := by
  have hi (i : Fin 2) :
      (∑ k : Fin 2,energy Q (fun x => mainFlatPlusCoordinate Q b L n (i,k) x))=
      (∑ k : Fin 2,energy Q (fun x => mainFlatMinusCoordinate Q b L n (i,k) x))+
        ∑ k : Fin 2,energy Q (fun x => oldSignedFlatHarmonicField Q b L n i x k) := by
    have ho : (∫ x in openCubeSet Q,vecDot
        (fun k => mainFlatMinusCoordinate Q b L n (i,k) x)
        (oldSignedFlatHarmonicField Q b L n i x) ∂volume)=0 := by
      obtain ⟨u,hu⟩ := old_signed_flat_minus_potential_zero_trace Q b L n i
      simpa only [hu,vecDot_comm] using (old_signed_flat_harmonic_spaces Q b L n i).2 u
    have hh := old_signed_normalized_energy_add_of_orthogonal Q (old_signed_flat_minus_memL2 Q b L n i)
      (old_signed_flat_harmonic_memL2 Q b L n i) ho
    have he (k : Fin 2) : (fun x => ((fun k => mainFlatMinusCoordinate Q b L n (i,k) x)+
        oldSignedFlatHarmonicField Q b L n i x) k)=(fun x => mainFlatPlusCoordinate Q b L n (i,k) x) := by
      funext x
      simp only [oldSignedFlatHarmonicField,Pi.sub_apply,Pi.add_apply]
      ring
    simp_rw [he] at hh
    exact hh
  unfold oldSignedFlatPlusModeEnergy oldSignedFlatDirichletModeEnergy oldSignedFlatBoundaryModeEnergy
  simp_rw [hi]
  exact Finset.sum_add_distrib

end
end ASDExplicitGamma.Native
