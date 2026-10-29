module

public import ASDExplicitGamma.Scalar.UpperCellEnergyResetBottomPairing
public import ASDExplicitGamma.Scalar.TopSourceResidual

/-! Deterministic full-history RESET bound for an actual bottom source. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
noncomputable section
open Homogenization Response Variational MeasureTheory Triadic Algsuperdiff.Section3
open scoped ENNReal

/-- The source's full-response history controls the actual weighted-projection residual energy.
All coefficient, projection, flux, and energy objects are the literal source constructions. -/
theorem upper_cell_reset_bottom_source_residual (Q : TriadicCube 2) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient (openCubeSet Q))
    (f : Vec 2 → Vec 2) (hf : ScalarPositiveHaarAdmissible Q f) :
    ENNReal.ofReal (cubeAverage Q (fun x => blockVecDot
      (scalarResidualField Q ν σ hν hσ k
        (toHilbertBlockL2OfBlockField (upper_cell_reset_bottom_load_memL2 Q hf.memLp)) x)
      (scalarCoefficientFlux (responseFramePlanarCoefficientField ν σ k)
        (scalarResidualField Q ν σ hν hσ k
          (toHilbertBlockL2OfBlockField (upper_cell_reset_bottom_load_memL2 Q hf.memLp))) x))) ≤
    completeFullResponseHistory Q (responseFramePlanarCoefficientField ν σ k) *
      ENNReal.ofReal (positiveSourceEnergy Q f) := by
  let a := responseFramePlanarCoefficientField ν σ k
  let H := toHilbertBlockL2OfBlockField (upper_cell_reset_bottom_load_memL2 Q hf.memLp)
  let Z : Vec 2 → BlockVec 2 := scalarResidualField Q ν σ hν hσ k H
  let r : Vec 2 → Vec 2 := fun x => (scalarCoefficientFlux a Z x).2
  let E : ℝ := cubeAverage Q (fun x => blockVecDot (Z x) (scalarCoefficientFlux a Z x))
  let W : ℝ := ∑ i,dualEnergy Q sourceHaarBase (fun x => r x i)
  let P : ℝ := positiveSourceEnergy Q f
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) ν σ hν hσ k
  have hZ : MemBlockL2 (openCubeSet Q) Z :=
    (scalarResidualField Q ν σ hν hσ k H).property
  have hflux := scalar_coefficient_flux_memL2 Q a hEll hZ
  have hRlocal : MemVectorL2 (openCubeSet Q) (fun x => (scalarCoefficientFlux a Z x).2) :=
    memVectorL2_snd_of_memBlockL2 hflux
  have hr (i : Fin 2) : MemLp (fun x => r x i) 2 (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On
      (Homogenization.memScalarL2_coord_of_memVectorL2 hRlocal i)
  have hfLocal : MemVectorL2 (openCubeSet Q) f :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hf.memLp
  have hfCoord (i : Fin 2) : MemLp (fun x => f x i) 2 (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On
      (Homogenization.memScalarL2_coord_of_memVectorL2 hfLocal i)
  have hpair := upper_cell_reset_bottom_energy_pairing Q ν σ hν hσ k hf.memLp
  have hhaar := vector_haar_pairing_bound Q r f hr hfCoord hf.increments
  have hEpos : 0 ≤ E := by
    dsimp [E]
    rw [cube_average_eq_volume_average_open]
    exact scalar_coefficient_energy_average_nonneg Q a hEll Z
  have hWpos : 0 ≤ W := by
    dsimp [W]
    exact Finset.sum_nonneg (fun i _ => dual_energy_nonneg Q (fun x => r x i))
  have hPpos : 0 ≤ P := by
    exact positive_source_energy_nonneg Q f
  have hpairE : E=∑ i,pairing Q (fun x => r x i) (fun x => f x i) := by
    simpa [E,r,Z,a,H] using hpair
  have hEbound : E ≤ Real.sqrt W * Real.sqrt P := by
    rw [hpairE]
    exact (le_abs_self _).trans hhaar
  have hEsq : E^2 ≤ W*P := by
    have hsw : Real.sqrt W ^ 2=W := Real.sq_sqrt hWpos
    have hsp : Real.sqrt P ^ 2=P := Real.sq_sqrt hPpos
    nlinarith [hEpos,Real.sqrt_nonneg W,Real.sqrt_nonneg P]
  have hweak := upper_cell_reset_bottom_weak_history Q ν σ hν hσ k H
  have hweak' : ENNReal.ofReal W ≤
      completeFullResponseHistory Q a * ENNReal.ofReal E := by
    simpa [W,E,r,Z,a] using hweak
  have hsqENN : ENNReal.ofReal E * ENNReal.ofReal E ≤ ENNReal.ofReal W * ENNReal.ofReal P := by
    rw [← ENNReal.ofReal_mul hEpos,← ENNReal.ofReal_mul hWpos]
    simpa only [pow_two] using ENNReal.ofReal_le_ofReal hEsq
  have hmul : ENNReal.ofReal W * ENNReal.ofReal P ≤
      (completeFullResponseHistory Q a * ENNReal.ofReal E) * ENNReal.ofReal P := by
    exact mul_le_mul_left hweak' (ENNReal.ofReal P)
  have hfinal : ENNReal.ofReal E * ENNReal.ofReal E ≤
      (completeFullResponseHistory Q a * ENNReal.ofReal P) * ENNReal.ofReal E := by
    exact hsqENN.trans (by simpa [mul_assoc,mul_left_comm,mul_comm] using hmul)
  change ENNReal.ofReal E ≤ completeFullResponseHistory Q a * ENNReal.ofReal P
  by_cases hEz : E=0
  · simp [hEz]
  · have hE0 : ENNReal.ofReal E ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (lt_of_le_of_ne hEpos (Ne.symm hEz))
    have hEtop : ENNReal.ofReal E ≠ ⊤ := ENNReal.ofReal_ne_top
    have hcancel := (ENNReal.mul_le_mul_iff_left hE0 hEtop).mp hfinal
    simpa [E,P] using hcancel


/-- The deterministic RESET bound on the exact Hilbert energy carrier used
by the physical expectation theorem. An AE bottom-load representation is
sufficient; its chosen measurable representative is immaterial. -/
theorem upper_cell_reset_bottom_hilbert_energy
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q))
    (f : Vec 2 → Vec 2) (hf : ScalarPositiveHaarAdmissible Q f)
    (F : HilbertBlockL2 (openCubeSet Q))
    (hF : F =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => HilbertBlockVec.ofBlockVec (0,f x)) :
    let Y := scalarProjectionResidual Q ν σ hν hσ k F
    ENNReal.ofReal ((scalarFrameRealization Q ν σ hν hσ k).energyBilin Y Y) ≤
      completeFullResponseHistory Q (responseFramePlanarCoefficientField ν σ k)*
        ENNReal.ofReal (positiveSourceEnergy Q f) := by
  have heq : F=toHilbertBlockL2OfBlockField (upper_cell_reset_bottom_load_memL2 Q hf.memLp) := by
    apply Lp.ext
    exact hF.trans (coeFn_toHilbertBlockL2OfBlockField
      (upper_cell_reset_bottom_load_memL2 Q hf.memLp)).symm
  rw [heq]
  dsimp only
  let H := toHilbertBlockL2OfBlockField (upper_cell_reset_bottom_load_memL2 Q hf.memLp)
  let Z := scalarResidualField Q ν σ hν hσ k H
  have hZ : MemBlockL2 (openCubeSet Q) Z := Lp.memLp Z
  have hr : toHilbertBlockL2OfBlockField hZ=scalarProjectionResidual Q ν σ hν hσ k H :=
    hilbert_field_rebuild _
  have hb := scalar_frame_bilinear_field Q ν σ hν hσ k hZ hZ
  rw [hr] at hb
  rw [hb,←cube_average_eq_volume_average_open]
  exact upper_cell_reset_bottom_source_residual Q ν σ hν hσ k f hf

end
end ASDExplicitGamma.Scalar
