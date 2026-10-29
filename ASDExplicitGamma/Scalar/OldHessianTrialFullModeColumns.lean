module

public import ASDExplicitGamma.Scalar.OldHessianTrialSourceEnvelope
public import ASDExplicitGamma.Scalar.OldHessianTrialBrokenModePairing

/-! Complete original mixed source columns for the oscillatory receiver cross. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The literal full mixed source column, including its frozen row. -/
def oldHessianFullModeColumn (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (p : whiteBasisIndex×Fin 2) : Vec 2 → Vec 2 :=
  fun x => (oldHessianMixedBottomSource Q coarse (coarse+1) nu sigma hnu hsigma k b L p.1 p.2 x).2

/-- Its exact broken positive energy on the original fine cells. -/
def oldHessianFullModeEnergy (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (p : whiteBasisIndex×Fin 2) : ℝ :=
  oldSignedCellAverage Q (coarse+1) (fun U =>
    vectorPositiveHaarEnergy U.val (oldHessianFullModeColumn Q coarse nu sigma hnu hsigma k b L p))

/-- Actual L2 membership and complete positive-Haar convergence precede
all spatial and mode pairings. -/
theorem old_hessian_full_mode_regular (n : ℤ) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (b : ℝ) (L : {l : ℝ // 0<l})
    (p : whiteBasisIndex×Fin 2) (U : OldSignedCellIndex (originCube 2 n) (coarse+1)) (i : Fin 2) :
    MemLp (fun x => oldHessianFullModeColumn (originCube 2 n) coarse nu sigma hnu hsigma k b L p x i)
      2 (normalizedCubeMeasure U.val) ∧
    Summable (fun j => (Real.sqrt 3)^(j+1)*energy U.val (cubeIncrement U.val (j+1)
      (fun x => oldHessianFullModeColumn (originCube 2 n) coarse nu sigma hnu hsigma k b L p x i))) := by
  have hm := (old_hessian_mixed_bottom_source_memL2 (originCube 2 n) coarse (coarse+1)
    nu sigma hnu hsigma k b L p.1 p.2).mono_measure
      (Measure.restrict_mono_set volume (openCubeSet_subset_of_mem_descendantsAtDepth U.property))
  refine ⟨memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hm) i),?_⟩
  exact (old_hessian_mixed_source_positive n (coarse+1) b L _ _ p.1 U.val U.property).1 i

/-- Full physical mode/load convergence and the exact two-load source energy. -/
theorem old_hessian_full_mode_series (n : ℤ) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 n
    let E := oldHessianFullModeEnergy Q coarse nu sigma hnu hsigma k b L
    Summable E ∧ (∑' p,E p)=∑ i : Fin 2,∑' j : whiteBasisIndex,
      oldHessianBrokenColumnEnergy Q (coarse+1) (fun _U =>
        oldHessianFullModeColumn Q coarse nu sigma hnu hsigma k b L (j,i)) := by
  intro Q E
  have he p : E p=oldHessianBrokenColumnEnergy Q (coarse+1) (fun _U =>
      oldHessianFullModeColumn Q coarse nu sigma hnu hsigma k b L p) :=
    old_signed_cell_average_eq_descendantsAverage Q (coarse+1)
      (fun U => vectorPositiveHaarEnergy U (oldHessianFullModeColumn Q coarse nu sigma hnu hsigma k b L p))
  have hs (i : Fin 2) : Summable (fun j : whiteBasisIndex => E (j,i)) := by
    simp_rw [he]
    exact (old_hessian_actual_mixed_source_energy n coarse nu sigma hnu hsigma k b L i).1
  have hn (p) : 0≤E p := old_signed_cell_average_nonneg _ _ _
    (fun U => vectorPositiveHaarEnergy_nonneg U.val _)
  have hprod : Summable E := (summable_prod_of_nonneg hn).2
      ⟨fun _ => Summable.of_finite,by
        simpa only [tsum_fintype] using summable_sum (s := Finset.univ) (fun i _ => hs i)⟩
  refine ⟨hprod,?_⟩
  rw [hprod.tsum_prod]
  simp only [tsum_fintype]
  rw [Summable.tsum_finsetSum (fun i _ => hs i)]
  simp_rw [he]

end
end ASDExplicitGamma.Scalar
