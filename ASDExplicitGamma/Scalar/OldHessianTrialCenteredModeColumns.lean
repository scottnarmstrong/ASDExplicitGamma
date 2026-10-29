module

public import ASDExplicitGamma.Scalar.OldHessianTrialCenteredRegularity
public import ASDExplicitGamma.Scalar.OldHessianTrialPrincipalContraction

/-! Full physical centered source columns before source/receiver contraction. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- One actual centered source column, with both load and mode labels. -/
def oldHessianCenteredModeColumn (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (p : whiteBasisIndex×Fin 2) (U : TriadicCube 2) : Vec 2 → Vec 2 :=
  let a := responseFramePlanarCoefficientField nu sigma k
  let ha := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  oldHessianCenteredMixedSource Q (coarse+1) b L
    (oldSignedCanonicalFirstCorrector Q a ha (0,basisVec p.2))
    (oldHessianCoarsePotential Q coarse nu sigma hnu hsigma k (basisVec p.2)) U p.1

def oldHessianCenteredModeEnergy (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (p : whiteBasisIndex×Fin 2) : ℝ :=
  oldHessianBrokenColumnEnergy Q (coarse+1) (oldHessianCenteredModeColumn Q coarse nu sigma hnu hsigma k b L p)

/-- Exact complete spatial centered-source energy, before any moment bound. -/
def oldHessianCenteredSpatialEnergy (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
  ∑ i : Fin 2,∑' n : whiteBasisIndex,oldHessianCenteredModeEnergy Q coarse nu sigma hnu hsigma k b L (n,i)

/-- The actual centered columns supply their own square membership and
all-depth positive-Haar convergence on each fine tile. -/
theorem old_hessian_centered_mode_regular (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (p : whiteBasisIndex×Fin 2) (U : TriadicCube 2) (hU : U∈descendantsAtDepth Q (coarse+1)) (l : Fin 2) :
    MemLp (fun x => oldHessianCenteredModeColumn Q coarse nu sigma hnu hsigma k b L p U x l)
      2 (normalizedCubeMeasure U) ∧
    Summable (fun d => (Real.sqrt 3)^(d+1)*energy U (cubeIncrement U (d+1)
      (fun x => oldHessianCenteredModeColumn Q coarse nu sigma hnu hsigma k b L p U x l))) :=
  old_hessian_centered_mixed_source_regular Q (coarse+1) b L _ _ U hU p.1 l

/-- The dependent fine-cell energy is exactly the physical broken norm. -/
theorem old_hessian_centered_mode_energy_average (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (p : whiteBasisIndex×Fin 2) :
    oldHessianCenteredModeEnergy Q coarse nu sigma hnu hsigma k b L p=
      oldSignedCellAverage Q (coarse+1) (fun U => vectorPositiveHaarEnergy U.val
        (oldHessianCenteredModeColumn Q coarse nu sigma hnu hsigma k b L p U.val)) :=
  (old_signed_cell_average_eq_descendantsAverage Q (coarse+1) _).symm

/-- The genuine complete mode/load source energy is summable and can be
reordered only after its actual two-load summability has been proved. -/
theorem old_hessian_centered_mode_series (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) :
    Summable (oldHessianCenteredModeEnergy Q coarse nu sigma hnu hsigma k b L) ∧
      (∑' p,oldHessianCenteredModeEnergy Q coarse nu sigma hnu hsigma k b L p)=
        oldHessianCenteredSpatialEnergy Q coarse nu sigma hnu hsigma k b L := by
  let E := oldHessianCenteredModeEnergy Q coarse nu sigma hnu hsigma k b L
  have hs (i : Fin 2) : Summable (fun n : whiteBasisIndex => E (n,i)) :=
    (old_hessian_actual_centered_mixed_energy Q coarse nu sigma hnu hsigma k b L i).1
  have hn (p) : 0≤E p := old_hessian_broken_column_energy_nonneg Q (coarse+1) _
  have hprod : Summable E := (summable_prod_of_nonneg hn).2 ⟨fun _ => Summable.of_finite,
    by simpa only [tsum_fintype] using summable_sum (s := Finset.univ) (fun i _ => hs i)⟩
  refine ⟨hprod,?_⟩
  rw [hprod.tsum_prod]
  simp only [tsum_fintype]
  exact Summable.tsum_finsetSum (fun i _ => hs i)

end
end ASDExplicitGamma.Scalar
