module

public import ASDExplicitGamma.Cold.PlateauGram

/-! # The actual graph mean of a variational response maximizer -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
namespace ASDExplicitGamma.Cold

/-- Actual harmonic maximizers on the square have the source coarse response graph.
All auxiliary basis maximizers and deterministic coarse witnesses are constructed here. -/
theorem harmonic_maximizer_graph_mean (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (p q : Vec 2)
    (w : AHarmonicFunction a (openCubeSet Q)) (hmax : IsResponseMaximizer (openCubeSet Q) p q a w) :
    coarseGraphMean Q w =
      (q+matVecMul (coarseBlockMatrix (openCubeSet Q) a).upperRight q-
          matVecMul (coarseBlockMatrix (openCubeSet Q) a).upperLeft p,
       -p+matVecMul (coarseBlockMatrix (openCubeSet Q) a).lowerRight q-
          matVecMul (coarseBlockMatrix (openCubeSet Q) a).lowerLeft p) := by
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_eq_volume_cubeSet,volume_cubeSet_toReal]
    exact cubeVolume_pos Q
  have hne : (openCubeSet Q).Nonempty := by
    by_contra hn
    have he := Set.not_nonempty_iff_eq_empty.mp hn
    rw [he] at hvol
    simp at hvol
  let gradBasis := fun i : Fin 2 => Classical.choice
    (ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain hne
      (isOpenBoundedConvexDomain_openCubeSet Q) hEll 0 (Pi.single i 1))
  let fluxBasis := fun i : Fin 2 => Classical.choice
    (ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain hne
      (isOpenBoundedConvexDomain_openCubeSet Q) hEll (Pi.single i 1) 0)
  obtain ⟨sigma,hA,_,hS,hK,hSigma,_,hdet⟩ :=
    Variational.exists_energyMap_coarseData (isOpenBoundedConvexDomain_openCubeSet Q) hEll hvol
  apply Prod.ext
  · exact basic_cg_identities_average_flux_formula_coarseBlockMatrix_of_isResponseMaximizer
      (openCubeSet Q) a hA hS hK hSigma hdet p q
      (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) w hmax
      (fun i => (fluxBasis i : AHarmonicFunction a (openCubeSet Q)))
      (fun i => (fluxBasis i).isResponseMaximizer)
  · exact basic_cg_identities_average_gradient_formula_coarseBlockMatrix_of_isResponseMaximizer
      (openCubeSet Q) a hA hS hK hdet p q
      (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) w hmax
      (fun i => (gradBasis i : AHarmonicFunction a (openCubeSet Q)))
      (fun i => (gradBasis i).isResponseMaximizer)

end ASDExplicitGamma.Cold
