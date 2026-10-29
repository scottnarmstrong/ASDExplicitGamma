module

public import ASDExplicitGamma.Scalar.LawAnnealedShift
public import ASDExplicitGamma.Scalar.LawCoarseShift

/-! Exact scalar self-similarity from the literal annealed top-block limit. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Book Filter
open Algsuperdiff.Section3

/-- The actual defining block limit gives the top-left diagonal scalar limit. -/
theorem annealed_top_entry_tendsto_sigmaBar (M : ABKModel 2) (n : ℤ) :
    Tendsto (fun k : ℕ => (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M n) (k:ℤ)).upperLeft 0 0)
      atTop (nhds (Annealed.sigmaBar M n : ℝ)) := by
  have h := (Annealed.sigmaBar_characterization M n).2.1
  have he := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h (Sum.inl (0:Fin 2)))) (Sum.inl (0:Fin 2))
  simpa [toFullBlockMat,Ch02.blockDiag] using he

/-- The exact scalar law for every natural shell increment, at every integer base label. -/
theorem sigmaBar_exact_law_nat (M : ABKModel 2) (n : ℤ) (j : ℕ) :
    (Annealed.sigmaBar M (n+(j:ℤ)) : ℝ)=
      Real.rpow 3 (M.gamma*(j:ℝ))*(Annealed.sigmaBar (viscosityShiftModel M (j:ℤ)) n : ℝ) := by
  have hl := (annealed_top_entry_tendsto_sigmaBar M (n+(j:ℤ))).comp (tendsto_add_atTop_nat j)
  have hr := (annealed_top_entry_tendsto_sigmaBar (viscosityShiftModel M (j:ℤ)) n).const_mul
    (Real.rpow 3 (M.gamma*(j:ℝ)))
  have he (k : ℕ) :
      (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M (n+(j:ℤ))) ((k+j:ℕ):ℤ)).upperLeft 0 0=
      Real.rpow 3 (M.gamma*(j:ℝ))*
        (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw (viscosityShiftModel M (j:ℤ)) n)
          (k:ℤ)).upperLeft 0 0 := by
    rw [Nat.add_comm k j]
    exact annealed_top_entry_scale_shift M j k n 0 0
  change Tendsto (fun k : ℕ => (Ch04.annealedBlockMatrixAtScale
    (Cutoff.coefficientCutoffLaw M (n+(j:ℤ))) ((k+j:ℕ):ℤ)).upperLeft 0 0) _ _ at hl
  simp_rw [he] at hl
  exact tendsto_nhds_unique hl hr

end ASDExplicitGamma.Scalar
