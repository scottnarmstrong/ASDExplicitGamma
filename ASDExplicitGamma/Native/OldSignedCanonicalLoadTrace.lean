module

public import ASDExplicitGamma.Response.Analytic

/-! Canonical top/bottom loads and the orthonormal paired loads give the
same actual response trace, before differentiating in the physical coefficient. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational
noncomputable section

/-- The minimized energy is half the actual affine-minimizer quadratic. -/
theorem old_signed_realization_mu_quadratic {U : Set (Vec 2)} {a : CoeffField 2}
    (M : MuHilbertRealization U a) (P : BlockVec 2) :
    2*M.muCandidate P=M.energyBilin (M.minimizerMap P) (M.minimizerMap P) := by
  change 2*((1/2:ℝ)*M.energyBilin (M.minimizerMap P) (M.minimizerMap P))=_
  ring

/-- The actual doubled response is the quadratic energy of its actual
linear affine-minimizer map. -/
theorem old_signed_frame_energy_quadratic {U : Set (Vec 2)}
    [IsFiniteMeasure (volumeMeasureOn U)] (hU : MeasurableSet U)
    (hvol : 0<(volume U).toReal) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient U) (P : BlockVec 2) :
    let M := (responseFrameMuOperatorSystemData hU hvol nu sigma hnu hsigma k).toMuHilbertRealization
    responseFrameEnergyObservable hU hvol nu sigma hnu hsigma P k=
      M.energyBilin (M.minimizerMap P) (M.minimizerMap P) := by
  intro M
  have he : responseFrameEnergyObservable hU hvol nu sigma hnu hsigma P k=2*M.muCandidate P := by
    simp only [responseFrameEnergyObservable,responseFrameEnergy]
    exact congrArg (fun z : ResponseCoefficient U => 2*
      (responseFrameMuOperatorSystemData hU hvol nu sigma hnu hsigma z).toMuHilbertRealization.muCandidate P)
      (zero_add k)
  exact he.trans (old_signed_realization_mu_quadratic M P)

/-- The actual two paired orthonormal responses equal the canonical
pure top/bottom responses, with exactly the same molecular parameter and frame. -/
theorem old_signed_frame_energy_canonical_pair {U : Set (Vec 2)}
    [IsFiniteMeasure (volumeMeasureOn U)] (hU : MeasurableSet U)
    (hvol : 0<(volume U).toReal) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient U) (i : Fin 2) :
    responseFrameEnergyObservable hU hvol nu sigma hnu hsigma (orthonormalFrameLoad i 1) k+
      responseFrameEnergyObservable hU hvol nu sigma hnu hsigma (orthonormalFrameLoad i (-1)) k=
    responseFrameEnergyObservable hU hvol nu sigma hnu hsigma (basisVec i,0) k+
      responseFrameEnergyObservable hU hvol nu sigma hnu hsigma (0,basisVec i) k := by
  simp_rw [old_signed_frame_energy_quadratic]
  let M := (responseFrameMuOperatorSystemData hU hvol nu sigma hnu hsigma k).toMuHilbertRealization
  let S := M.minimizerMap
  let B := M.energyBilin
  let P : BlockVec 2 := blockBasis (Sum.inl i)
  let Q : BlockVec 2 := blockBasis (Sum.inr i)
  let t := (Real.sqrt 2)⁻¹
  change B (S (t • (P+1 • Q))) (S (t • (P+1 • Q)))+
    B (S (t • (P+(-1:ℝ) • Q))) (S (t • (P+(-1:ℝ) • Q)))=B (S P) (S P)+B (S Q) (S Q)
  have ht : t^2=(1/2:ℝ) := by
    dsimp only [t]
    rw [inv_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    norm_num
  simp only [one_smul,neg_one_smul,map_smul,map_add,map_neg,
    add_apply,neg_apply,smul_apply,smul_eq_mul]
  calc
    _ = (2*t^2)*(B (S P) (S P)+B (S Q) (S Q)) := by ring
    _ = _ := by rw [ht]; ring

end
end ASDExplicitGamma.Native
