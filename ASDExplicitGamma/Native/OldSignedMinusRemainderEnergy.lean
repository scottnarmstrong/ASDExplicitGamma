module

public import ASDExplicitGamma.Native.OldSignedNormalizedEnergy
public import ASDExplicitGamma.Native.OldSignedRotatedEnergyTrace

/-! Complete-mode energy subtraction for the actual minus harmonic
remainder. Summability is established before any real tsum is consumed. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Main
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

/-- Actual normalized local Dirichlet energy of both rotated affine loads. -/
def oldSignedFlatDirichletModeEnergy (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) : ℝ :=
  ∑ i : Fin 2,∑ k : Fin 2,energy Q (fun x => mainFlatMinusCoordinate Q b L n (i,k) x)

/-- Actual normalized energy of both minus harmonic remainders. -/
def oldSignedFlatMinusRemainderModeEnergy (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) : ℝ :=
  ∑ i : Fin 2,∑ k : Fin 2,energy Q (fun x => oldSignedFlatMinusRemainder Q b L n i x k)

/-- Both complete nonnegative energy series converge, and exact
orthogonal subtraction survives the complete white-mode limit. -/
theorem old_signed_flat_minus_complete_energy (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    Summable (oldSignedFlatDirichletModeEnergy Q b L) ∧
      Summable (oldSignedFlatMinusRemainderModeEnergy Q b L) ∧
      HasSum (oldSignedFlatMinusRemainderModeEnergy Q b L)
        (b^2-∑' n,oldSignedFlatDirichletModeEnergy Q b L n) := by
  let p := fun n : whiteBasisIndex => ∑ i : Fin 2,∑ k : Fin 2,
    energy Q (fun x => oldSignedRotatedProjectedField b L (whiteBasis n) i x k)
  let y := oldSignedFlatDirichletModeEnergy Q b L
  let r := oldSignedFlatMinusRemainderModeEnergy Q b L
  have hp : HasSum p (b^2) := old_signed_rotated_projected_energy_trace Q b L
  have hy0 (n) : 0≤y n := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => energy_nonneg Q _))
  have hr0 (n) : 0≤r n := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => energy_nonneg Q _))
  have he (n) : p n=y n+r n := by
    dsimp only [p,y,r,oldSignedFlatDirichletModeEnergy,oldSignedFlatMinusRemainderModeEnergy]
    simp_rw [old_signed_flat_minus_normalized_energy]
    exact Finset.sum_add_distrib
  have hy : Summable y := hp.summable.of_nonneg_of_le hy0
    (fun n => by rw [he]; exact le_add_of_nonneg_right (hr0 n))
  have hr : Summable r := hp.summable.of_nonneg_of_le hr0
    (fun n => by rw [he]; exact le_add_of_nonneg_left (hy0 n))
  refine ⟨hy,hr,?_⟩
  have hh := hp.sub hy.hasSum
  convert hh using 1
  funext n
  rw [he]
  ring

/-- The exact complete minus boundary energy is nonnegative and at most
one shell variance. No default value for a divergent real series is used. -/
theorem old_signed_flat_minus_remainder_energy_bounds (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    0≤∑' n,oldSignedFlatMinusRemainderModeEnergy Q b L n ∧
      (∑' n,oldSignedFlatMinusRemainderModeEnergy Q b L n)≤b^2 := by
  have hh := old_signed_flat_minus_complete_energy Q b L
  have hy : 0≤∑' n,oldSignedFlatDirichletModeEnergy Q b L n :=
    tsum_nonneg (fun n => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => energy_nonneg Q _)))
  refine ⟨tsum_nonneg (fun n => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => energy_nonneg Q _))),?_⟩
  rw [hh.2.2.tsum_eq]
  exact sub_le_self _ hy

end
end ASDExplicitGamma.Native
