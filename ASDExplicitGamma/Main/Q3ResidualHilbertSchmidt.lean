module

public import ASDExplicitGamma.Main.Q3ResidualCoordinates
public import ASDExplicitGamma.Main.Q3DiagResidualEstimate

/-! Full infinite covariance residual sums with the physical planar quarter turn. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational
open scoped BigOperators

local instance mainQ3ResidualHSFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The actual planar J is an isometry of the full source positive energy. -/
theorem main_vectorPositiveHaarEnergy_quarterTurn (Q : TriadicCube 2) (F : Vec 2 → Fin 2 → ℝ) :
    vectorPositiveHaarEnergy Q (fun x => planarQuarterTurn (F x)) = vectorPositiveHaarEnergy Q F := by
  unfold vectorPositiveHaarEnergy
  simp only [Fin.sum_univ_two, planarQuarterTurn, ite_true,
    show (1:Fin 2) ≠ 0 by decide, ite_false, primalEnergy_neg]
  ring

/-- The complete broken energy of one actual Gaussian residual source column,
including its physical spatial quarter turn. -/
noncomputable def mainQ3ResidualEnergy {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (j : ℕ)
    (φ : H1Function (openCubeSet Q)) (l : ι) : ℝ :=
  descendantsAverage Q j (fun U => vectorPositiveHaarEnergy U
    (fun x => planarQuarterTurn (mainQ3ResidualCoordinate e b L Q j φ U l x)))

/-- Finite averaging commutes with the actual finite source-column sum. -/
theorem main_descendantsAverage_finset_sum {ι : Type*} (Q : TriadicCube 2) (j : ℕ)
    (s : Finset ι) (f : ι → TriadicCube 2 → ℝ) :
    descendantsAverage Q j (fun U => ∑ l ∈ s, f l U) =
      ∑ l ∈ s, descendantsAverage Q j (f l) := by
  dsimp only [descendantsAverage]
  rw [Finset.sum_comm, Finset.mul_sum]

/-- Uniform finite-family residual estimates bound the true column-energy sums. -/
theorem main_q3_residual_energy_finset {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (j : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet Q)) :
    let φ := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    (∑ l ∈ s, mainQ3ResidualEnergy e b L Q j φ l) ≤
      (mainQ3RemainderExact (diagMeshRadius Q j) b L.1*Real.sqrt (lemmaVTiledWeakEnergy Q j φ.grad))^2 := by
  intro φ
  let E := fun U => hilbertPrimalEnergy U (Real.sqrt 3) (mainQ3DiagResidualColumn e s b L Q j φ U)
  have he : descendantsAverage Q j E = ∑ l ∈ s, mainQ3ResidualEnergy e b L Q j φ l := by
    simp only [mainQ3ResidualEnergy]
    rw [← main_descendantsAverage_finset_sum]
    dsimp only [descendantsAverage]
    congr 1
    apply Finset.sum_congr rfl
    intro U hU
    dsimp only [E]
    rw [main_q3_residual_energy_coordinates e s b L Q j p u U hU]
    apply Finset.sum_congr rfl
    intro l _
    rw [main_vectorPositiveHaarEnergy_quarterTurn U (mainQ3ResidualCoordinate e b L Q j φ U l)]
    rfl
  have hEn : 0 ≤ descendantsAverage Q j E := by
    rw [he]
    apply Finset.sum_nonneg
    intro l _
    unfold mainQ3ResidualEnergy descendantsAverage
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun U _ => vectorPositiveHaarEnergy_nonneg U _)
  have hb := (main_q3_diag_residual_estimate e s b L Q j p u).2
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hb 2
  rw [Real.sq_sqrt hEn, he] at hs
  exact hs

/-- The actual infinite residual sources are Hilbert--Schmidt in the broken
positive-Haar norm and obey the exact source coefficient. No finite-rank,
convergence, covariance, or product-estimate premise remains. -/
theorem main_q3_residual_hilbert_schmidt {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (j : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet Q)) :
    let φ := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    Summable (mainQ3ResidualEnergy e b L Q j φ) ∧
    Real.sqrt (∑' l, mainQ3ResidualEnergy e b L Q j φ l) ≤
      mainQ3RemainderExact (diagMeshRadius Q j) b L.1*Real.sqrt (lemmaVTiledWeakEnergy Q j φ.grad) := by
  intro φ
  have hn (l : ι) : 0 ≤ mainQ3ResidualEnergy e b L Q j φ l := by
    unfold mainQ3ResidualEnergy descendantsAverage
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun U _ => vectorPositiveHaarEnergy_nonneg U _)
  have hb := main_q3_residual_energy_finset e (b := b) (L := L) (Q := Q) (j := j) (p := p) (u := u)
  have hs := summable_of_sum_le hn hb
  refine ⟨hs, (Real.sqrt_le_iff).2 ⟨?_, Real.tsum_le_of_sum_le hn hb⟩⟩
  have hr := (diagMeshRadius_pos Q j).le
  have hc0 : 0 ≤ planarC0 := Real.sqrt_nonneg _
  have hc1 : 0 ≤ planarC1 := Real.sqrt_nonneg _
  unfold mainQ3RemainderExact
  positivity

end ASDExplicitGamma.Main
