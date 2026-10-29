module

public import ASDExplicitGamma.Variational.LemmaVTiles
public import ASDExplicitGamma.Variational.LemmaVMinimizer

/-! Lift, finite-direction linearity, and tile K/P duality for the row form. -/

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic

noncomputable section

/-- A finite linear combination of the row-form fields. -/
def lemmaVRowCombination {ι : Type*} {U : Set (Vec 2)}
    (I : H1Function U →ₗ[ℝ] H1Function U) (η : ι → H1Function U)
    (v : H1Function U) (s : Finset ι) (c : ι → ℝ) : Vec 2 → Vec 2 :=
  fun x => ∑ i ∈ s, c i • lemmaVPlanarRowField I (η i) v x

/-- L² regularity of finite row combinations. -/
theorem lemmaVRowCombination_memL2 {ι : Type*} {U : Set (Vec 2)}
    (I : H1Function U →ₗ[ℝ] H1Function U) (η : ι → H1Function U)
    (v : H1Function U) (s : Finset ι) (c : ι → ℝ)
    (hη : ∀ i ∈ s, MemLp (η i) (⊤ : ENNReal) (volume.restrict U))
    (hDη : ∀ i ∈ s, ∀ b, MemLp (fun x => (η i).grad x b) (⊤ : ENNReal) (volume.restrict U)) :
    MemVectorL2 U (lemmaVRowCombination I η v s c) := by
  exact memLp_finsetSum s fun i hi =>
    (lemmaVPlanarRowField_memL2 I (η i) v (hη i hi) (hDη i hi)).const_smul (c i)

/-- Finite direction sums lift to their row combination without a boundary
condition on the tested H¹ function. -/
theorem lemmaV_sum_pairing_eq_row {ι : Type*} {U : Set (Vec 2)}
    [IsFiniteMeasure (volumeMeasureOn U)] (hU : IsOpenBoundedConvexDomain U)
    (I : H1Function U →ₗ[ℝ] H1Function U) (η : ι → H1Function U)
    (v w : H1Function U) (s : Finset ι) (c : ι → ℝ)
    (hres : MemH10 U (v - I v).toFun)
    (hη : ∀ i ∈ s, MemLp (η i) (⊤ : ENNReal) (volume.restrict U))
    (hDη : ∀ i ∈ s, ∀ b, MemLp (fun x => (η i).grad x b) (⊤ : ENNReal) (volume.restrict U)) :
    (∑ i ∈ s, c i * volumeAverage U (fun x => vecDot
      ((η i) x • matVecMul responsePlanarJ (v.grad x)) (w.grad x))) =
      volumeAverage U (fun x => vecDot (lemmaVRowCombination I η v s c x) (w.grad x)) := by
  have hlift (i : ι) (hi : i ∈ s) :=
    lemmaV_pairing_lift_of_interpolant hU I v (η i) w hres (hη i hi) (hDη i hi)
  calc
    _ = ∑ i ∈ s, c i * volumeAverage U
        (fun x => vecDot (lemmaVPlanarRowField I (η i) v x) (w.grad x)) :=
      Finset.sum_congr rfl fun i hi => congrArg (fun z : ℝ => c i * z) (hlift i hi)
    _ = volumeAverage U (fun x => ∑ i ∈ s,
        c i * vecDot (lemmaVPlanarRowField I (η i) v x) (w.grad x)) := by
      rw [volumeAverage_sum]
      · apply Finset.sum_congr rfl
        intro i _
        exact (volumeAverage_smul U (c i) (fun x =>
          vecDot (lemmaVPlanarRowField I (η i) v x) (w.grad x))).symm
      · intro i hi
        exact (integrableOn_vecDot_of_memVectorL2
          (lemmaVPlanarRowField_memL2 I (η i) v (hη i hi) (hDη i hi))
          w.grad_memVectorL2).const_mul (c i)
    _ = _ := by
      congr 1
      funext x
      simp [lemmaVRowCombination, vecDot, Finset.sum_mul,
        Finset.sum_comm, mul_assoc, mul_add]

/-- The row-form estimate before applying H2. -/
theorem lemmaV_row_estimate {ι : Type*} (Q : TriadicCube 2) (j : ℕ)
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q))
    (η : ι → H1Function (openCubeSet Q)) (v w : H1Function (openCubeSet Q))
    (s : Finset ι) (c : ι → ℝ)
    (hres : MemH10 (openCubeSet Q) (v - I v).toFun)
    (hη : ∀ i ∈ s, MemLp (η i) (⊤ : ENNReal) (volume.restrict (openCubeSet Q)))
    (hDη : ∀ i ∈ s, ∀ b, MemLp (fun x => (η i).grad x b)
      (⊤ : ENNReal) (volume.restrict (openCubeSet Q)))
    (hpos : ∀ R ∈ descendantsAtDepth Q j, ∀ b,
      Summable (fun k => (Real.sqrt 3) ^ (k + 1) * energy R
        (cubeIncrement R (k + 1) (fun x => lemmaVRowCombination I η v s c x b)))) :
    |∑ i ∈ s, c i * volumeAverage (openCubeSet Q) (fun x => vecDot
      ((η i) x • matVecMul responsePlanarJ (v.grad x)) (w.grad x))| ≤
      Real.sqrt (lemmaVTiledWeakEnergy Q j w.grad) *
        Real.sqrt (lemmaVTiledPositiveEnergy Q j (lemmaVRowCombination I η v s c)) := by
  let instFiniteQ : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  rw [lemmaV_sum_pairing_eq_row (isOpenBoundedConvexDomain_openCubeSet Q) I η v w s c hres hη hDη]
  have hmem := lemmaVRowCombination_memL2 I η v s c hη hDη
  have hG (b : Fin 2) : MemLp (fun x => lemmaVRowCombination I η v s c x b)
      2 (normalizedCubeMeasure Q) :=
    memL2On_openCubeSet_normalizedCubeMeasure (hmem.eval b)
  have heq : (fun x => vecDot (lemmaVRowCombination I η v s c x) (w.grad x)) =
      fun x => vecDot (w.grad x) (lemmaVRowCombination I η v s c x) :=
    funext fun x => vecDot_comm _ _
  rw [heq]
  change |integralAverage (openCubeSet Q) _| ≤ _
  rw [← cubeAverage_eq_integralAverage_openCubeSet]
  exact lemmaV_tiled_pairing_le Q j w.grad_memL2_normalizedCubeMeasure hG hpos

/-- Combine a signed first variation with the abstract lift and a finite H2
bound. This is a numerical/row-form helper; the actual first variations are
supplied by `lemmaV_load_bounds` in the final theorem. -/
theorem lemmaV_directional_row_bound (Q : TriadicCube 2) (j : ℕ)
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q))
    (η : ℕ → H1Function (openCubeSet Q)) (v w : H1Function (openCubeSet Q))
    (H : ℕ → ResponseCoefficient (openCubeSet Q)) (σ : ℝ) (D : ℕ → ℝ)
    (ε : ℝ) (hε : |ε| = 1) (s : Finset ℕ) (c : ℕ → ℝ) (κ : ℝ)
    (hres : MemH10 (openCubeSet Q) (v - I v).toFun)
    (hη : ∀ l, MemLp (η l) (⊤ : ENNReal) (volume.restrict (openCubeSet Q)))
    (hDη : ∀ l b, MemLp (fun x => (η l).grad x b) (⊤ : ENNReal)
      (volume.restrict (openCubeSet Q)))
    (hlink : ∀ l, (η l).toFun =ᵐ[volume.restrict (openCubeSet Q)]
      fun x => responseCoefficientExtension (H l) x / σ)
    (hDer : ∀ l, D l = 2 * ε * volumeAverage (openCubeSet Q) (fun x => vecDot
      ((responseCoefficientExtension (H l) x / σ) • matVecMul responsePlanarJ (v.grad x)) (w.grad x)))
    (hpos : ∀ R ∈ descendantsAtDepth Q j, ∀ b,
      Summable (fun n => (Real.sqrt 3) ^ (n + 1) * energy R
        (cubeIncrement R (n + 1) (fun x => lemmaVRowCombination I η v s c x b))))
    (hP : Real.sqrt (lemmaVTiledPositiveEnergy Q j (lemmaVRowCombination I η v s c)) ≤
      κ * Real.sqrt (∑ l ∈ s, c l ^ 2) * Real.sqrt (lemmaVTiledWeakEnergy Q j v.grad)) :
    |∑ l ∈ s, c l * D l| ≤ (2 * κ * Real.sqrt (∑ l ∈ s, c l ^ 2)) *
      (Real.sqrt (lemmaVTiledWeakEnergy Q j w.grad) * Real.sqrt (lemmaVTiledWeakEnergy Q j v.grad)) := by
  let instFiniteQ : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hrow := lemmaV_row_estimate Q j I η v w s c hres
    (fun l _ => hη l) (fun l _ => hDη l) hpos
  have hd (l : ℕ) : D l = 2 * ε * volumeAverage (openCubeSet Q) (fun x => vecDot
      ((η l) x • matVecMul responsePlanarJ (v.grad x)) (w.grad x)) := by
    rw [hDer]
    congr 1
    unfold volumeAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [hlink l] with x hx
    rw [hx]
  have hs : (∑ l ∈ s, c l * D l) = (2 * ε) * ∑ l ∈ s, c l *
      volumeAverage (openCubeSet Q) (fun x => vecDot
        ((η l) x • matVecMul responsePlanarJ (v.grad x)) (w.grad x)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [hd]
    ring
  rw [hs, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), hε, mul_one]
  calc
    _ ≤ 2 * (Real.sqrt (lemmaVTiledWeakEnergy Q j w.grad) *
        Real.sqrt (lemmaVTiledPositiveEnergy Q j (lemmaVRowCombination I η v s c))) :=
      mul_le_mul_of_nonneg_left hrow (by norm_num)
    _ ≤ 2 * (Real.sqrt (lemmaVTiledWeakEnergy Q j w.grad) *
        (κ * Real.sqrt (∑ l ∈ s, c l ^ 2) * Real.sqrt (lemmaVTiledWeakEnergy Q j v.grad))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP (Real.sqrt_nonneg _)) (by norm_num)
    _ = _ := by ring

end

end ASDExplicitGamma.Variational
