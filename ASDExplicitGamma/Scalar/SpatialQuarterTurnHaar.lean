module

public import ASDExplicitGamma.Triadic.VectorHaar
public import ASDExplicitGamma.Triadic.DiagMesh
public import ASDExplicitGamma.Cold.ProjectedGraphEnergy
public import Homogenization.Sobolev.H1.OriginCubeSymmetry

/-! Spatial quarter-turn covariance for the actual origin-cube Haar projection. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal

noncomputable section

/-- The quarter-turn as an actual volume-preserving linear equivalence. -/
noncomputable def spatialQuarterTurnEquiv : Vec 2 ≃L[ℝ] Vec 2 :=
  (swapVecContinuousLinearEquiv 0 1).trans (signFlipVecContinuousLinearEquiv 0)

def spatialQuarterTurn (x : Vec 2) : Vec 2 := ![-x 1, x 0]

@[simp] theorem spatialQuarterTurnEquiv_apply (x : Vec 2) :
    spatialQuarterTurnEquiv x = spatialQuarterTurn x := by
  ext i
  fin_cases i <;> simp [spatialQuarterTurnEquiv, spatialQuarterTurn,
    swapVecContinuousLinearEquiv_apply, signFlipVecContinuousLinearEquiv_apply,
    matVecMul_swap_eq_comp, matVecMul_signFlipMatrix_apply]

theorem spatialQuarterTurn_measurePreserving :
    MeasurePreserving spatialQuarterTurn MeasureTheory.volume MeasureTheory.volume := by
  have h :=
    (measurePreserving_signFlipVecContinuousLinearEquiv (d := 2) 0).comp
      (measurePreserving_swapVecContinuousLinearEquiv (d := 2) 0 1)
  have hfun :
      (fun x => signFlipVecContinuousLinearEquiv 0
        (swapVecContinuousLinearEquiv 0 1 x)) = spatialQuarterTurn := by
    funext x
    exact spatialQuarterTurnEquiv_apply x
  rw [← hfun]
  exact h

/-- The triadic cell obtained by rotating its index about the origin. -/
def quarterTurnCube (R : TriadicCube 2) : TriadicCube 2 :=
  { scale := R.scale
    index := fun i => if i = 0 then -R.index 1 else R.index 0 }

private theorem quarterTurnCube_corner_zero (R : TriadicCube 2) :
    cubeCorner (quarterTurnCube R) 0 =
      -(cubeCorner R 1 + cubeScaleFactor R) := by
  simp [quarterTurnCube, cubeCorner, cubeScaleFactor]
  ring

private theorem quarterTurnCube_corner_one (R : TriadicCube 2) :
    cubeCorner (quarterTurnCube R) 1 = cubeCorner R 0 := by
  simp [quarterTurnCube, cubeCorner, cubeScaleFactor]

private theorem quarterTurnCube_scaleFactor (R : TriadicCube 2) :
    cubeScaleFactor (quarterTurnCube R) = cubeScaleFactor R := rfl

private theorem interval_reflection (a s x : ℝ) :
    (-(a + s) < -x ∧ -x < -(a + s) + s) ↔ x < a + s ∧ a < x := by
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    constructor <;> linarith

/-- Open cells are carried exactly to the corresponding rotated open cells. -/
theorem spatialQuarterTurn_openCubeSet (R : TriadicCube 2) :
    spatialQuarterTurn ⁻¹' openCubeSet (quarterTurnCube R) = openCubeSet R := by
  ext x
  rw [openCubeSet_eq_box, openCubeSet_eq_box]
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
  change (∀ i, (cubeCorner (quarterTurnCube R) i <
      spatialQuarterTurn x i ∧
      spatialQuarterTurn x i < cubeCorner (quarterTurnCube R) i +
        cubeScaleFactor (quarterTurnCube R))) ↔
    ∀ i, (cubeCorner R i < x i ∧ x i < cubeCorner R i + cubeScaleFactor R)
  rw [Fin.forall_fin_two, Fin.forall_fin_two]
  constructor
  · rintro ⟨h₀, h₁⟩
    constructor
    · simpa only [spatialQuarterTurn, Matrix.cons_val_zero, Matrix.cons_val_one,
        quarterTurnCube_corner_one, quarterTurnCube_scaleFactor] using h₁
    · have h₀' : -(cubeCorner R 1 + cubeScaleFactor R) < -x 1 ∧
          -x 1 < -(cubeCorner R 1 + cubeScaleFactor R) + cubeScaleFactor R := by
        simpa only [spatialQuarterTurn, Matrix.cons_val_zero, Matrix.cons_val_one,
          quarterTurnCube_corner_zero,
          quarterTurnCube_scaleFactor] using h₀
      rcases (interval_reflection _ _ _).mp h₀' with ⟨hupper, hlower⟩
      exact ⟨hlower, hupper⟩
  · rintro ⟨h₀, h₁⟩
    constructor
    · have h₁' := (interval_reflection _ _ _).mpr ⟨h₁.2, h₁.1⟩
      simpa only [spatialQuarterTurn, Matrix.cons_val_zero, Matrix.cons_val_one,
        quarterTurnCube_corner_zero,
        quarterTurnCube_scaleFactor] using h₁'
    · simpa only [spatialQuarterTurn, Matrix.cons_val_zero, Matrix.cons_val_one,
        quarterTurnCube_corner_one,
        quarterTurnCube_scaleFactor] using h₀

/-- Cube averages transform under the actual spatial quarter-turn. -/
theorem cubeAverage_spatialQuarterTurn (R : TriadicCube 2) (f : Vec 2 → ℝ) :
    cubeAverage R (fun x => f (spatialQuarterTurn x)) =
      cubeAverage (quarterTurnCube R) f := by
  let T := spatialQuarterTurn
  let S := quarterTurnCube R
  have hfun : (spatialQuarterTurnEquiv.toHomeomorph : Vec 2 → Vec 2) =
      spatialQuarterTurn := by
    funext x
    exact spatialQuarterTurnEquiv_apply x
  have hEmb : MeasurableEmbedding T := by
    simpa only [T, hfun] using
      spatialQuarterTurnEquiv.toHomeomorph.measurableEmbedding
  have hμ := spatialQuarterTurn_measurePreserving.restrict_preimage_emb
    hEmb (openCubeSet S)
  have hμ' : MeasurePreserving T (MeasureTheory.volume.restrict (openCubeSet R))
      (MeasureTheory.volume.restrict (openCubeSet S)) := by
    simpa only [spatialQuarterTurn_openCubeSet, T, S] using hμ
  have hint : ∫ x in openCubeSet R, f (T x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet S, f x ∂MeasureTheory.volume := by
    simpa only [T] using hμ'.integral_comp hEmb f
  have hvol : cubeVolume R = cubeVolume S := by
    simp [S, quarterTurnCube, cubeVolume, cubeScaleFactor]
  unfold cubeAverage
  rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet,
    setIntegral_cubeSet_eq_setIntegral_openCubeSet]
  rw [hvol, hint]

/-- The finite cell grid is stable under a quarter-turn when rooted at the
centered source cube. -/
theorem spatialQuarterTurn_descendant (m : ℤ) (j : ℕ)
    {R : TriadicCube 2}
    (hR : R ∈ descendantsAtDepth (originCube 2 m) j) :
    quarterTurnCube R ∈ descendantsAtDepth (originCube 2 m) j := by
  classical
  let Q := originCube 2 m
  let k : Fin 2 → Fin (3 ^ j) := (diagMeshCellEquiv Q j).symm ⟨R, hR⟩
  let n : ℕ := 3 ^ j
  let k' : Fin 2 → Fin n := fun i =>
    if hi : i = 0 then ⟨n - 1 - (k 1).val, by
      have hn : 0 < n := by dsimp [n]; exact Nat.pow_pos (by omega)
      have hk : (k 1).val < n := (k 1).isLt
      omega⟩ else k 0
  have hkR : diagMeshCell Q j k = R := by
    have h := (diagMeshCellEquiv Q j).apply_symm_apply ⟨R, hR⟩
    exact congrArg Subtype.val h
  have hscale : (quarterTurnCube (diagMeshCell Q j k)).scale =
      (diagMeshCell Q j k').scale := by
    change (diagMeshCell Q j k).scale = (diagMeshCell Q j k').scale
    rw [scale_eq_sub_of_mem_descendantsAtDepth (diagMeshCell_mem Q j k),
      scale_eq_sub_of_mem_descendantsAtDepth (diagMeshCell_mem Q j k')]
  have hside : (3 : ℝ) ^ j * diagMeshRadius Q j = cubeScaleFactor Q := by
    unfold diagMeshRadius
    field_simp
  have hcorner : ∀ i,
      cubeCorner (quarterTurnCube (diagMeshCell Q j k)) i =
        cubeCorner (diagMeshCell Q j k') i := by
    intro i
    fin_cases i
    · change cubeCorner (quarterTurnCube (diagMeshCell Q j k)) 0 =
        cubeCorner (diagMeshCell Q j k') 0
      have hk1 : ((k 1).val : ℝ) +
          ((3 ^ j - 1 - (k 1).val : ℕ) : ℝ) + 1 = (3 : ℝ) ^ j := by
        have hkn : (k 1).val < 3 ^ j := (k 1).isLt
        have hn : 0 < 3 ^ j := Nat.pow_pos (by omega)
        have hn' : (k 1).val + (3 ^ j - 1 - (k 1).val) + 1 = 3 ^ j := by omega
        exact_mod_cast hn'
      have hroot : cubeCorner Q 0 = -(1 / 2 : ℝ) * cubeScaleFactor Q := by
        simp [cubeCorner, Q, originCube]
      rw [quarterTurnCube_corner_zero]
      rw [diagMeshCell_corner, diagMeshCell_corner]
      simp [k', n]
      have hroot1 : cubeCorner Q 1 = -(1 / 2 : ℝ) * cubeScaleFactor Q := by
        simp [cubeCorner, Q, originCube]
      rw [hroot, hroot1]
      rw [← hside]
      nlinarith [diagMeshRadius_pos Q j]
    · have hroot : cubeCorner Q 0 = -(1 / 2 : ℝ) * cubeScaleFactor Q := by
        simp [cubeCorner, Q, originCube]
      change cubeCorner (quarterTurnCube (diagMeshCell Q j k)) 1 =
        cubeCorner (diagMeshCell Q j k') 1
      rw [quarterTurnCube_corner_one]
      rw [diagMeshCell_corner, diagMeshCell_corner]
      simp [k', n]
      have hroot1 : cubeCorner Q 1 = -(1 / 2 : ℝ) * cubeScaleFactor Q := by
        simp [cubeCorner, Q, originCube]
      rw [hroot, hroot1]
  have hcube : quarterTurnCube (diagMeshCell Q j k) = diagMeshCell Q j k' :=
    diagCube_eq_of_scale_corner hscale hcorner
  rw [← hkR, hcube]
  exact diagMeshCell_mem Q j k'

private theorem triadicCube_ext' {A B : TriadicCube 2}
    (hs : A.scale = B.scale) (hi : A.index = B.index) : A = B := by
  cases A
  cases B
  simp_all

private theorem quarterTurnCube_fourth (R : TriadicCube 2) :
    quarterTurnCube (quarterTurnCube (quarterTurnCube
      (quarterTurnCube R))) = R := by
  apply triadicCube_ext'
  · rfl
  · funext i
    fin_cases i <;> simp [quarterTurnCube]

private theorem quarterTurn_originCube (m : ℤ) :
    quarterTurnCube (originCube 2 m) = originCube 2 m := by
  apply triadicCube_ext'
  · rfl
  · funext i
    fin_cases i <;> simp [quarterTurnCube, originCube]

private noncomputable def quarterTurnSquareCellEquiv (m : ℤ) (j : ℕ) :
    Cold.SquareCells (originCube 2 m) j ≃ Cold.SquareCells (originCube 2 m) j where
  toFun R := ⟨quarterTurnCube R.val,
    spatialQuarterTurn_descendant m j R.property⟩
  invFun R := ⟨quarterTurnCube (quarterTurnCube (quarterTurnCube R.val)), by
    exact spatialQuarterTurn_descendant m j
      (spatialQuarterTurn_descendant m j
        (spatialQuarterTurn_descendant m j R.property))⟩
  left_inv R := by
    apply Subtype.ext
    exact quarterTurnCube_fourth R.val
  right_inv R := by
    apply Subtype.ext
    exact quarterTurnCube_fourth R.val

private theorem squareCellMean_spatialQuarterTurn (m : ℤ) (j : ℕ)
    (f : Vec 2 → ℝ) :
    Cold.squareCellMean (originCube 2 m) j
        (fun R => (cubeAverage (quarterTurnCube R.val) f) ^ 2) =
      Cold.squareCellMean (originCube 2 m) j
        (fun R => (cubeAverage R.val f) ^ 2) := by
  unfold Cold.squareCellMean
  congr 1
  exact Equiv.sum_comp (quarterTurnSquareCellEquiv m j)
    (fun R => (cubeAverage R.val f) ^ 2)

private theorem originCube_normalizedMeasure_spatialQuarterTurn (m : ℤ) :
    MeasurePreserving spatialQuarterTurn
      (normalizedCubeMeasure (originCube 2 m))
      (normalizedCubeMeasure (originCube 2 m)) := by
  let Q := originCube 2 m
  have hfun : (spatialQuarterTurnEquiv.toHomeomorph : Vec 2 → Vec 2) =
      spatialQuarterTurn := by
    funext x
    exact spatialQuarterTurnEquiv_apply x
  have hEmb : MeasurableEmbedding spatialQuarterTurn := by
    simpa only [hfun] using spatialQuarterTurnEquiv.toHomeomorph.measurableEmbedding
  have hpre : spatialQuarterTurn ⁻¹' openCubeSet (originCube 2 m) =
      openCubeSet (originCube 2 m) := by
    calc
      spatialQuarterTurn ⁻¹' openCubeSet (originCube 2 m) =
          spatialQuarterTurn ⁻¹' openCubeSet
            (quarterTurnCube (originCube 2 m)) := by
        rw [quarterTurn_originCube m]
      _ = openCubeSet (originCube 2 m) :=
        spatialQuarterTurn_openCubeSet (originCube 2 m)
  have hμ := spatialQuarterTurn_measurePreserving.restrict_preimage_emb
    hEmb (openCubeSet Q)
  have hμ' : MeasurePreserving spatialQuarterTurn
      (MeasureTheory.volume.restrict (openCubeSet Q))
      (MeasureTheory.volume.restrict (openCubeSet Q)) := by
    simpa only [Q, hpre] using hμ
  have hnorm : normalizedCubeMeasure Q =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) • MeasureTheory.volume.restrict (openCubeSet Q) := by
    rw [normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  rw [hnorm]
  refine ⟨hμ'.measurable, ?_⟩
  rw [Measure.map_smul _ hμ'.aemeasurable, hμ'.map_eq]

theorem cubeProjection_energy_spatialQuarterTurn (m : ℤ) (j : ℕ)
    (f : Vec 2 → ℝ) (hf : MemLp f 2 (normalizedCubeMeasure (originCube 2 m))) :
    energy (originCube 2 m)
      (cubeProjection (originCube 2 m) j (fun x => f (spatialQuarterTurn x))) =
    energy (originCube 2 m) (cubeProjection (originCube 2 m) j f) := by
  let Q := originCube 2 m
  have hft : MemLp (fun x => f (spatialQuarterTurn x)) 2 (normalizedCubeMeasure Q) :=
    hf.comp_measurePreserving (originCube_normalizedMeasure_spatialQuarterTurn m)
  have havg (R : Cold.SquareCells Q j) :
      cubeAverage R.val (fun x => f (spatialQuarterTurn x)) =
        cubeAverage (quarterTurnCube R.val) f :=
    cubeAverage_spatialQuarterTurn R.val f
  calc
    energy Q (cubeProjection Q j (fun x => f (spatialQuarterTurn x))) =
        Cold.squareCellMean Q j
          (fun R => (cubeAverage (quarterTurnCube R.val) f) ^ 2) := by
      rw [Cold.energy_projection_eq_squareCellMean Q j hft]
      congr 1
      funext R
      exact congrArg (fun z : ℝ => z ^ 2) (havg R)
    _ = Cold.squareCellMean Q j (fun R => (cubeAverage R.val f) ^ 2) := by
      rw [squareCellMean_spatialQuarterTurn]
    _ = energy Q (cubeProjection Q j f) :=
      (Cold.energy_projection_eq_squareCellMean Q j hf).symm

private theorem energy_cubeIncrement_spatialQuarterTurn (m : ℤ) (j : ℕ)
    (f : Vec 2 → ℝ) (hf : MemLp f 2 (normalizedCubeMeasure (originCube 2 m))) :
    energy (originCube 2 m)
      (cubeIncrement (originCube 2 m) j (fun x => f (spatialQuarterTurn x))) =
    energy (originCube 2 m) (cubeIncrement (originCube 2 m) j f) := by
  let Q := originCube 2 m
  have hft : MemLp (fun x => f (spatialQuarterTurn x)) 2 (normalizedCubeMeasure Q) :=
    hf.comp_measurePreserving (originCube_normalizedMeasure_spatialQuarterTurn m)
  cases j with
  | zero =>
      simpa only [cubeIncrement_zero] using cubeProjection_energy_spatialQuarterTurn m 0 f hf
  | succ k =>
      rw [energy_increment_succ Q k hft, energy_increment_succ Q k hf,
        cubeProjection_energy_spatialQuarterTurn m (k + 1) f hf,
        cubeProjection_energy_spatialQuarterTurn m k f hf]

theorem primalEnergy_spatialQuarterTurn (m : ℤ) (q : ℝ) (f : Vec 2 → ℝ)
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube 2 m))) :
    primalEnergy (originCube 2 m) q (fun x => f (spatialQuarterTurn x)) =
      primalEnergy (originCube 2 m) q f := by
  unfold primalEnergy
  rw [energy_cubeIncrement_spatialQuarterTurn m 0 f hf]
  congr 1
  apply tsum_congr
  intro k
  rw [energy_cubeIncrement_spatialQuarterTurn m (k + 1) f hf]

theorem vectorWeakHaarEnergy_spatialQuarterTurn (m : ℤ)
    (F : Vec 2 → Fin 2 → ℝ)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure (originCube 2 m))) :
    vectorWeakHaarEnergy (originCube 2 m)
      (fun x i => F (spatialQuarterTurn x) i) =
    vectorWeakHaarEnergy (originCube 2 m) F := by
  unfold vectorWeakHaarEnergy
  apply Finset.sum_congr rfl
  intro i hi
  unfold dualEnergy
  exact primalEnergy_spatialQuarterTurn m (Real.sqrt 3)⁻¹
    (fun x => F x i) (hF i)

end
end ASDExplicitGamma.Scalar
