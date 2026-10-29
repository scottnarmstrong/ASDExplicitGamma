module

public import ASDExplicitGamma.Scalar.PsdTiledHaar
public import ASDExplicitGamma.Gaussian.CovarianceRow
public import ASDExplicitGamma.Native.OldSignedSourceMultiplier

/-! Physical q3 defect source fields at a fixed mesh as elements of
`TiledHaarField`, with the weak-face (1, 1.440, .285) row and column bounds. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Native
  ASDExplicitGamma.Inverse
open scoped BigOperators

noncomputable section

local instance rowFieldFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The source field of mode `l` acting on the potential `r`: the negative DIAG row at
mesh `m`. -/
def rowField (Q : TriadicCube 2) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (l : whiteBasisIndex) (r : H10Function (openCubeSet Q)) : Vec 2 → Vec 2 :=
  fun p => -lemmaVPlanarRowField (diagInterpolant Q m)
    (mainQ3DirectionW2 Q b L (whiteBasis l)).value r.toH1Function p

/-- The weak-face row constant `|b| + r 1.44 √15.6 |b|/L + r² .285 √929.76 |b|/L²`. -/
def rowKappa (Q : TriadicCube 2) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l}) : ℝ :=
  Real.sqrt (b ^ 2) + diagMeshRadius Q m * (36 / 25) * Real.sqrt ((78 / 5) * b ^ 2 / L.1 ^ 2) +
    (diagMeshRadius Q m) ^ 2 * (57 / 200) * Real.sqrt ((23244 / 25) * b ^ 2 / L.1 ^ 4)

/-- The weak-face column constant (31.2, 1859.52). -/
def colKappa (Q : TriadicCube 2) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l}) : ℝ :=
  oldSignedSourceMultiplier Q m b L

theorem rowKappa_le_ColKappa (Q : TriadicCube 2) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l}) :
    rowKappa Q m b L ≤ colKappa Q m b L := by
  unfold rowKappa colKappa oldSignedSourceMultiplier
  have hr := (diagMeshRadius_pos Q m).le
  have h1 : Real.sqrt ((78 / 5) * b ^ 2 / L.1 ^ 2) ≤ Real.sqrt ((156 / 5) * b ^ 2 / L.1 ^ 2) :=
    Real.sqrt_le_sqrt (by
      have : 0 ≤ b ^ 2 / L.1 ^ 2 := by positivity
      have e1 : (78 / 5) * b ^ 2 / L.1 ^ 2 = (78 / 5) * (b ^ 2 / L.1 ^ 2) := by ring
      have e2 : (156 / 5) * b ^ 2 / L.1 ^ 2 = (156 / 5) * (b ^ 2 / L.1 ^ 2) := by ring
      rw [e1, e2]; nlinarith)
  have h2 : Real.sqrt ((23244 / 25) * b ^ 2 / L.1 ^ 4) ≤ Real.sqrt ((46488 / 25) * b ^ 2 / L.1 ^ 4) :=
    Real.sqrt_le_sqrt (by
      have : 0 ≤ b ^ 2 / L.1 ^ 4 := by positivity
      have e1 : (23244 / 25) * b ^ 2 / L.1 ^ 4 = (23244 / 25) * (b ^ 2 / L.1 ^ 4) := by ring
      have e2 : (46488 / 25) * b ^ 2 / L.1 ^ 4 = (46488 / 25) * (b ^ 2 / L.1 ^ 4) := by ring
      rw [e1, e2]; nlinarith)
  have hs : 0 ≤ diagMeshRadius Q m * (36 / 25) := by positivity
  have hs2 : 0 ≤ (diagMeshRadius Q m) ^ 2 * (57 / 200) := by positivity
  have := mul_le_mul_of_nonneg_left h1 hs
  have := mul_le_mul_of_nonneg_left h2 hs2
  simp only [mul_assoc] at *
  linarith

theorem rowField_memLp_tile (Q : TriadicCube 2) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (l : whiteBasisIndex) (r : H10Function (openCubeSet Q)) {R : TriadicCube 2}
    (hR : R ∈ descendantsAtDepth Q m) (i : Fin 2) :
    MemLp (fun x => rowField Q m b L l r x i) 2 (normalizedCubeMeasure R) := by
  let η := mainQ3DirectionW2 Q b L (whiteBasis l)
  have hη : MemLp η.value.toFun ⊤ (volume.restrict (openCubeSet Q)) := η.value_memLp_top
  have hDη : ∀ i, MemLp (fun p => η.value.grad p i) ⊤ (volume.restrict (openCubeSet Q)) :=
    fun i => PlanarW2Infinity.gradient_memLp_top_volume η i
  have hrow := lemmaVPlanarRowField_memL2 (diagInterpolant Q m) η.value r.toH1Function hη hDη
  have hneg : MemVectorL2 (openCubeSet Q) (rowField Q m b L l r) := hrow.neg
  have hc := memScalarL2_coord_of_memVectorL2 hneg i
  exact memLp_normalized_of_memL2On
    (memL2On_mono (openCubeSet_subset_of_mem_descendantsAtDepth hR) hc)

theorem rowField_eq_neg_distinct (Q : TriadicCube 2) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (s : Finset whiteBasisIndex) (z : whiteBasisIndex → H10Function (openCubeSet Q)) :
    (fun p => ∑ l ∈ s, rowField Q m b L l (z l) p) =
      fun p => -q3DistinctRow whiteBasis s b L Q m z p := by
  funext p
  funext i
  simp [rowField, q3DistinctRow, Finset.sum_apply, Finset.sum_neg_distrib]

theorem tiled_positive_neg (Q : TriadicCube 2) (m : ℕ) (F : Vec 2 → Vec 2) :
    lemmaVTiledPositiveEnergy Q m (fun p => -F p) = lemmaVTiledPositiveEnergy Q m F := by
  unfold lemmaVTiledPositiveEnergy
  congr 1
  funext R
  unfold vectorPositiveHaarEnergy
  refine Finset.sum_congr rfl fun i _ => ?_
  exact primalEnergy_neg R (Real.sqrt 3) (fun p => F p i)

theorem rowField_summable (Q : TriadicCube 2) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (l : whiteBasisIndex) (r : H10Function (openCubeSet Q)) {R : TriadicCube 2}
    (hR : R ∈ descendantsAtDepth Q m) (i : Fin 2) :
    Summable (fun k : ℕ => (Real.sqrt 3) ^ (k + 1) *
      energy R (cubeIncrement R (k + 1) (fun x => rowField Q m b L l r x i))) := by
  have h := (q3_distinct_h10_row_bound whiteBasis {l} b L Q m (fun _ => r)).1 R hR i
  have hneg : ∀ k : ℕ, energy R (cubeIncrement R (k + 1) (fun x => rowField Q m b L l r x i)) =
      energy R (cubeIncrement R (k + 1) (fun x => q3DistinctRow whiteBasis {l} b L Q m
        (fun _ => r) x i)) := by
    intro k
    have e1 : (fun x => rowField Q m b L l r x i) =
        fun x => -q3DistinctRow whiteBasis {l} b L Q m (fun _ => r) x i := by
      funext x
      simp [rowField, q3DistinctRow]
    rw [e1, cubeIncrement_neg, energy_neg]
  simpa only [hneg] using h

/-- The source field as an element of the admissible module. -/
def rowElt (Q : TriadicCube 2) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (l : whiteBasisIndex) (r : H10Function (openCubeSet Q)) : TiledHaarField Q m :=
  ⟨rowField Q m b L l r, fun _ hR i =>
    ⟨rowField_memLp_tile Q m b L l r hR i, rowField_summable Q m b L l r hR i⟩⟩

theorem rowElt_coe (Q : TriadicCube 2) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (l : whiteBasisIndex) (r : H10Function (openCubeSet Q)) :
    (rowElt Q m b L l r).1 = rowField Q m b L l r := rfl

/-- Row bound: distinct potentials on distinct modes. -/
theorem rowElt_diag_sum_bound (Q : TriadicCube 2) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})
    {n : Type*} [Fintype n] (e : n → whiteBasisIndex) (he : Function.Injective e)
    (d : n → H10Function (openCubeSet Q)) :
    tiledPositiveEnergy Q m (∑ i, rowElt Q m b L (e i) (d i)) ≤
      rowKappa Q m b L ^ 2 * ∑ i, lemmaVTiledWeakEnergy Q m (d i).toH1Function.grad := by
  classical
  let s : Finset whiteBasisIndex := Finset.univ.image e
  let z : whiteBasisIndex → H10Function (openCubeSet Q) := fun l =>
    if h : ∃ i, e i = l then d h.choose else 0
  have hz : ∀ i, z (e i) = d i := by
    intro i
    have h : ∃ j, e j = e i := ⟨i, rfl⟩
    simp only [z, dif_pos h]
    rw [he h.choose_spec]
  have hcoe : (↑(∑ i, rowElt Q m b L (e i) (d i)) : Vec 2 → Vec 2) =
      fun p => -q3DistinctRow whiteBasis s b L Q m z p := by
    rw [← rowField_eq_neg_distinct]
    funext p
    simp only [Submodule.coe_sum, Finset.sum_apply]
    rw [Finset.sum_image (fun i _ j _ hij => he hij)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hz i]
    rfl
  have hrow := (q3_distinct_h10_row_bound whiteBasis s b L Q m z).2
  have hsum : ∑ l ∈ s, lemmaVTiledWeakEnergy Q m (z l).toH1Function.grad =
      ∑ i, lemmaVTiledWeakEnergy Q m (d i).toH1Function.grad := by
    rw [Finset.sum_image (fun i _ j _ hij => he hij)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hz i]
  have hW : 0 ≤ ∑ i, lemmaVTiledWeakEnergy Q m (d i).toH1Function.grad :=
    Finset.sum_nonneg fun i _ => lemmaVTiledWeakEnergy_nonneg Q m _
  unfold tiledPositiveEnergy
  rw [hcoe, tiled_positive_neg]
  have hnn := lemmaVTiledPositiveEnergy_nonneg Q m (q3DistinctRow whiteBasis s b L Q m z)
  rw [hsum] at hrow
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hrow 2
  rw [Real.sq_sqrt hnn, mul_pow, Real.sq_sqrt hW] at h2
  exact h2

theorem affine_zero (nQ : ℤ) (r : H10Function (openCubeSet (originCube 2 nQ))) :
    lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet (originCube 2 nQ)) 0 r =
      r.toH1Function := by
  ext p
  · simp only [lemmaVAffinePotential, H1Function.add_toFun,
      H1Function.affineOnIsSobolevRegularDomain_apply]
    simp
  · simp only [lemmaVAffinePotential, H1Function.add_grad,
      H1Function.affineOnIsSobolevRegularDomain_grad]
    simp

theorem rowElt_energy_eq_pureFlux (nQ : ℤ) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (l : whiteBasisIndex) (r : H10Function (openCubeSet (originCube 2 nQ))) :
    tiledPositiveEnergy (originCube 2 nQ) m (rowElt (originCube 2 nQ) m b L l r) =
      pureFluxMainQ3RowEnergy nQ b 1 L m 0 r l := by
  unfold tiledPositiveEnergy pureFluxMainQ3RowEnergy lemmaVTiledPositiveEnergy
  dsimp only
  rw [affine_zero]
  congr 1
  funext U
  unfold pureFluxMainQ3BasisFrameMultiplier
  simp only [inv_one, one_smul]
  unfold vectorPositiveHaarEnergy
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rowElt_coe]
  exact primalEnergy_neg U (Real.sqrt 3) (fun p =>
    lemmaVPlanarRowField (diagInterpolant (originCube 2 nQ) m)
      (mainQ3DirectionW2 (originCube 2 nQ) b L (whiteBasis l)).value r.toH1Function p i)

/-- Column bound (weak-face triple 1, 1.440, .285 at the doubled moments). -/
theorem rowElt_column_bound (nQ : ℤ) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (s : Finset whiteBasisIndex) (r : H10Function (openCubeSet (originCube 2 nQ))) :
    ∑ l ∈ s, tiledPositiveEnergy (originCube 2 nQ) m (rowElt (originCube 2 nQ) m b L l r) ≤
      colKappa (originCube 2 nQ) m b L ^ 2 *
        lemmaVTiledWeakEnergy (originCube 2 nQ) m r.toH1Function.grad := by
  have h := old_signed_q3_row_energy_bound nQ b L m 0 r
  dsimp only at h
  rw [affine_zero] at h
  obtain ⟨hs, hb⟩ := h
  calc ∑ l ∈ s, tiledPositiveEnergy (originCube 2 nQ) m (rowElt (originCube 2 nQ) m b L l r)
      = ∑ l ∈ s, pureFluxMainQ3RowEnergy nQ b 1 L m 0 r l :=
        Finset.sum_congr rfl fun l _ => rowElt_energy_eq_pureFlux nQ m b L l r
    _ ≤ ∑' l, pureFluxMainQ3RowEnergy nQ b 1 L m 0 r l :=
        hs.sum_le_tsum _ (fun l _ => by
          unfold pureFluxMainQ3RowEnergy
          exact descendantsAverage_nonneg _ m _ (fun U _ => vectorPositiveHaarEnergy_nonneg U _))
    _ ≤ _ := by
        simpa [colKappa] using hb

end

end ASDExplicitGamma.Scalar
