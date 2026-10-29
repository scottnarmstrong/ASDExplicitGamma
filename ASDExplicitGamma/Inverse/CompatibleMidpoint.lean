module

public import ASDExplicitGamma.Inverse.WhitneyRootTiles
public import ASDExplicitGamma.Triadic.DiagGeometry
public import ASDExplicitGamma.Variational.LemmaVLiftSource

/-! A finite, loading-independent midpoint field on the actual DIAG mesh. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open ASDExplicitGamma.Response
open scoped BigOperators

noncomputable section

local instance compatibleRootFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

abbrev InteriorNode (j : ℕ) := Fin 2 → Fin (3 ^ j - 1)

/-- The same interior node, recorded on any finer triadic mesh of its cube. -/
def refineInteriorNode {j J : ℕ} (hdepth : j ≤ J)
    (z : InteriorNode j) : InteriorNode J :=
  fun i => ⟨((z i).val + 1) * 3 ^ (J - j) - 1, by
    have hz : (z i).val + 1 < 3 ^ j := by have := (z i).isLt; omega
    have hmul : ((z i).val + 1) * 3 ^ (J - j) < 3 ^ j * 3 ^ (J - j) :=
      (Nat.mul_lt_mul_right (by positivity : 0 < 3 ^ (J - j))).2 hz
    have hpow : 3 ^ j * 3 ^ (J - j) = 3 ^ J := by
      rw [← Nat.pow_add]
      congr 1
      omega
    let n := ((z i).val + 1) * 3 ^ (J - j)
    have hn : n < 3 ^ J := by dsimp [n]; exact hmul.trans_eq hpow
    have hnpos : 0 < n := by dsimp [n]; positivity
    change n - 1 < 3 ^ J - 1
    omega⟩

theorem refine_interior_node_succ {j J : ℕ} (hdepth : j ≤ J)
    (z : InteriorNode j) (i : Fin 2) :
    ((refineInteriorNode hdepth z) i).val + 1 =
      ((z i).val + 1) * 3 ^ (J - j) := by
  let n := ((z i).val + 1) * 3 ^ (J - j)
  have hpos : 0 < n := by dsimp [n]; positivity
  change n - 1 + 1 = n
  omega

theorem refine_interior_vertex (Q : TriadicCube 2) {j J : ℕ}
    (hdepth : j ≤ J) (z : InteriorNode j) :
    diagInteriorVertex Q J (refineInteriorNode hdepth z) =
      diagInteriorVertex Q j z := by
  funext i
  unfold diagInteriorVertex diagMeshRadius
  have hnode := refine_interior_node_succ hdepth z i
  have hnodeR : ((refineInteriorNode hdepth z i).val : ℝ) + 1 =
      (((z i).val + 1) * 3 ^ (J - j) : ℕ) := by exact_mod_cast hnode
  rw [hnodeR]
  have hscale : (3 : ℝ) ^ J = (3 : ℝ) ^ j * (3 : ℝ) ^ (J - j) := by
    rw [← pow_add]
    congr 1
    omega
  push_cast
  rw [hscale]
  field_simp

/-- Finite node sets from different layers are represented on one common
finer mesh by refining each local node without changing its physical point. -/
def refineComponent {ι : Type*} (J : ℕ) (depth : ι → ℕ)
    (hdepth : ∀ a, depth a ≤ J)
    (components : ∀ a, Finset (InteriorNode (depth a))) (a : ι) :
    Finset (InteriorNode J) :=
  (components a).image (fun z => refineInteriorNode (hdepth a) z)

def componentCoordinateSet (Q : TriadicCube 2) (j : ℕ)
    (C : Finset (InteriorNode j)) (i : Fin 2) : Finset ℝ :=
  C.image fun z => diagInteriorVertex Q j z i

theorem component_coordinateSet_nonempty (Q : TriadicCube 2) (j : ℕ)
    (C : Finset (InteriorNode j)) (hC : C.Nonempty) (i : Fin 2) :
    (componentCoordinateSet Q j C i).Nonempty := by
  rcases hC with ⟨z, hz⟩
  exact ⟨diagInteriorVertex Q j z i, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩

noncomputable def componentCoordinateMin (Q : TriadicCube 2) (j : ℕ)
    (C : Finset (InteriorNode j)) (hC : C.Nonempty) (i : Fin 2) : ℝ :=
  (componentCoordinateSet Q j C i).min'
    (component_coordinateSet_nonempty Q j C hC i)

noncomputable def componentCoordinateMax (Q : TriadicCube 2) (j : ℕ)
    (C : Finset (InteriorNode j)) (hC : C.Nonempty) (i : Fin 2) : ℝ :=
  (componentCoordinateSet Q j C i).max'
    (component_coordinateSet_nonempty Q j C hC i)

/-- The source's bounding-box midpoint for a nonempty finite component. -/
def componentMidpoint (Q : TriadicCube 2) (j : ℕ)
    (C : Finset (InteriorNode j)) (hC : C.Nonempty) : Vec 2 :=
  fun i => (componentCoordinateMin Q j C hC i +
    componentCoordinateMax Q j C hC i) / 2

theorem refine_component_nonempty {ι : Type*} (J : ℕ) (depth : ι → ℕ)
    (hdepth : ∀ a, depth a ≤ J)
    (components : ∀ a, Finset (InteriorNode (depth a)))
    (hne : ∀ a, (components a).Nonempty) (a : ι) :
    (refineComponent J depth hdepth components a).Nonempty := by
  rcases hne a with ⟨z, hz⟩
  exact ⟨refineInteriorNode (hdepth a) z,
    Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩

theorem refined_component_coordinateSet_eq {ι : Type*}
    (Q : TriadicCube 2) (J : ℕ) (depth : ι → ℕ) (hdepth : ∀ a, depth a ≤ J)
    (components : ∀ a, Finset (InteriorNode (depth a))) (a : ι) (i : Fin 2) :
    componentCoordinateSet Q J (refineComponent J depth hdepth components a) i =
      componentCoordinateSet Q (depth a) (components a) i := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨zJ, hzJ, hzx⟩
    rcases Finset.mem_image.mp hzJ with ⟨z, hz, hzz⟩
    subst zJ
    refine Finset.mem_image.mpr ⟨z, hz, ?_⟩
    rw [← refine_interior_vertex Q (hdepth a) z]
    exact hzx
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨z, hz, hzx⟩
    refine Finset.mem_image.mpr ⟨refineInteriorNode (hdepth a) z,
      Finset.mem_image.mpr ⟨z, hz, rfl⟩, ?_⟩
    rw [refine_interior_vertex Q (hdepth a) z]
    exact hzx

private theorem finset_min'_eq_of_eq {α : Type*} [LinearOrder α]
    {s t : Finset α} (hst : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by
  subst t
  rfl

private theorem finset_max'_eq_of_eq {α : Type*} [LinearOrder α]
    {s t : Finset α} (hst : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.max' hs = t.max' ht := by
  subst t
  rfl

theorem refined_component_midpoint_eq {ι : Type*}
    (Q : TriadicCube 2) (J : ℕ) (depth : ι → ℕ) (hdepth : ∀ a, depth a ≤ J)
    (components : ∀ a, Finset (InteriorNode (depth a)))
    (hne : ∀ a, (components a).Nonempty) (a : ι) (i : Fin 2) :
    componentMidpoint Q J (refineComponent J depth hdepth components a)
        (refine_component_nonempty J depth hdepth components hne a) i =
      componentMidpoint Q (depth a) (components a) (hne a) i := by
  have hset := refined_component_coordinateSet_eq Q J depth hdepth components a i
  have hmin : componentCoordinateMin Q J
      (refineComponent J depth hdepth components a)
      (refine_component_nonempty J depth hdepth components hne a) i =
      componentCoordinateMin Q (depth a) (components a) (hne a) i := by
    unfold componentCoordinateMin
    exact finset_min'_eq_of_eq hset _ _
  have hmax : componentCoordinateMax Q J
      (refineComponent J depth hdepth components a)
      (refine_component_nonempty J depth hdepth components hne a) i =
      componentCoordinateMax Q (depth a) (components a) (hne a) i := by
    unfold componentCoordinateMax
    exact finset_max'_eq_of_eq hset _ _
  unfold componentMidpoint
  rw [hmin, hmax]

theorem component_midpoint_coordinate_bounds (Q : TriadicCube 2) (j : ℕ)
    (C : Finset (InteriorNode j)) (hC : C.Nonempty) (i : Fin 2) :
    componentCoordinateMin Q j C hC i ≤ componentMidpoint Q j C hC i ∧
    componentMidpoint Q j C hC i ≤ componentCoordinateMax Q j C hC i := by
  have hmin : componentCoordinateMin Q j C hC i ≤
      diagInteriorVertex Q j (Classical.choose hC) i := by
    exact Finset.min'_le _ _ (Finset.mem_image.mpr
      ⟨Classical.choose hC, Classical.choose_spec hC, rfl⟩)
  have hmax : diagInteriorVertex Q j (Classical.choose hC) i ≤
      componentCoordinateMax Q j C hC i := by
    change diagInteriorVertex Q j (Classical.choose hC) i ≤
      (componentCoordinateSet Q j C i).max'
        (component_coordinateSet_nonempty Q j C hC i)
    exact (componentCoordinateSet Q j C i).le_max' _ (Finset.mem_image.mpr
      ⟨Classical.choose hC, Classical.choose_spec hC, rfl⟩)
  constructor <;> dsimp [componentMidpoint] <;> nlinarith

theorem component_coordinate_mem_bounds (Q : TriadicCube 2) (j : ℕ)
    (C : Finset (InteriorNode j)) (hC : C.Nonempty) (z : InteriorNode j)
    (hz : z ∈ C) (i : Fin 2) :
    componentCoordinateMin Q j C hC i ≤ diagInteriorVertex Q j z i ∧
    diagInteriorVertex Q j z i ≤ componentCoordinateMax Q j C hC i := by
  have hset : diagInteriorVertex Q j z i ∈ componentCoordinateSet Q j C i :=
    Finset.mem_image.mpr ⟨z, hz, rfl⟩
  constructor
  · change (componentCoordinateSet Q j C i).min' _ ≤ _
    exact (componentCoordinateSet Q j C i).min'_le _ hset
  · change _ ≤ (componentCoordinateSet Q j C i).max' _
    exact (componentCoordinateSet Q j C i).le_max' _ hset

theorem component_midpoint_displacement_bound (Q : TriadicCube 2) (j : ℕ)
    (C : Finset (InteriorNode j)) (hC : C.Nonempty) (z : InteriorNode j)
    (hz : z ∈ C) (i : Fin 2) :
    |componentMidpoint Q j C hC i - diagInteriorVertex Q j z i| ≤
      (componentCoordinateMax Q j C hC i -
        componentCoordinateMin Q j C hC i) / 2 := by
  rcases component_coordinate_mem_bounds Q j C hC z hz i with ⟨hlo, hhi⟩
  rcases component_midpoint_coordinate_bounds Q j C hC i with ⟨hmlo, hmhi⟩
  rw [abs_le]
  constructor <;> dsimp [componentMidpoint] <;> nlinarith

private theorem component_choice_eq {ι : Type*} [Fintype ι] (j : ℕ)
    (components : ι → Finset (InteriorNode j))
    (hdisj : ∀ a b, a ≠ b → Disjoint (components a) (components b))
    {z : InteriorNode j} (h : ∃ a, z ∈ components a) (a : ι)
    (ha : z ∈ components a) : Classical.choose h = a := by
  by_contra hab
  have hchosen : z ∈ components (Classical.choose h) := Classical.choose_spec h
  exact Finset.disjoint_left.mp (hdisj _ _ hab) hchosen ha

/-- The nodal correction is assigned once from component geometry.  Its
definition has no loading argument; every load uses this same map. -/
def midpointNodalCorrection {ι : Type*} [Fintype ι] (Q : TriadicCube 2)
    (j : ℕ) (components : ι → Finset (InteriorNode j))
    (hne : ∀ a, (components a).Nonempty)
    (i : Fin 2) (z : InteriorNode j) : ℝ := by
  classical
  exact if h : ∃ a, z ∈ components a then
    componentMidpoint Q j (components (Classical.choose h)) (hne (Classical.choose h)) i -
      diagInteriorVertex Q j z i
  else 0

theorem midpoint_nodal_correction_on_component {ι : Type*} [Fintype ι]
    (Q : TriadicCube 2) (j : ℕ) (components : ι → Finset (InteriorNode j))
    (hne : ∀ a, (components a).Nonempty)
    (hdisj : ∀ a b, a ≠ b → Disjoint (components a) (components b))
    (a : ι) {z : InteriorNode j} (hz : z ∈ components a) (i : Fin 2) :
    midpointNodalCorrection Q j components hne i z =
      componentMidpoint Q j (components a) (hne a) i - diagInteriorVertex Q j z i := by
  classical
  unfold midpointNodalCorrection
  split_ifs with hcomp
  · have hindex := component_choice_eq j components hdisj hcomp a hz
    simp [hindex]
  · exact False.elim (hcomp ⟨a, hz⟩)

theorem midpoint_nodal_correction_off_components {ι : Type*} [Fintype ι]
    (Q : TriadicCube 2) (j : ℕ) (components : ι → Finset (InteriorNode j))
    (hne : ∀ a, (components a).Nonempty)
    (i : Fin 2) {z : InteriorNode j} (hz : ∀ a, z ∉ components a) :
    midpointNodalCorrection Q j components hne i z = 0 := by
  classical
  unfold midpointNodalCorrection
  have hnone : ¬ ∃ a, z ∈ components a := by
    rintro ⟨a, ha⟩
    exact hz a ha
  simp [hnone]

/-- The finite mesh correction synthesized from the one component-midpoint
assignment. -/
def midpointCorrectionH1 {ι : Type*} [Fintype ι] (Q : TriadicCube 2)
    (j : ℕ) (components : ι → Finset (InteriorNode j))
    (hne : ∀ a, (components a).Nonempty)
    (i : Fin 2) : H1Function (openCubeSet Q) :=
  diagSynthesisH1Linear Q j (midpointNodalCorrection Q j components hne i)

theorem midpoint_correction_memH10 {ι : Type*} [Fintype ι]
    (Q : TriadicCube 2) (j : ℕ) (components : ι → Finset (InteriorNode j))
    (hne : ∀ a, (components a).Nonempty) (i : Fin 2) :
    MemH10 (openCubeSet Q)
      (midpointCorrectionH1 Q j components hne i).toFun := by
  exact diagSynthesis_memH10 Q j (midpointNodalCorrection Q j components hne i)

/-- The single linear map from an endpoint slope to its compatible midpoint
field.  The component corrections depend only on the geometry, so the same
map serves every loading. -/
def compatibleMidpointLoadLinear {ι : Type*} [Fintype ι]
    (Q : TriadicCube 2) (j : ℕ) (components : ι → Finset (InteriorNode j))
    (hne : ∀ a, (components a).Nonempty) :
    Vec 2 →ₗ[ℝ] H1Function (openCubeSet Q) where
  toFun p := diagAffineLinear Q p +
    ∑ i : Fin 2, p i • midpointCorrectionH1 Q j components hne i
  map_add' p q := by
    simp only [Pi.add_apply, add_smul, LinearMap.map_add, Finset.sum_add_distrib]
    abel
  map_smul' a p := by
    change diagAffineLinear Q (a • p) +
        ∑ i : Fin 2, (a • p) i • midpointCorrectionH1 Q j components hne i =
      a • (diagAffineLinear Q p +
        ∑ i : Fin 2, p i • midpointCorrectionH1 Q j components hne i)
    rw [LinearMap.map_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [smul_add, Finset.smul_sum]
    simp only [smul_smul]

/-- The compatible midpoint interpolant on the parent H¹ space.  It keeps the
mean-gradient endpoint load and applies the geometry-only midpoint correction
to that load. -/
def compatibleMidpointLinearInterpolant {ι : Type*} [Fintype ι]
    (Q : TriadicCube 2) (j : ℕ) (components : ι → Finset (InteriorNode j))
    (hne : ∀ a, (components a).Nonempty) :
    H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q) :=
  (compatibleMidpointLoadLinear Q j components hne).comp (diagMeanGradientLinear Q)

private theorem midpoint_correction_sum_memH10 {ι : Type*} [Fintype ι]
    (Q : TriadicCube 2) (j : ℕ) (components : ι → Finset (InteriorNode j))
    (hne : ∀ a, (components a).Nonempty) (p : Vec 2) :
    MemH10 (openCubeSet Q)
      ((∑ i : Fin 2, p i • midpointCorrectionH1 Q j components hne i).toFun) := by
  rw [Fin.sum_univ_two]
  change MemH10 (openCubeSet Q)
    (fun x => p 0 * (midpointCorrectionH1 Q j components hne 0).toFun x +
      p 1 * (midpointCorrectionH1 Q j components hne 1).toFun x)
  exact memH10_add
    (memH10_smul (p 0) (midpoint_correction_memH10 Q j components hne 0))
    (memH10_smul (p 1) (midpoint_correction_memH10 Q j components hne 1))

/-- The geometry-only interpolant has the zero-trace residual required by the
source variational lift for every affine endpoint and every H¹₀ correction. -/
theorem compatible_midpoint_interpolant_residual_memH10 {ι : Type*} [Fintype ι]
    (Q : TriadicCube 2) (j : ℕ) (components : ι → Finset (InteriorNode j))
    (hne : ∀ a, (components a).Nonempty) (p : Vec 2)
    (r : H10Function (openCubeSet Q)) :
    MemH10 (openCubeSet Q)
      (ASDExplicitGamma.Variational.lemmaVAffinePotential
        (isOpenBoundedConvexDomain_openCubeSet Q) p r -
        compatibleMidpointLinearInterpolant Q j components hne
          (ASDExplicitGamma.Variational.lemmaVAffinePotential
            (isOpenBoundedConvexDomain_openCubeSet Q) p r)).toFun := by
  let c : H1Function (openCubeSet Q) :=
    ∑ i : Fin 2, p i • midpointCorrectionH1 Q j components hne i
  have hc : MemH10 (openCubeSet Q) c.toFun := by
    exact midpoint_correction_sum_memH10 Q j components hne p
  have hI : compatibleMidpointLinearInterpolant Q j components hne
      (ASDExplicitGamma.Variational.lemmaVAffinePotential
        (isOpenBoundedConvexDomain_openCubeSet Q) p r) =
      diagAffineLinear Q p + c := by
    change compatibleMidpointLoadLinear Q j components hne
      (diagMeanGradientLinear Q
        (ASDExplicitGamma.Variational.lemmaVAffinePotential
          (isOpenBoundedConvexDomain_openCubeSet Q) p r)) = _
    rw [diagMeanGradient_affinePotential]
    rfl
  have hres := memH10_sub r.memH10 hc
  convert hres using 1
  rw [hI]
  simp only [ASDExplicitGamma.Variational.lemmaVAffinePotential, diagAffineLinear,
    LinearMap.coe_mk, AddHom.coe_mk, H1Function.sub_toFun, H1Function.add_toFun]
  funext x
  abel

/-- The compatible midpoint map lifts affine endpoint data into the actual
parent response space by the source weak column-divergence identity. -/
theorem compatible_midpoint_endpoint_lift_source {ι : Type*} [Fintype ι]
    (Q : TriadicCube 2) (j : ℕ) (components : ι → Finset (InteriorNode j))
    (hne : ∀ a, (components a).Nonempty) (p : Vec 2)
    (r : H10Function (openCubeSet Q)) (η w : H1Function (openCubeSet Q))
    (hη : MemLp η.toFun (⊤ : ENNReal) (volume.restrict (openCubeSet Q)))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) (⊤ : ENNReal)
      (volume.restrict (openCubeSet Q))) :
    let U := openCubeSet Q
    let hU := isOpenBoundedConvexDomain_openCubeSet Q
    let I := compatibleMidpointLinearInterpolant Q j components hne
    let v := ASDExplicitGamma.Variational.lemmaVAffinePotential hU p r
    MemVectorL2 U (localizedColumnProductDivergence η (v-I v)) ∧
    IsSolenoidalZeroNormalTraceOn U (localizedColumnProductDivergence η (v-I v)) ∧
    (∀ x, localizedColumnProductDivergence η (v-I v) x =
      (v-I v).toFun x • lemmaVPlanarWeakColumnDivergence η x -
        η.toFun x • matVecMul responsePlanarJ ((v-I v).grad x)) ∧
    volumeAverage U (fun x => vecDot
      (η.toFun x • matVecMul responsePlanarJ (v.grad x)) (w.grad x)) =
    volumeAverage U (fun x => vecDot (lemmaVPlanarRowField I η v x) (w.grad x)) := by
  dsimp
  exact ASDExplicitGamma.Variational.lemmaV_interpolant_lift_source
    (isOpenBoundedConvexDomain_openCubeSet Q)
    (compatibleMidpointLinearInterpolant Q j components hne)
    (ASDExplicitGamma.Variational.lemmaVAffinePotential
      (isOpenBoundedConvexDomain_openCubeSet Q) p r) η w
    (compatible_midpoint_interpolant_residual_memH10 Q j components hne p r)
    hη hDη

private theorem synthesis_nodal_value (Q : TriadicCube 2) (j : ℕ)
    (b : InteriorNode j → ℝ) (z : InteriorNode j) :
    (diagSynthesisH1Linear Q j b).toFun (diagInteriorVertex Q j z) = b z := by
  classical
  rw [diagSynthesisH1Linear_toFun]
  simp only [diagPhysicalHat_at_vertex]
  rw [Finset.sum_eq_single z]
  · simp
  · intro w hw hwz
    rw [ite_eq_right hwz, mul_zero]
  · intro hz
    exact (hz (Finset.mem_univ z)).elim

/-- The linear parent interpolant takes every affine endpoint load to the
component's physical bounding-box midpoint at marked nodes. -/
theorem compatible_midpoint_linear_interpolant_at_component_node
    {ι : Type*} [Fintype ι] (Q : TriadicCube 2) (j : ℕ)
    (components : ι → Finset (InteriorNode j))
    (hne : ∀ a, (components a).Nonempty)
    (hdisj : ∀ a b, a ≠ b → Disjoint (components a) (components b))
    (a : ι) {z : InteriorNode j} (hz : z ∈ components a)
    (p : Vec 2) (r : H10Function (openCubeSet Q)) :
    (compatibleMidpointLinearInterpolant Q j components hne
      (ASDExplicitGamma.Variational.lemmaVAffinePotential
        (isOpenBoundedConvexDomain_openCubeSet Q) p r)).toFun
      (diagInteriorVertex Q j z) =
        ∑ i : Fin 2, p i * componentMidpoint Q j (components a) (hne a) i := by
  have hI : compatibleMidpointLinearInterpolant Q j components hne
      (ASDExplicitGamma.Variational.lemmaVAffinePotential
        (isOpenBoundedConvexDomain_openCubeSet Q) p r) =
      diagAffineLinear Q p +
        ∑ i : Fin 2, p i • midpointCorrectionH1 Q j components hne i := by
    change compatibleMidpointLoadLinear Q j components hne
      (diagMeanGradientLinear Q
        (ASDExplicitGamma.Variational.lemmaVAffinePotential
          (isOpenBoundedConvexDomain_openCubeSet Q) p r)) = _
    rw [diagMeanGradient_affinePotential]
    rfl
  have hcorr (i : Fin 2) :
      (midpointCorrectionH1 Q j components hne i).toFun
          (diagInteriorVertex Q j z) =
        componentMidpoint Q j (components a) (hne a) i -
          diagInteriorVertex Q j z i := by
    rw [midpointCorrectionH1, synthesis_nodal_value,
      midpoint_nodal_correction_on_component Q j components hne hdisj a hz]
  rw [hI]
  simp only [H1Function.add_toFun, H1Function.smul_toFun, Fin.sum_univ_two]
  rw [hcorr 0, hcorr 1]
  have haff : (diagAffineLinear Q p).toFun (diagInteriorVertex Q j z) =
      ∑ i : Fin 2, p i * diagInteriorVertex Q j z i := by
    change (∑ i : Fin 2, p i * diagInteriorVertex Q j z i) = _
    rfl
  rw [haff, Fin.sum_univ_two]
  ring

/-- Natural generation depth of the source Whitney layer k inside one root. -/
def compatibleWhitneyMeshDepth (H k : ℕ) : ℕ :=
  k + whitneyProfile H k

theorem compatible_whitney_mesh_depth_cast (H k : ℕ) :
    (compatibleWhitneyMeshDepth H k : ℤ) = resetDepth H k := by
  unfold compatibleWhitneyMeshDepth whitneyProfile resetDepth
  push_cast
  ring

/-- The natural common-mesh generation is the actual root-relative scale of
each cube in the source Whitney layer. -/
theorem whitney_layer_mesh_scale (l : ℤ) (H k : ℕ)
    {Q : TriadicCube 2} (hQ : Q ∈ bankWhitneyLayer l H k) :
    Q.scale = l - (compatibleWhitneyMeshDepth H k : ℤ) := by
  rw [whitney_layer_scale l H k hQ, compatible_whitney_mesh_depth_cast]

theorem compatible_whitney_adjacent_mesh_depths (H k : ℕ) :
    1 ≤ compatibleWhitneyMeshDepth H (k + 1) -
        compatibleWhitneyMeshDepth H k ∧
    compatibleWhitneyMeshDepth H (k + 1) -
        compatibleWhitneyMeshDepth H k ≤ 2 := by
  unfold compatibleWhitneyMeshDepth whitneyProfile
  omega

/-- Actual neighboring Whitney layers use at most two mesh generations of
mismatch.  Their finite component data refine to one parent interpolant, with
the source midpoint values, H¹₀ residuals, and variational lift all attached
to the same loading-independent linear map. -/
theorem exists_adjacent_whitney_compatible_parent_interpolant
    {ι : Type*} [Fintype ι] (Q : TriadicCube 2) (H k : ℕ)
    (layer : ι → ℕ) (hlayer : ∀ a, layer a = k ∨ layer a = k + 1)
    (components : ∀ a,
      Finset (InteriorNode (compatibleWhitneyMeshDepth H (layer a))))
    (hne : ∀ a, (components a).Nonempty)
    (hdisj : ∀ a b, a ≠ b →
      Disjoint
        (refineComponent (compatibleWhitneyMeshDepth H (k + 1))
          (fun a => compatibleWhitneyMeshDepth H (layer a))
          (by
            intro a
            rcases hlayer a with ha | ha
            · rw [ha]
              unfold compatibleWhitneyMeshDepth whitneyProfile
              omega
            · rw [ha])
          components a)
        (refineComponent (compatibleWhitneyMeshDepth H (k + 1))
          (fun a => compatibleWhitneyMeshDepth H (layer a))
          (by
            intro a
            rcases hlayer a with ha | ha
            · rw [ha]
              unfold compatibleWhitneyMeshDepth whitneyProfile
              omega
            · rw [ha])
          components b)) :
    ∃ I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q),
      (∀ a z, z ∈ components a → ∀ p (r : H10Function (openCubeSet Q)),
        (I (ASDExplicitGamma.Variational.lemmaVAffinePotential
          (isOpenBoundedConvexDomain_openCubeSet Q) p r)).toFun
          (diagInteriorVertex Q (compatibleWhitneyMeshDepth H (layer a)) z) =
          ∑ i : Fin 2, p i *
            componentMidpoint Q (compatibleWhitneyMeshDepth H (layer a))
              (components a) (hne a) i) ∧
      (∀ p (r : H10Function (openCubeSet Q)),
        MemH10 (openCubeSet Q)
          (ASDExplicitGamma.Variational.lemmaVAffinePotential
            (isOpenBoundedConvexDomain_openCubeSet Q) p r -
            I (ASDExplicitGamma.Variational.lemmaVAffinePotential
              (isOpenBoundedConvexDomain_openCubeSet Q) p r)).toFun) ∧
      (∀ p (r : H10Function (openCubeSet Q)) (η w : H1Function (openCubeSet Q)),
        (hη : MemLp η.toFun (⊤ : ENNReal) (volume.restrict (openCubeSet Q))) →
        (hDη : ∀ i, MemLp (fun x => η.grad x i) (⊤ : ENNReal)
          (volume.restrict (openCubeSet Q))) →
        let U := openCubeSet Q
        let hU := isOpenBoundedConvexDomain_openCubeSet Q
        let v := ASDExplicitGamma.Variational.lemmaVAffinePotential hU p r
        MemVectorL2 U (localizedColumnProductDivergence η (v-I v)) ∧
        IsSolenoidalZeroNormalTraceOn U (localizedColumnProductDivergence η (v-I v)) ∧
        (∀ x, localizedColumnProductDivergence η (v-I v) x =
          (v-I v).toFun x • lemmaVPlanarWeakColumnDivergence η x -
            η.toFun x • matVecMul responsePlanarJ ((v-I v).grad x)) ∧
        volumeAverage U (fun x => vecDot
          (η.toFun x • matVecMul responsePlanarJ (v.grad x)) (w.grad x)) =
        volumeAverage U (fun x => vecDot (lemmaVPlanarRowField I η v x) (w.grad x))) := by
  let depth : ι → ℕ := fun a => compatibleWhitneyMeshDepth H (layer a)
  let J : ℕ := compatibleWhitneyMeshDepth H (k + 1)
  have hdepth : ∀ a, depth a ≤ J := by
    intro a
    rcases hlayer a with ha | ha
    · dsimp [depth, J]
      rw [ha]
      unfold compatibleWhitneyMeshDepth whitneyProfile
      omega
    · dsimp [depth, J]
      rw [ha]
  let common : ∀ a, Finset (InteriorNode J) :=
    refineComponent J depth hdepth components
  have hcommon : ∀ a, (common a).Nonempty := by
    intro a
    exact refine_component_nonempty J depth hdepth components hne a
  refine ⟨compatibleMidpointLinearInterpolant Q J common hcommon,
    ?_, ?_, ?_⟩
  · intro a z hz p r
    have hzcommon : refineInteriorNode (hdepth a) z ∈ common a :=
      Finset.mem_image.mpr ⟨z, hz, rfl⟩
    have hvalue := compatible_midpoint_linear_interpolant_at_component_node
      Q J common hcommon hdisj a hzcommon p r
    have hmid :
        (∑ i : Fin 2, p i * componentMidpoint Q J (common a) (hcommon a) i) =
          ∑ i : Fin 2, p i * componentMidpoint Q (depth a)
            (components a) (hne a) i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [refined_component_midpoint_eq Q J depth hdepth components hne a i]
    rw [refine_interior_vertex Q (hdepth a) z] at hvalue
    rw [hmid] at hvalue
    exact hvalue
  · intro p r
    exact compatible_midpoint_interpolant_residual_memH10 Q J common hcommon p r
  · intro p r η w hη hDη
    exact compatible_midpoint_endpoint_lift_source Q J common hcommon p r η w hη hDη

end

end ASDExplicitGamma.Inverse
