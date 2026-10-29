module

public import ASDExplicitGamma.Scalar.GSlotSpace

/-! The positive and weak embeddings `Φ`, `Ψ` of tile fields into the increment Hilbert space,
their norm identities, and the duality `⟪Φ F, Ψ g⟫ = tile-averaged pairing`. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Filter ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped BigOperators Topology InnerProductSpace ENNReal

noncomputable section

variable (Q : TriadicCube 2) (m : ℕ)

/-- Fields whose coordinates are `L²` on every depth-`m` tile (no Haar summability). -/
def TiledL2Field : Submodule ℝ (Vec 2 → Vec 2) where
  carrier := {g | ∀ R ∈ descendantsAtDepth Q m, ∀ i : Fin 2,
    MemLp (fun x => g x i) 2 (normalizedCubeMeasure R)}
  zero_mem' := fun R _ i => by
    simpa using (MemLp.zero : MemLp (fun _ : Vec 2 => (0 : ℝ)) 2 (normalizedCubeMeasure R))
  add_mem' := fun {F G} hF hG R hR i => (hF R hR i).add (hG R hR i)
  smul_mem' := fun c F hF R hR i => (hF R hR i).const_mul c

/-- The `L²` class of a coordinate of a tile field on a tile. -/
def tileL2Coord (R : descendantsAtDepth Q m) (i : Fin 2) :
    TiledL2Field Q m →ₗ[ℝ] Lp ℝ 2 (normalizedCubeMeasure R.1) where
  toFun g := ((g.2 R.1 R.2 i)).toLp (fun x => g.1 x i)
  map_add' g h := MemLp.toLp_add ((g.2 R.1 R.2 i)) ((h.2 R.1 R.2 i))
  map_smul' c g := MemLp.toLp_const_smul (c := c) ((g.2 R.1 R.2 i))

theorem tileL2Coord_ae (R : descendantsAtDepth Q m) (i : Fin 2) (g : TiledL2Field Q m) :
    (fun x => tileL2Coord Q m R i g x) =ᵐ[normalizedCubeMeasure R.1] fun x => g.1 x i :=
  (g.2 R.1 R.2 i).coeFn_toLp

variable {Q m}

theorem primalEnergy_congr_ae (R : TriadicCube 2) (q : ℝ) {f g : Vec 2 → ℝ}
    (h : f =ᵐ[normalizedCubeMeasure R] g) : primalEnergy R q f = primalEnergy R q g := by
  unfold primalEnergy
  simp only [cubeIncrement_congr_ae R _ h]

theorem phi_summable (F : TiledHaarField Q m) (R : descendantsAtDepth Q m) (i : Fin 2) :
    Summable (fun k : ℕ => (Real.sqrt 3) ^ k *
      energy R.1 (cubeIncrement R.1 k (fun x => tileCoordLp Q m R i F x))) := by
  have h := tiled_summable_all R.1 (F.2 R.1 R.2 i).2
  refine h.congr fun k => ?_
  rw [cubeIncrement_congr_ae R.1 k (tileCoordLp_ae Q m R i F)]

theorem psi_summable (g : TiledL2Field Q m) (R : descendantsAtDepth Q m) (i : Fin 2) :
    Summable (fun k : ℕ => (Real.sqrt 3)⁻¹ ^ k *
      energy R.1 (cubeIncrement R.1 k (fun x => tileL2Coord Q m R i g x))) :=
  gseq_summable_weak (by positivity) (inv_le_one_of_one_le₀ (by
    have : (1 : ℝ) ≤ Real.sqrt 3 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    exact this)) R.1 _

theorem sqrt3_nonneg' : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg _

theorem sqrt3_inv_nonneg' : (0 : ℝ) ≤ (Real.sqrt 3)⁻¹ := by positivity

theorem sqrt3_mul_inv' : Real.sqrt 3 * (Real.sqrt 3)⁻¹ = 1 :=
  mul_inv_cancel₀ (by positivity)

variable (Q m)

variable {Q m} in
theorem gseqFun_add (q : ℝ) (f g : GCoord Q m) (j : GIdx Q m) :
    gseqFun q (f + g) j = gseqFun q f j + gseqFun q g j := by
  simp only [gseqFun, Pi.add_apply, map_add, smul_add]

variable {Q m} in
theorem gseqFun_smul (q c : ℝ) (f : GCoord Q m) (j : GIdx Q m) :
    gseqFun q (c • f) j = c • gseqFun q f j := by
  simp only [gseqFun, Pi.smul_apply, map_smul, smul_comm c]

/-- The positive embedding. -/
def PhiL : TiledHaarField Q m →ₗ[ℝ] GSpace Q m where
  toFun F := gseq sqrt3_nonneg' (fun R i => tileCoordLp Q m R i F) (phi_summable F)
  map_add' F G := by
    refine Subtype.ext (funext fun j => ?_)
    have h := gseqFun_add (Real.sqrt 3) (fun R i => tileCoordLp Q m R i F)
      (fun R i => tileCoordLp Q m R i G) j
    exact h
  map_smul' c F := by
    refine Subtype.ext (funext fun j => ?_)
    have h := gseqFun_smul (Real.sqrt 3) c (fun R i => tileCoordLp Q m R i F) j
    exact h

/-- The weak embedding. -/
def PsiL : TiledL2Field Q m →ₗ[ℝ] GSpace Q m where
  toFun g := gseq sqrt3_inv_nonneg' (fun R i => tileL2Coord Q m R i g) (psi_summable g)
  map_add' F G := by
    refine Subtype.ext (funext fun j => ?_)
    have h := gseqFun_add (Real.sqrt 3)⁻¹ (fun R i => tileL2Coord Q m R i F)
      (fun R i => tileL2Coord Q m R i G) j
    exact h
  map_smul' c F := by
    refine Subtype.ext (funext fun j => ?_)
    have h := gseqFun_smul (Real.sqrt 3)⁻¹ c (fun R i => tileL2Coord Q m R i F) j
    exact h

theorem phi_norm_sq (F : TiledHaarField Q m) :
    ‖PhiL Q m F‖ ^ 2 = tiledPositiveEnergy Q m F := by
  have h := gseq_norm_sq sqrt3_nonneg' (fun R i => tileCoordLp Q m R i F) (phi_summable F)
  change ‖gseq sqrt3_nonneg' (fun R i => tileCoordLp Q m R i F) (phi_summable F)‖ ^ 2 = _
  rw [h]
  unfold tiledPositiveEnergy lemmaVTiledPositiveEnergy descendantsAverage vectorPositiveHaarEnergy
  dsimp only
  rw [← Finset.sum_coe_sort (descendantsAtDepth Q m)
    (fun R => ∑ i, primalEnergy R (Real.sqrt 3) (fun x => F.1 x i))]
  congr 1
  refine Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl fun i _ => ?_
  exact primalEnergy_congr_ae R.1 _ (tileCoordLp_ae Q m R i F)

theorem psi_norm_sq (g : TiledL2Field Q m) :
    ‖PsiL Q m g‖ ^ 2 = lemmaVTiledWeakEnergy Q m g.1 := by
  have h := gseq_norm_sq sqrt3_inv_nonneg' (fun R i => tileL2Coord Q m R i g) (psi_summable g)
  change ‖gseq sqrt3_inv_nonneg' (fun R i => tileL2Coord Q m R i g) (psi_summable g)‖ ^ 2 = _
  rw [h]
  unfold lemmaVTiledWeakEnergy descendantsAverage vectorWeakHaarEnergy dualEnergy
  dsimp only
  rw [← Finset.sum_coe_sort (descendantsAtDepth Q m)
    (fun R => ∑ i, primalEnergy R (Real.sqrt 3)⁻¹ (fun x => g.1 x i))]
  congr 1
  refine Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl fun i _ => ?_
  exact primalEnergy_congr_ae R.1 _ (tileL2Coord_ae Q m R i g)

theorem phi_psi_inner (F : TiledHaarField Q m) (g : TiledL2Field Q m) :
    ⟪PhiL Q m F, PsiL Q m g⟫_ℝ =
      descendantsAverage Q m (fun R => vectorPairing R F.1 g.1) := by
  have h := gseq_inner sqrt3_nonneg' sqrt3_inv_nonneg' sqrt3_mul_inv'
    (fun R i => tileCoordLp Q m R i F) (fun R i => tileL2Coord Q m R i g) (phi_summable F)
    (psi_summable g)
  change ⟪gseq sqrt3_nonneg' (fun R i => tileCoordLp Q m R i F) (phi_summable F),
    gseq sqrt3_inv_nonneg' (fun R i => tileL2Coord Q m R i g) (psi_summable g)⟫_ℝ = _
  rw [h]
  unfold descendantsAverage vectorPairing
  dsimp only
  rw [← Finset.sum_coe_sort (descendantsAtDepth Q m)
    (fun R => ∑ i, pairing R (fun x => F.1 x i) (fun x => g.1 x i))]
  congr 1
  refine Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl fun i _ => ?_
  rw [inner_lp, pairing_congr_ae R.1 (tileCoordLp_ae Q m R i F) (tileL2Coord_ae Q m R i g)]

theorem phiL_apply (F : TiledHaarField Q m) (j : GIdx Q m) :
    (PhiL Q m F : GSpace Q m) j =
      gseqFun (Real.sqrt 3) (fun R i => tileCoordLp Q m R i F) j := rfl

theorem psiL_apply (g : TiledL2Field Q m) (j : GIdx Q m) :
    (PsiL Q m g : GSpace Q m) j =
      gseqFun (Real.sqrt 3)⁻¹ (fun R i => tileL2Coord Q m R i g) j := rfl

end

end ASDExplicitGamma.Scalar
