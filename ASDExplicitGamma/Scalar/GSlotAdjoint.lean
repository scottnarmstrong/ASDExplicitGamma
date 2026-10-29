module

public import ASDExplicitGamma.Scalar.GSlotSynth
public import ASDExplicitGamma.Scalar.GSlotHilbert
public import ASDExplicitGamma.Scalar.DefectCoeff

/-! The potential-slot source `G_l(g)`: the minimum-norm positive-Haar extension of
`p ↦ ⟨F_l(p), g⟩` (`relative_growth_interpolant_paired_covariance.md` (2.3)), built from the
Hilbert transposition of the row field `F_l` in the increment space. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Filter ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Gaussian
open scoped BigOperators Topology InnerProductSpace ENNReal

noncomputable section

section Setup

variable (nQ : ℤ) (m : ℕ)

local notation "QQ" => originCube 2 nQ

theorem grad_memLp_tile (r : H10Function (openCubeSet QQ)) {R : TriadicCube 2}
    (hR : R ∈ descendantsAtDepth QQ m) (i : Fin 2) :
    MemLp (fun x => r.toH1Function.grad x i) 2 (normalizedCubeMeasure R) := by
  have hc := memScalarL2_coord_of_memVectorL2 r.toH1Function.grad_memVectorL2 i
  exact memLp_normalized_of_memL2On
    (memL2On_mono (openCubeSet_subset_of_mem_descendantsAtDepth hR) hc)

/-- The gradient of a potential as a tile `L²` field. -/
def gradL2f (r : H10Function (openCubeSet QQ)) : TiledL2Field QQ m :=
  ⟨r.toH1Function.grad, fun _ hR i => grad_memLp_tile nQ m r hR i⟩

theorem gradL2f_sub (r r' : H10Function (openCubeSet QQ)) :
    gradL2f nQ m (r - r') = gradL2f nQ m r - gradL2f nQ m r' := by
  apply Subtype.ext
  funext x
  exact congrFun (H1Function.sub_grad _ _) x

theorem gradL2f_add (r r' : H10Function (openCubeSet QQ)) :
    gradL2f nQ m (r + r') = gradL2f nQ m r + gradL2f nQ m r' := by
  apply Subtype.ext
  funext x
  exact congrFun (H1Function.add_grad _ _) x

theorem gradL2f_smul (c : ℝ) (r : H10Function (openCubeSet QQ)) :
    gradL2f nQ m (c • r) = c • gradL2f nQ m r := by
  apply Subtype.ext
  funext x
  exact congrFun (H1Function.smul_grad _ _) x

theorem psi_norm_sq' (r : H10Function (openCubeSet QQ)) :
    ‖PsiL QQ m (gradL2f nQ m r)‖ ^ 2 = lemmaVTiledWeakEnergy QQ m r.toH1Function.grad :=
  psi_norm_sq QQ m (gradL2f nQ m r)

/-- Same gradient class, same weak embedding. -/
theorem psi_eq_of_class (r r' : H10Function (openCubeSet QQ))
    (h : r.toH1Function.gradToHilbertVectorL2 = r'.toH1Function.gradToHilbertVectorL2) :
    PsiL QQ m (gradL2f nQ m r) = PsiL QQ m (gradL2f nQ m r') := by
  have hg := gn_sub_eq_zero nQ r r' h
  have h1 := weak_le_gn nQ m (r - r')
  rw [hg] at h1
  have h2 := psi_norm_sq' nQ m (r - r')
  have h3 : ‖PsiL QQ m (gradL2f nQ m (r - r'))‖ ^ 2 ≤ 0 := by
    rw [h2]; simpa using h1
  have h4 : PsiL QQ m (gradL2f nQ m (r - r')) = 0 := by
    have : ‖PsiL QQ m (gradL2f nQ m (r - r'))‖ = 0 := by nlinarith [norm_nonneg (PsiL QQ m (gradL2f nQ m (r - r')))]
    exact norm_eq_zero.1 this
  rw [gradL2f_sub, map_sub] at h4
  exact sub_eq_zero.1 h4

variable (b : ℝ) (L : {l : ℝ // 0 < l})

/-- Same gradient class, same row embedding. -/
theorem phi_row_eq_of_class (l : whiteBasisIndex) (r r' : H10Function (openCubeSet QQ))
    (h : r.toH1Function.gradToHilbertVectorL2 = r'.toH1Function.gradToHilbertVectorL2) :
    PhiL QQ m (rowElt QQ m b L l r) = PhiL QQ m (rowElt QQ m b L l r') := by
  have hg := gn_sub_eq_zero nQ r r' h
  have h1 := rowElt_energy_le nQ m b L l (r - r')
  rw [hg] at h1
  have h2 : ‖PhiL QQ m (rowElt QQ m b L l (r - r'))‖ ^ 2 ≤ 0 := by
    rw [phi_norm_sq]; simpa using h1
  have h4 : PhiL QQ m (rowElt QQ m b L l (r - r')) = 0 := by
    have : ‖PhiL QQ m (rowElt QQ m b L l (r - r'))‖ = 0 := by
      nlinarith [norm_nonneg (PhiL QQ m (rowElt QQ m b L l (r - r')))]
    exact norm_eq_zero.1 this
  rw [rowElt_sub, map_sub] at h4
  exact sub_eq_zero.1 h4

theorem rep_class_add (z z' : H10GraphClosedSpace (openCubeSet QQ)) :
    (rep'' nQ (z + z')).toH1Function.gradToHilbertVectorL2 =
      (rep'' nQ z + rep'' nQ z').toH1Function.gradToHilbertVectorL2 := by
  have e : (rep'' nQ z + rep'' nQ z').toH1Function =
      (rep'' nQ z).toH1Function + (rep'' nQ z').toH1Function := rfl
  rw [e, H1Function.gradToHilbertVectorL2_add, rep_class, rep_class, rep_class, map_add]

theorem rep_class_smul (t : ℝ) (z : H10GraphClosedSpace (openCubeSet QQ)) :
    (rep'' nQ (t • z)).toH1Function.gradToHilbertVectorL2 =
      (t • rep'' nQ z).toH1Function.gradToHilbertVectorL2 := by
  have e : (t • rep'' nQ z).toH1Function = t • (rep'' nQ z).toH1Function := rfl
  rw [e, H1Function.gradToHilbertVectorL2_smul, rep_class, rep_class, map_smul]

/-- The weak embedding of a closed-graph potential. -/
def psiZ : H10GraphClosedSpace (openCubeSet QQ) →ₗ[ℝ] GSpace QQ m where
  toFun z := PsiL QQ m (gradL2f nQ m (rep'' nQ z))
  map_add' z z' := by
    rw [psi_eq_of_class nQ m _ _ (rep_class_add nQ z z'), gradL2f_add, map_add]
  map_smul' t z := by
    rw [psi_eq_of_class nQ m _ _ (rep_class_smul nQ t z), gradL2f_smul, map_smul]
    rfl

/-- The row embedding of a closed-graph potential. -/
def tZ (l : whiteBasisIndex) : H10GraphClosedSpace (openCubeSet QQ) →ₗ[ℝ] GSpace QQ m where
  toFun z := PhiL QQ m (rowElt QQ m b L l (rep'' nQ z))
  map_add' z z' := by
    rw [phi_row_eq_of_class nQ m b L l _ _ (rep_class_add nQ z z'), rowElt_add, map_add]
  map_smul' t z := by
    rw [phi_row_eq_of_class nQ m b L l _ _ (rep_class_smul nQ t z), rowElt_smul, map_smul]
    rfl

end Setup

section Duality

variable {Q : TriadicCube 2} {m : ℕ}

theorem gseqFun_inc_fixed (q : ℝ) (f : GCoord Q m) (j : GIdx Q m) :
    incL j.1.1 j.2.2 (gseqFun q f j) = gseqFun q f j := by
  unfold gseqFun
  rw [map_smul, inc_inc]
  simp

theorem psiL_inc_fixed (g : TiledL2Field Q m) (j : GIdx Q m) :
    incL j.1.1 j.2.2 ((PsiL Q m g : GSpace Q m) j) = (PsiL Q m g : GSpace Q m) j := by
  rw [psiL_apply]
  exact gseqFun_inc_fixed _ _ j

/-- If `Φ G` is the increment projection of `c`, pairing with `Ψ g` sees all of `c`. -/
theorem gphi_inner_eq (G : TiledHaarField Q m) (c : GSpace Q m)
    (hG : ∀ j : GIdx Q m, (PhiL Q m G : GSpace Q m) j = incL j.1.1 j.2.2 (c j))
    (g : TiledL2Field Q m) :
    ⟪PhiL Q m G, PsiL Q m g⟫_ℝ = ⟪c, PsiL Q m g⟫_ℝ := by
  rw [lp.inner_eq_tsum (𝕜 := ℝ), lp.inner_eq_tsum (𝕜 := ℝ)]
  refine tsum_congr fun j => ?_
  rw [hG j]
  have := inner_inc_left j.1.1 j.2.2 (c j) ((PsiL Q m g : GSpace Q m) j)
  rw [this, psiL_inc_fixed]

theorem gphi_norm_le (G : TiledHaarField Q m) (c : GSpace Q m)
    (hG : ∀ j : GIdx Q m, (PhiL Q m G : GSpace Q m) j = incL j.1.1 j.2.2 (c j)) :
    ‖PhiL Q m G‖ ≤ ‖c‖ := by
  have hn : ∀ x : GSpace Q m, ‖x‖ ^ 2 = ∑' j, ‖x j‖ ^ 2 := by
    intro x
    have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) x
    rw [show ((2 : ℝ≥0∞).toReal) = 2 by norm_num, Real.rpow_two] at h
    rw [h]
    refine tsum_congr fun j => ?_
    rw [Real.rpow_two]
  have h1 : ‖PhiL Q m G‖ ^ 2 ≤ ‖c‖ ^ 2 := by
    rw [hn, hn c]
    refine Summable.tsum_le_tsum (fun j => ?_) ?_ (c_sq_summable c)
    · rw [hG j]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_inc_le _ _ _) 2
    · have := (memℓp_gen_iff (p := 2) (by norm_num)).1 (PhiL Q m G).2
      simpa using this
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

theorem gphi_sum (ι : Type*) (s : Finset ι) (G : ι → TiledHaarField Q m) (c : ι → GSpace Q m)
    (hG : ∀ l, ∀ j : GIdx Q m, (PhiL Q m (G l) : GSpace Q m) j = incL j.1.1 j.2.2 (c l j)) :
    ∀ j : GIdx Q m, (PhiL Q m (∑ l ∈ s, G l) : GSpace Q m) j =
      incL j.1.1 j.2.2 ((∑ l ∈ s, c l : GSpace Q m) j) := by
  intro j
  have hs : ∀ u : ι → GSpace Q m, ((∑ i ∈ s, u i : GSpace Q m) : GSpace Q m) j =
      ∑ i ∈ s, (u i : GSpace Q m) j := fun u => by
    rw [lp.coeFn_sum]
    exact Finset.sum_apply j s fun c => ↑(u c)
  rw [map_sum, hs, hs, map_sum]
  exact Finset.sum_congr rfl fun l _ => hG l j

end Duality

end

end ASDExplicitGamma.Scalar
