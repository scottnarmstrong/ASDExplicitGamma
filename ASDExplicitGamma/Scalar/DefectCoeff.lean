module

public import ASDExplicitGamma.Scalar.DefectOptModes
public import ASDExplicitGamma.Scalar.DefectModePotential
public import ASDExplicitGamma.Native.OldSignedAveragePairing
public import ASDExplicitGamma.Main.InterpolantStability

/-! Continuity of the quadratic coefficients of the defect rows in the H10 potentials. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Gaussian ASDExplicitGamma.Native ASDExplicitGamma.Main
open scoped BigOperators

noncomputable section

/-- Cauchy–Schwarz for a symmetric positive-semidefinite bilinear form. -/
theorem PsdForm.sq_le {P : Type*} [AddCommGroup P] [Module ℝ P] (β : PsdForm P) (x y : P) :
    (β.form x y) ^ 2 ≤ β.form x x * β.form y y := by
  have h : ∀ t : ℝ, 0 ≤ β.form x x * t * t + (2 * β.form x y) * t + β.form y y := by
    intro t
    have := β.nonneg (y + t • x)
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at this
    rw [β.symm y x] at this
    nlinarith [this]
  have hd := discrim_le_zero (a := β.form x x) (b := 2 * β.form x y) (c := β.form y y)
    (fun t => by rw [← mul_assoc]; exact h t)
  unfold discrim at hd
  nlinarith [hd]

/-- Gradient energy on the cube versus the Hilbert norm of the gradient class. -/
theorem gradEnergy_eq (Q : TriadicCube 2) (u : H1Function (openCubeSet Q)) :
    ∑ i : Fin 2, energy Q (fun x => u.grad x i) =
      (cubeVolume Q)⁻¹ * ‖u.gradToHilbertVectorL2‖ ^ 2 := by
  have hmem := u.grad_memVectorL2
  have h := old_signed_vector_average_pairing Q u.grad u.grad hmem hmem
  have hn : ‖u.gradToHilbertVectorL2‖ ^ 2 = ∫ x in openCubeSet Q, vecDot (u.grad x) (u.grad x)
      ∂MeasureTheory.volume := by
    rw [← real_inner_self_eq_norm_sq]
    exact inner_toHilbertVectorL2OfVecField_eq_integral hmem hmem
  rw [hn]
  have hv : (MeasureTheory.volume (openCubeSet Q)).toReal = cubeVolume Q :=
    volume_openCubeSet_toReal Q
  unfold volumeAverage at h
  rw [hv] at h
  exact h.symm

section Rows

variable (Q : TriadicCube 2) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l}) (l : whiteBasisIndex)

theorem rowField_add (r r' : H10Function (openCubeSet Q)) :
    rowField Q m b L l (r + r') =
      fun p => rowField Q m b L l r p + rowField Q m b L l r' p := by
  funext p
  have h1 : (r + r').toH1Function = r.toH1Function + r'.toH1Function := rfl
  simp only [rowField, lemmaVPlanarRowField, h1, map_add, H1Function.add_grad,
    H1Function.add_toFun, H1Function.sub_toFun, Pi.neg_apply, matVecMul_add]
  module

theorem rowField_smul (c : ℝ) (r : H10Function (openCubeSet Q)) :
    rowField Q m b L l (c • r) = fun p => c • rowField Q m b L l r p := by
  funext p
  have h1 : (c • r).toH1Function = c • r.toH1Function := rfl
  simp only [rowField, lemmaVPlanarRowField, h1, map_smul, H1Function.smul_grad,
    H1Function.smul_toFun, H1Function.sub_toFun, Pi.neg_apply, matVecMul_smul, Pi.smul_apply,
    smul_eq_mul]
  module

theorem rowField_sub (r r' : H10Function (openCubeSet Q)) :
    rowField Q m b L l (r - r') =
      fun p => rowField Q m b L l r p - rowField Q m b L l r' p := by
  have h : r - r' = r + (-1 : ℝ) • r' := rfl
  rw [h, rowField_add, rowField_smul]
  funext p
  module

theorem rowElt_add (r r' : H10Function (openCubeSet Q)) :
    rowElt Q m b L l (r + r') = rowElt Q m b L l r + rowElt Q m b L l r' := by
  apply Subtype.ext
  exact rowField_add Q m b L l r r'

theorem rowElt_smul (c : ℝ) (r : H10Function (openCubeSet Q)) :
    rowElt Q m b L l (c • r) = c • rowElt Q m b L l r := by
  apply Subtype.ext
  exact rowField_smul Q m b L l c r

theorem rowElt_sub (r r' : H10Function (openCubeSet Q)) :
    rowElt Q m b L l (r - r') = rowElt Q m b L l r - rowElt Q m b L l r' := by
  apply Subtype.ext
  exact rowField_sub Q m b L l r r'

end Rows

section Bound

variable (nQ : ℤ) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})

/-- The Hilbert norm of the gradient class of a potential. -/
def gn' (nQ : ℤ) (r : H10Function (openCubeSet (originCube 2 nQ))) : ℝ :=
  ‖r.toH1Function.gradToHilbertVectorL2‖

/-- The weak tiled energy of the gradient is controlled by the gradient class. -/
theorem weak_le_gn (r : H10Function (openCubeSet (originCube 2 nQ))) :
    lemmaVTiledWeakEnergy (originCube 2 nQ) m r.toH1Function.grad ≤
      (cubeVolume (originCube 2 nQ))⁻¹ * gn' nQ r ^ 2 := by
  rw [gn', ← gradEnergy_eq]
  exact main_tiledWeak_le_gradient_energy (originCube 2 nQ) m r.toH1Function

/-- Single-mode energy bound for a source row, in terms of the gradient class. -/
theorem rowElt_energy_le (l : whiteBasisIndex)
    (r : H10Function (openCubeSet (originCube 2 nQ))) :
    tiledPositiveEnergy (originCube 2 nQ) m (rowElt (originCube 2 nQ) m b L l r) ≤
      colKappa (originCube 2 nQ) m b L ^ 2 * ((cubeVolume (originCube 2 nQ))⁻¹ *
        gn' nQ r ^ 2) := by
  have h := rowElt_column_bound nQ m b L {l} r
  rw [Finset.sum_singleton] at h
  refine h.trans (mul_le_mul_of_nonneg_left (weak_le_gn nQ m r) (sq_nonneg _))

/-- Cauchy–Schwarz bound for a PSD form dominated by the tiled energy. -/
theorem form_rowElt_sq_le (β : PsdForm (TiledHaarField (originCube 2 nQ) m))
    (hβ : ∀ x, β.form x x ≤ tiledPositiveEnergy (originCube 2 nQ) m x)
    (a c : whiteBasisIndex) (r r' : H10Function (openCubeSet (originCube 2 nQ))) :
    (β.form (rowElt (originCube 2 nQ) m b L a r) (rowElt (originCube 2 nQ) m b L c r')) ^ 2 ≤
      (colKappa (originCube 2 nQ) m b L ^ 2 * (cubeVolume (originCube 2 nQ))⁻¹) ^ 2 *
        (gn' nQ r ^ 2 * gn' nQ r' ^ 2) := by
  refine (β.sq_le _ _).trans ?_
  have h1 := (hβ _).trans (rowElt_energy_le nQ m b L a r)
  have h2 := (hβ _).trans (rowElt_energy_le nQ m b L c r')
  have n1 := β.nonneg (rowElt (originCube 2 nQ) m b L a r)
  have n2 := β.nonneg (rowElt (originCube 2 nQ) m b L c r')
  calc _ ≤ (colKappa (originCube 2 nQ) m b L ^ 2 * ((cubeVolume (originCube 2 nQ))⁻¹ *
        gn' nQ r ^ 2)) * (colKappa (originCube 2 nQ) m b L ^ 2 *
          ((cubeVolume (originCube 2 nQ))⁻¹ * gn' nQ r' ^ 2)) :=
        mul_le_mul h1 h2 n2 ((n1.trans h1))
    _ = _ := by ring

end Bound

section Bilinear

variable (nQ : ℤ) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})
  (β : PsdForm (TiledHaarField (originCube 2 nQ) m))
  (hβ : ∀ x, β.form x x ≤ tiledPositiveEnergy (originCube 2 nQ) m x)

theorem gn_sub_eq_zero (r r' : H10Function (openCubeSet (originCube 2 nQ)))
    (h : r.toH1Function.gradToHilbertVectorL2 = r'.toH1Function.gradToHilbertVectorL2) :
    gn' nQ (r - r') = 0 := by
  have e : (r - r').toH1Function = r.toH1Function + (-1 : ℝ) • r'.toH1Function := rfl
  unfold gn'
  rw [e, H1Function.gradToHilbertVectorL2_add, H1Function.gradToHilbertVectorL2_smul, h]
  simp

include hβ in
theorem form_null (a : whiteBasisIndex)
    (r r' : H10Function (openCubeSet (originCube 2 nQ)))
    (h : r.toH1Function.gradToHilbertVectorL2 = r'.toH1Function.gradToHilbertVectorL2)
    (x : TiledHaarField (originCube 2 nQ) m) :
    β.form (rowElt (originCube 2 nQ) m b L a r) x =
      β.form (rowElt (originCube 2 nQ) m b L a r') x := by
  have hg := gn_sub_eq_zero nQ r r' h
  have h1 := (hβ _).trans (rowElt_energy_le nQ m b L a (r - r'))
  rw [hg] at h1
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h1
  have h2 := β.sq_le (rowElt (originCube 2 nQ) m b L a (r - r')) x
  have h3 : β.form (rowElt (originCube 2 nQ) m b L a (r - r'))
      (rowElt (originCube 2 nQ) m b L a (r - r')) = 0 :=
    le_antisymm h1 (β.nonneg _)
  rw [h3, zero_mul] at h2
  have h4 : β.form (rowElt (originCube 2 nQ) m b L a (r - r')) x = 0 := by
    nlinarith [sq_nonneg (β.form (rowElt (originCube 2 nQ) m b L a (r - r')) x)]
  rw [rowElt_sub] at h4
  simp only [map_sub, LinearMap.sub_apply] at h4
  linarith

/-- The `H10` representative of a closed-graph point. -/
def rep'' (nQ : ℤ) (z : H10GraphClosedSpace (openCubeSet (originCube 2 nQ))) :
    H10Function (openCubeSet (originCube 2 nQ)) :=
  defectWeakPotentialRepresentative (originCube 2 nQ) (ULift.up.{0} z)

theorem rep_class (z : H10GraphClosedSpace (openCubeSet (originCube 2 nQ))) :
    (rep'' nQ z).toH1Function.gradToHilbertVectorL2 = H10GraphClosed.gradientCLM z :=
  defectWeakPotentialRepresentative_gradient (originCube 2 nQ) (ULift.up.{0} z)

/-- The quadratic coefficient of two defect rows in the closed-graph potentials. -/
def coef' (a c : whiteBasisIndex)
    (z w : H10GraphClosedSpace (openCubeSet (originCube 2 nQ))) : ℝ :=
  β.form (rowElt (originCube 2 nQ) m b L a (rep'' nQ z))
    (rowElt (originCube 2 nQ) m b L c (rep'' nQ w))

include hβ in
theorem coef_add_left (a c : whiteBasisIndex) (z z' w : H10GraphClosedSpace (openCubeSet (originCube 2 nQ))) :
    coef' nQ m b L β a c (z + z') w = coef' nQ m b L β a c z w + coef' nQ m b L β a c z' w := by
  unfold coef'
  have hcl : (rep'' nQ (z + z')).toH1Function.gradToHilbertVectorL2 =
      (rep'' nQ z + rep'' nQ z').toH1Function.gradToHilbertVectorL2 := by
    have e : (rep'' nQ z + rep'' nQ z').toH1Function =
        (rep'' nQ z).toH1Function + (rep'' nQ z').toH1Function := rfl
    rw [e, H1Function.gradToHilbertVectorL2_add, rep_class, rep_class, rep_class,
      map_add]
  rw [form_null nQ m b L β hβ a _ _ hcl, rowElt_add]
  simp only [map_add, LinearMap.add_apply]

include hβ in
theorem coef_smul_left (a c : whiteBasisIndex) (t : ℝ)
    (z w : H10GraphClosedSpace (openCubeSet (originCube 2 nQ))) :
    coef' nQ m b L β a c (t • z) w = t * coef' nQ m b L β a c z w := by
  unfold coef'
  have hcl : (rep'' nQ (t • z)).toH1Function.gradToHilbertVectorL2 =
      (t • rep'' nQ z).toH1Function.gradToHilbertVectorL2 := by
    have e : (t • rep'' nQ z).toH1Function = t • (rep'' nQ z).toH1Function := rfl
    rw [e, H1Function.gradToHilbertVectorL2_smul, rep_class, rep_class, map_smul]
  rw [form_null nQ m b L β hβ a _ _ hcl, rowElt_smul]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem coef_symm (a c : whiteBasisIndex)
    (z w : H10GraphClosedSpace (openCubeSet (originCube 2 nQ))) :
    coef' nQ m b L β a c z w = coef' nQ m b L β c a w z := by
  unfold coef'
  exact β.symm _ _

include hβ in
theorem coef_add_right (a c : whiteBasisIndex) (z w w' : H10GraphClosedSpace (openCubeSet (originCube 2 nQ))) :
    coef' nQ m b L β a c z (w + w') = coef' nQ m b L β a c z w + coef' nQ m b L β a c z w' := by
  rw [coef_symm, coef_add_left nQ m b L β hβ, coef_symm nQ m b L β c a w z,
    coef_symm nQ m b L β c a w' z]

include hβ in
theorem coef_smul_right (a c : whiteBasisIndex) (t : ℝ)
    (z w : H10GraphClosedSpace (openCubeSet (originCube 2 nQ))) :
    coef' nQ m b L β a c z (t • w) = t * coef' nQ m b L β a c z w := by
  rw [coef_symm, coef_smul_left nQ m b L β hβ, coef_symm nQ m b L β c a w z]

include hβ in
theorem coef_abs_le (a c : whiteBasisIndex)
    (z w : H10GraphClosedSpace (openCubeSet (originCube 2 nQ))) :
    |coef' nQ m b L β a c z w| ≤
      (colKappa (originCube 2 nQ) m b L ^ 2 * (cubeVolume (originCube 2 nQ))⁻¹) *
        (‖H10GraphClosed.gradientCLM z‖ * ‖H10GraphClosed.gradientCLM w‖) := by
  have h := form_rowElt_sq_le nQ m b L β hβ a c (rep'' nQ z) (rep'' nQ w)
  have hz : gn' nQ (rep'' nQ z) = ‖H10GraphClosed.gradientCLM z‖ := by
    unfold gn'; rw [rep_class]
  have hw : gn' nQ (rep'' nQ w) = ‖H10GraphClosed.gradientCLM w‖ := by
    unfold gn'; rw [rep_class]
  rw [hz, hw] at h
  have hC : 0 ≤ colKappa (originCube 2 nQ) m b L ^ 2 * (cubeVolume (originCube 2 nQ))⁻¹ := by
    have := (cubeVolume_pos (originCube 2 nQ)).le
    positivity
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  unfold coef'
  calc _ ≤ _ := h
    _ = _ := by ring

/-- The coefficient as a continuous bilinear form on the closed graph. -/
def coefCLM (a c : whiteBasisIndex) :
    H10GraphClosedSpace (openCubeSet (originCube 2 nQ)) →L[ℝ]
      H10GraphClosedSpace (openCubeSet (originCube 2 nQ)) →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (coef' nQ m b L β a c)
      (coef_add_left nQ m b L β hβ a c) (coef_smul_left nQ m b L β hβ a c)
      (coef_add_right nQ m b L β hβ a c) (coef_smul_right nQ m b L β hβ a c))
    ((colKappa (originCube 2 nQ) m b L ^ 2 * (cubeVolume (originCube 2 nQ))⁻¹) *
      ‖(H10GraphClosed.gradientCLM (d := 2) (U := openCubeSet (originCube 2 nQ)))‖ ^ 2)
    (fun z w => by
      rw [LinearMap.mk₂_apply, Real.norm_eq_abs]
      refine (coef_abs_le nQ m b L β hβ a c z w).trans ?_
      have hC : 0 ≤ colKappa (originCube 2 nQ) m b L ^ 2 * (cubeVolume (originCube 2 nQ))⁻¹ := by
        have := (cubeVolume_pos (originCube 2 nQ)).le
        positivity
      have h1 := (H10GraphClosed.gradientCLM (d := 2) (U := openCubeSet (originCube 2 nQ))).le_opNorm z
      have h2 := (H10GraphClosed.gradientCLM (d := 2) (U := openCubeSet (originCube 2 nQ))).le_opNorm w
      calc _ ≤ (colKappa (originCube 2 nQ) m b L ^ 2 * (cubeVolume (originCube 2 nQ))⁻¹) *
            ((‖(H10GraphClosed.gradientCLM (d := 2) (U := openCubeSet (originCube 2 nQ)))‖ * ‖z‖) *
              (‖(H10GraphClosed.gradientCLM (d := 2) (U := openCubeSet (originCube 2 nQ)))‖ * ‖w‖)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) hC
        _ = _ := by ring)

include hβ in
theorem coef_continuous (a c : whiteBasisIndex) :
    Continuous fun p : H10GraphClosedSpace (openCubeSet (originCube 2 nQ)) ×
        H10GraphClosedSpace (openCubeSet (originCube 2 nQ)) => coef' nQ m b L β a c p.1 p.2 := by
  have h : Continuous fun p : H10GraphClosedSpace (openCubeSet (originCube 2 nQ)) ×
        H10GraphClosedSpace (openCubeSet (originCube 2 nQ)) =>
        coefCLM nQ m b L β hβ a c p.1 p.2 :=
    ((coefCLM nQ m b L β hβ a c).continuous.comp continuous_fst).clm_apply continuous_snd
  exact h

end Bilinear
end

end ASDExplicitGamma.Scalar
