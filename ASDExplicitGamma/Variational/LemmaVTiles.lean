module

public import ASDExplicitGamma.Variational.LemmaVHaar
public import ASDExplicitGamma.Variational.LemmaVEstimate

/-! Tile-averaged weak and positive Haar energies and complete inverse history. -/

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory ASDExplicitGamma.Triadic

noncomputable section

/-- The square of DIAG's tile-averaged weak norm. -/
def lemmaVTiledWeakEnergy (Q : TriadicCube 2) (j : ℕ) (F : Vec 2 → Vec 2) : ℝ :=
  descendantsAverage Q j (fun R => vectorWeakHaarEnergy R F)

/-- The square of DIAG's tile-averaged positive norm, on fields with finite
positive Haar series. Convergence is recorded in each use of H2. -/
def lemmaVTiledPositiveEnergy (Q : TriadicCube 2) (j : ℕ) (F : Vec 2 → Vec 2) : ℝ :=
  descendantsAverage Q j (fun R => vectorPositiveHaarEnergy R F)

/-- The maximum of the complete inverse histories of all tiles. -/
def lemmaVTileHistory (Q : TriadicCube 2) (j : ℕ) (a : CoeffField 2) : ℝ :=
  Book.Ch02.finsetSupReal (descendantsAtDepth Q j)
    (fun R => lemmaVInverseHistory R a (Real.sqrt 3))

theorem lemmaVInverseHistory_nonneg {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) {q : ℝ} (hq : 1 < q) : 0 ≤ lemmaVInverseHistory Q a q := by
  apply mul_nonneg (sub_nonneg.mpr (inv_le_one_of_one_le₀ hq.le))
  exact tsum_nonneg fun k => mul_nonneg (pow_nonneg (by positivity) _)
    (lemmaVInverseDepthMax_nonneg Q a k)

theorem lemmaVTileHistory_nonneg (Q : TriadicCube 2) (j : ℕ) (a : CoeffField 2) :
    0 ≤ lemmaVTileHistory Q j a := by
  apply Book.Ch02.finsetSupReal_nonneg
  intro R _
  apply lemmaVInverseHistory_nonneg
  have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 3)
  simpa using h

theorem lemmaVTiledWeakEnergy_nonneg (Q : TriadicCube 2) (j : ℕ) (F : Vec 2 → Vec 2) :
    0 ≤ lemmaVTiledWeakEnergy Q j F := by
  unfold lemmaVTiledWeakEnergy descendantsAverage
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun R _ => vectorWeakHaarEnergy_nonneg R F)

theorem lemmaVTiledPositiveEnergy_nonneg (Q : TriadicCube 2) (j : ℕ) (F : Vec 2 → Vec 2) :
    0 ≤ lemmaVTiledPositiveEnergy Q j F := by
  unfold lemmaVTiledPositiveEnergy descendantsAverage
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun R _ => vectorPositiveHaarEnergy_nonneg R F)

/-- Tilewise H1, summed with normalized cell volumes. -/
theorem lemmaV_harmonic_tiledWeakEnergy_le (Q : TriadicCube 2) (j : ℕ)
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (u : AHarmonicFunction a (openCubeSet Q)) :
    lemmaVTiledWeakEnergy Q j u.toH1.grad ≤
      lemmaVTileHistory Q j a * cubeAverage Q (scalarVariationEnergyIntegrand a u) := by
  let instFiniteQ : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hInt : IntegrableOn (scalarVariationEnergyIntegrand a u) (cubeSet Q) volume :=
    integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr
      ((ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll).energy u)
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q j _ hInt]
  have hpoint (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q j) :
      vectorWeakHaarEnergy R u.toH1.grad ≤
        lemmaVTileHistory Q j a * cubeAverage R (scalarVariationEnergyIntegrand a u) := by
    have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hR
    have hEllR := hEll.mono (measurableSet_openCubeSet R) hsub
    let instFiniteR : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
      (isOpenBoundedConvexDomain_openCubeSet R).isFiniteMeasure_restrict_volume
    let uR := u.restrictOfIsEllipticFieldOn (isOpen_openCubeSet Q) (isOpen_openCubeSet R)
      hsub hEllR
    have h := lemmaV_harmonic_vectorWeakHaarEnergy_le R hEllR uR
    apply h.trans
    have hE : 0 ≤ cubeAverage R (scalarVariationEnergyIntegrand a u) := by
      rw [cubeAverage_eq_integralAverage_openCubeSet]
      exact volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
        (openCubeSet R) a hEllR uR
    apply mul_le_mul_of_nonneg_right _ hE
    unfold lemmaVTileHistory Book.Ch02.finsetSupReal
    exact le_csSup (((Set.toFinite _).image _).bddAbove) ⟨R, hR, rfl⟩
  unfold lemmaVTiledWeakEnergy descendantsAverage
  calc
    _ ≤ ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j,
          lemmaVTileHistory Q j a * cubeAverage R (scalarVariationEnergyIntegrand a u) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpoint) (by positivity)
    _ = _ := by rw [← Finset.mul_sum]; exact mul_left_comm _ _ _

/-- Midpoint convexity survives normalized tile averaging. -/
theorem lemmaV_tiledWeakEnergy_midpoint_le (Q : TriadicCube 2) (j : ℕ)
    (v f g : H1Function (openCubeSet Q))
    (hmid : v.grad =ᵐ[volume.restrict (openCubeSet Q)]
      fun x i => (f.grad x i + g.grad x i) / 2) :
    lemmaVTiledWeakEnergy Q j v.grad ≤
      (lemmaVTiledWeakEnergy Q j f.grad + lemmaVTiledWeakEnergy Q j g.grad) / 2 := by
  have hpoint (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q j) :
      vectorWeakHaarEnergy R v.grad ≤
        (vectorWeakHaarEnergy R f.grad + vectorWeakHaarEnergy R g.grad) / 2 := by
    exact lemmaV_vectorWeakHaarEnergy_midpoint_le R
      (v.restrictToOpenSubcube hR) (f.restrictToOpenSubcube hR) (g.restrictToOpenSubcube hR)
      (ae_restrict_of_ae_restrict_of_subset (openCubeSet_subset_of_mem_descendantsAtDepth hR) hmid)
  unfold lemmaVTiledWeakEnergy descendantsAverage
  calc
    _ ≤ ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j,
          (vectorWeakHaarEnergy R f.grad + vectorWeakHaarEnergy R g.grad) / 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpoint) (by positivity)
    _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib]; ring

/-- Adjoint invariance of the maximum of the tile histories. -/
theorem lemmaVTileHistory_adjoint_eq (Q : TriadicCube 2) (j : ℕ)
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    lemmaVTileHistory Q j (adjointCoeffField a) = lemmaVTileHistory Q j a := by
  unfold lemmaVTileHistory
  apply Book.Ch02.finsetSupReal_congr
  intro R hR
  exact lemmaVInverseHistory_adjoint_eq R
    (hEll.mono (measurableSet_openCubeSet R) (openCubeSet_subset_of_mem_descendantsAtDepth hR)) _

/-- Tilewise H1 for the adjoint, using the same B. -/
theorem lemmaV_adjoint_tiledWeakEnergy_le (Q : TriadicCube 2) (j : ℕ)
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (u : AHarmonicFunction (adjointCoeffField a) (openCubeSet Q)) :
    lemmaVTiledWeakEnergy Q j u.toH1.grad ≤
      lemmaVTileHistory Q j a * cubeAverage Q (scalarVariationEnergyIntegrand (adjointCoeffField a) u) := by
  have h := lemmaV_harmonic_tiledWeakEnergy_le Q j (isEllipticFieldOn_adjointCoeffField hEll) u
  rwa [lemmaVTileHistory_adjoint_eq Q j hEll] at h

/-- The vector pairing is the normalized average of the Euclidean dot product. -/
theorem lemmaV_cubeAverage_vecDot_eq_vectorPairing (Q : TriadicCube 2)
    {F G : Vec 2 → Vec 2}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => vecDot (F x) (G x)) = vectorPairing Q F G := by
  unfold vectorPairing pairing vecDot
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  exact integral_finsetSum _ fun i _ => (hF i).integrable_mul (hG i)

/-- Tilewise K/P duality with constant one. The explicit summability premise
is exactly the finiteness of the positive norm appearing in H2. -/
theorem lemmaV_tiled_pairing_le (Q : TriadicCube 2) (j : ℕ)
    {F G : Vec 2 → Vec 2}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hGpos : ∀ R ∈ descendantsAtDepth Q j, ∀ i,
      Summable (fun k => (Real.sqrt 3) ^ (k + 1) *
        energy R (cubeIncrement R (k + 1) (fun x => G x i)))) :
    |cubeAverage Q (fun x => vecDot (F x) (G x))| ≤
      Real.sqrt (lemmaVTiledWeakEnergy Q j F) * Real.sqrt (lemmaVTiledPositiveEnergy Q j G) := by
  have hInt : IntegrableOn (fun x => vecDot (F x) (G x)) (cubeSet Q) volume := by
    apply integrableOn_of_integrable_normalizedCubeMeasure Q
    exact integrable_finsetSum _ fun i _ => (hF i).integrable_mul (hG i)
  have hpoint (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q j) :
      |cubeAverage R (fun x => vecDot (F x) (G x))| ≤
        Real.sqrt (vectorWeakHaarEnergy R F) * Real.sqrt (vectorPositiveHaarEnergy R G) := by
    have hFr (i : Fin 2) := memLp_on_descendant_of_memLp hR (hF i)
    have hGr (i : Fin 2) := memLp_on_descendant_of_memLp hR (hG i)
    have h := abs_vectorPairing_le_vectorPositiveHaarNorm_mul_vectorWeakHaarNorm
      R hGr hFr (hGpos R hR)
    rw [← lemmaV_cubeAverage_vecDot_eq_vectorPairing R hGr hFr] at h
    have heq : (fun x => vecDot (G x) (F x)) = fun x => vecDot (F x) (G x) :=
      funext fun x => vecDot_comm _ _
    rw [heq] at h
    simpa only [vectorWeakHaarNorm, vectorPositiveHaarNorm, mul_comm] using h
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q j _ hInt]
  unfold descendantsAverage
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((descendantsAtDepth Q j).card : ℝ)⁻¹)]
  calc
    _ ≤ ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j, |cubeAverage R (fun x => vecDot (F x) (G x))| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j,
          Real.sqrt (vectorWeakHaarEnergy R F) * Real.sqrt (vectorPositiveHaarEnergy R G) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpoint) (by positivity)
    _ ≤ _ := lemmaV_average_sqrt_products_le (descendantsAtDepth Q j)
      (fun R => vectorWeakHaarEnergy R F) (fun R => vectorPositiveHaarEnergy R G)
      (fun R _ => vectorWeakHaarEnergy_nonneg R F)
      (fun R _ => vectorPositiveHaarEnergy_nonneg R G)

end

end ASDExplicitGamma.Variational
