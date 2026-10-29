module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorCenteredSource
public import ASDExplicitGamma.Inverse.PureFluxGeneratorSharpTrace
public import ASDExplicitGamma.Main.HotPatchRowCopy
public import ASDExplicitGamma.Main.ObsLowerDistinctRow

/-! Observer-level (depth `m` source mesh) uncentered q3 source-column trace: the
Hilbert--Schmidt bound of the row energies and positive-series membership. -/

@[expose] public section
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Model ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Scalar
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- The sharp uncentered column coefficient on the depth-`m` mesh of `Q`. -/
noncomputable def obsColumnCoefficient (Q : TriadicCube 2) (m : ℕ) (b : ℝ)
    (L : {l : ℝ // 0 < l}) : ℝ :=
  Real.sqrt (b^2) + diagMeshRadius Q m * (36/25) *
      Real.sqrt ((156/5)*b^2/L.1^2) +
    (diagMeshRadius Q m)^2 * (57/200) *
      Real.sqrt ((46488/25)*b^2/L.1^4)

private theorem pureFluxMainQ3BasisFrameMultiplier_scale
    (n : ℤ) (b σ : ℝ) (L : {l : ℝ // 0 < l}) (l : whiteBasisIndex) :
    pureFluxMainQ3BasisFrameMultiplier n b σ L l =
      (σ⁻¹ : ℝ) • pureFluxMainQ3BasisFrameMultiplier n b 1 L l := by
  simp [pureFluxMainQ3BasisFrameMultiplier]

private theorem pureFluxMainQ3CenteredRow_vectorEnergy_scale
    (n : ℤ) (b σ : ℝ) (L : {l : ℝ // 0 < l}) (m : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet (originCube 2 n)))
    (U : TriadicCube 2) (l : whiteBasisIndex) :
    vectorPositiveHaarEnergy U (lemmaVPlanarRowField (diagInterpolant (originCube 2 n) m)
        (pureFluxMainQ3BasisFrameMultiplier n b σ L l)
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) p u)) =
      (σ⁻¹)^2 * vectorPositiveHaarEnergy U
        (lemmaVPlanarRowField (diagInterpolant (originCube 2 n) m)
          (pureFluxMainQ3BasisFrameMultiplier n b 1 L l)
          (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) p u)) := by
  let Q := originCube 2 n
  let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
  let I := diagInterpolant Q m
  let c := σ⁻¹
  have hη := pureFluxMainQ3BasisFrameMultiplier_scale n b σ L l
  have hdiv (x : Vec 2) :
      lemmaVPlanarWeakColumnDivergence
          (c • pureFluxMainQ3BasisFrameMultiplier n b 1 L l) x =
        c • lemmaVPlanarWeakColumnDivergence
          (pureFluxMainQ3BasisFrameMultiplier n b 1 L l) x := by
    simp only [lemmaVPlanarWeakColumnDivergence, H1Function.smul_grad,
      Pi.smul_apply]
    ext i
    simp [Homogenization.matVecMul, ASDExplicitGamma.Response.responsePlanarJ,
      Fin.sum_univ_two, smul_eq_mul]
    ring
  have hval (x : Vec 2) :
      (c • pureFluxMainQ3BasisFrameMultiplier n b 1 L l) x =
        c * (pureFluxMainQ3BasisFrameMultiplier n b 1 L l) x := by
    simp [H1Function.smul_toFun, smul_eq_mul]
  have hfield : (fun x => lemmaVPlanarRowField I
        (pureFluxMainQ3BasisFrameMultiplier n b σ L l) v x) =
      fun x => c • lemmaVPlanarRowField I
        (pureFluxMainQ3BasisFrameMultiplier n b 1 L l) v x := by
    funext x
    rw [hη]
    simp only [lemmaVPlanarRowField]
    rw [hval, hdiv]
    ext i
    simp [Pi.smul_apply, smul_eq_mul]
    ring_nf
  have hcomponent (i : Fin 2) :
      (fun x => lemmaVPlanarRowField I
        (pureFluxMainQ3BasisFrameMultiplier n b σ L l) v x i) =
        fun x => c * lemmaVPlanarRowField I
          (pureFluxMainQ3BasisFrameMultiplier n b 1 L l) v x i := by
    funext x
    have hx := congrFun hfield x
    simpa [Pi.smul_apply, smul_eq_mul] using congrFun hx i
  unfold vectorPositiveHaarEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show (fun x => lemmaVPlanarRowField I
      (pureFluxMainQ3BasisFrameMultiplier n b σ L l) v x i) =
      fun x => c * lemmaVPlanarRowField I
        (pureFluxMainQ3BasisFrameMultiplier n b 1 L l) v x i from hcomponent i]
  exact sensitivity_primalEnergy_smul U (Real.sqrt 3)
    (fun x => lemmaVPlanarRowField I
      (pureFluxMainQ3BasisFrameMultiplier n b 1 L l) v x i) c

private theorem pureFluxMainQ3RowEnergy_scale
    (n : ℤ) (b σ : ℝ) (L : {l : ℝ // 0 < l}) (m : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet (originCube 2 n)))
    (l : whiteBasisIndex) :
    pureFluxMainQ3RowEnergy n b σ L m p u l =
      (σ⁻¹)^2 * pureFluxMainQ3RowEnergy n b 1 L m p u l := by
  change descendantsAverage (originCube 2 n) m (fun U : TriadicCube 2 => vectorPositiveHaarEnergy U
      (lemmaVPlanarRowField (diagInterpolant (originCube 2 n) m)
        (pureFluxMainQ3BasisFrameMultiplier n b σ L l)
        (lemmaVAffinePotential
          (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) p u))) =
    (σ⁻¹)^2 * descendantsAverage (originCube 2 n) m (fun U => vectorPositiveHaarEnergy U
        (lemmaVPlanarRowField (diagInterpolant (originCube 2 n) m)
          (pureFluxMainQ3BasisFrameMultiplier n b 1 L l)
          (lemmaVAffinePotential
            (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) p u)))
  rw [show (fun U : TriadicCube 2 => vectorPositiveHaarEnergy U
      (lemmaVPlanarRowField (diagInterpolant (originCube 2 n) m)
        (pureFluxMainQ3BasisFrameMultiplier n b σ L l)
        (lemmaVAffinePotential
          (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) p u))) =
      fun U => (σ⁻¹)^2 * vectorPositiveHaarEnergy U
        (lemmaVPlanarRowField (diagInterpolant (originCube 2 n) m)
          (pureFluxMainQ3BasisFrameMultiplier n b 1 L l)
          (lemmaVAffinePotential
            (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) p u)) by
      funext U
      exact pureFluxMainQ3CenteredRow_vectorEnergy_scale n b σ L m p u U l]
  rw [descendantsAverage_mul_left]


/-- The actual centered source row is Hilbert--Schmidt on every aligned mesh,
with the exact normalized source coefficient and physical frame factor. -/
theorem obs_row_trace_bound (n : ℤ) (m : ℕ)
    (b σ : ℝ) (L : {l : ℝ // 0 < l})
    (p : Vec 2) (u : H10Function (openCubeSet (originCube 2 n))) :
    let Q := originCube 2 n
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    Summable (pureFluxMainQ3RowEnergy n b σ L m p u) ∧
      Real.sqrt (∑' l, pureFluxMainQ3RowEnergy n b σ L m p u l) ≤
        |σ⁻¹| * obsColumnCoefficient (originCube 2 n) m b L *
          Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) := by
  let Q := originCube 2 n
  let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
  let R := pureFluxMainQ3RowEnergy n b σ L m p u
  let C := |σ⁻¹| * obsColumnCoefficient (originCube 2 n) m b L *
    Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad)
  have hsharp (s : Finset whiteBasisIndex) :
      Real.sqrt (∑ l ∈ s, R l) ≤ C := by
    have hscale : (∑ l ∈ s, R l) =
        (σ⁻¹)^2 * ∑ l ∈ s, pureFluxMainQ3RowEnergy n b 1 L m p u l := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun l _ => pureFluxMainQ3RowEnergy_scale n b σ L m p u l)
    have hbase := pureFluxMainQ3Row_trace_finset_sharp n b L m p u s
    dsimp only at hbase
    rw [hscale, Real.sqrt_mul (sq_nonneg (σ⁻¹)), Real.sqrt_sq_eq_abs]
    simpa only [C, Q, v, obsColumnCoefficient, mul_assoc] using
      mul_le_mul_of_nonneg_left hbase (abs_nonneg (σ⁻¹))
  have hRnonneg (l : whiteBasisIndex) : 0 ≤ R l := by
    unfold R pureFluxMainQ3RowEnergy descendantsAverage
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun U _ => vectorPositiveHaarEnergy_nonneg U _
  have hC : 0 ≤ C := by
    have hr : 0 ≤ diagMeshRadius Q m := (diagMeshRadius_pos Q m).le
    have hcoef : 0 ≤ obsColumnCoefficient Q m b L := by
      unfold obsColumnCoefficient
      positivity
    exact mul_nonneg (mul_nonneg (abs_nonneg _) hcoef) (Real.sqrt_nonneg _)
  have hfinite (s : Finset whiteBasisIndex) : ∑ l ∈ s, R l ≤ C^2 := by
    have hs0 : 0 ≤ ∑ l ∈ s, R l := Finset.sum_nonneg fun l _ => hRnonneg l
    have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hsharp s) 2
    rw [Real.sq_sqrt hs0] at hs
    exact hs
  have hsum : Summable R := summable_of_sum_le hRnonneg hfinite
  have htotal : ∑' l, R l ≤ C^2 := Real.tsum_le_of_sum_le hRnonneg hfinite
  exact ⟨hsum, (Real.sqrt_le_iff).2 ⟨hC, htotal⟩⟩

/-- Every centered source-row coordinate has its genuine positive Haar series. -/
theorem obs_row_positive_series_unit
    (n : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) (m : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet (originCube 2 n)))
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) m)
    (l0 : whiteBasisIndex) :
    ∀ i : Fin 2, Summable (fun k => (Real.sqrt 3)^(k+1)*energy U
      (cubeIncrement U (k+1) (fun x => lemmaVPlanarRowField
        (diagInterpolant (originCube 2 n) m)
        (pureFluxMainQ3BasisFrameMultiplier n b 1 L l0)
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) p u) x i))) := by
  classical
  let Q := originCube 2 n
  let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
  let I := diagInterpolant Q m
  let s : Finset whiteBasisIndex := {l0}
  let l : s := ⟨l0, Finset.mem_singleton_self _⟩
  let C := pureFluxMainQ3FiniteRawRow whiteBasis s b L Q m v
  have hd := pureFluxMainQ3FiniteRawRow_tile_bound_hotcopy Q m p u s U hU b L
  have hmem : MemLp C 2 (normalizedCubeMeasure U) := hd.1
  have hsum : Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy U
      (hilbertCubeIncrement U (k+1) C)) := hd.2.1
  let η := pureFluxMainQ3BasisFrameMultiplier n b 1 L l
  let f := fun x i => η.toFun x * (I v).grad x i - η.grad x i * (v-I v).toFun x
  have heta : η = (mainQ3DirectionW2 Q b L (whiteBasis l)).value := by
    simp [η, pureFluxMainQ3BasisFrameMultiplier, Q]
  have hvalue (x : Vec 2) : η.toFun x =
      q3Convolution b L h3Zero (whiteBasis l) x := by
    rw [heta, mainQ3DirectionW2_value]
  have hgrad (x : Vec 2) (i : Fin 2) : η.grad x i =
      (fderiv ℝ (q3Convolution b L h3Zero (whiteBasis l)) x)
        (basisVec i) := by
    have hj := obsDirection_grad Q b L (whiteBasis l) x i
    have hderiv : (fderiv ℝ (q3Convolution b L h3Zero
        (whiteBasis l)) x) (basisVec i) =
        q3Convolution b L (mainQ3JetIndex (.first i))
          (whiteBasis l) x := by
      rw [q3Convolution_fderiv_basis b L h3Zero (by decide)]
      fin_cases i <;> norm_num [mainQ3JetIndex, h3Next, h3Zero,
        Model.Q3SpatialJet.count]
    rw [heta]
    exact hj.trans hderiv.symm
  have hcoord (x : Vec 2) (i : Fin 2) :
      (C x).ofLp (l,i) = f x i := by
    rw [pureFluxMainQ3FiniteRawRow_coordinate_hotcopy]
    simp only [f]
    rw [hvalue, hgrad]
    ring
  have hfield : (fun x => lemmaVPlanarRowField I η v x) =
      (fun x => planarQuarterTurn (f x)) := by
    rw [lemmaVH2_rowField_eq]
  have hp (i : Fin 2) : Summable (fun k => (Real.sqrt 3)^(k+1)*energy U
      (cubeIncrement U (k+1) (fun x => f x i))) := by
    have hc := main_hilbert_coordinate_summable U hmem hsum (l,i)
    have hf : (fun x => f x i) = fun x => (C x).ofLp (l,i) :=
      funext fun x => (hcoord x i).symm
    rw [hf]
    exact hc
  intro i
  change Summable (fun k => (Real.sqrt 3)^(k+1)*energy U
    (cubeIncrement U (k+1) (fun x => lemmaVPlanarRowField I η v x i)))
  have hfi : (fun x => lemmaVPlanarRowField I η v x i) =
      fun x => planarQuarterTurn (f x) i := by
    funext x
    exact congrFun (congrFun hfield x) i
  rw [hfi]
  exact positive_series_quarterTurn U f hp i

/-- Genuine positive-series membership for every physical centered source row. -/
theorem obs_row_positive_series
    (n : ℤ) (b σ : ℝ) (L : {l : ℝ // 0 < l}) (m : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet (originCube 2 n)))
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) m)
    (l : whiteBasisIndex) (i : Fin 2) :
    Summable (fun k => (Real.sqrt 3)^(k+1)*energy U
      (cubeIncrement U (k+1) (fun x => lemmaVPlanarRowField
        (diagInterpolant (originCube 2 n) m)
        (pureFluxMainQ3BasisFrameMultiplier n b σ L l)
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) p u) x i))) := by
  let Q := originCube 2 n
  let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
  let I := diagInterpolant Q m
  have hη := pureFluxMainQ3BasisFrameMultiplier_scale n b σ L l
  have hf : (fun x => lemmaVPlanarRowField I
      (pureFluxMainQ3BasisFrameMultiplier n b σ L l) v x i) =
      fun x => σ⁻¹ * lemmaVPlanarRowField I
        (pureFluxMainQ3BasisFrameMultiplier n b 1 L l) v x i := by
    simp_rw [hη, pureFluxPlanarRowField_smul]
    rfl
  change Summable (fun k => (Real.sqrt 3)^(k+1)*energy U
    (cubeIncrement U (k+1) (fun x => lemmaVPlanarRowField I
      (pureFluxMainQ3BasisFrameMultiplier n b σ L l) v x i)))
  rw [hf]
  exact pureFlux_positive_series_smul U _ (σ⁻¹)
    (obs_row_positive_series_unit n b L m p u U hU l i)


end
end ASDExplicitGamma.Inverse
