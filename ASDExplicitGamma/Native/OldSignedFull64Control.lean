module

public import ASDExplicitGamma.Native.OldSignedFull64Generator
public import ASDExplicitGamma.Native.OldSignedRemainderBrace
public import ASDExplicitGamma.Main.EnvelopeHFixedFrameGenerator

/-! The actual depthwise full64 control and its retained spatial decay. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Set Homogenization MeasureTheory Gaussian Inverse Scalar Variational Triadic Algsuperdiff.Section3
noncomputable section

/-- The exact deterministic coefficient in the fixed-old-frame p=20 row,
at cell depth `j` below the five-level OLD parent. -/
noncomputable def oldSignedP20Full64Control
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (j : ℕ) : ℝ :=
  let q : ℤ := m - ((5 + j : ℕ) : ℤ)
  let s : ℕ := 6 + j
  let Q := originCube 2 q
  let σ : ℝ := Annealed.sigmaBar M m
  let κ := rawTraceRemainderKappaF
    (cubeScaleFactor Q / (q3ModelLength (q + (s : ℤ))).1)
    (diagMeshRadius Q (pureFluxBankSourceDepth s) /
      (q3ModelLength (q + (s : ℤ))).1)
  let κB := rawTraceRemainderB
    (cubeScaleFactor Q / (q3ModelLength (q + (s : ℤ))).1)
    (diagMeshRadius Q (pureFluxBankSourceDepth s) /
      (q3ModelLength (q + (s : ℤ))).1)
  let μR := rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0
    (rawTraceRemainderA (pureFluxCovarianceRho 0 (s - 1))
      (pureFluxCovarianceDelta 0 (s - 1)))
    (rawTraceRemainderB (pureFluxCovarianceRho 0 (s - 1))
      (pureFluxCovarianceDelta 0 (s - 1)))
  let v := (q3ModelAmplitude M h (q + (s : ℤ))) ^ 2 / σ ^ 2
  let C := rawTraceOldFrameP20LocalClock M.gamma s
  let fCap := oldSignedP20Full64Cap M.gamma s
  v * ((78 + 76 * κ) * (C * (3683 / 2500 : ℝ)) +
    2 * κ * (C * (3683 / 2500 : ℝ)) * fCap +
    (μR + 38 * (κB ^ 2 + κ)) * (C * (3683 / 2500 : ℝ)) ^ 2 * fCap)

/-- For every cell depth `q=m-5-j`, the p=20 derivative row is supplied by
the actual raw-shell producer, with the frame held at `sigmaBar M m` and
the inserted shell at `m+1`. No abstract generator estimate is assumed. -/
theorem old_signed_full64_depth_generator
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n) (j : ℕ) :
    ∀ t ∈ Ioo (0 : ℝ) 1,
      deriv (modelTracePowerHeatAverage
        (m - ((5 + j : ℕ) : ℤ)) M m 20) t ≤
        20 * modelTracePowerHeatAverage
          (m - ((5 + j : ℕ) : ℤ)) M m 20 t ^ ((19 : ℝ) / 20) *
          oldSignedP20Full64Control M h m j := by
  let q : ℤ := m - ((5 + j : ℕ) : ℤ)
  let s : ℕ := 6 + j
  have hqs : q + (s : ℤ) = m + 1 := by
    dsimp [q, s]
    omega
  have hs : 6 ≤ s := by dsimp [s]; omega
  have hrow := old_signed_p20_generator_full64
    M h hM hg q m s hqs hs hpast
  intro t ht
  simpa [oldSignedP20Full64Control, q, s, hqs] using hrow t ht


/-- The actual radius and source mesh both equal 3^(-6-j) on the
six-generation OLD depth sequence. -/
theorem old_signed_full64_depth_parameters (q : ℤ) (j : ℕ) :
    let z := (1/3:ℝ)^j
    cubeScaleFactor (originCube 2 q)/(q3ModelLength (q+((6+j:ℕ):ℤ))).1=z/729 ∧
    diagMeshRadius (originCube 2 q) (pureFluxBankSourceDepth (6+j))/
      (q3ModelLength (q+((6+j:ℕ):ℤ))).1=z/729 ∧
    pureFluxCovarianceRho 0 (6+j-1)=z/729 ∧
    pureFluxCovarianceDelta 0 (6+j-1)=z/729 := by
  intro z
  have hs := Main.main_rawShell_fixed_old_frame_p20_source_scales q (6+j) (by omega)
  have hr : pureFluxCovarianceRho 0 (6+j-1)=z/729 := by
    unfold pureFluxCovarianceRho
    rw [show 0+(6+j-1)+1=6+j by omega,pow_add]
    norm_num
    dsimp [z]
    ring
  have hz : z≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hd : pureFluxCovarianceDelta 0 (6+j-1)=z/729 := by
    rw [pureFluxCovarianceDelta,hr,min_eq_right]
    linarith only [hz]
  exact ⟨hs.1.trans hr,hs.2.trans hd,hr,hd⟩

/-- Retain the squared depth decay in the physical full64 generator.
Only its inverse trace term uses the slower frame clock. -/
theorem old_signed_full64_control_decay (M : ABKModel 2) (h : ℝ) (n : ℤ) (j : ℕ) :
    oldSignedP20Full64Control M h n j ≤
      ((q3ModelAmplitude M h (n+1))^2/(Annealed.sigmaBar M n:ℝ)^2)*
        (120*rawTraceOldFrameP20LocalClock M.gamma (6+j)+
          (7/125)*((1/3:ℝ)^j)^2*rawTraceOldFrameP20LocalClock M.gamma (6+j)^2*
            oldSignedP20Full64Cap M.gamma (6+j)) := by
  let q : ℤ := n-((5+j:ℕ):ℤ)
  have hJ : q+((6+j:ℕ):ℤ)=n+1 := by dsimp [q]; omega
  have hp := old_signed_full64_depth_parameters q j
  dsimp only at hp
  have hz : 0≤(1/3:ℝ)^j := pow_nonneg (by norm_num) j
  have hz1 : (1/3:ℝ)^j≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hg := M.shellPrefix.gamma_pos.le
  have hC : 1≤rawTraceOldFrameP20LocalClock M.gamma (6+j) := by
    unfold rawTraceOldFrameP20LocalClock
    apply Real.one_le_rpow (by norm_num)
    have hs : (1:ℝ)≤((6+j:ℕ):ℝ) := by exact_mod_cast (show 1≤6+j by omega)
    positivity
  have hF : 0≤oldSignedP20Full64Cap M.gamma (6+j) := by
    unfold oldSignedP20Full64Cap
    positivity
  have hbrace := old_signed_full64_generator_brace ((1/3:ℝ)^j)
    (rawTraceOldFrameP20LocalClock M.gamma (6+j)) (oldSignedP20Full64Cap M.gamma (6+j))
    hz hz1 hC hF
  unfold oldSignedP20Full64Control
  change ((q3ModelAmplitude M h (q+((6+j:ℕ):ℤ)))^2/(Annealed.sigmaBar M n:ℝ)^2)*_≤_
  rw [hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,hJ]
  exact mul_le_mul_of_nonneg_left hbrace (div_nonneg (sq_nonneg _) (sq_nonneg _))

end
end ASDExplicitGamma.Native
