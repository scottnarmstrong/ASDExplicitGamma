module

public import ASDExplicitGamma.Scalar.DefectFinal2
public import ASDExplicitGamma.Scalar.RefFinal

/-! Successor of the two-slot final assembly and of the physical final theorem with the rough
`L^{128/127}` constant `R` as an explicit parameter:
`F_def = 3A²[b₊Λ + 1.026 ε₊ R]`. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse Filter
open scoped InnerProductSpace BigOperators ENNReal Topology

noncomputable section

/-- `F_def = 3A²[b₊ Λ + 1.026 ε₊ R]` with the rough constant `R` as a parameter. -/
def defectFdefR (a5 ξ mStar bOld εOld bNew εNew R : ℝ) : ℝ :=
  3 * defectA ^ 2 *
    (bNew * defectLambda a5 ξ mStar bOld εOld + (513 / 500 : ℝ) * εNew * R)

theorem two_slot_final_of_piecesRR {Ω 𝒪 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒪]
    (Rr : ℝ) (hRr : 0 ≤ Rr) (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure 𝒪) [IsProbabilityMeasure ν]
    (o : Ω → 𝒪) (z : Ω → ℕ → ℝ) (ho : Measurable o) (hz : Measurable z)
    (hcouple : μ.map (fun ω => (o ω, z ω)) = ν.prod standardGaussianInfinitePi)
    (Q : TriadicCube 2) (m : ℕ) (vol : ℝ) (hvol : 0 ≤ vol)
    (BF BG : ∀ n : ℕ, 𝒪 → Fin n → Fin n → TiledHaarField Q m)
    (hBF : ∀ n o i j, BF n o i j = BF n o j i) (hBG : ∀ n o i j, BG n o i j = BG n o j i)
    (hFmeas : ∀ n, Measurable (fun p : 𝒪 × (ℕ → ℝ) =>
      tiledPositiveEnergy Q m (psdDefectSource (BF n p.1) (fun i : Fin n => p.2 i))))
    (hGmeas : ∀ n, Measurable (fun p : 𝒪 × (ℕ → ℝ) =>
      tiledPositiveEnergy Q m (psdDefectSource (BG n p.1) (fun i : Fin n => p.2 i))))
    (v a5 ξ mStar εOld : ℝ) (hv : 0 ≤ v)
    (ΛF ΛG : ℕ → 𝒪 → ℝ) (hΛFm : ∀ n, Measurable (ΛF n)) (hΛGm : ∀ n, Measurable (ΛG n))
    (hΛFi : ∀ n, Integrable (ΛF n) ν) (hΛGi : ∀ n, Integrable (ΛG n) ν)
    (hΛF0 : ∀ n o, 0 ≤ ΛF n o) (hΛG0 : ∀ n o, 0 ≤ ΛG n o)
    (hwickF : ∀ n o, tiledPositiveEnergy Q m (∑ i, BF n o i i) +
        2 * ∑ i, ∑ j, tiledPositiveEnergy Q m (BF n o i j) ≤ 3 * defectA ^ 2 * v * ΛF n o)
    (hwickG : ∀ n o, tiledPositiveEnergy Q m (∑ i, BG n o i i) +
        2 * ∑ i, ∑ j, tiledPositiveEnergy Q m (BG n o i j) ≤ 3 * defectA ^ 2 * v * ΛG n o)
    (Bs R : Ω → ℝ) (hRm : Measurable R)
    (hBs0 : ∀ ω, 0 ≤ Bs ω) (hBR : ∀ ω, Bs ω ≤ 14103 / 10000 + R ω) (hR0 : ∀ ω, 0 ≤ R ω)
    (hΛ1 : ∀ n, ∫ o, (ΛF n o + ΛG n o) ∂ν ≤ v * defectLambda a5 ξ mStar (14103 / 10000) εOld)
    (hΛq : ∀ n, eLpNorm (fun o => ΛF n o + ΛG n o) (ENNReal.ofReal (128 / 127)) ν ≤
      ENNReal.ofReal (v * Rr))
    (hR : eLpNorm R 128 μ ≤ ENNReal.ofReal (5 / 10 ^ 24))
    (hBH : ∀ n, Integrable (fun ω => Bs ω *
      (tiledPositiveEnergy Q m (psdDefectSource (BF n (o ω)) (fun i : Fin n => z ω i)) +
       tiledPositiveEnergy Q m (psdDefectSource (BG n (o ω)) (fun i : Fin n => z ω i)))) μ)
    (Dn : ℕ → Ω → ℝ) (Dinf : Ω → ℝ)
    (hDnm : ∀ n, Measurable (Dn n)) (hDinfm : Measurable Dinf)
    (hpath : ∀ n ω, Dn n ω ≤ (44 / 25 : ℝ) * (vol * (Bs ω *
      (tiledPositiveEnergy Q m (psdDefectSource (BF n (o ω)) (fun i : Fin n => z ω i)) +
       tiledPositiveEnergy Q m (psdDefectSource (BG n (o ω)) (fun i : Fin n => z ω i))))))
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => Dn n ω) atTop (𝓝 (Dinf ω)))
    (hLam0 : 0 ≤ defectLambda a5 ξ mStar (14103 / 10000) εOld) :
    Integrable (fun ω => max (Dinf ω) 0) μ ∧
      ∫ ω, max (Dinf ω) 0 ∂μ ≤
        vol * ((44 / 25 : ℝ) * v ^ 2 *
          defectFdefR a5 ξ mStar (14103 / 10000) εOld (14103 / 10000) (5 / 10 ^ 24) Rr) := by
  set A := defectA with hA
  set Lh := defectLambda a5 ξ mStar (14103 / 10000) εOld with hLh
  set rough : ℝ := Rr with hrough
  have hrough0 : 0 ≤ rough := hRr
  have hκ2 : 0 ≤ 3 * A ^ 2 * v := by positivity
  have hLq : 0 ≤ v * rough := by positivity
  obtain ⟨hint, hbd⟩ := two_slot_of_pieces μ ν o z ho hz hcouple Q m BF BG hBF hBG hFmeas
    hGmeas ΛF ΛG hΛFm hΛGm hΛFi hΛGi hΛF0 hΛG0
    (3 * A ^ 2 * v) hκ2 hwickF hwickG Bs R hRm (14103 / 10000) (5 / 10 ^ 24) (v * Lh) (v * rough)
    (by norm_num) (by positivity) hLq hBs0 hBR hR0 hΛ1 hΛq hR hBH ((44 / 25) * vol)
    (by positivity) Dn Dinf hDnm hDinfm
    (fun n ω => by have := hpath n ω; linarith [this, show (44/25:ℝ) * (vol * (Bs ω * _)) = (44 / 25 * vol) * (Bs ω * _) by ring]) hlim
  refine ⟨hint, hbd.trans ?_⟩
  have hCp : (1 + Real.sqrt 15) ^ (2 / (128 : ℝ)) ≤ (513 / 500 : ℝ) := by
    norm_num only [show 2 / (128 : ℝ) = (1 / 64 : ℝ) by norm_num]
    exact Numerics.Scalar.f7_factors_source.2.1.le
  have hε : (0 : ℝ) ≤ 5 / 10 ^ 24 := by positivity
  have h1 : (5 / 10 ^ 24 : ℝ) * ((1 + Real.sqrt 15) ^ (2 / (128 : ℝ)) * (v * rough)) ≤
      (5 / 10 ^ 24 : ℝ) * ((513 / 500) * (v * rough)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCp hLq) hε
  have h2 : 3 * A ^ 2 * v * ((14103 / 10000) * (v * Lh) +
      (5 / 10 ^ 24) * ((1 + Real.sqrt 15) ^ (2 / (128 : ℝ)) * (v * rough))) ≤
      3 * A ^ 2 * v * ((14103 / 10000) * (v * Lh) +
      (5 / 10 ^ 24) * ((513 / 500) * (v * rough))) :=
    mul_le_mul_of_nonneg_left (by linarith) hκ2
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 44 / 25 * vol)
  refine h3.trans (le_of_eq ?_)
  simp only [defectFdefR, hLh, hrough, hA]
  ring


end

end ASDExplicitGamma.Scalar
