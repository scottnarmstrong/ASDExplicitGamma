module

public import ASDExplicitGamma.Cold.PlateauTopBlock
public import ASDExplicitGamma.Cold.NeumannFinePotential

/-! # Fine-potential decay and the actual fine transport entries -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- The square-root form of the proved fine Neumann-potential estimate. -/
theorem neumann_fine_L2_bridge (Q : TriadicCube 2) (r : ℕ)
    {G : Vec 2 → Vec 2} (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hz : ∀ i, cubeProjection Q r (fun x => G x i) = 0)
    {u : H1Function (openCubeSet Q)}
    (hu : Support.Localization.IsNeumannPrimitive Q G u) :
    Real.sqrt (energy Q u.toFun) ≤ cubeScaleFactor Q / ((3 : ℝ) ^ r * Real.pi) *
      Real.sqrt (squareVectorEnergy Q G) := by
  have hℓ := cubeScaleFactor_pos' Q
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · rw [mul_pow, Real.sq_sqrt (squareVectorEnergy_nonneg Q G)]
    convert neumann_fine_L2_bridge_sq Q r hG hz hu using 1
    congr 1
    rw [div_pow, mul_pow, ← pow_mul, Nat.mul_comm r 2, pow_mul]
    norm_num

/-- A fine source gives the exact `9⁻ᵏ` decay of its actual transport entry. -/
theorem abs_plateauTransport_fine_left_le (Q : TriadicCube 2) (k : ℕ)
    {G : Vec 2 → Vec 2} (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hz : ∀ i, cubeProjection Q (2*k) (fun x => G x i) = 0)
    {u : H1Function (openCubeSet Q)} (hu : Support.Localization.IsNeumannPrimitive Q G u)
    (w : H1Function (openCubeSet Q)) :
    |plateauTransport Q u w| ≤ (48 / (7 * Real.pi)) * (1 / 9 : ℝ) ^ k *
      Real.sqrt (squareVectorEnergy Q G) * Real.sqrt (squareVectorEnergy Q w.grad) := by
  have hℓ := cubeScaleFactor_pos' Q
  have h1 := abs_plateauTransport_le Q u w
  have h2 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (neumann_fine_L2_bridge Q (2*k) hG hz hu)
      (by positivity : 0 ≤ 48 / (7 * cubeScaleFactor Q)))
    (Real.sqrt_nonneg (squareVectorEnergy Q w.grad))
  refine h1.trans (h2.trans_eq ?_)
  have hp : (3 : ℝ) ^ (2*k) = 9 ^ k := by rw [pow_mul]; norm_num
  rw [hp, one_div_pow]
  field_simp [hℓ.ne']

/-- Two actual fine sources give the symmetric decay at the larger fine scale. -/
theorem abs_plateauTransport_fine_pair_le (Q : TriadicCube 2) (k l : ℕ)
    {G H : Vec 2 → Vec 2}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hH : ∀ i, MemLp (fun x => H x i) 2 (normalizedCubeMeasure Q))
    (hGz : ∀ i, cubeProjection Q (2*k) (fun x => G x i) = 0)
    (hHz : ∀ i, cubeProjection Q (2*l) (fun x => H x i) = 0)
    {u w : H1Function (openCubeSet Q)}
    (hu : Support.Localization.IsNeumannPrimitive Q G u)
    (hw : Support.Localization.IsNeumannPrimitive Q H w)
    (hGu : squareVectorEnergy Q u.grad ≤ squareVectorEnergy Q G)
    (hHw : squareVectorEnergy Q w.grad ≤ squareVectorEnergy Q H) :
    |plateauTransport Q u w| ≤ (48 / (7 * Real.pi)) * (1 / 9 : ℝ) ^ (max k l) *
      Real.sqrt (squareVectorEnergy Q G) * Real.sqrt (squareVectorEnergy Q H) := by
  have hC : 0 ≤ (48 : ℝ) / (7 * Real.pi) := by positivity
  by_cases hkl : l ≤ k
  · rw [max_eq_left hkl]
    exact (abs_plateauTransport_fine_left_le Q k hG hGz hu w).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hHw) (by positivity))
  · rw [max_eq_right (le_of_not_ge hkl)]
    rw [← abs_neg (plateauTransport Q u w), ← plateauTransport_swap]
    have h := (abs_plateauTransport_fine_left_le Q l hH hHz hw u).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hGu) (by positivity))
    convert h using 1
    ring

end ASDExplicitGamma.Cold
