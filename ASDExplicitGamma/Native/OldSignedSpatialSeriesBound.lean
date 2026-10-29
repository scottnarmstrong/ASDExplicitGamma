module

public import ASDExplicitGamma.Native.OldSignedCellAverage

/-! Complete physical mode bounds retain finite spatial averages of joint
cell factors. This introduces neither independence nor a maximal cell. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization
noncomputable section

/-- A signed complete-mode estimate on every cell yields the same bound
under the actual finite physical average. -/
theorem old_signed_cell_average_series_bound {I : Type*} (Q : TriadicCube 2) (depth : ℕ)
    (f : I → OldSignedCellIndex Q depth → ℝ) (B : OldSignedCellIndex Q depth → ℝ)
    (hs : ∀ U,Summable (fun n => f n U)) (hb : ∀ U,|∑' n,f n U|≤B U) :
    Summable (fun n => oldSignedCellAverage Q depth (f n)) ∧
      |∑' n,oldSignedCellAverage Q depth (f n)|≤oldSignedCellAverage Q depth B := by
  obtain ⟨hh,he⟩ := old_signed_cell_average_series Q depth f hs
  refine ⟨hh,?_⟩
  rw [he]
  exact (old_signed_cell_average_abs_le Q depth _).trans
    (old_signed_cell_average_mono Q depth hb)

/-- A complete upper energy bound likewise retains the actual cell factors
and all signed affine contributions. -/
theorem old_signed_cell_average_series_upper {I : Type*} (Q : TriadicCube 2) (depth : ℕ)
    (f : I → OldSignedCellIndex Q depth → ℝ) (B : OldSignedCellIndex Q depth → ℝ)
    (hs : ∀ U,Summable (fun n => f n U)) (hb : ∀ U,(∑' n,f n U)≤B U) :
    Summable (fun n => oldSignedCellAverage Q depth (f n)) ∧
      (∑' n,oldSignedCellAverage Q depth (f n))≤oldSignedCellAverage Q depth B := by
  obtain ⟨hh,he⟩ := old_signed_cell_average_series Q depth f hs
  exact ⟨hh,he.trans_le (old_signed_cell_average_mono Q depth hb)⟩

end
end ASDExplicitGamma.Native
