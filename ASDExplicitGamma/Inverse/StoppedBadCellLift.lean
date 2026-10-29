module

public import ASDExplicitGamma.Inverse.StoppedElementaryCoverage
public import ASDExplicitGamma.Inverse.StoppedQ3Marks

/-! Actual cell failures lift to the same parent-and-two-generation blocked
event used by the proved stopped-cluster estimate. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization ASDExplicitGamma.Gaussian Algsuperdiff.Section3
noncomputable section

/-- Literal bad-cell event: raw history at its own old label or a failed
derivative gate at a positive later shell, in that same cell's true frame. -/
def cellFailure (M : ABKModel 2) (τ η : ℝ) (V : TriadicCube 2) :
    Set (Cutoff.CutoffSample 2) :=
  {ω | ENNReal.ofReal τ < clippedCellRawHistory M (V.scale+40) V ω ∨
    ∃ n : ℕ, η*(3:ℝ)^(-((n:ℝ)+1)/8) <
      waveGateDerivativeSize (cubeCenter V) (cubeScaleFactor V)
        (Annealed.sigmaBar M (V.scale+40):ℝ) (ω.val (V.scale+40+(n+1:ℤ)))}

/-- A raw positive mark occupies its own site in the actual aligned
activation model, with the entire positive cube retained. -/
theorem raw_positive_mark_occupied {Ω : Type*} (B : PlanarMarks Ω)
    (ω : Ω) (n : ℕ) (x : BlockSite) (hx : ω ∈ B.positiveMark n x) :
    x ∈ markedOccupied B ω := by
  have hside : 0 < 3^(n+1) := by positivity
  have hcube := mem_own_aligned_cube (3^(n+1)) hside x
  refine Or.inr ⟨n,alignedCubeIndex (3^(n+1)) x,?_,hcube⟩
  exact Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr
    ⟨(mem_cube_sites _ _ _).mpr hcube,hx⟩⟩

/-- A bad descendant through exactly the two allowed generations marks its
actual ancestor's block. No new diameter or independence premise is used. -/
theorem q3_bad_descendant_occupied (M : ABKModel 2) (j : ℤ) (τ η : ℝ)
    (x : BlockSite) {r : ℕ} (hr : r ≤ 2) {V : TriadicCube 2}
    (hV : V ∈ descendantsAtDepth (⟨j,x⟩ : TriadicCube 2) r)
    (ω : Cutoff.CutoffSample 2) (hbad : ω ∈ cellFailure M τ η V) :
    fineBlockIndex x ∈ markedOccupied (q3PlanarMarks M j τ η) ω := by
  obtain ⟨i,hi⟩ := elementary_cubes_cover j x hr hV
  rcases hbad with hhist | ⟨n,hn⟩
  · apply Or.inl
    change ∃ i, ENNReal.ofReal τ <
      clippedCellRawHistory M ((elementaryCube j (fineBlockIndex x) i).scale+40)
        (elementaryCube j (fineBlockIndex x) i) ω
    exact ⟨i,by rw [hi]; exact hhist⟩
  · apply raw_positive_mark_occupied _ ω n
    change ∃ i, η*(3:ℝ)^(-((n+1:ℕ):ℝ)/8) <
      waveGateDerivativeSize (cubeCenter (elementaryCube j (fineBlockIndex x) i))
        (cubeScaleFactor (elementaryCube j (fineBlockIndex x) i))
        (Annealed.sigmaBar M ((elementaryCube j (fineBlockIndex x) i).scale+40):ℝ)
        (ω.val ((elementaryCube j (fineBlockIndex x) i).scale+40+(n+1:ℕ)))
    refine ⟨i,?_⟩
    rw [hi]
    simpa only [Nat.cast_add,Nat.cast_one,Int.cast_add,Int.cast_natCast,Int.cast_one] using hn

end
end ASDExplicitGamma.Inverse
