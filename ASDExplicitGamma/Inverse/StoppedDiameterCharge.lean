module

public import ASDExplicitGamma.Inverse.StoppedClusterSpan

/-! The source integer-diameter square payment and exact planar charge
S_b=2700*3^(2b), with the active-cell baseline retained. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open scoped ENNReal
noncomputable section

theorem real_diameter_one_of_near_occupied {Ω : Type*} (B : PlanarMarks Ω) (ω : Ω)
    (x r : BlockSite) (hr : ∀ d, |r d-x d| ≤ 2)
    (hfinite : diameterField B ω x ≠ ∞) (hocc : r ∈ markedOccupied B ω) :
    1 ≤ realDiameterField B x ω := by
  have hm : r ∈ clusterSites B ω r := ⟨hocc,hocc,SimpleGraph.Reachable.rfl⟩
  simpa only [blockDistance,sub_self,Int.natAbs_zero,max_self,zero_add,Nat.cast_one] using
    real_diameter_member_pair B ω x r hr hfinite hm hm

/-- The literal source diameter is zero or at least one. Its ordinary real
form does not introduce fractional positive diameters. -/
theorem real_diameter_zero_or_one_le {Ω : Type*} (B : PlanarMarks Ω) (ω : Ω)
    (x : BlockSite) (hfinite : diameterField B ω x ≠ ∞) :
    realDiameterField B x ω = 0 ∨ 1 ≤ realDiameterField B x ω := by
  classical
  by_cases hh : ∃ r ∈ diameterRoots x, r ∈ markedOccupied B ω
  · obtain ⟨r,hr,hocc⟩ := hh
    have hnear : ∀ d, |r d-x d| ≤ 2 := by
      intro d
      have hd := (mem_cube_sites _ _ _).mp hr d
      change x d-2 ≤ r d ∧ r d < x d-2+(5:ℤ) at hd
      rw [abs_le]
      omega
    exact Or.inr (real_diameter_one_of_near_occupied B ω x r hnear hfinite hocc)
  · have hz : diameterField B ω x = 0 := by
      apply le_antisymm _ zero_le
      unfold diameterField
      apply Finset.sup_le
      intro r hr
      unfold clusterDiameter
      apply iSup_le
      intro u
      apply iSup_le
      intro v
      by_cases hp : u ∈ clusterSites B ω r ∧ v ∈ clusterSites B ω r
      · exact False.elim (hh ⟨r,hr,hp.1.1⟩)
      · simp only [Set.indicator,Set.mem_ofPred_eq,hp,ite_false,le_refl]
    exact Or.inl (by rw [realDiameterField,hz,ENNReal.toReal_zero])

theorem real_diameter_le_square {Ω : Type*} (B : PlanarMarks Ω) (ω : Ω)
    (x : BlockSite) (hfinite : diameterField B ω x ≠ ∞) :
    realDiameterField B x ω ≤ (realDiameterField B x ω)^2 := by
  rcases real_diameter_zero_or_one_le B ω x hfinite with hz | hz
  · rw [hz]
    norm_num
  · have hh := mul_nonneg (show 0 ≤ realDiameterField B x ω by unfold realDiameterField; positivity)
      (sub_nonneg.mpr hz)
    nlinarith only [hh]

/-- Literal source planar gradient/active charge. -/
def planarGradientCharge (b : ℕ) : ℝ := 2700*(3:ℝ)^(2*b)

private theorem two_group_square (c z w : ℝ) (hc : 0 ≤ c) (hz : z ≤ z^2) (hw : w ≤ w^2) :
    (1+c*(z+w))^2 ≤ 1+(2*c^2+2*c)*(z^2+w^2) := by
  have hlin := mul_le_mul_of_nonneg_left (add_le_add hz hw) (show 0 ≤ 2*c by positivity)
  have hcs : (z+w)^2 ≤ 2*(z^2+w^2) := by nlinarith only [sq_nonneg (z-w)]
  have hquad := mul_le_mul_of_nonneg_left hcs (sq_nonneg c)
  nlinarith only [hlin,hquad]

/-- Exact source two-mesh inequality (4.3); the square payment is valid for
the actual diameter fields because they are zero or at least one. -/
theorem two_mesh_square_charge (b : ℕ) (z w : ℝ) (hz : z ≤ z^2) (hw : w ≤ w^2) :
    (1+36*(3:ℝ)^b*(z+w))^2 ≤ 1+planarGradientCharge b*(z^2+w^2) := by
  have ht : 1 ≤ (3:ℝ)^b := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 3)
  have hm := mul_nonneg (show 0 ≤ (3:ℝ)^b by positivity) (sub_nonneg.mpr ht)
  have hc : 2*(36*(3:ℝ)^b)^2+2*(36*(3:ℝ)^b) ≤ planarGradientCharge b := by
    unfold planarGradientCharge
    rw [show 2*b=b*2 by omega,pow_mul]
    nlinarith only [hm,sq_nonneg ((3:ℝ)^b)]
  exact (two_group_square (36*(3:ℝ)^b) z w (by positivity) hz hw).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hc (by positivity)))

/-- Exact source active-cell payment (AC), once an actual neighboring bad
component gives a diameter at least one on one of the three resolutions. -/
theorem active_three_resolution_charge (b : ℕ) (Z : Fin 3 → ℝ)
    (hactive : ∃ e, 1 ≤ Z e) :
    1+planarGradientCharge b*(∑ e, (Z e)^2) ≤
      (planarGradientCharge b+1)*(∑ e, (Z e)^2) := by
  obtain ⟨e,he⟩ := hactive
  have hs : 1 ≤ ∑ k, (Z k)^2 := by
    have h1 : 1 ≤ (Z e)^2 := by nlinarith only [he]
    exact h1.trans (Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ e))
  nlinarith only [hs]

end
end ASDExplicitGamma.Inverse
