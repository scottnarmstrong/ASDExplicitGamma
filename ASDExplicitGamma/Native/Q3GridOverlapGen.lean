module

public import ASDExplicitGamma.Native.Q3GridOverlap

/-! The overlap-count estimate without the hypothesis that the kernel is
smaller than the grid: when the kernel width exceeds the grid, the factor
`q3GridOverlapFactor s n` equals `1` (natural-number truncation) and the bound
is the trivial one. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization Set ASDExplicitGamma.Gaussian

theorem q3GridActiveFinset_card_ratio_le_Gen (s n : ℕ) (hn : 1 ≤ n)
    (x : Vec 2) :
    ((q3GridActiveFinset s n x).card : ℝ) / ((3 : ℝ)^s)^2 ≤ q3GridOverlapFactor s n := by
  by_cases hns : n ≤ s
  · exact q3GridActiveFinset_card_ratio_le s n hn hns x
  · have hsub : s - n = 0 := Nat.sub_eq_zero_of_le (by omega)
    have hN : 0 < ((3 : ℝ)^s)^2 := by positivity
    have hcard : ((q3GridActiveFinset s n x).card : ℝ) ≤ ((3 : ℝ)^s)^2 := by
      have h1 := Finset.card_le_univ (q3GridActiveFinset s n x)
      have h2 : (q3GridActiveFinset s n x).card ≤ (3^s)^2 := by
        simpa [pow_two] using h1
      exact_mod_cast h2
    have hone : ((q3GridActiveFinset s n x).card : ℝ) / ((3 : ℝ)^s)^2 ≤ 1 :=
      (div_le_iff₀ hN).2 (by simpa using hcard)
    have hfac : q3GridOverlapFactor s n = 1 := by
      unfold q3GridOverlapFactor
      rw [hsub]
      norm_num
    rw [hfac]
    exact hone

end ASDExplicitGamma.Native
