module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part004

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B66 : ModeBlockData :=
  ⟨⟨68, 70, (15833532353746031127/2500000000000000000000 : ℚ), (2212069416378950347/10000000000000000000000 : ℚ)⟩, [
    (68, modeDataJ3M69),
    (69, modeDataJ3M70)], (31667064707492062253/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b66 : entryChecks 3 bflatBlockJ3B66.entries = true := by
  simp only [entryChecks,bflatBlockJ3B66,List.all_cons,List.all_nil,
    mode_checked_j3_m69,
    mode_checked_j3_m70,Bool.and_self]
theorem block_mass_checked_j3_b66 : blockMassCheck bflatBlockJ3B66 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
