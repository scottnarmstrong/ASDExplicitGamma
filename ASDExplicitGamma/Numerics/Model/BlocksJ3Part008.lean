module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B8 : ModeBlockData :=
  ⟨⟨8, 9, (220225373460151646727/10000000000000000000000 : ℚ), (784860354206203003/2500000000000000000000 : ℚ)⟩, [
    (8, modeDataJ3M9)], (110112686730075823363/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b8 : entryChecks 3 bflatBlockJ3B8.entries = true := by
  simp only [entryChecks,bflatBlockJ3B8,List.all_cons,List.all_nil,
    mode_checked_j3_m9,Bool.and_self]
theorem block_mass_checked_j3_b8 : blockMassCheck bflatBlockJ3B8 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
