module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B16 : ModeBlockData :=
  ⟨⟨16, 17, (2336105906639056211/312500000000000000000 : ℚ), (7058397332560989/200000000000000000000 : ℚ)⟩, [
    (16, modeDataJ4M17)], (74755389012449798751/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b16 : entryChecks 4 bflatBlockJ4B16.entries = true := by
  simp only [entryChecks,bflatBlockJ4B16,List.all_cons,List.all_nil,
    mode_checked_j4_m17,Bool.and_self]
theorem block_mass_checked_j4_b16 : blockMassCheck bflatBlockJ4B16 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
