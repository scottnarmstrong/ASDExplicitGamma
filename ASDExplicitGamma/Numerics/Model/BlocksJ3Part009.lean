module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B9 : ModeBlockData :=
  ⟨⟨9, 10, (109333411523843563661/5000000000000000000000 : ℚ), (3125251599471761333/10000000000000000000000 : ℚ)⟩, [
    (9, modeDataJ3M10)], (218666823047687127321/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b9 : entryChecks 3 bflatBlockJ3B9.entries = true := by
  simp only [entryChecks,bflatBlockJ3B9,List.all_cons,List.all_nil,
    mode_checked_j3_m10,Bool.and_self]
theorem block_mass_checked_j3_b9 : blockMassCheck bflatBlockJ3B9 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
