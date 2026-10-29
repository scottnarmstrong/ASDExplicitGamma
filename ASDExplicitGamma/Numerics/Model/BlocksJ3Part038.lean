module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B38 : ModeBlockData :=
  ⟨⟨38, 39, (25375803341822581933/2000000000000000000000 : ℚ), (1120638249096533189/5000000000000000000000 : ℚ)⟩, [
    (38, modeDataJ3M39)], (3964969272159778427/312500000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b38 : entryChecks 3 bflatBlockJ3B38.entries = true := by
  simp only [entryChecks,bflatBlockJ3B38,List.all_cons,List.all_nil,
    mode_checked_j3_m39,Bool.and_self]
theorem block_mass_checked_j3_b38 : blockMassCheck bflatBlockJ3B38 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
