module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B41 : ModeBlockData :=
  ⟨⟨41, 42, (115283390784402383113/10000000000000000000000 : ℚ), (2120429861224779467/10000000000000000000000 : ℚ)⟩, [
    (41, modeDataJ3M42)], (14410423848050297889/1250000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b41 : entryChecks 3 bflatBlockJ3B41.entries = true := by
  simp only [entryChecks,bflatBlockJ3B41,List.all_cons,List.all_nil,
    mode_checked_j3_m42,Bool.and_self]
theorem block_mass_checked_j3_b41 : blockMassCheck bflatBlockJ3B41 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
