module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part004

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B67 : ModeBlockData :=
  ⟨⟨70, 72, (27869706010998497687/5000000000000000000000 : ℚ), (2094723060226844417/10000000000000000000000 : ℚ)⟩, [
    (70, modeDataJ3M71),
    (71, modeDataJ3M72)], (13934853005499248843/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b67 : entryChecks 3 bflatBlockJ3B67.entries = true := by
  simp only [entryChecks,bflatBlockJ3B67,List.all_cons,List.all_nil,
    mode_checked_j3_m71,
    mode_checked_j3_m72,Bool.and_self]
theorem block_mass_checked_j3_b67 : blockMassCheck bflatBlockJ3B67 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
