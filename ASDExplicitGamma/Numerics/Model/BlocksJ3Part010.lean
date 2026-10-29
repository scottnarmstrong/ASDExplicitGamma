module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B10 : ModeBlockData :=
  ⟨⟨10, 11, (216955930527947817101/10000000000000000000000 : ℚ), (777412472587454523/2500000000000000000000 : ℚ)⟩, [
    (10, modeDataJ3M11)], (2169559305279478171/100000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b10 : entryChecks 3 bflatBlockJ3B10.entries = true := by
  simp only [entryChecks,bflatBlockJ3B10,List.all_cons,List.all_nil,
    mode_checked_j3_m11,Bool.and_self]
theorem block_mass_checked_j3_b10 : blockMassCheck bflatBlockJ3B10 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
