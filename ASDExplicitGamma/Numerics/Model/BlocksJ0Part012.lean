module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B12 : ModeBlockData :=
  ⟨⟨12, 13, (24449935143969557833/10000000000000000000000 : ℚ), (60529603190901719/25000000000000000000 : ℚ)⟩, [
    (12, modeDataJ0M13)], (3056241892996194729/1250000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b12 : entryChecks 0 bflatBlockJ0B12.entries = true := by
  simp only [entryChecks,bflatBlockJ0B12,List.all_cons,List.all_nil,
    mode_checked_j0_m13,Bool.and_self]
theorem block_mass_checked_j0_b12 : blockMassCheck bflatBlockJ0B12 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
