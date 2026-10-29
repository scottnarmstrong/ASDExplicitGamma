module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B11 : ModeBlockData :=
  ⟨⟨11, 12, (287962419988639649/100000000000000000000 : ℚ), (5692788249878229367/2000000000000000000000 : ℚ)⟩, [
    (11, modeDataJ0M12)], (28796241998863964899/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b11 : entryChecks 0 bflatBlockJ0B11.entries = true := by
  simp only [entryChecks,bflatBlockJ0B11,List.all_cons,List.all_nil,
    mode_checked_j0_m12,Bool.and_self]
theorem block_mass_checked_j0_b11 : blockMassCheck bflatBlockJ0B11 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
