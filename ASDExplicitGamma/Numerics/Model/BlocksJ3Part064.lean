module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part004

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B64 : ModeBlockData :=
  ⟨⟨64, 66, (40256486139529679969/5000000000000000000000 : ℚ), (2462245521272424533/10000000000000000000000 : ℚ)⟩, [
    (64, modeDataJ3M65),
    (65, modeDataJ3M66)], (1258015191860302499/156250000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b64 : entryChecks 3 bflatBlockJ3B64.entries = true := by
  simp only [entryChecks,bflatBlockJ3B64,List.all_cons,List.all_nil,
    mode_checked_j3_m65,
    mode_checked_j3_m66,Bool.and_self]
theorem block_mass_checked_j3_b64 : blockMassCheck bflatBlockJ3B64 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
