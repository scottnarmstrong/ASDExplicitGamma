module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B13 : ModeBlockData :=
  ⟨⟨13, 14, (25197540290216621737/10000000000000000000000 : ℚ), (9873091925399093/2500000000000000000000 : ℚ)⟩, [
    (13, modeDataJ5M14)], (3149692536277077717/1250000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b13 : entryChecks 5 bflatBlockJ5B13.entries = true := by
  simp only [entryChecks,bflatBlockJ5B13,List.all_cons,List.all_nil,
    mode_checked_j5_m14,Bool.and_self]
theorem block_mass_checked_j5_b13 : blockMassCheck bflatBlockJ5B13 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
