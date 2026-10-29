module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B14 : ModeBlockData :=
  ⟨⟨14, 15, (208661562323714925281/10000000000000000000000 : ℚ), (3033634336808898623/10000000000000000000000 : ℚ)⟩, [
    (14, modeDataJ3M15)], (1304134764523218283/62500000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b14 : entryChecks 3 bflatBlockJ3B14.entries = true := by
  simp only [entryChecks,bflatBlockJ3B14,List.all_cons,List.all_nil,
    mode_checked_j3_m15,Bool.and_self]
theorem block_mass_checked_j3_b14 : blockMassCheck bflatBlockJ3B14 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
