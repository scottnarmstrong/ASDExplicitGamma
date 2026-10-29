module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part007

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B90 : ModeBlockData :=
  ⟨⟨124, 127, (513716510245005757/5000000000000000000000 : ℚ), (836265438526125033/10000000000000000000000 : ℚ)⟩, [
    (124, modeDataJ3M125),
    (125, modeDataJ3M126),
    (126, modeDataJ3M127)], (1027433020490011511/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b90 : entryChecks 3 bflatBlockJ3B90.entries = true := by
  simp only [entryChecks,bflatBlockJ3B90,List.all_cons,List.all_nil,
    mode_checked_j3_m125,
    mode_checked_j3_m126,
    mode_checked_j3_m127,Bool.and_self]
theorem block_mass_checked_j3_b90 : blockMassCheck bflatBlockJ3B90 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
