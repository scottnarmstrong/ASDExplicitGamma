module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part005

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B75 : ModeBlockData :=
  ⟨⟨86, 88, (16179666341091683389/10000000000000000000000 : ℚ), (134471049651611431/1000000000000000000000 : ℚ)⟩, [
    (86, modeDataJ3M87),
    (87, modeDataJ3M88)], (16179666341091683387/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b75 : entryChecks 3 bflatBlockJ3B75.entries = true := by
  simp only [entryChecks,bflatBlockJ3B75,List.all_cons,List.all_nil,
    mode_checked_j3_m87,
    mode_checked_j3_m88,Bool.and_self]
theorem block_mass_checked_j3_b75 : blockMassCheck bflatBlockJ3B75 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
