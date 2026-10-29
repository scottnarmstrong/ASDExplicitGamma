module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B62 : ModeBlockData :=
  ⟨⟨62, 63, (23148432560675530133/5000000000000000000000 : ℚ), (1314260649473923253/10000000000000000000000 : ℚ)⟩, [
    (62, modeDataJ3M63)], (9259373024270212053/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b62 : entryChecks 3 bflatBlockJ3B62.entries = true := by
  simp only [entryChecks,bflatBlockJ3B62,List.all_cons,List.all_nil,
    mode_checked_j3_m63,Bool.and_self]
theorem block_mass_checked_j3_b62 : blockMassCheck bflatBlockJ3B62 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
