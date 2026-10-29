module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B45 : ModeBlockData :=
  ⟨⟨45, 46, (24974034311015148903/10000000000000000000000 : ℚ), (9817354582619079/2500000000000000000000 : ℚ)⟩, [
    (45, modeDataJ5M46)], (12487017155507574451/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b45 : entryChecks 5 bflatBlockJ5B45.entries = true := by
  simp only [entryChecks,bflatBlockJ5B45,List.all_cons,List.all_nil,
    mode_checked_j5_m46,Bool.and_self]
theorem block_mass_checked_j5_b45 : blockMassCheck bflatBlockJ5B45 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
