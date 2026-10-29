module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B58 : ModeBlockData :=
  ⟨⟨58, 59, (4963246741687615001/2000000000000000000000 : ℚ), (391117530055873/100000000000000000000 : ℚ)⟩, [
    (58, modeDataJ5M59)], (6204058427109518751/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b58 : entryChecks 5 bflatBlockJ5B58.entries = true := by
  simp only [entryChecks,bflatBlockJ5B58,List.all_cons,List.all_nil,
    mode_checked_j5_m59,Bool.and_self]
theorem block_mass_checked_j5_b58 : blockMassCheck bflatBlockJ5B58 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
