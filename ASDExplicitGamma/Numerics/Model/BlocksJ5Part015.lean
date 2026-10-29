module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B15 : ModeBlockData :=
  ⟨⟨15, 16, (12595264141480249213/5000000000000000000000 : ℚ), (9871344903146387/2500000000000000000000 : ℚ)⟩, [
    (15, modeDataJ5M16)], (1007621131318419937/400000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b15 : entryChecks 5 bflatBlockJ5B15.entries = true := by
  simp only [entryChecks,bflatBlockJ5B15,List.all_cons,List.all_nil,
    mode_checked_j5_m16,Bool.and_self]
theorem block_mass_checked_j5_b15 : blockMassCheck bflatBlockJ5B15 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
