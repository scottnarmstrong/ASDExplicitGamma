module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B10 : ModeBlockData :=
  ⟨⟨10, 11, (45417144294565482673/1000000000000000000000 : ℚ), (11142476693061084671/5000000000000000000000 : ℚ)⟩, [
    (10, modeDataJ2M11)], (454171442945654826729/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b10 : entryChecks 2 bflatBlockJ2B10.entries = true := by
  simp only [entryChecks,bflatBlockJ2B10,List.all_cons,List.all_nil,
    mode_checked_j2_m11,Bool.and_self]
theorem block_mass_checked_j2_b10 : blockMassCheck bflatBlockJ2B10 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
