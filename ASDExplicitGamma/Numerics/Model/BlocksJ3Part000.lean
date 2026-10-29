module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B0 : ModeBlockData :=
  ⟨⟨0, 1, (45379908791439461763/2000000000000000000000 : ℚ), (639993398179536491/2000000000000000000000 : ℚ)⟩, [
    (0, modeDataJ3M1)], (113449771978598654407/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b0 : entryChecks 3 bflatBlockJ3B0.entries = true := by
  simp only [entryChecks,bflatBlockJ3B0,List.all_cons,List.all_nil,
    mode_checked_j3_m1,Bool.and_self]
theorem block_mass_checked_j3_b0 : blockMassCheck bflatBlockJ3B0 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
