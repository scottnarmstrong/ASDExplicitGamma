module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B49 : ModeBlockData :=
  ⟨⟨49, 50, (85776060942924225191/10000000000000000000000 : ℚ), (7023929204948269/39062500000000000000 : ℚ)⟩, [
    (49, modeDataJ3M50)], (8577606094292422519/1000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b49 : entryChecks 3 bflatBlockJ3B49.entries = true := by
  simp only [entryChecks,bflatBlockJ3B49,List.all_cons,List.all_nil,
    mode_checked_j3_m50,Bool.and_self]
theorem block_mass_checked_j3_b49 : blockMassCheck bflatBlockJ3B49 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
