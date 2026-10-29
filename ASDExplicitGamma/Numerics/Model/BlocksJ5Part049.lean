module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B49 : ModeBlockData :=
  ⟨⟨49, 50, (12464775034245638083/5000000000000000000000 : ℚ), (122578106004133/31250000000000000000 : ℚ)⟩, [
    (49, modeDataJ5M50)], (4985910013698255233/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b49 : entryChecks 5 bflatBlockJ5B49.entries = true := by
  simp only [entryChecks,bflatBlockJ5B49,List.all_cons,List.all_nil,
    mode_checked_j5_m50,Bool.and_self]
theorem block_mass_checked_j5_b49 : blockMassCheck bflatBlockJ5B49 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
