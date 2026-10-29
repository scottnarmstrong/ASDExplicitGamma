module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B19 : ModeBlockData :=
  ⟨⟨19, 20, (7814198579034514507/400000000000000000000 : ℚ), (2910299649271224507/10000000000000000000000 : ℚ)⟩, [
    (19, modeDataJ3M20)], (97677482237931431337/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b19 : entryChecks 3 bflatBlockJ3B19.entries = true := by
  simp only [entryChecks,bflatBlockJ3B19,List.all_cons,List.all_nil,
    mode_checked_j3_m20,Bool.and_self]
theorem block_mass_checked_j3_b19 : blockMassCheck bflatBlockJ3B19 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
