module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B18 : ModeBlockData :=
  ⟨⟨18, 19, (99125775282066291/5000000000000000000 : ℚ), (293729871155308829/1000000000000000000000 : ℚ)⟩, [
    (18, modeDataJ3M19)], (198251550564132581999/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b18 : entryChecks 3 bflatBlockJ3B18.entries = true := by
  simp only [entryChecks,bflatBlockJ3B18,List.all_cons,List.all_nil,
    mode_checked_j3_m19,Bool.and_self]
theorem block_mass_checked_j3_b18 : blockMassCheck bflatBlockJ3B18 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
