module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B18 : ModeBlockData :=
  ⟨⟨18, 19, (6194496026832951233/5000000000000000000000 : ℚ), (2346541347841579961/2000000000000000000000 : ℚ)⟩, [
    (18, modeDataJ1M19)], (2477798410733180493/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b18 : entryChecks 1 bflatBlockJ1B18.entries = true := by
  simp only [entryChecks,bflatBlockJ1B18,List.all_cons,List.all_nil,
    mode_checked_j1_m19,Bool.and_self]
theorem block_mass_checked_j1_b18 : blockMassCheck bflatBlockJ1B18 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
