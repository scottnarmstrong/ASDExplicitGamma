module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B9 : ModeBlockData :=
  ⟨⟨9, 10, (112638041779121350237/10000000000000000000000 : ℚ), (2034945601947538117/400000000000000000000 : ℚ)⟩, [
    (9, modeDataJ1M10)], (28159510444780337559/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b9 : entryChecks 1 bflatBlockJ1B9.entries = true := by
  simp only [entryChecks,bflatBlockJ1B9,List.all_cons,List.all_nil,
    mode_checked_j1_m10,Bool.and_self]
theorem block_mass_checked_j1_b9 : blockMassCheck bflatBlockJ1B9 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
