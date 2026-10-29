module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B40 : ModeBlockData :=
  ⟨⟨40, 41, (48876003540677791/19531250000000000000 : ℚ), (1965990469068469/500000000000000000000 : ℚ)⟩, [
    (40, modeDataJ5M41)], (25024513812827028991/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b40 : entryChecks 5 bflatBlockJ5B40.entries = true := by
  simp only [entryChecks,bflatBlockJ5B40,List.all_cons,List.all_nil,
    mode_checked_j5_m41,Bool.and_self]
theorem block_mass_checked_j5_b40 : blockMassCheck bflatBlockJ5B40 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
