module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B52 : ModeBlockData :=
  ⟨⟨52, 53, (33631874342947011301/5000000000000000000000 : ℚ), (41271322504699367/1250000000000000000000 : ℚ)⟩, [
    (52, modeDataJ4M53)], (67263748685894022601/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b52 : entryChecks 4 bflatBlockJ4B52.entries = true := by
  simp only [entryChecks,bflatBlockJ4B52,List.all_cons,List.all_nil,
    mode_checked_j4_m53,Bool.and_self]
theorem block_mass_checked_j4_b52 : blockMassCheck bflatBlockJ4B52 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
