module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part005

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B68 : ModeBlockData :=
  ⟨⟨80, 85, (141417528426096426939/5000000000000000000000 : ℚ), (1483434322914904697/10000000000000000000000 : ℚ)⟩, [
    (80, modeDataJ4M81),
    (81, modeDataJ4M82),
    (82, modeDataJ4M83),
    (83, modeDataJ4M84),
    (84, modeDataJ4M85)], (282835056852192853873/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b68 : entryChecks 4 bflatBlockJ4B68.entries = true := by
  simp only [entryChecks,bflatBlockJ4B68,List.all_cons,List.all_nil,
    mode_checked_j4_m81,
    mode_checked_j4_m82,
    mode_checked_j4_m83,
    mode_checked_j4_m84,
    mode_checked_j4_m85,Bool.and_self]
theorem block_mass_checked_j4_b68 : blockMassCheck bflatBlockJ4B68 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
