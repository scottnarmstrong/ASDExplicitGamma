module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B45 : ModeBlockData :=
  ⟨⟨45, 46, (34626346912153837623/5000000000000000000000 : ℚ), (336261511619706243/10000000000000000000000 : ℚ)⟩, [
    (45, modeDataJ4M46)], (13850538764861535049/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b45 : entryChecks 4 bflatBlockJ4B45.entries = true := by
  simp only [entryChecks,bflatBlockJ4B45,List.all_cons,List.all_nil,
    mode_checked_j4_m46,Bool.and_self]
theorem block_mass_checked_j4_b45 : blockMassCheck bflatBlockJ4B45 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
