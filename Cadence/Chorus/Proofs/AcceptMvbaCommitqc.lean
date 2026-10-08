import Cadence.Chorus
import Cadence.ProofPrelude

/-! # `Chorus` proofs — action `accept_mvba_commitqc`

Scaffolded by `#gen_proof_files Chorus`; yours to edit. Proves every
registered VC of `accept_mvba_commitqc` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
[Certify.lean](../Certify.lean)'s `#gen_composition`.

Manual cells go on `#prove_vc Chorus accept_mvba_commitqc <property> by <tac>` lines
*before* the `#prove_action` — it consumes them as-is after a statement
check. Solver options are read in this file at tactic runtime (no
`#gen_spec` capture applies on the cross-file path); `veil.smt.trust
false` is written out below, and the shared blocks from
[ProofPrelude.lean](../../ProofPrelude.lean) record what each of the other options is
for. -/

open Veil Chorus

-- The no-trusted-solver rule ([README.md](../../../README.md)) stays written out per proof file so
-- it remains greppable; the shared blocks below are defined and documented
-- in [ProofPrelude.lean](../../ProofPrelude.lean).
set_option veil.smt.trust false
veil_proof_options
veil_large_clump_budgets

namespace Chorus.Proofs

/- Written out: the solver closes this cell, but its time varies between
runs up to the budget on CI's 4-core runner. -/

#prove_vc Chorus accept_mvba_commitqc mvba_recorded_entries by
  unveil_local
  veil_inv_have h_mr := mvba_reachable
  veil_inv_have h_rb := local_mvba_recorded_backed
  veil_inv_have h_tp := mvba_decided_pos_tied
  veil_inv_have h_tn := mvba_decided_neg_tied
  obtain ⟨-, hfun, hexcl⟩ := has
  intro _hbyz _hfresh _hmsg hin I J V M hI hrec hdec
  -- The new state is reachable, and every correct decision in it agrees on
  -- entries with the decision or certificate the recorded entry is tied to.
  have htr := MVBASafety.accept_trans _ _ _ _ hin
  have hreach := TransitionSystemSafety.reachable_trans _ _ h_mr htr
  have hI' : ¬ (ByzNodeSet.is_byz I = true) := by simp [hI]
  rcases h_rb I J hI hrec with ⟨M0, hpos⟩ | hneg
  · rcases h_tp J M0 hpos with ⟨I0, hI0, V0, hdec0, hmv0⟩ | ⟨C, E, hcert, hmv0⟩
    · have heq := MVBASafety.agreement _ hreach I I0 V V0 hI' (by simp [hI0]) hdec
        (MVBASafety.decided_mono _ _ _ _ htr hdec0)
      refine ⟨fun hmv => ?_, fun hn => ?_⟩
      · rw [heq] at hmv
        rw [hfun _ J M M0 hmv hmv0]; exact hpos
      · rw [heq] at hn
        exact absurd ⟨hmv0, hn⟩ (hexcl _ J M0)
    · have heq := MVBASafety.certified_decided _ hreach C E I V
        (MVBASafety.certified_mono _ _ _ _ htr hcert) hI' hdec
      refine ⟨fun hmv => ?_, fun hn => ?_⟩
      · rw [heq] at hmv
        rw [hfun _ J M M0 hmv hmv0]; exact hpos
      · rw [heq] at hn
        exact absurd ⟨hmv0, hn⟩ (hexcl _ J M0)
  · rcases h_tn J hneg with ⟨I0, hI0, V0, hdec0, hmv0⟩ | ⟨C, E, hcert, hmv0⟩
    · have heq := MVBASafety.agreement _ hreach I I0 V V0 hI' (by simp [hI0]) hdec
        (MVBASafety.decided_mono _ _ _ _ htr hdec0)
      refine ⟨fun hmv => ?_, fun _ => hneg⟩
      rw [heq] at hmv
      exact absurd ⟨hmv, hmv0⟩ (hexcl _ J M)
    · have heq := MVBASafety.certified_decided _ hreach C E I V
        (MVBASafety.certified_mono _ _ _ _ htr hcert) hI' hdec
      refine ⟨fun hmv => ?_, fun _ => hneg⟩
      rw [heq] at hmv
      exact absurd ⟨hmv, hmv0⟩ (hexcl _ J M)

#prove_action Chorus accept_mvba_commitqc

end Chorus.Proofs
