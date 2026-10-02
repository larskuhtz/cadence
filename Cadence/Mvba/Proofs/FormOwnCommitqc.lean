import Cadence.Mvba
import Cadence.ProofPrelude

/-! # `Mvba` proofs — action `form_own_commitqc`

Scaffolded by `#gen_proof_files Mvba`; yours to edit. Proves every
registered VC of `form_own_commitqc` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
[Certify.lean](../Certify.lean)'s `#gen_composition`.

Manual cells go on `#prove_vc Mvba form_own_commitqc <property> by <tac>` lines
*before* the `#prove_action` — it consumes them as-is after a statement
check. Solver options are read in this file at tactic runtime (no
`#gen_spec` capture applies on the cross-file path); `veil.smt.trust
false` is written out below, and the shared block from
[ProofPrelude.lean](../../ProofPrelude.lean) record what each of the other options is
for. -/

open Veil Mvba

-- The no-trusted-solver rule ([README.md](../../../README.md)) stays written out per proof file so
-- it remains greppable; the shared block below is defined and documented in
-- [ProofPrelude.lean](../../ProofPrelude.lean).
set_option veil.smt.trust false
veil_proof_options
-- The clump passed the point where the default elaboration budgets
-- suffice when liveness's invariants and the `entered_needs_certificate`
-- step property went in; the Chorus family has carried this since it was
-- written ([ProofPrelude.lean](../../ProofPrelude.lean)).
veil_large_clump_budgets

namespace Mvba.Proofs

/- **Manual cell — agreement at the certificate level**, for the
certificate a correct validator forms itself. The argument is
`form_commitqc`'s, verbatim ([FormCommitqc.lean](FormCommitqc.lean) has
it in words): the new certificate `(v, e)` against every commit certificate
already on the wire, by the honest common signer in the same view and by
`prepqc_blocks_lower_commits` across views. Written out for the same
reason as that cell: it is a real argument, and a slower runner's budget
is not guaranteed. -/
#prove_vc Mvba form_own_commitqc commitqc_agree by
  unveil_local
  veil_inv_have h_honest_commit_accepted := honest_commit_accepted
  veil_inv_have h_local_prepqc_backed := local_prepqc_backed
  veil_inv_have h_local_prepqc_unique := local_prepqc_unique
  veil_inv_have h_commitqc_backed := commitqc_backed
  veil_inv_have h_commitqc_implies_prepqc := commitqc_implies_prepqc
  veil_inv_have h_commit_no_later_noqc_timeout := commit_no_later_noqc_timeout
  veil_inv_have h_commit_later_timeout_carries_lock := commit_later_timeout_carries_lock
  veil_inv_have h_blocks := prepqc_blocks_lower_commits
  clear hinv
  intro _ _ _ _ _ _ _ hsup_q hq _ V V' E E' hc1 hc2
  -- The new certificate is on the decided representation's entries.
  generalize th.ent x = e at hq hc1 hc2
  -- An honest validator that committed `E0` in `V0` is not blocked there:
  -- its later timeouts carry a view-`≥ V0` lock, and its view-`V0` lock is
  -- on `E0`.
  have no_block : ∀ (n : node) (V0 : view) (E0 : evec),
      ByzNodeSet.is_byz n = false → st.msg_commit n V0 E0 = true →
      ((∃ v', TotalOrderWithMinimum.le V0 v' ∧
          (st.msg_timeout_noqc n v' = true ∨
            ∃ w, (∃ x, st.msg_timeout_qc n v' w x = true) ∧ TotalOrderWithMinimum.lt w V0)) ∨
        ∃ e', ¬ e' = E0 ∧ st.local_prepqc n V0 e' = true) → False := by
    intro n V0 E0 hn hcm hb
    rcases hb with ⟨v', hle, hnoqc | ⟨w, ⟨x, hto⟩, hltw⟩⟩ | ⟨e', hne', hheld⟩
    · have h := h_commit_no_later_noqc_timeout n V0 v' E0 hn hcm hnoqc
      have h' := (TotalOrderWithMinimum.le_lt v' V0).mp h
      exact h'.2 (TotalOrderWithMinimum.le_antisymm _ _ h'.1 hle)
    · have h := h_commit_later_timeout_carries_lock n V0 v' w E0 x hn hcm hto hle
      have h' := (TotalOrderWithMinimum.le_lt w V0).mp hltw
      exact h'.2 (TotalOrderWithMinimum.le_antisymm _ _ h'.1 h)
    · have hheld0 := (h_honest_commit_accepted n V0 E0 hn hcm).1
      exact hne' (h_local_prepqc_unique n V0 e' E0 hn hheld hheld0)
  -- Every commit certificate already on the wire is on the new one's value.
  have key : ∀ (V0 : view) (E0 : evec), st.msg_commitqc V0 E0 = true → E0 = e := by
    intro V0 E0 hc0
    by_contra hneq
    obtain ⟨Q0, hQ0_sup, hQ0⟩ := h_commitqc_backed V0 E0 hc0
    by_cases hVeq : V0 = v
    · -- Same view: the two commit quorums share an honest signer, who
      -- held a view-`V0` prepare certificate on both vectors.
      subst hVeq
      obtain ⟨b, hbq, hbQ0, hb_hon⟩ :=
        nset.supermajorities_intersect_in_honest q Q0 hsup_q hQ0_sup
      have hb_hon' : ByzNodeSet.is_byz b = false := Bool.eq_false_iff.mpr hb_hon
      have h1 := (h_honest_commit_accepted b V0 e hb_hon' (hq b hbq)).1
      have h2 := (h_honest_commit_accepted b V0 E0 hb_hon' (hQ0 b hbQ0)).1
      exact hneq (h_local_prepqc_unique b V0 E0 e hb_hon' h2 h1)
    · rcases TotalOrderWithMinimum.le_total V0 v with hle | hle
      · -- `V0 < v`: the new certificate's honest signers held a view-`v`
        -- prepare certificate on `e`; it blocks `Q0` from committing `E0`
        -- in `V0`, yet `Q0` did.
        have hlt : TotalOrderWithMinimum.lt V0 v :=
          (TotalOrderWithMinimum.le_lt V0 v).mpr ⟨hle, hVeq⟩
        obtain ⟨c, hcq, hc_hon⟩ :=
          nset.greater_than_third_one_honest q (nset.supermajority_greater_than_third q hsup_q)
        have hc_hon' : ByzNodeSet.is_byz c = false := Bool.eq_false_iff.mpr hc_hon
        have hpq_v : st.msg_prepqc v e = true :=
          h_local_prepqc_backed c v e hc_hon' (h_honest_commit_accepted c v e hc_hon' (hq c hcq)).1
        obtain ⟨n, hnQ0, hn_hon, hb⟩ := h_blocks v V0 e E0 Q0 hpq_v hlt hneq hQ0_sup
        exact no_block n V0 E0 hn_hon (hQ0 n hnQ0) hb
      · -- `v < V0`: the old certificate's view-`V0` prepare certificate
        -- blocks `q` from committing `e` in `v`, yet `q` did.
        have hlt : TotalOrderWithMinimum.lt v V0 :=
          (TotalOrderWithMinimum.le_lt v V0).mpr ⟨hle, fun h => hVeq h.symm⟩
        have hpq0 := h_commitqc_implies_prepqc V0 E0 hc0
        obtain ⟨n, hnq, hn_hon, hb⟩ :=
          h_blocks V0 v E0 e q hpq0 hlt (fun h => hneq h.symm) hsup_q
        exact no_block n v e hn_hon (hq n hnq) hb
  have hE : E = e := by
    by_cases h : v = V ∧ e = E
    · exact h.2.symm
    · exact key V E (hc1 (fun h1 h2 => h ⟨h1, h2⟩))
  have hE' : E' = e := by
    by_cases h : v = V' ∧ e = E'
    · exact h.2.symm
    · exact key V' E' (hc2 (fun h1 h2 => h ⟨h1, h2⟩))
  rw [hE, hE']

/- **Manual cell — Supplement, Theorem 1 (`thm:agreement`) at the decision this step makes.** The
step decides `e`, so agreement needs every earlier decision to be on `e`:
an earlier decision is certificate-backed (`decided_backed`), and the
certificate-level argument of the cell above (`key`) puts that certificate
on `e`. -/
#prove_vc Mvba form_own_commitqc agreement by
  unveil_local
  veil_inv_have h_honest_commit_accepted := honest_commit_accepted
  veil_inv_have h_local_prepqc_backed := local_prepqc_backed
  veil_inv_have h_local_prepqc_unique := local_prepqc_unique
  veil_inv_have h_commitqc_backed := commitqc_backed
  veil_inv_have h_commitqc_implies_prepqc := commitqc_implies_prepqc
  veil_inv_have h_commit_no_later_noqc_timeout := commit_no_later_noqc_timeout
  veil_inv_have h_commit_later_timeout_carries_lock := commit_later_timeout_carries_lock
  veil_inv_have h_blocks := prepqc_blocks_lower_commits
  veil_inv_have h_decided_backed := decided_backed
  clear hinv
  intro _ _ _ _ _ _ _ hsup_q hq _ I J X X' hI hJ hd1 hd2
  -- The new certificate is on the decided representation's entries.
  generalize he : th.ent x = e at hq
  -- An honest validator that committed `E0` in `V0` is not blocked there:
  -- its later timeouts carry a view-`≥ V0` lock, and its view-`V0` lock is
  -- on `E0`.
  have no_block : ∀ (n : node) (V0 : view) (E0 : evec),
      ByzNodeSet.is_byz n = false → st.msg_commit n V0 E0 = true →
      ((∃ v', TotalOrderWithMinimum.le V0 v' ∧
          (st.msg_timeout_noqc n v' = true ∨
            ∃ w, (∃ x, st.msg_timeout_qc n v' w x = true) ∧ TotalOrderWithMinimum.lt w V0)) ∨
        ∃ e', ¬ e' = E0 ∧ st.local_prepqc n V0 e' = true) → False := by
    intro n V0 E0 hn hcm hb
    rcases hb with ⟨v', hle, hnoqc | ⟨w, ⟨x, hto⟩, hltw⟩⟩ | ⟨e', hne', hheld⟩
    · have h := h_commit_no_later_noqc_timeout n V0 v' E0 hn hcm hnoqc
      have h' := (TotalOrderWithMinimum.le_lt v' V0).mp h
      exact h'.2 (TotalOrderWithMinimum.le_antisymm _ _ h'.1 hle)
    · have h := h_commit_later_timeout_carries_lock n V0 v' w E0 x hn hcm hto hle
      have h' := (TotalOrderWithMinimum.le_lt w V0).mp hltw
      exact h'.2 (TotalOrderWithMinimum.le_antisymm _ _ h'.1 h)
    · have hheld0 := (h_honest_commit_accepted n V0 E0 hn hcm).1
      exact hne' (h_local_prepqc_unique n V0 e' E0 hn hheld hheld0)
  -- Every commit certificate already on the wire is on the new one's value.
  have key : ∀ (V0 : view) (E0 : evec), st.msg_commitqc V0 E0 = true → E0 = e := by
    intro V0 E0 hc0
    by_contra hneq
    obtain ⟨Q0, hQ0_sup, hQ0⟩ := h_commitqc_backed V0 E0 hc0
    by_cases hVeq : V0 = v
    · -- Same view: the two commit quorums share an honest signer, who
      -- held a view-`V0` prepare certificate on both vectors.
      subst hVeq
      obtain ⟨b, hbq, hbQ0, hb_hon⟩ :=
        nset.supermajorities_intersect_in_honest q Q0 hsup_q hQ0_sup
      have hb_hon' : ByzNodeSet.is_byz b = false := Bool.eq_false_iff.mpr hb_hon
      have h1 := (h_honest_commit_accepted b V0 e hb_hon' (hq b hbq)).1
      have h2 := (h_honest_commit_accepted b V0 E0 hb_hon' (hQ0 b hbQ0)).1
      exact hneq (h_local_prepqc_unique b V0 E0 e hb_hon' h2 h1)
    · rcases TotalOrderWithMinimum.le_total V0 v with hle | hle
      · -- `V0 < v`: the new certificate's honest signers held a view-`v`
        -- prepare certificate on `e`; it blocks `Q0` from committing `E0`
        -- in `V0`, yet `Q0` did.
        have hlt : TotalOrderWithMinimum.lt V0 v :=
          (TotalOrderWithMinimum.le_lt V0 v).mpr ⟨hle, hVeq⟩
        obtain ⟨c, hcq, hc_hon⟩ :=
          nset.greater_than_third_one_honest q (nset.supermajority_greater_than_third q hsup_q)
        have hc_hon' : ByzNodeSet.is_byz c = false := Bool.eq_false_iff.mpr hc_hon
        have hpq_v : st.msg_prepqc v e = true :=
          h_local_prepqc_backed c v e hc_hon' (h_honest_commit_accepted c v e hc_hon' (hq c hcq)).1
        obtain ⟨n, hnQ0, hn_hon, hb⟩ := h_blocks v V0 e E0 Q0 hpq_v hlt hneq hQ0_sup
        exact no_block n V0 E0 hn_hon (hQ0 n hnQ0) hb
      · -- `v < V0`: the old certificate's view-`V0` prepare certificate
        -- blocks `q` from committing `e` in `v`, yet `q` did.
        have hlt : TotalOrderWithMinimum.lt v V0 :=
          (TotalOrderWithMinimum.le_lt v V0).mpr ⟨hle, fun h => hVeq h.symm⟩
        have hpq0 := h_commitqc_implies_prepqc V0 E0 hc0
        obtain ⟨n, hnq, hn_hon, hb⟩ :=
          h_blocks V0 v E0 e q hpq0 hlt (fun h => hneq h.symm) hsup_q
        exact no_block n v e hn_hon (hq n hnq) hb
  have hE : th.ent X = e := by
    by_cases h : i = I ∧ x = X
    · rw [← h.2]; exact he
    · obtain ⟨V0, hV0⟩ := h_decided_backed I X hI (hd1 (fun h1 h2 => h ⟨h1, h2⟩))
      exact key V0 _ hV0
  have hE' : th.ent X' = e := by
    by_cases h : i = J ∧ x = X'
    · rw [← h.2]; exact he
    · obtain ⟨V0, hV0⟩ := h_decided_backed J X' hJ (hd2 (fun h1 h2 => h ⟨h1, h2⟩))
      exact key V0 _ hV0
  rw [hE, hE']

#prove_action Mvba form_own_commitqc

end Mvba.Proofs
