import BilinearMcGap.Circuit
import BilinearMcGap.Lower

/-!
# Main results (n = 4^N; `Idx N` has `4^N` elements, see `card_Idx`)

* `universal_circuit` (Theorem 1): every bilinear map `𝔽₂ⁿ × 𝔽₂ⁿ → 𝔽₂ⁿ` has a circuit with
  exactly `2·12^N` AND gates.
* `rank_le_two_mul_size` (Lemma 5): a quadratic circuit with `s` AND gates for `φ` gives
  `rank φ ≤ 2s`.
* `gap` (Theorem 2, part 2): for `N ≥ 9`, the maps having a quadratic circuit with at most
  `2·12^N` AND gates form at most a `2^{-n}` fraction of all `2^{n³}` bilinear maps.
* `rank_gap` (Theorem 2, part 1): for `N ≥ 7`, the maps of rank `≤ 2·12^N` form at most a
  `2^{-n}` fraction.
-/

open Classical

namespace BilinearMcGap

/-- Theorem 2 in one statement: for `N ≥ 9`, every bilinear map has an unrestricted circuit
with `2·12^N` AND gates, while all but a `2^{-n}` fraction have no quadratic circuit with
that many AND gates. -/
theorem mc_lt_qmc (N : ℕ) (hN : 9 ≤ N) :
    (∀ φ : Idx N → Idx N → Idx N → F,
        ∃ C : Circuit (Idx N ⊕ Idx N) (Idx N), C.size = 2 * 12 ^ N ∧ Computes C φ) ∧
    (Finset.univ.filter (fun φ : Idx N → Idx N → Idx N → F =>
        ∃ C : Circuit (Idx N ⊕ Idx N) (Idx N), C.IsQuadratic ∧ Computes C φ ∧
          C.size ≤ 2 * 12 ^ N)).card * 2 ^ (4 ^ N) ≤ 2 ^ ((4 ^ N) ^ 3) :=
  ⟨universal_circuit N, gap N hN⟩

end BilinearMcGap
