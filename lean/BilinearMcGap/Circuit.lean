import BilinearMcGap.Base

/-!
# From frames to circuits; Theorem 1
-/

namespace BilinearMcGap

open Finset

set_option linter.unusedSectionVars false

variable {X Y D G P : Type} [Fintype X] [Fintype Y] [Fintype D] [Fintype G] [Fintype P]

/-- The circuit of a frame with wiring `Q`: gates `0 … |P|-1` are the products,
gates `|P| … |P|+|G|-1` the second layer. -/
noncomputable def Frame.toCircuit (Fr : Frame X Y D G P) (Q : G → P → F) : Circuit (X ⊕ Y) D where
  size := Fintype.card P + Fintype.card G
  left r := (finSumFinEquiv.symm r).elim
    (fun j => ⟨0, Sum.elim (Fr.xi ((Fintype.equivFin P).symm j)) 0, 0⟩)
    (fun i => ⟨0, Sum.elim (Fr.lam ((Fintype.equivFin G).symm i)) 0, 0⟩)
  right r := (finSumFinEquiv.symm r).elim
    (fun j => ⟨0, Sum.elim 0 (Fr.eta ((Fintype.equivFin P).symm j)), 0⟩)
    (fun i => ⟨0, 0, fun r' => (finSumFinEquiv.symm r').elim
      (fun j => Q ((Fintype.equivFin G).symm i) ((Fintype.equivFin P).symm j)) (fun _ => 0)⟩)
  out a := ⟨0, 0, fun r => (finSumFinEquiv.symm r).elim (fun _ => 0)
    (fun i => Fr.c ((Fintype.equivFin G).symm i) a)⟩

theorem gateVal_unfold {I O : Type} [Fintype I] (C : Circuit I O) (x : I → F) (r : Fin C.size) :
    C.gateVal x r = (C.left r).evalBelow x r.val (fun j _ => C.gateVal x j) *
      (C.right r).evalBelow x r.val (fun j _ => C.gateVal x j) := by
  rw [Circuit.gateVal]

theorem lin_inl (ℓ : X → F) (x : X → F) (y : Y → F) :
    ∑ i, Sum.elim ℓ (0 : Y → F) i * Sum.elim x y i = lin ℓ x := by
  simp [Fintype.sum_sum_type, lin]

theorem lin_inr (ℓ : Y → F) (x : X → F) (y : Y → F) :
    ∑ i, Sum.elim (0 : X → F) ℓ i * Sum.elim x y i = lin ℓ y := by
  simp [Fintype.sum_sum_type, lin]

section fields
variable (Fr : Frame X Y D G P) (Q : G → P → F)

theorem toC_left_castAdd (j : Fin (Fintype.card P)) :
    (Fr.toCircuit Q).left (Fin.castAdd (Fintype.card G) j) =
      ⟨0, Sum.elim (Fr.xi ((Fintype.equivFin P).symm j)) 0, 0⟩ := by
  simp only [Frame.toCircuit, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Sum.elim_inl, Sum.elim_inr]
  rfl

theorem toC_right_castAdd (j : Fin (Fintype.card P)) :
    (Fr.toCircuit Q).right (Fin.castAdd (Fintype.card G) j) =
      ⟨0, Sum.elim 0 (Fr.eta ((Fintype.equivFin P).symm j)), 0⟩ := by
  simp only [Frame.toCircuit, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Sum.elim_inl, Sum.elim_inr]
  rfl

theorem toC_left_natAdd (i : Fin (Fintype.card G)) :
    (Fr.toCircuit Q).left (Fin.natAdd (Fintype.card P) i) =
      ⟨0, Sum.elim (Fr.lam ((Fintype.equivFin G).symm i)) 0, 0⟩ := by
  simp only [Frame.toCircuit, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Sum.elim_inl, Sum.elim_inr]
  rfl

theorem toC_right_natAdd (i : Fin (Fintype.card G)) :
    (Fr.toCircuit Q).right (Fin.natAdd (Fintype.card P) i) =
      ⟨0, 0, fun r' => (finSumFinEquiv.symm r').elim
        (fun j => Q ((Fintype.equivFin G).symm i) ((Fintype.equivFin P).symm j)) (fun _ => 0)⟩ := by
  simp only [Frame.toCircuit, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Sum.elim_inl, Sum.elim_inr]

theorem toC_out (a : D) :
    (Fr.toCircuit Q).out a = ⟨0, 0, fun r => (finSumFinEquiv.symm r).elim (fun _ => 0)
      (fun i => Fr.c ((Fintype.equivFin G).symm i) a)⟩ := rfl

end fields

theorem Frame.toCircuit_prod (Fr : Frame X Y D G P) (Q : G → P → F) (x : X → F) (y : Y → F)
    (j : Fin (Fintype.card P)) :
    (Fr.toCircuit Q).gateVal (Sum.elim x y) (Fin.castAdd (Fintype.card G) j) =
      lin (Fr.xi ((Fintype.equivFin P).symm j)) x * lin (Fr.eta ((Fintype.equivFin P).symm j)) y := by
  erw [gateVal_unfold, toC_left_castAdd, toC_right_castAdd]
  simp [Affine.evalBelow, lin_inl, lin_inr, lin]

theorem Frame.toCircuit_second (Fr : Frame X Y D G P) (Q : G → P → F) (x : X → F) (y : Y → F)
    (i : Fin (Fintype.card G)) :
    (Fr.toCircuit Q).gateVal (Sum.elim x y) (Fin.natAdd (Fintype.card P) i) =
      lin (Fr.lam ((Fintype.equivFin G).symm i)) x *
        ∑ j, Q ((Fintype.equivFin G).symm i) j * (lin (Fr.xi j) x * lin (Fr.eta j) y) := by
  erw [gateVal_unfold, toC_left_natAdd, toC_right_natAdd]
  simp only [Affine.evalBelow, lin_inl, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero,
    zero_add, dite_eq_ite, ite_self]
  congr 1
  erw [Fin.sum_univ_add]
  have hlt : ∀ j : Fin (Fintype.card P), j.val < Fintype.card P + i.val := fun j => by omega
  simp only [Fin.val_castAdd, Fin.val_natAdd, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Sum.elim_inl, Sum.elim_inr, zero_mul, dite_eq_ite, ite_self,
    Finset.sum_const_zero, add_zero, hlt, dite_true, Frame.toCircuit_prod]
  exact Equiv.sum_comp (Fintype.equivFin P).symm
    (fun j => Q ((Fintype.equivFin G).symm i) j * (lin (Fr.xi j) x * lin (Fr.eta j) y))

theorem Frame.toCircuit_out (Fr : Frame X Y D G P) (Q : G → P → F) (x : X → F) (y : Y → F) (a : D) :
    (Fr.toCircuit Q).outVal (Sum.elim x y) a = Fr.eval Q x y a := by
  rw [Circuit.outVal, toC_out]
  simp only [Affine.evalBelow, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, Fin.is_lt,
    dite_true]
  erw [Fin.sum_univ_add]
  simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inl,
    Sum.elim_inr, zero_mul, Finset.sum_const_zero, zero_add, Frame.toCircuit_second]
  exact Equiv.sum_comp (Fintype.equivFin G).symm
    (fun i => Fr.c i a * (lin (Fr.lam i) x * ∑ j, Q i j * (lin (Fr.xi j) x * lin (Fr.eta j) y)))

/-- **Theorem 1.** For `n = 4^N`, every bilinear map `𝔽₂ⁿ × 𝔽₂ⁿ → 𝔽₂ⁿ` is computed by a
circuit with exactly `2·12^N` AND gates. -/
theorem universal_circuit (N : ℕ) (φ : Idx N → Idx N → Idx N → F) :
    ∃ C : Circuit (Idx N ⊕ Idx N) (Idx N), C.size = 2 * 12 ^ N ∧ Computes C φ := by
  obtain ⟨Q, hQ⟩ := powFrame_universal N φ
  refine ⟨(powFrame N).toCircuit Q, ?_, fun x y a => ?_⟩
  · show Fintype.card (PT N) + Fintype.card (GT N) = _
    rw [card_PT, card_GT]; ring
  · rw [Frame.toCircuit_out, Frame.eval_of_good _ _ _ hQ]

end BilinearMcGap
