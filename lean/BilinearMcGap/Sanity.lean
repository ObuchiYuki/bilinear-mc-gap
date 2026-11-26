import BilinearMcGap.Defs

/-!
# Sanity checks on the definitions

`Computes` is not vacuous: a circuit without AND gates cannot compute the product `x·y`.
-/

namespace BilinearMcGap

theorem no_free_product :
    ¬ ∃ C : Circuit (Unit ⊕ Unit) Unit, C.size = 0 ∧ Computes C (fun _ _ _ => 1) := by
  rintro ⟨C, hs, hC⟩
  have key : ∀ x y : F, (C.out ()).const + (C.out ()).lin (Sum.inl ()) * x +
      (C.out ()).lin (Sum.inr ()) * y = x * y := by
    intro x y
    have h := hC (fun _ => x) (fun _ => y) ()
    simp only [Circuit.outVal, Affine.evalBelow, bil, Fintype.sum_sum_type, Fintype.univ_unit,
      Finset.sum_singleton, Sum.elim_inl, Sum.elim_inr, one_mul] at h
    have h0 : ∀ f : Fin C.size → F, ∑ j, f j = 0 := fun f => by
      rw [Finset.sum_eq_zero]; intro j _; exact absurd j.isLt (by omega)
    rw [h0, add_zero] at h
    rw [← h]; ring
  have h00 := key 0 0
  have h10 := key 1 0
  have h01 := key 0 1
  have h11 := key 1 1
  generalize (C.out ()).const = c at *
  generalize (C.out ()).lin (Sum.inl ()) = u at *
  generalize (C.out ()).lin (Sum.inr ()) = v at *
  revert c u v
  decide

end BilinearMcGap
