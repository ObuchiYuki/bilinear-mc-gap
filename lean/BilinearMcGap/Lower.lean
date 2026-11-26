import BilinearMcGap.Defs

open Classical

namespace BilinearMcGap

section Rank

set_option linter.unusedSectionVars false

variable {X Y : Type} [Fintype X] [Fintype Y]

/-- `x`-part of the linear part of an affine form on `X ⊕ Y`. -/
def lx {g : ℕ} (A : Affine (X ⊕ Y) g) (x : X → F) : F := ∑ i, A.lin (Sum.inl i) * x i

/-- `y`-part of the linear part of an affine form on `X ⊕ Y`. -/
def ly {g : ℕ} (A : Affine (X ⊕ Y) g) (y : Y → F) : F := ∑ i, A.lin (Sum.inr i) * y i

lemma sum_lin_elim {g : ℕ} (A : Affine (X ⊕ Y) g) (x : X → F) (y : Y → F) :
    ∑ i, A.lin i * Sum.elim x y i = lx A x + ly A y := by
  simp [Fintype.sum_sum_type, lx, ly]

lemma lx_zero {g : ℕ} (A : Affine (X ⊕ Y) g) : lx A 0 = 0 := by simp [lx]
lemma ly_zero {g : ℕ} (A : Affine (X ⊕ Y) g) : ly A 0 = 0 := by simp [ly]

lemma lx_single [DecidableEq X] {g : ℕ} (A : Affine (X ⊕ Y) g) (k : X) :
    lx A (Pi.single k 1) = A.lin (Sum.inl k) := by
  simp [lx, Pi.single_apply]

lemma ly_single [DecidableEq Y] {g : ℕ} (A : Affine (X ⊕ Y) g) (s : Y) :
    ly A (Pi.single s 1) = A.lin (Sum.inr s) := by
  simp [ly, Pi.single_apply]

lemma evalBelow_of_gat_zero {I : Type} [Fintype I] {g : ℕ} (A : Affine I g)
    (hA : ∀ j, A.gat j = 0) (x : I → F) (b : ℕ) (v : (j : Fin g) → j.val < b → F) :
    A.evalBelow x b v = A.const + ∑ i, A.lin i * x i := by
  simp [Affine.evalBelow, hA]

lemma two_eq_zero_F : (2 : F) = 0 := rfl

lemma alg {ι : Type} [Fintype ι] (c u v : F) (g cl al bl cr ar br : ι → F) :
    (c + u + v + ∑ j, g j * ((cl j + al j + bl j) * (cr j + ar j + br j)))
    + (c + u + 0 + ∑ j, g j * ((cl j + al j + 0) * (cr j + ar j + 0)))
    + (c + 0 + v + ∑ j, g j * ((cl j + 0 + bl j) * (cr j + 0 + br j)))
    + (c + 0 + 0 + ∑ j, g j * ((cl j + 0 + 0) * (cr j + 0 + 0)))
    = ∑ j, g j * (al j * br j + bl j * ar j) := by
  have hS : (∑ j, g j * ((cl j + al j + bl j) * (cr j + ar j + br j)))
      + (∑ j, g j * ((cl j + al j + 0) * (cr j + ar j + 0)))
      + (∑ j, g j * ((cl j + 0 + bl j) * (cr j + 0 + br j)))
      + (∑ j, g j * ((cl j + 0 + 0) * (cr j + 0 + 0)))
      = ∑ j, g j * (al j * br j + bl j * ar j) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    linear_combination (g j * (2 * cl j * cr j + cl j * ar j + cl j * br j + al j * cr j
      + al j * ar j + bl j * cr j + bl j * br j)) * two_eq_zero_F
  linear_combination hS + (2 * c + u + v) * two_eq_zero_F

theorem rank_le_two_mul_size {X Y D : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    [DecidableEq Y] (C : Circuit (X ⊕ Y) D) (hq : C.IsQuadratic) (φ : X → Y → D → F)
    (h : Computes C φ) : RankLE φ (2 * C.size) := by
  have hgate : ∀ (x : X → F) (y : Y → F) (r : Fin C.size),
      C.gateVal (Sum.elim x y) r =
        ((C.left r).const + lx (C.left r) x + ly (C.left r) y) *
        ((C.right r).const + lx (C.right r) x + ly (C.right r) y) := by
    intro x y r
    rw [Circuit.gateVal, evalBelow_of_gat_zero _ (fun j => (hq r j).1),
      evalBelow_of_gat_zero _ (fun j => (hq r j).2), sum_lin_elim, sum_lin_elim]
    ring
  have hout : ∀ (x : X → F) (y : Y → F) (a : D),
      C.outVal (Sum.elim x y) a = (C.out a).const + lx (C.out a) x + ly (C.out a) y +
        ∑ j, (C.out a).gat j *
          (((C.left j).const + lx (C.left j) x + ly (C.left j) y) *
          ((C.right j).const + lx (C.right j) x + ly (C.right j) y)) := by
    intro x y a
    simp only [Circuit.outVal, Affine.evalBelow, Fin.is_lt, dite_true, sum_lin_elim, hgate]
    ring
  have hbil : ∀ k s a, φ k s a = bil φ (Pi.single k 1) (Pi.single s 1) a
      + bil φ (Pi.single k 1) 0 a + bil φ 0 (Pi.single s 1) a + bil φ 0 0 a := by
    intro k s a
    simp [bil, Pi.single_apply]
  have key : ∀ k s a, φ k s a = ∑ j, (C.out a).gat j *
      ((C.left j).lin (Sum.inl k) * (C.right j).lin (Sum.inr s)
        + (C.left j).lin (Sum.inr s) * (C.right j).lin (Sum.inl k)) := by
    intro k s a
    rw [hbil, ← h, ← h, ← h, ← h, hout, hout, hout, hout]
    simp only [lx_zero, ly_zero]
    rw [alg]
    simp only [lx_single, ly_single]
  refine ⟨fun ρ => Fin.addCases (fun j => fun k => (C.left j).lin (Sum.inl k))
      (fun j => fun k => (C.right j).lin (Sum.inl k)) (Fin.cast (two_mul _) ρ),
    fun ρ => Fin.addCases (fun j => fun s => (C.right j).lin (Sum.inr s))
      (fun j => fun s => (C.left j).lin (Sum.inr s)) (Fin.cast (two_mul _) ρ),
    fun ρ => Fin.addCases (fun j => fun a => (C.out a).gat j)
      (fun j => fun a => (C.out a).gat j) (Fin.cast (two_mul _) ρ), ?_⟩
  intro k s a
  rw [key, ← (finCongr (two_mul C.size)).symm.sum_comp]
  simp only [finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

end Rank

theorem RankLE.mono {X Y D : Type} {φ : X → Y → D → F} {r r' : ℕ} (h : RankLE φ r)
    (hr : r ≤ r') : RankLE φ r' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  obtain ⟨u, v, w, huvw⟩ := h
  refine ⟨Fin.addCases u (fun _ => 0), Fin.addCases v (fun _ => 0),
    Fin.addCases w (fun _ => 0), fun k s a => ?_⟩
  rw [huvw, Fin.sum_univ_add]
  simp

theorem card_rankLE_le {X Y D : Type} [Fintype X] [Fintype Y] [Fintype D] [DecidableEq X]
    [DecidableEq Y] [DecidableEq D] (r : ℕ) :
    (Finset.univ.filter (fun φ : X → Y → D → F => RankLE φ r)).card ≤
      2 ^ ((Fintype.card X + Fintype.card Y + Fintype.card D) * r) := by
  let g : (Fin r → (X → F) × (Y → F) × (D → F)) → (X → Y → D → F) :=
    fun t k s a => ∑ ρ, (t ρ).1 k * (t ρ).2.1 s * (t ρ).2.2 a
  have hsub : Finset.univ.filter (fun φ : X → Y → D → F => RankLE φ r) ⊆
      Finset.univ.image g := by
    intro φ hφ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hφ
    obtain ⟨u, v, w, h⟩ := hφ
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ρ => (u ρ, v ρ, w ρ), by funext k s a; simp [g, h]⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_prod, ZMod.card,
    Fintype.card_fin]
  rw [pow_mul, pow_add, pow_add, mul_assoc]

lemma card_bound (N r : ℕ) (h : 3 * r + 1 ≤ 16 ^ N) :
    (Finset.univ.filter (fun φ : Idx N → Idx N → Idx N → F => RankLE φ r)).card
      * 2 ^ (4 ^ N) ≤ 2 ^ ((4 ^ N) ^ 3) := by
  have hc := card_rankLE_le (X := Idx N) (Y := Idx N) (D := Idx N) r
  rw [card_Idx] at hc
  have h16 : (4 ^ N) ^ 2 = 16 ^ N := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hexp : (4 ^ N + 4 ^ N + 4 ^ N) * r + 4 ^ N ≤ (4 ^ N) ^ 3 := by
    have : (4 ^ N) ^ 3 = 4 ^ N * (4 ^ N) ^ 2 := by ring
    rw [this, h16]
    calc (4 ^ N + 4 ^ N + 4 ^ N) * r + 4 ^ N = 4 ^ N * (3 * r + 1) := by ring
      _ ≤ 4 ^ N * 16 ^ N := Nat.mul_le_mul_left _ h
  calc _ ≤ 2 ^ ((4 ^ N + 4 ^ N + 4 ^ N) * r) * 2 ^ (4 ^ N) := Nat.mul_le_mul_right _ hc
    _ = 2 ^ ((4 ^ N + 4 ^ N + 4 ^ N) * r + 4 ^ N) := by rw [pow_add]
    _ ≤ 2 ^ ((4 ^ N) ^ 3) := Nat.pow_le_pow_right (by norm_num) hexp

lemma ineq9 (N : ℕ) (hN : 9 ≤ N) : 12 * 12 ^ N < 16 ^ N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ n _ ih =>
    rw [pow_succ, pow_succ]
    have : 12 * (12 ^ n * 12) = 12 * (12 * 12 ^ n) := by ring
    rw [this]
    calc 12 * (12 * 12 ^ n) < 12 * 16 ^ n := by omega
      _ ≤ 16 ^ n * 16 := by omega

lemma ineq7 (N : ℕ) (hN : 7 ≤ N) : 6 * 12 ^ N < 16 ^ N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ n _ ih =>
    rw [pow_succ, pow_succ]
    have : 6 * (12 ^ n * 12) = 12 * (6 * 12 ^ n) := by ring
    rw [this]
    calc 12 * (6 * 12 ^ n) < 12 * 16 ^ n := by omega
      _ ≤ 16 ^ n * 16 := by omega

theorem gap (N : ℕ) (hN : 9 ≤ N) :
    (Finset.univ.filter (fun φ : Idx N → Idx N → Idx N → F =>
       ∃ C : Circuit (Idx N ⊕ Idx N) (Idx N), C.IsQuadratic ∧ Computes C φ ∧
         C.size ≤ 2 * 12 ^ N)).card
      * 2 ^ (4 ^ N) ≤ 2 ^ ((4 ^ N) ^ 3) := by
  have hsub : Finset.univ.filter (fun φ : Idx N → Idx N → Idx N → F =>
       ∃ C : Circuit (Idx N ⊕ Idx N) (Idx N), C.IsQuadratic ∧ Computes C φ ∧
         C.size ≤ 2 * 12 ^ N) ⊆
      Finset.univ.filter (fun φ : Idx N → Idx N → Idx N → F => RankLE φ (4 * 12 ^ N)) := by
    intro φ hφ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hφ ⊢
    obtain ⟨C, hq, hc, hs⟩ := hφ
    exact (rank_le_two_mul_size C hq φ hc).mono (by omega)
  refine le_trans (Nat.mul_le_mul_right _ (Finset.card_le_card hsub)) (card_bound N _ ?_)
  have := ineq9 N hN
  omega

theorem rank_gap (N : ℕ) (hN : 7 ≤ N) :
    (Finset.univ.filter (fun φ : Idx N → Idx N → Idx N → F => RankLE φ (2 * 12 ^ N))).card
      * 2 ^ (4 ^ N) ≤ 2 ^ ((4 ^ N) ^ 3) := by
  refine card_bound N _ ?_
  have := ineq7 N hN
  omega

end BilinearMcGap
