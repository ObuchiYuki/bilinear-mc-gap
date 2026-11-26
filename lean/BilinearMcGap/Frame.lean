import BilinearMcGap.Defs

/-!
# Two-layer frames and the Ω criterion
-/

namespace BilinearMcGap

open Finset

theorem F_mul_self (z : F) : z * z = z := by
  revert z; decide

theorem F_add_self (z : F) : z + z = 0 := by
  revert z; decide

/-- A two-layer frame: gates `(λ_i ; c_i)` and products `ξ_j(x) η_j(y)`. -/
structure Frame (X Y D G P : Type) where
  lam : G → X → F
  c : G → D → F
  xi : P → X → F
  eta : P → Y → F

set_option linter.unusedSectionVars false

variable {X Y D G P : Type} [Fintype X] [Fintype Y] [Fintype D] [Fintype G] [Fintype P]
  [DecidableEq X] [DecidableEq Y] [DecidableEq D]

/-- Linear form. -/
def lin {Z : Type} [Fintype Z] (ℓ : Z → F) (z : Z → F) : F := ∑ k, ℓ k * z k

/-- Output `a` of the frame with wiring `Q`. -/
def Frame.eval (Fr : Frame X Y D G P) (Q : G → P → F) (x : X → F) (y : Y → F) (a : D) : F :=
  ∑ i, Fr.c i a * (lin (Fr.lam i) x * ∑ j, Q i j * (lin (Fr.xi j) x * lin (Fr.eta j) y))

/-- The 4-index tensor Ω. -/
def Frame.omega (Fr : Frame X Y D G P) (Q : G → P → F) (k l : X) (s : Y) (a : D) : F :=
  ∑ i, ∑ j, Q i j * (Fr.lam i k * Fr.c i a * Fr.xi j l * Fr.eta j s)

/-- `Q` satisfies the criterion for `φ`. -/
def Frame.Good (Fr : Frame X Y D G P) (Q : G → P → F) (φ : X → Y → D → F) : Prop :=
  (∀ k l s a, Fr.omega Q k l s a = Fr.omega Q l k s a) ∧ ∀ k s a, Fr.omega Q k k s a = φ k s a

def Frame.Universal (Fr : Frame X Y D G P) : Prop := ∀ φ, ∃ Q, Fr.Good Q φ

theorem Frame.eval_eq (Fr : Frame X Y D G P) (Q : G → P → F) (x : X → F) (y : Y → F) (a : D) :
    Fr.eval Q x y a = ∑ k, ∑ l, ∑ s, Fr.omega Q k l s a * (x k * x l * y s) := by
  simp only [Frame.eval, Frame.omega, lin, Finset.mul_sum, Finset.sum_mul]
  let e : (X × X × Y × G × P) ≃ (G × P × Y × X × X) :=
    { toFun := fun t => (t.2.2.2.1, t.2.2.2.2, t.2.2.1, t.2.1, t.1)
      invFun := fun t => (t.2.2.2.2, t.2.2.2.1, t.2.2.1, t.1, t.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := Fintype.sum_equiv e
    (fun t : X × X × Y × G × P => Q t.2.2.2.1 t.2.2.2.2 * (Fr.lam t.2.2.2.1 t.1 * Fr.c t.2.2.2.1 a *
        Fr.xi t.2.2.2.2 t.2.1 * Fr.eta t.2.2.2.2 t.2.2.1) * (x t.1 * x t.2.1 * y t.2.2.1))
    (fun t : G × P × Y × X × X => Fr.c t.1 a * (Fr.lam t.1 t.2.2.2.2 * x t.2.2.2.2 *
        (Q t.1 t.2.1 * (Fr.xi t.2.1 t.2.2.2.1 * x t.2.2.2.1 * (Fr.eta t.2.1 t.2.2.1 * y t.2.2.1)))))
    (fun t => by simp only [e, Equiv.coe_fn_mk]; ring)
  simp only [Fintype.sum_prod_type] at h
  exact h.symm

/-- The criterion (Lemma 1, sufficiency): if `Q` is good for `φ`, the frame computes `φ`. -/
theorem Frame.eval_of_good (Fr : Frame X Y D G P) (Q : G → P → F) (φ : X → Y → D → F)
    (hQ : Fr.Good Q φ) (x : X → F) (y : Y → F) (a : D) :
    Fr.eval Q x y a = bil φ x y a := by
  rw [Fr.eval_eq]
  set g : X → X → F := fun k l => ∑ s, Fr.omega Q k l s a * (x k * x l * y s) with hg
  have split : ∀ k l, g k l = (if k = l then g k l else 0) + (if k = l then 0 else g k l) := by
    intro k l; split_ifs <;> simp
  have hoff : ∑ p : X × X, (if p.1 = p.2 then 0 else g p.1 p.2) = 0 := by
    refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ (fun _ _ => Finset.mem_univ _)
      (fun p _ => Prod.swap_swap p)
    · intro p _
      by_cases h : p.1 = p.2
      · simp [h]
      · have h' : ¬ p.2 = p.1 := fun e => h e.symm
        simp only [Prod.fst_swap, Prod.snd_swap, h, h', if_false]
        have : g p.2 p.1 = g p.1 p.2 := by
          simp only [hg]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [hQ.1 p.2 p.1 s a]; ring
        rw [this, F_add_self]
    · intro p _ hne heq
      apply hne
      have : p.1 = p.2 := by
        have := congrArg Prod.fst heq; simpa using this.symm
      simp [this]
  calc ∑ k, ∑ l, ∑ s, Fr.omega Q k l s a * (x k * x l * y s) = ∑ k, ∑ l, g k l := rfl
    _ = ∑ k, ∑ l, (if k = l then g k l else 0) + ∑ p : X × X, (if p.1 = p.2 then 0 else g p.1 p.2) := by
        rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => split k l
    _ = ∑ k, g k k := by rw [hoff, add_zero]; simp
    _ = bil φ x y a := by
        simp only [hg, bil]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun s _ => ?_
        rw [hQ.2 k s a, F_mul_self]; ring

/-- Basis tensor. -/
def basisT (b : X × Y × D) : X → Y → D → F := fun k s a => if (k, s, a) = b then 1 else 0

theorem Frame.omega_lin (Fr : Frame X Y D G P) {B : Type} [Fintype B] (w : B → F)
    (Qb : B → G → P → F) (k l : X) (s : Y) (a : D) :
    Fr.omega (fun i j => ∑ b, w b * Qb b i j) k l s a = ∑ b, w b * Fr.omega (Qb b) k l s a := by
  simp only [Frame.omega, Finset.sum_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro b _
  ring

theorem Frame.universal_of_basis (Fr : Frame X Y D G P)
    (h : ∀ b : X × Y × D, ∃ Q, Fr.Good Q (basisT b)) : Fr.Universal := by
  intro φ
  choose Qb hQb using h
  refine ⟨fun i j => ∑ b : X × Y × D, φ b.1 b.2.1 b.2.2 * Qb b i j, ?_, ?_⟩
  · intro k l s a
    rw [Fr.omega_lin, Fr.omega_lin]
    exact Finset.sum_congr rfl fun b _ => by rw [(hQb b).1]
  · intro k s a
    rw [Fr.omega_lin]
    simp only [(hQb _).2, basisT, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp

/-- Tensor product of frames. -/
def Frame.prod {X₁ Y₁ D₁ G₁ P₁ X₂ Y₂ D₂ G₂ P₂ : Type} (F₁ : Frame X₁ Y₁ D₁ G₁ P₁)
    (F₂ : Frame X₂ Y₂ D₂ G₂ P₂) : Frame (X₁ × X₂) (Y₁ × Y₂) (D₁ × D₂) (G₁ × G₂) (P₁ × P₂) where
  lam i k := F₁.lam i.1 k.1 * F₂.lam i.2 k.2
  c i a := F₁.c i.1 a.1 * F₂.c i.2 a.2
  xi j k := F₁.xi j.1 k.1 * F₂.xi j.2 k.2
  eta j s := F₁.eta j.1 s.1 * F₂.eta j.2 s.2

section prod
variable {X₁ Y₁ D₁ G₁ P₁ X₂ Y₂ D₂ G₂ P₂ : Type}
  [Fintype X₁] [Fintype Y₁] [Fintype D₁] [Fintype G₁] [Fintype P₁]
  [Fintype X₂] [Fintype Y₂] [Fintype D₂] [Fintype G₂] [Fintype P₂]
  [DecidableEq X₁] [DecidableEq Y₁] [DecidableEq D₁] [DecidableEq X₂] [DecidableEq Y₂] [DecidableEq D₂]

theorem Frame.omega_prod (F₁ : Frame X₁ Y₁ D₁ G₁ P₁) (F₂ : Frame X₂ Y₂ D₂ G₂ P₂)
    (Q₁ : G₁ → P₁ → F) (Q₂ : G₂ → P₂ → F) (k l : X₁ × X₂) (s : Y₁ × Y₂) (a : D₁ × D₂) :
    (F₁.prod F₂).omega (fun i j => Q₁ i.1 j.1 * Q₂ i.2 j.2) k l s a =
      F₁.omega Q₁ k.1 l.1 s.1 a.1 * F₂.omega Q₂ k.2 l.2 s.2 a.2 := by
  simp only [Frame.omega, Frame.prod, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  let e : (G₁ × G₂ × P₁ × P₂) ≃ (G₂ × P₂ × G₁ × P₁) :=
    { toFun := fun t => (t.2.1, t.2.2.2, t.1, t.2.2.1)
      invFun := fun t => (t.2.2.1, t.1, t.2.2.2, t.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := Fintype.sum_equiv e
    (fun t : G₁ × G₂ × P₁ × P₂ => Q₁ t.1 t.2.2.1 * Q₂ t.2.1 t.2.2.2 *
      (F₁.lam t.1 k.1 * F₂.lam t.2.1 k.2 * (F₁.c t.1 a.1 * F₂.c t.2.1 a.2) *
        (F₁.xi t.2.2.1 l.1 * F₂.xi t.2.2.2 l.2) * (F₁.eta t.2.2.1 s.1 * F₂.eta t.2.2.2 s.2)))
    (fun t : G₂ × P₂ × G₁ × P₁ => Q₁ t.2.2.1 t.2.2.2 *
      (F₁.lam t.2.2.1 k.1 * F₁.c t.2.2.1 a.1 * F₁.xi t.2.2.2 l.1 * F₁.eta t.2.2.2 s.1) *
        (Q₂ t.1 t.2.1 * (F₂.lam t.1 k.2 * F₂.c t.1 a.2 * F₂.xi t.2.1 l.2 * F₂.eta t.2.1 s.2)))
    (fun t => by simp only [e, Equiv.coe_fn_mk]; ring)
  simp only [Fintype.sum_prod_type] at h
  exact h

theorem Frame.prod_universal (F₁ : Frame X₁ Y₁ D₁ G₁ P₁) (F₂ : Frame X₂ Y₂ D₂ G₂ P₂)
    (h₁ : F₁.Universal) (h₂ : F₂.Universal) : (F₁.prod F₂).Universal := by
  refine Frame.universal_of_basis _ fun b => ?_
  obtain ⟨Q₁, hQ₁⟩ := h₁ (basisT (b.1.1, b.2.1.1, b.2.2.1))
  obtain ⟨Q₂, hQ₂⟩ := h₂ (basisT (b.1.2, b.2.1.2, b.2.2.2))
  refine ⟨fun i j => Q₁ i.1 j.1 * Q₂ i.2 j.2, ?_, ?_⟩
  · intro k l s a
    rw [Frame.omega_prod, Frame.omega_prod, hQ₁.1, hQ₂.1]
  · intro k s a
    rw [Frame.omega_prod, hQ₁.2, hQ₂.2]
    obtain ⟨⟨b1, b2⟩, ⟨b3, b4⟩, ⟨b5, b6⟩⟩ := b
    simp only [basisT, Prod.mk.injEq]
    split_ifs <;> simp_all [Prod.ext_iff]
end prod

section reindex
variable {X' Y' D' : Type} [Fintype X'] [Fintype Y'] [Fintype D']
  [DecidableEq X'] [DecidableEq Y'] [DecidableEq D']

/-- Rename the coordinates of a frame. -/
def Frame.reindex (Fr : Frame X Y D G P) (eX : X' ≃ X) (eY : Y' ≃ Y) (eD : D' ≃ D) :
    Frame X' Y' D' G P where
  lam i k := Fr.lam i (eX k)
  c i a := Fr.c i (eD a)
  xi j k := Fr.xi j (eX k)
  eta j s := Fr.eta j (eY s)

theorem Frame.reindex_universal (Fr : Frame X Y D G P) (eX : X' ≃ X) (eY : Y' ≃ Y) (eD : D' ≃ D)
    (h : Fr.Universal) : (Fr.reindex eX eY eD).Universal := by
  intro φ
  obtain ⟨Q, hQ⟩ := h (fun k s a => φ (eX.symm k) (eY.symm s) (eD.symm a))
  refine ⟨Q, fun k l s a => hQ.1 (eX k) (eX l) (eY s) (eD a), fun k s a => ?_⟩
  have := hQ.2 (eX k) (eY s) (eD a)
  simp only [Equiv.symm_apply_apply] at this
  exact this
end reindex

end BilinearMcGap
