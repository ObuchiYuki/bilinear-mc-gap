import Mathlib

/-!
# Definitions: XOR–AND circuits over `𝔽₂`, bilinear maps, tensor rank

All statements of the project are phrased with these definitions only.

* A bilinear map with index types `X Y D` is a coefficient tensor `φ : X → Y → D → 𝔽₂`;
  output `a` on inputs `x, y` is `∑ k s, φ k s a * x k * y s`.
* A circuit on inputs `I` with outputs `O` has `size` AND gates (fan-in two).  Each AND
  input and each output is an affine combination (over `𝔽₂`) of the inputs and of the
  *earlier* AND gates.  XOR and constants are free: they live inside the affine combinations.
  So `size` is the number of AND gates, and `MC ≤ s` means "some circuit with `size = s`".
* A circuit is *quadratic* if no AND input uses an AND gate (AND-depth one; level-one
  circuits `L₁` of Mirwald–Schnorr, quadratic circuits of Boyar–Find).
-/

namespace BilinearMcGap

/-- The field with two elements. -/
abbrev F := ZMod 2

/-- An affine combination of the inputs `I` and of `g` gate values. -/
structure Affine (I : Type) (g : ℕ) where
  const : F
  lin : I → F
  gat : Fin g → F

/-- A circuit with `size` fan-in-two AND gates; gate `r` may only read gates `j < r`
(entries of `gat` at indices `≥ r` are ignored). -/
structure Circuit (I O : Type) where
  size : ℕ
  left : Fin size → Affine I size
  right : Fin size → Affine I size
  out : O → Affine I size

variable {I O : Type} [Fintype I]

/-- Value of an affine combination, reading only gates `j` with `j < bound`. -/
def Affine.evalBelow {g : ℕ} (A : Affine I g) (x : I → F) (bound : ℕ)
    (v : (j : Fin g) → j.val < bound → F) : F :=
  A.const + ∑ i, A.lin i * x i + ∑ j : Fin g, (if h : j.val < bound then A.gat j * v j h else 0)

/-- The value of AND gate `r` on input `x`. -/
def Circuit.gateVal (C : Circuit I O) (x : I → F) (r : Fin C.size) : F :=
  (C.left r).evalBelow x r.val (fun j _ => C.gateVal x j) *
  (C.right r).evalBelow x r.val (fun j _ => C.gateVal x j)
termination_by r.val
decreasing_by all_goals assumption

/-- The value of output `o` on input `x`. -/
def Circuit.outVal (C : Circuit I O) (x : I → F) (o : O) : F :=
  (C.out o).evalBelow x C.size (fun j _ => C.gateVal x j)

/-- A circuit is quadratic if no AND gate reads another AND gate. -/
def Circuit.IsQuadratic (C : Circuit I O) : Prop :=
  ∀ r j, (C.left r).gat j = 0 ∧ (C.right r).gat j = 0

/-- The bilinear map with coefficient tensor `φ`. -/
def bil {X Y D : Type} [Fintype X] [Fintype Y] (φ : X → Y → D → F)
    (x : X → F) (y : Y → F) (a : D) : F :=
  ∑ k, ∑ s, φ k s a * x k * y s

/-- `C` computes the bilinear map `φ` (inputs are `x ⊕ y`, as Boolean functions). -/
def Computes {X Y D : Type} [Fintype X] [Fintype Y] (C : Circuit (X ⊕ Y) D)
    (φ : X → Y → D → F) : Prop :=
  ∀ (x : X → F) (y : Y → F) (a : D), C.outVal (Sum.elim x y) a = bil φ x y a

/-- `φ` has tensor rank at most `r`. -/
def RankLE {X Y D : Type} (φ : X → Y → D → F) (r : ℕ) : Prop :=
  ∃ (u : Fin r → X → F) (v : Fin r → Y → F) (w : Fin r → D → F),
    ∀ k s a, φ k s a = ∑ ρ, u ρ k * v ρ s * w ρ a

/-- Index type of size `4 ^ N`: `Idx 0 = Unit`, `Idx (N+1) = Idx N × Fin 4`. -/
def Idx : ℕ → Type
  | 0 => Unit
  | N + 1 => Idx N × Fin 4

instance instFintypeIdx : ∀ N, Fintype (Idx N)
  | 0 => inferInstanceAs (Fintype Unit)
  | N + 1 => @instFintypeProd _ _ (instFintypeIdx N) (inferInstanceAs (Fintype (Fin 4)))

instance instDecEqIdx : ∀ N, DecidableEq (Idx N)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | N + 1 => @instDecidableEqProd _ _ (instDecEqIdx N) (inferInstanceAs (DecidableEq (Fin 4)))

theorem card_Idx : ∀ N, Fintype.card (Idx N) = 4 ^ N
  | 0 => rfl
  | N + 1 => by
    show Fintype.card (Idx N × Fin 4) = _
    rw [Fintype.card_prod, card_Idx N, Fintype.card_fin, pow_succ]

end BilinearMcGap
