import FormalConjectures.Arxiv.«0805.3777».TensorRank

/-!
# The maximal rank of complex `3 × 3 × 5` tensors is six

This file proves the `research open` theorem `Arxiv.«0805.3777».isMaxRank_three_three_five` of
Formal Conjectures with the answer `6`: every complex `3 × 3 × 5` tensor has rank at most six, and
some tensor has rank exactly six. The definition `IsMaxRank` (and Mathlib's `Holor.cprank`) are the
ones imported from Formal Conjectures (commit `2424bb48`). The theorem
`Arxiv.«0805.3777».isMaxRank_three_three_five_bounds` (`6 ≤ R ≤ 7`) follows as well.

The development lives in the namespace `TensorRank335`; the two targets are at the end of the
file. The sections are, in order:

* `Bridge`: tensor rank ↔ spans of rank-one matrices containing the five slices;
* `Defs`: the pairing `dotM`, annihilators, column cubics;
* `LowerBound`: an explicit tensor of rank six;
* `ReflexR`: Lemma R — a squarefree column cubic gives a cover by six rank-one matrices;
* `Pencil`: a Bertini theorem for pencils of plane cubics;
* `Syzygy`, `SyzygyN`: the linear system of column cubics of the hyperplanes of `ann S`;
* `Nilpotent3`: Gerstenhaber's bound for `3 × 3` matrices, and four rank-one matrices suffice;
* `Degenerate`: the degenerate cases, by normal forms;
* `Upper`, `Main`: the case analysis and the final theorem.
-/

/- ## Section: `Bridge` -/

section

/-
# Rank of `3 × 3 × 5` tensors via spans of rank-one matrices

A tensor `T : Holor ℂ [3, 3, 5]` has five slices `slice T k : Matrix (Fin 3) (Fin 3) ℂ`
(`k : Fin 5`), obtained by fixing the last index. The classical bridge between tensor rank and
matrix spaces says that `T` has rank at most `r` exactly when the span of its slices is contained
in the span of `r` matrices of rank at most one. This is `cprank_le_iff`, phrased with the
predicate `CoveredBy`.

We also record the invariance of `CoveredBy` under `X ↦ P * X * Q` (for invertible `P`, `Q`) and
under transposition, and reduce a universal rank bound for `3 × 3 × 5` tensors to a statement about
subspaces of `3 × 3` matrices of dimension at most five (`cprank_le_of_forall_coveredBy`).

## Main declarations

* `TensorRank335.CoveredBy S r`: `S` lies in the span of `r` matrices of rank at most one.
* `TensorRank335.ev`, `TensorRank335.slice`, `TensorRank335.sliceSpan`, `TensorRank335.ofSlices`:
  entries, slices and the span of the slices of a `3 × 3 × 5` holor.
* `TensorRank335.cprank_le_iff`: `T.cprank ≤ r ↔ CoveredBy (sliceSpan T) r`.
* `TensorRank335.cprank_le_of_forall_coveredBy`.
-/

namespace TensorRank335

open Matrix

local infixl:70 " ⊗ " => Holor.mul

/- ### Rank-one spans of `3 × 3` matrices -/

/-- `S` lies in the span of `r` matrices of rank at most one. -/
def CoveredBy (S : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℂ)) (r : ℕ) : Prop :=
  ∃ a b : Fin r → Fin 3 → ℂ,
    S ≤ Submodule.span ℂ (Set.range fun l => vecMulVec (a l) (b l))

theorem CoveredBy.mono {S S' : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℂ)} {r : ℕ} (h : S' ≤ S)
    (hS : CoveredBy S r) : CoveredBy S' r := by
  obtain ⟨a, b, hab⟩ := hS
  exact ⟨a, b, h.trans hab⟩

theorem CoveredBy.mono_right {S : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℂ)} {r r' : ℕ} (h : r ≤ r')
    (hS : CoveredBy S r) : CoveredBy S r' := by
  obtain ⟨a, b, hab⟩ := hS
  refine ⟨fun l => if hl : l.1 < r then a ⟨l.1, hl⟩ else 0,
    fun l => if hl : l.1 < r then b ⟨l.1, hl⟩ else 0, hab.trans (Submodule.span_mono ?_)⟩
  rintro _ ⟨l, rfl⟩
  exact ⟨Fin.castLE h l, by simp⟩

/-- A linear map sending rank-one matrices to rank-one matrices preserves `CoveredBy`. -/
theorem CoveredBy.map {S : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℂ)} {r : ℕ}
    (f : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ)
    (hf : ∀ a b : Fin 3 → ℂ, ∃ a' b' : Fin 3 → ℂ, f (vecMulVec a b) = vecMulVec a' b')
    (hS : CoveredBy S r) : CoveredBy (S.map f) r := by
  obtain ⟨a, b, hab⟩ := hS
  choose a' b' h using hf
  refine ⟨fun l => a' (a l) (b l), fun l => b' (a l) (b l), (Submodule.map_mono hab).trans ?_⟩
  rw [Submodule.map_span, ← Set.range_comp]
  exact le_of_eq (congrArg _ (congrArg _ (funext fun l => h _ _)))

/-- `X ↦ P * X * Q` -/
def lrMul (P Q : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ where
  toFun X := P * X * Q
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

@[simp]
theorem lrMul_apply (P Q X : Matrix (Fin 3) (Fin 3) ℂ) : lrMul P Q X = P * X * Q :=
  rfl

theorem CoveredBy.map_lrMul {S : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℂ)} {r : ℕ}
    (P Q : Matrix (Fin 3) (Fin 3) ℂ) (hS : CoveredBy S r) : CoveredBy (S.map (lrMul P Q)) r :=
  hS.map _ fun a b => ⟨P *ᵥ a, b ᵥ* Q, by rw [lrMul_apply, mul_vecMulVec, vecMulVec_mul]⟩

/-- invariance: covering `P S Q` for invertible `P Q` covers `S` -/
theorem CoveredBy.of_map_lrMul {S : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℂ)} {r : ℕ}
    {P Q : Matrix (Fin 3) (Fin 3) ℂ} (hP : IsUnit P) (hQ : IsUnit Q)
    (h : CoveredBy (S.map (lrMul P Q)) r) : CoveredBy S r := by
  refine (h.map_lrMul ↑hP.unit⁻¹ ↑hQ.unit⁻¹).mono fun X hX => ?_
  rw [← Submodule.map_comp]
  refine ⟨X, hX, ?_⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, lrMul_apply]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP.val_inv_mul, Matrix.one_mul, Matrix.mul_assoc,
    hQ.mul_val_inv, Matrix.mul_one]

theorem CoveredBy.map_transpose {S : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℂ)} {r : ℕ}
    (hS : CoveredBy S r) :
    CoveredBy (S.map (Matrix.transposeLinearEquiv (Fin 3) (Fin 3) ℂ ℂ).toLinearMap) r :=
  hS.map _ fun a b => ⟨b, a, by simp⟩

theorem CoveredBy.of_map_transpose {S : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℂ)} {r : ℕ}
    (h : CoveredBy (S.map (Matrix.transposeLinearEquiv (Fin 3) (Fin 3) ℂ ℂ).toLinearMap) r) :
    CoveredBy S r := by
  refine h.map_transpose.mono fun X hX => ?_
  rw [← Submodule.map_comp]
  exact ⟨X, hX, by simp⟩

/- ### Entries and slices of `3 × 3 × 5` holors -/

/-- The index `(i, j, k)` of a `3 × 3 × 5` holor. -/
def ix (i j : Fin 3) (k : Fin 5) : HolorIndex [3, 3, 5] :=
  ⟨[i.1, j.1, k.1], .cons i.2 (.cons j.2 (.cons k.2 .nil))⟩

theorem ix_surjective (t : HolorIndex [3, 3, 5]) : ∃ i j k, t = ix i j k := by
  obtain ⟨l, h⟩ := t
  cases h with
  | cons ha h =>
    cases h with
    | cons hb h =>
      cases h with
      | cons hc h =>
        cases h
        exact ⟨⟨_, ha⟩, ⟨_, hb⟩, ⟨_, hc⟩, rfl⟩

/-- entry `(i,j,k)` of a `3×3×5` holor -/
def ev (T : Holor ℂ [3, 3, 5]) (i j : Fin 3) (k : Fin 5) : ℂ :=
  T (ix i j k)

theorem holor_ext {T T' : Holor ℂ [3, 3, 5]} (h : ∀ i j k, ev T i j k = ev T' i j k) :
    T = T' := by
  funext t
  obtain ⟨i, j, k, rfl⟩ := ix_surjective t
  exact h i j k

@[simp]
theorem ev_zero (i j : Fin 3) (k : Fin 5) : ev 0 i j k = 0 :=
  rfl

@[simp]
theorem ev_add (T T' : Holor ℂ [3, 3, 5]) (i j : Fin 3) (k : Fin 5) :
    ev (T + T') i j k = ev T i j k + ev T' i j k :=
  rfl

@[simp]
theorem ev_smul (c : ℂ) (T : Holor ℂ [3, 3, 5]) (i j : Fin 3) (k : Fin 5) :
    ev (c • T) i j k = c * ev T i j k :=
  rfl

theorem ev_sum {ι : Type*} (s : Finset ι) (f : ι → Holor ℂ [3, 3, 5]) (i j : Fin 3) (k : Fin 5) :
    ev (∑ l ∈ s, f l) i j k = ∑ l ∈ s, ev (f l) i j k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ev_add, ih]

/-- The `k`-th slice of a `3 × 3 × 5` holor. -/
def slice (T : Holor ℂ [3, 3, 5]) (k : Fin 5) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun i j => ev T i j k

@[simp]
theorem slice_apply (T : Holor ℂ [3, 3, 5]) (k : Fin 5) (i j : Fin 3) :
    slice T k i j = ev T i j k :=
  rfl

/-- The span of the slices of a `3 × 3 × 5` holor. -/
def sliceSpan (T : Holor ℂ [3, 3, 5]) : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℂ) :=
  Submodule.span ℂ (Set.range (slice T))

theorem headI_lt {d : ℕ} {ds : List ℕ} (t : HolorIndex (d :: ds)) : t.1.headI < d := by
  obtain ⟨l, h⟩ := t
  cases h with
  | cons ha _ => exact ha

theorem forall₂_tail {d : ℕ} {ds : List ℕ} (t : HolorIndex (d :: ds)) :
    List.Forall₂ (· < ·) t.1.tail ds := by
  obtain ⟨l, h⟩ := t
  cases h with
  | cons _ h => exact h

/-- The first coordinate of a holor index. -/
def idxHead {d : ℕ} {ds : List ℕ} (t : HolorIndex (d :: ds)) : Fin d :=
  ⟨t.1.headI, headI_lt t⟩

/-- The remaining coordinates of a holor index. -/
def idxTail {d : ℕ} {ds : List ℕ} (t : HolorIndex (d :: ds)) : HolorIndex ds :=
  ⟨t.1.tail, forall₂_tail t⟩

/-- The `3 × 3 × 5` holor with prescribed slices. -/
def ofSlices (M : Fin 5 → Matrix (Fin 3) (Fin 3) ℂ) : Holor ℂ [3, 3, 5] := fun t =>
  M (idxHead (idxTail (idxTail t))) (idxHead t) (idxHead (idxTail t))

@[simp]
theorem ev_ofSlices (M : Fin 5 → Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) (k : Fin 5) :
    ev (ofSlices M) i j k = M k i j :=
  rfl

theorem slice_ofSlices (M : Fin 5 → Matrix (Fin 3) (Fin 3) ℂ) : slice (ofSlices M) = M :=
  rfl

/- ### Rank-one holors -/

/-- A vector as a one-dimensional holor. -/
def vec {n : ℕ} (u : Fin n → ℂ) : Holor ℂ [n] := fun t => u (idxHead t)

/-- The scalar holor `1`. -/
def one0 : Holor ℂ [] := fun _ => 1

/-- The rank-one holor `u ⊗ v ⊗ w`. -/
def r1 (u v : Fin 3 → ℂ) (w : Fin 5 → ℂ) : Holor ℂ [3, 3, 5] :=
  vec u ⊗ (vec v ⊗ (vec w ⊗ one0))

@[simp]
theorem ev_r1 (u v : Fin 3 → ℂ) (w : Fin 5 → ℂ) (i j : Fin 3) (k : Fin 5) :
    ev (r1 u v w) i j k = u i * v j * w k := by
  show u i * (v j * (w k * 1)) = _
  ring

theorem cprankMax1_r1 (u v : Fin 3 → ℂ) (w : Fin 5 → ℂ) : Holor.CPRankMax1 (r1 u v w) :=
  .cons _ _ (.cons _ _ (.cons _ _ (.nil _)))

theorem cprankMax1_cons {α : Type} [Mul α] {d : ℕ} {ds : List ℕ} {x : Holor α (d :: ds)}
    (h : Holor.CPRankMax1 x) :
    ∃ (u : Holor α [d]) (y : Holor α ds), Holor.CPRankMax1 y ∧ x = u ⊗ y := by
  cases h with
  | cons u y hy => exact ⟨u, y, hy, rfl⟩

/-- The one-coordinate holor index `[i]`. -/
def ix1 {n : ℕ} (i : Fin n) : HolorIndex [n] :=
  ⟨[i.1], .cons i.2 .nil⟩

theorem cprankMax1_iff {x : Holor ℂ [3, 3, 5]} :
    Holor.CPRankMax1 x ↔ ∃ u v w, x = r1 u v w := by
  constructor
  · intro h
    obtain ⟨u₁, y₁, h₁, rfl⟩ := cprankMax1_cons h
    obtain ⟨u₂, y₂, h₂, rfl⟩ := cprankMax1_cons h₁
    obtain ⟨u₃, y₃, -, rfl⟩ := cprankMax1_cons h₂
    refine ⟨fun i => u₁ (ix1 i), fun j => u₂ (ix1 j), fun k => u₃ (ix1 k) * y₃ ⟨[], .nil⟩,
      holor_ext fun i j k => ?_⟩
    rw [ev_r1]
    show u₁ (ix1 i) * (u₂ (ix1 j) * (u₃ (ix1 k) * y₃ ⟨[], .nil⟩)) = _
    ring
  · rintro ⟨u, v, w, rfl⟩
    exact cprankMax1_r1 u v w

/- ### CP rank -/

/-- A holor of CP rank at most `n` is a sum of `n` holors of rank at most one. -/
theorem exists_sum_of_cprankMax {α : Type} [Mul α] [AddCommMonoid α] {ds : List ℕ} {n : ℕ}
    {x : Holor α ds} (h : Holor.CPRankMax n x) :
    ∃ f : Fin n → Holor α ds, (∀ l, Holor.CPRankMax1 (f l)) ∧ x = ∑ l, f l := by
  induction h with
  | zero => exact ⟨Fin.elim0, fun l => l.elim0, by simp⟩
  | succ n x y hx _ ih =>
    obtain ⟨f, hf, rfl⟩ := ih
    refine ⟨Fin.cons x f, fun l => Fin.cases hx hf l, ?_⟩
    rw [Fin.sum_univ_succ]
    rfl

theorem cprankMax_cprank {ds : List ℕ} (x : Holor ℂ ds) : Holor.CPRankMax x.cprank x :=
  @Nat.find_spec (fun n => Holor.CPRankMax n x) (Classical.decPred _)
    ⟨ds.prod, Holor.cprankMax_upper_bound x⟩

theorem cprank_le_of_cprankMax {ds : List ℕ} {x : Holor ℂ ds} {n : ℕ}
    (h : Holor.CPRankMax n x) : x.cprank ≤ n :=
  @Nat.find_min' (fun n => Holor.CPRankMax n x) (Classical.decPred _)
    ⟨ds.prod, Holor.cprankMax_upper_bound x⟩ n h

/-- the key bridge -/
theorem cprank_le_iff (T : Holor ℂ [3, 3, 5]) (r : ℕ) :
    T.cprank ≤ r ↔ CoveredBy (sliceSpan T) r := by
  constructor
  · intro h
    obtain ⟨n, hn, hTn⟩ : ∃ n, n ≤ r ∧ Holor.CPRankMax n T := ⟨_, h, cprankMax_cprank T⟩
    obtain ⟨f, hf, rfl⟩ := exists_sum_of_cprankMax hTn
    choose u v w huvw using fun l => cprankMax1_iff.mp (hf l)
    refine CoveredBy.mono_right hn ⟨u, v, Submodule.span_le.mpr ?_⟩
    rintro _ ⟨k, rfl⟩
    refine (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨fun l => w l k, ?_⟩
    ext i j
    rw [Matrix.sum_apply, slice_apply, ev_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [huvw, ev_r1, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    ring
  · rintro ⟨a, b, hS⟩
    have hk : ∀ k, ∃ c : Fin r → ℂ, ∑ l, c l • vecMulVec (a l) (b l) = slice T k := fun k =>
      (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hS (Submodule.subset_span ⟨k, rfl⟩))
    choose c hc using hk
    have hT : T = ∑ l, r1 (a l) (b l) (fun k => c k l) := by
      refine holor_ext fun i j k => ?_
      rw [ev_sum, ← slice_apply, ← hc k, Matrix.sum_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [ev_r1, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
      ring
    have hr := Holor.cprankMax_sum (n := 1) Finset.univ (fun l => r1 (a l) (b l) (fun k => c k l))
      fun l _ => Holor.cprankMax_1 (cprankMax1_r1 _ _ _)
    rw [Finset.card_univ, Fintype.card_fin, mul_one, ← hT] at hr
    exact cprank_le_of_cprankMax hr

theorem finrank_sliceSpan_le (T : Holor ℂ [3, 3, 5]) : Module.finrank ℂ (sliceSpan T) ≤ 5 :=
  (finrank_range_le_card (R := ℂ) (slice T)).trans_eq (Fintype.card_fin 5)

/-- universal bound reduces to subspaces of dimension ≤ 5 -/
theorem cprank_le_of_forall_coveredBy {r : ℕ}
    (h : ∀ S : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℂ), Module.finrank ℂ S ≤ 5 → CoveredBy S r)
    (T : Holor ℂ [3, 3, 5]) : T.cprank ≤ r :=
  (cprank_le_iff T r).mpr (h _ (finrank_sliceSpan_le T))

end TensorRank335

end

/- ## Section: `Defs` -/

section

/-
# Shared definitions for the universal upper bound

The universal bound `mrank(3, 3, 5) ≤ 6` is proved on the level of subspaces `S` of `3 × 3`
matrices. This file fixes the notation shared by all files of that proof:

* `TensorRank335.Mat`: complex `3 × 3` matrices.
* `TensorRank335.dotM X B = ∑ i j, X i j * B i j`, the bilinear trace pairing. For a rank-one
  matrix, `dotM (vecMulVec a b) B = a ⬝ᵥ (B *ᵥ b)`.
* `TensorRank335.ann S`: the annihilator of `S` for `dotM`.
* `TensorRank335.Kmat B`: for `B : Fin n → Mat`, the `3 × n` matrix of linear forms in the
  variables `X 0, X 1, X 2` whose column `k` is `B k *ᵥ X`.
* `TensorRank335.colCubic B = det (Kmat B)` for `B : Fin 3 → Mat`, the column cubic.
* `TensorRank335.crossMat b`, the matrix of `v ↦ b ×₃ v`.
-/

namespace TensorRank335

open Matrix MvPolynomial

/-- Complex `3 × 3` matrices. -/
abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ

/-- The bilinear pairing `⟨X, B⟩ = ∑ X_ij B_ij` on `3 × 3` matrices. -/
def dotM (X B : Mat) : ℂ := ∑ i, ∑ j, X i j * B i j

theorem dotM_comm (X B : Mat) : dotM X B = dotM B X := by
  simp [dotM, mul_comm]

@[simp] theorem dotM_zero_left (B : Mat) : dotM 0 B = 0 := by simp [dotM]

@[simp] theorem dotM_zero_right (X : Mat) : dotM X 0 = 0 := by simp [dotM]

theorem dotM_add_left (X Y B : Mat) : dotM (X + Y) B = dotM X B + dotM Y B := by
  simp [dotM, add_mul, Finset.sum_add_distrib]

theorem dotM_add_right (X B C : Mat) : dotM X (B + C) = dotM X B + dotM X C := by
  simp [dotM, mul_add, Finset.sum_add_distrib]

theorem dotM_smul_left (c : ℂ) (X B : Mat) : dotM (c • X) B = c * dotM X B := by
  simp [dotM, Finset.mul_sum, mul_assoc]

theorem dotM_smul_right (c : ℂ) (X B : Mat) : dotM X (c • B) = c * dotM X B := by
  simp [dotM, Finset.mul_sum, mul_left_comm]

theorem dotM_sum_left {ι : Type*} (s : Finset ι) (f : ι → Mat) (B : Mat) :
    dotM (∑ l ∈ s, f l) B = ∑ l ∈ s, dotM (f l) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert l s hl ih => rw [Finset.sum_insert hl, Finset.sum_insert hl, dotM_add_left, ih]

theorem dotM_sum_right {ι : Type*} (s : Finset ι) (X : Mat) (f : ι → Mat) :
    dotM X (∑ l ∈ s, f l) = ∑ l ∈ s, dotM X (f l) := by
  rw [dotM_comm, dotM_sum_left]
  simp [dotM_comm]

theorem dotM_vecMulVec (a b : Fin 3 → ℂ) (B : Mat) :
    dotM (vecMulVec a b) B = a ⬝ᵥ (B *ᵥ b) := by
  simp only [dotM, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dotM_transpose (X B : Mat) : dotM Xᵀ Bᵀ = dotM X B := by
  simp only [dotM, transpose_apply]
  exact Finset.sum_comm

/-- `dotM` is compatible with `X ↦ P * X * Q`. -/
theorem dotM_mul_mul (P Q X B : Mat) : dotM (P * X * Q) B = dotM X (Pᵀ * B * Qᵀ) := by
  simp only [dotM, mul_apply, transpose_apply, Fin.sum_univ_three]
  ring

/-- The annihilator of a subspace for `dotM`. -/
def ann (S : Submodule ℂ Mat) : Submodule ℂ Mat where
  carrier := {B | ∀ X ∈ S, dotM X B = 0}
  add_mem' {B C} hB hC X hX := by rw [dotM_add_right, hB X hX, hC X hX, add_zero]
  zero_mem' X _ := dotM_zero_right X
  smul_mem' c B hB X hX := by rw [dotM_smul_right, hB X hX, mul_zero]

theorem mem_ann {S : Submodule ℂ Mat} {B : Mat} : B ∈ ann S ↔ ∀ X ∈ S, dotM X B = 0 :=
  Iff.rfl

/-- `K(b)` as a matrix of linear forms: column `k` is `B k *ᵥ X`. -/
noncomputable def Kmat {n : ℕ} (B : Fin n → Mat) :
    Matrix (Fin 3) (Fin n) (MvPolynomial (Fin 3) ℂ) :=
  Matrix.of fun i k => ∑ j, C (B k i j) * X j

/-- The column cubic `det [B₀ b | B₁ b | B₂ b]`. -/
noncomputable def colCubic (B : Fin 3 → Mat) : MvPolynomial (Fin 3) ℂ :=
  (Kmat B).det

theorem eval_Kmat {n : ℕ} (B : Fin n → Mat) (b : Fin 3 → ℂ) (i : Fin 3) (k : Fin n) :
    eval b (Kmat B i k) = (B k *ᵥ b) i := by
  simp [Kmat, mulVec, dotProduct]

theorem eval_colCubic (B : Fin 3 → Mat) (b : Fin 3 → ℂ) :
    eval b (colCubic B) = (Matrix.of fun i k => (B k *ᵥ b) i).det := by
  rw [colCubic, RingHom.map_det]
  congr 1
  ext i k
  simp [eval_Kmat]

/-- The matrix of `v ↦ b ×₃ v`. -/
def crossMat (b : Fin 3 → ℂ) : Mat :=
  !![0, -b 2, b 1; b 2, 0, -b 0; -b 1, b 0, 0]

theorem crossMat_mulVec (b v : Fin 3 → ℂ) : crossMat b *ᵥ v = b ⨯₃ v := by
  ext i
  fin_cases i <;> simp [crossMat, mulVec, dotProduct, Fin.sum_univ_three, cross_apply] <;> ring

end TensorRank335

end

/- ## Section: `LowerBound` -/

section

/-
# A `3 × 3 × 5` tensor of rank six

We exhibit an explicit tensor `T₀ : Holor ℂ [3, 3, 5]` of rank exactly six. Its five slices are
`E₁₂, E₁₃, E₂₃, E₁₁ - E₂₂, E₂₂ - E₃₃`, a basis of the space of upper triangular `3 × 3`
matrices of trace zero.

* Upper bound: the slices lie in the span of the six upper triangular matrix units.
* Lower bound: suppose the slices lie in the span of five rank-one matrices `vecMulVec aₗ bₗ`.
  The slices are linearly independent, so by a dimension count the two spans coincide, and each
  `vecMulVec aₗ bₗ` is upper triangular of trace zero. A rank-one matrix of this shape has
  vanishing diagonal, so every matrix in the span has `(0, 0)` entry zero; but the slice
  `E₁₁ - E₂₂` does not.

## Main results

* `TensorRank335.cprank_T₀ : T₀.cprank = 6`.
* `TensorRank335.exists_cprank_eq_six : ∃ T : Holor ℂ [3, 3, 5], T.cprank = 6`.
-/

namespace TensorRank335

open Matrix

/-- The `3 × 3 × 5` tensor with slices `E₁₂, E₁₃, E₂₃, E₁₁ - E₂₂, E₂₂ - E₃₃`. -/
def T₀ : Holor ℂ [3, 3, 5] :=
  ofSlices ![single 0 1 1, single 0 2 1, single 1 2 1, single 0 0 1 - single 1 1 1,
    single 1 1 1 - single 2 2 1]

theorem slice_T₀ : slice T₀ = ![single 0 1 1, single 0 2 1, single 1 2 1,
    single 0 0 1 - single 1 1 1, single 1 1 1 - single 2 2 1] :=
  slice_ofSlices _

theorem ev_T₀ (i j : Fin 3) (k : Fin 5) : ev T₀ i j k = ![single 0 1 1, single 0 2 1,
    single 1 2 1, single 0 0 1 - single 1 1 1, single 1 1 1 - single 2 2 1] k i j :=
  rfl

/- ### Upper bound -/

/-- Rows of the six upper triangular positions. -/
def rowIdx : Fin 6 → Fin 3 := ![0, 0, 0, 1, 1, 2]

/-- Columns of the six upper triangular positions. -/
def colIdx : Fin 6 → Fin 3 := ![0, 1, 2, 1, 2, 2]

theorem coveredBy_six : CoveredBy (sliceSpan T₀) 6 := by
  refine ⟨fun l => Pi.single (rowIdx l) 1, fun l => Pi.single (colIdx l) 1, ?_⟩
  simp_rw [← single_eq_single_vecMulVec_single]
  rw [sliceSpan, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  have h : ∀ l, single (rowIdx l) (colIdx l) (1 : ℂ) ∈
      Submodule.span ℂ (Set.range fun l => single (rowIdx l) (colIdx l) (1 : ℂ)) :=
    fun l => Submodule.subset_span ⟨l, rfl⟩
  rw [slice_T₀]
  fin_cases k
  · exact h 1
  · exact h 2
  · exact h 4
  · exact Submodule.sub_mem _ (h 0) (h 3)
  · exact Submodule.sub_mem _ (h 3) (h 5)

/- ### Lower bound -/

theorem linearIndependent_slice_T₀ : LinearIndependent ℂ (slice T₀) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have e : ∀ i j, ∑ k, g k * slice T₀ k i j = 0 := fun i j => by
    simpa [Matrix.sum_apply] using congrFun (congrFun hg i) j
  have h01 := e 0 1
  have h02 := e 0 2
  have h12 := e 1 2
  have h00 := e 0 0
  have h22 := e 2 2
  simp [Fin.sum_univ_succ, ev_T₀] at h01 h02 h12 h00 h22
  intro k
  fin_cases k <;> simp_all

theorem finrank_sliceSpan_T₀ : Module.finrank ℂ (sliceSpan T₀) = 5 := by
  rw [sliceSpan, finrank_span_eq_card linearIndependent_slice_T₀, Fintype.card_fin]

/-- Every matrix in the span of the slices of `T₀` is upper triangular of trace zero. -/
theorem upperTriangular_of_mem {X : Matrix (Fin 3) (Fin 3) ℂ} (hX : X ∈ sliceSpan T₀) :
    X 1 0 = 0 ∧ X 2 0 = 0 ∧ X 2 1 = 0 ∧ X 0 0 + X 1 1 + X 2 2 = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hX
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Matrix.sum_apply, Fin.sum_univ_succ, slice_T₀]

/-- A rank-one matrix in the span of the slices of `T₀` has zero `(0, 0)` entry. -/
theorem mul_diag_eq_zero {a b : Fin 3 → ℂ} (h : vecMulVec a b ∈ sliceSpan T₀) :
    a 0 * b 0 = 0 := by
  obtain ⟨h10, h20, -, htr⟩ := upperTriangular_of_mem h
  simp only [vecMulVec_apply] at h10 h20 htr
  have : (a 0 * b 0) ^ 2 = 0 := by
    linear_combination (a 0 * b 0) * htr - (a 0 * b 1) * h10 - (a 0 * b 2) * h20
  exact (pow_eq_zero_iff two_ne_zero).mp this

theorem not_coveredBy_five : ¬ CoveredBy (sliceSpan T₀) 5 := by
  rintro ⟨a, b, hle⟩
  have hfin : Module.finrank ℂ (Submodule.span ℂ (Set.range fun l => vecMulVec (a l) (b l))) ≤
      Module.finrank ℂ (sliceSpan T₀) := by
    rw [finrank_sliceSpan_T₀]
    exact (finrank_range_le_card (R := ℂ) _).trans_eq (Fintype.card_fin 5)
  have heq := Submodule.eq_of_le_of_finrank_le hle hfin
  have h00 : ∀ l, a l 0 * b l 0 = 0 := by
    intro l
    apply mul_diag_eq_zero
    rw [heq]
    exact Submodule.subset_span ⟨l, rfl⟩
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hle (Submodule.subset_span ⟨3, rfl⟩))
  have := congrFun (congrFun hc 0) 0
  simp [Matrix.sum_apply, vecMulVec_apply, h00, ev_T₀] at this

theorem cprank_T₀ : T₀.cprank = 6 := by
  have h6 := (cprank_le_iff T₀ 6).mpr coveredBy_six
  have h5 : ¬ T₀.cprank ≤ 5 := fun h => not_coveredBy_five ((cprank_le_iff T₀ 5).mp h)
  omega

theorem exists_cprank_eq_six : ∃ T : Holor ℂ [3, 3, 5], T.cprank = 6 :=
  ⟨T₀, cprank_T₀⟩

end TensorRank335

end

/- ## Section: `ReflexR` -/

section

/-
# Lemma R: matrices vanishing on the rank-one kernel of a squarefree pencil

Let `B : Fin 3 → Mat` and let `f = colCubic B = det K` be the column cubic, where
`K = Kmat B` is the `3 × 3` matrix of linear forms whose column `k` is `B k *ᵥ X`.

*Lemma R* (`TensorRank335.mem_span_of_forall_rankOne`): if `f` is squarefree and `A : Mat`
satisfies `a ⬝ᵥ (A *ᵥ b) = 0` whenever `a ⬝ᵥ (B k *ᵥ b) = 0` for all `k`, then `A` lies in the
span of the `B k`.

Proof. Put `L = A *ᵥ X` (a vector of linear forms) and `P = cramer K L = adj(K) *ᵥ L`.
1. Each `P i` vanishes on the zero locus of `f`: if `f(b) = 0`, then every row `r` of
   `adj(K(b))` satisfies `r ⬝ᵥ (B k *ᵥ b) = 0` for all `k` (since `adj(K(b)) * K(b) = 0`), hence
   `r ⬝ᵥ (A *ᵥ b) = 0` by hypothesis, i.e. `P(b) = adj(K(b)) *ᵥ (A *ᵥ b) = 0`.
2. By the Nullstellensatz and squarefreeness, `f ∣ P i`.
3. `P i` and `f` are homogeneous cubics and `f ≠ 0`, so `P i = f * C (c i)` for constants `c i`.
4. `K *ᵥ P = f • L` (Cramer's rule), so cancelling `f` gives `L = K *ᵥ C c`, and comparing
   coefficients gives `A = ∑ k, c k • B k`.

As a consequence (`TensorRank335.coveredBy_six_of_squarefree_colCubic`), if `B 0, B 1, B 2`
annihilate `S` and `colCubic B` is squarefree, then `S` lies in the span of six rank-one
matrices: the common kernel of the functionals `dotM · (B k)` is six-dimensional (the `B k` are
linearly independent), and by Lemma R and duality it is spanned by the rank-one matrices it
contains. `TensorRank335.coveredBy_six_of_squarefree_colCubic_transpose` is the transposed version.
-/

namespace TensorRank335

open Matrix MvPolynomial

/- ### Homogeneity of the polynomials involved -/

/-- A linear form `∑ j, C (v j) * X j` is homogeneous of degree one. -/
theorem isHomogeneous_linForm (v : Fin 3 → ℂ) :
    (∑ j, C (v j) * X j : MvPolynomial (Fin 3) ℂ).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _

theorem isHomogeneous_Kmat {n : ℕ} (B : Fin n → Mat) (i : Fin 3) (k : Fin n) :
    (Kmat B i k).IsHomogeneous 1 := by
  simp only [Kmat, of_apply]
  exact isHomogeneous_linForm _

/-- The determinant of a `3 × 3` matrix of linear forms is a cubic form. -/
theorem isHomogeneous_det_of_linear {M : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ)}
    (hM : ∀ i j, (M i j).IsHomogeneous 1) : M.det.IsHomogeneous 3 := by
  have h : ∀ a b c d e g : Fin 3, (M a b * M c d * M e g).IsHomogeneous 3 :=
    fun a b c d e g => ((hM a b).mul (hM c d)).mul (hM e g)
  rw [det_fin_three]
  exact IsHomogeneous.sub (IsHomogeneous.add (IsHomogeneous.add (IsHomogeneous.sub
    (IsHomogeneous.sub (h _ _ _ _ _ _) (h _ _ _ _ _ _)) (h _ _ _ _ _ _)) (h _ _ _ _ _ _))
    (h _ _ _ _ _ _)) (h _ _ _ _ _ _)

/-- A nonzero cubic form divides a cubic form only up to a constant factor. -/
theorem exists_eq_mul_C_of_dvd {f p : MvPolynomial (Fin 3) ℂ} (hf : f ≠ 0)
    (hfh : f.IsHomogeneous 3) (hp : p.IsHomogeneous 3) (hdvd : f ∣ p) :
    ∃ c : ℂ, p = f * C c := by
  obtain ⟨q, rfl⟩ := hdvd
  have hdeg : q.totalDegree = 0 := by
    rcases eq_or_ne q 0 with rfl | hq
    · exact totalDegree_zero
    · have h := hp.totalDegree_le
      rw [totalDegree_mul_of_isDomain hf hq, hfh.totalDegree hf] at h
      omega
  exact ⟨q.coeff 0, by rw [← totalDegree_eq_zero_iff_eq_C.mp hdeg]⟩

/- ### The Nullstellensatz step -/

/-- A squarefree polynomial divides every polynomial vanishing on its zero locus. -/
theorem dvd_of_forall_eval_eq_zero {f p : MvPolynomial (Fin 3) ℂ} (hsq : Squarefree f)
    (h : ∀ b : Fin 3 → ℂ, eval b f = 0 → eval b p = 0) : f ∣ p := by
  have hmem : p ∈ vanishingIdeal ℂ (zeroLocus ℂ (Ideal.span {f})) := by
    rw [mem_vanishingIdeal_iff]
    intro x hx
    rw [mem_zeroLocus_iff] at hx
    have hfx : eval x f = 0 := hx f (Ideal.subset_span rfl)
    show eval x p = 0
    exact h x hfx
  rw [vanishingIdeal_zeroLocus_eq_radical, Ideal.mem_radical_iff] at hmem
  obtain ⟨n, hn⟩ := hmem
  exact hsq.isRadical n p (Ideal.mem_span_singleton.mp hn)

/- ### Proof of Lemma R -/

/-- The vector `A *ᵥ X` of linear forms. -/
noncomputable def linVec (A : Mat) : Fin 3 → MvPolynomial (Fin 3) ℂ :=
  fun k => ∑ j, C (A k j) * X j

theorem eval_linVec (A : Mat) (b : Fin 3 → ℂ) (k : Fin 3) :
    eval b (linVec A k) = (A *ᵥ b) k := by
  simp [linVec, mulVec, dotProduct]

theorem isHomogeneous_linVec (A : Mat) (k : Fin 3) : (linVec A k).IsHomogeneous 1 :=
  isHomogeneous_linForm _

/-- The numerical matrix `K(b) = [B 0 *ᵥ b | B 1 *ᵥ b | B 2 *ᵥ b]`. -/
def evalKmat (B : Fin 3 → Mat) (b : Fin 3 → ℂ) : Mat :=
  Matrix.of fun i k => (B k *ᵥ b) i

@[simp]
theorem evalKmat_apply (B : Fin 3 → Mat) (b : Fin 3 → ℂ) (i k : Fin 3) :
    evalKmat B b i k = (B k *ᵥ b) i :=
  rfl

theorem mapMatrix_eval_Kmat (B : Fin 3 → Mat) (b : Fin 3 → ℂ) :
    (eval b).mapMatrix (Kmat B) = evalKmat B b := by
  ext i k
  simp [eval_Kmat]

/-- Step 1: the entries of `adj(K) *ᵥ (A *ᵥ X)` vanish on the zero locus of `colCubic B`. -/
theorem eval_cramer_eq_zero (B : Fin 3 → Mat) (A : Mat)
    (hA : ∀ a b : Fin 3 → ℂ, (∀ k, a ⬝ᵥ (B k *ᵥ b) = 0) → a ⬝ᵥ (A *ᵥ b) = 0)
    (b : Fin 3 → ℂ) (hb : eval b (colCubic B) = 0) (i : Fin 3) :
    eval b (cramer (Kmat B) (linVec A) i) = 0 := by
  have hdet : (evalKmat B b).det = 0 := (eval_colCubic B b).symm.trans hb
  have hrow : ∀ k, adjugate (evalKmat B b) i ⬝ᵥ (B k *ᵥ b) = 0 := by
    intro k
    have h := congrFun (congrFun (adjugate_mul (evalKmat B b)) i) k
    rw [hdet, zero_smul] at h
    simpa [Matrix.mul_apply, dotProduct] using h
  have hadj : ∀ k, eval b (adjugate (Kmat B) i k) = adjugate (evalKmat B b) i k := by
    intro k
    rw [← mapMatrix_eval_Kmat, ← RingHom.map_adjugate]
    rfl
  calc eval b (cramer (Kmat B) (linVec A) i)
      = ∑ k, eval b (adjugate (Kmat B) i k) * eval b (linVec A k) := by
        rw [cramer_eq_adjugate_mulVec]
        simp only [mulVec, dotProduct, map_sum, map_mul]
    _ = adjugate (evalKmat B b) i ⬝ᵥ (A *ᵥ b) := by
        simp only [dotProduct, eval_linVec, hadj]
    _ = 0 := hA _ _ hrow

/-- **Lemma R.** -/
theorem mem_span_of_forall_rankOne (B : Fin 3 → Mat) (hsq : Squarefree (colCubic B)) (A : Mat)
    (hA : ∀ a b : Fin 3 → ℂ, (∀ k, a ⬝ᵥ (B k *ᵥ b) = 0) → a ⬝ᵥ (A *ᵥ b) = 0) :
    A ∈ Submodule.span ℂ (Set.range B) := by
  have hf0 : colCubic B ≠ 0 := hsq.ne_zero
  have hfh : (colCubic B).IsHomogeneous 3 := isHomogeneous_det_of_linear (isHomogeneous_Kmat B)
  -- Steps 1–3: `cramer K L = f • C c`
  have hP : ∀ i, ∃ c : ℂ, cramer (Kmat B) (linVec A) i = colCubic B * C c := by
    intro i
    refine exists_eq_mul_C_of_dvd hf0 hfh ?_ ?_
    · rw [cramer_apply]
      refine isHomogeneous_det_of_linear fun r s => ?_
      rw [updateCol_apply]
      split_ifs
      · exact isHomogeneous_linVec A r
      · exact isHomogeneous_Kmat B r s
    · exact dvd_of_forall_eval_eq_zero hsq fun b hb => eval_cramer_eq_zero B A hA b hb i
  choose c hc using hP
  -- Step 4: cancel `f` in `K *ᵥ cramer K L = f • L`
  have hlin : ∀ i, linVec A i = ∑ k, Kmat B i k * C (c k) := by
    intro i
    have h1 := congrFun (mulVec_cramer (Kmat B) (linVec A)) i
    simp only [mulVec, dotProduct, hc, Pi.smul_apply, smul_eq_mul] at h1
    rw [show (Kmat B).det = colCubic B from rfl] at h1
    apply mul_left_cancel₀ hf0
    rw [← h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  -- compare coefficients by evaluating at the standard basis vectors
  have hA' : ∑ k, c k • B k = A := by
    ext i j
    have h := congrArg (fun p => eval (Pi.single j 1 : Fin 3 → ℂ) p) (hlin i)
    simp only [eval_linVec, map_sum, map_mul, eval_Kmat, eval_C, mulVec_single_one,
      col_apply] at h
    rw [Matrix.sum_apply, h]
    exact Finset.sum_congr rfl fun k _ => by rw [Matrix.smul_apply, smul_eq_mul, mul_comm]
  exact (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨c, hA'⟩

/- ### Linear algebra around `dotM` -/

/-- `X ↦ dotM X B` as a linear functional. -/
def dotMLeft (B : Mat) : Module.Dual ℂ Mat where
  toFun X := dotM X B
  map_add' X Y := dotM_add_left X Y B
  map_smul' c X := dotM_smul_left c X B

@[simp]
theorem dotMLeft_apply (B X : Mat) : dotMLeft B X = dotM X B :=
  rfl

/-- `X ↦ (dotM X (B k))ₖ`. -/
def dotMap {n : ℕ} (B : Fin n → Mat) : Mat →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi fun k => dotMLeft (B k)

@[simp]
theorem dotMap_apply {n : ℕ} (B : Fin n → Mat) (X : Mat) (k : Fin n) :
    dotMap B X k = dotM X (B k) :=
  rfl

theorem dotM_single_one (i j : Fin 3) (M : Mat) : dotM (single i j 1) M = M i j := by
  rw [single_eq_single_vecMulVec_single, dotM_vecMulVec, mulVec_single_one, single_dotProduct,
    one_mul, col_apply]

/-- Every linear functional on `Mat` is of the form `dotM · A`. -/
theorem exists_dotM_eq (ψ : Module.Dual ℂ Mat) : ∃ A : Mat, ∀ X, ψ X = dotM X A := by
  refine ⟨Matrix.of fun i j => ψ (single i j 1), fun X => ?_⟩
  conv_lhs => rw [matrix_eq_sum_single X]
  simp only [map_sum, dotM, of_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

/-- If `colCubic B ≠ 0`, the matrices `B k` are linearly independent. -/
theorem eq_zero_of_sum_smul_eq_zero (B : Fin 3 → Mat) (hf : colCubic B ≠ 0) (c : Fin 3 → ℂ)
    (hc : ∑ k, c k • B k = 0) : c = 0 := by
  have hKv : Kmat B *ᵥ (fun k => C (c k)) = 0 := by
    funext i
    have h : ∀ j, ∑ k, c k * B k i j = 0 := fun j => by
      have := congrFun (congrFun hc i) j
      simpa [Matrix.sum_apply] using this
    simp only [mulVec, dotProduct, Kmat, of_apply, Pi.zero_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have e : ∑ k, C (B k i j) * X j * C (c k) =
        (C (∑ k, c k * B k i j) * X j : MvPolynomial (Fin 3) ℂ) := by
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul]
      ring
    rw [e, h j, map_zero, zero_mul]
  have h2 : (Kmat B).det • (fun k => C (c k) : Fin 3 → MvPolynomial (Fin 3) ℂ) = 0 := by
    calc (Kmat B).det • (fun k => C (c k) : Fin 3 → MvPolynomial (Fin 3) ℂ)
        = (adjugate (Kmat B) * Kmat B) *ᵥ (fun k => C (c k)) := by
          rw [adjugate_mul, smul_mulVec, one_mulVec]
      _ = 0 := by rw [← mulVec_mulVec, hKv, mulVec_zero]
  funext k
  have h3 := congrFun h2 k
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_eq_zero, C_eq_zero] at h3
  exact h3.resolve_left hf

/-- If `colCubic B ≠ 0`, then `X ↦ (dotM X (B k))ₖ` is surjective. -/
theorem range_dotMap_eq_top (B : Fin 3 → Mat) (hf : colCubic B ≠ 0) :
    LinearMap.range (dotMap B) = ⊤ := by
  rw [← Submodule.dualAnnihilator_eq_bot_iff, eq_bot_iff]
  intro ψ hψ
  rw [Submodule.mem_dualAnnihilator] at hψ
  rw [Submodule.mem_bot]
  obtain ⟨c, hc⟩ : ∃ c : Fin 3 → ℂ, ∀ v, ψ v = ∑ k, v k * c k :=
    ⟨fun k => ψ fun j => if k = j then 1 else 0, fun v => by
      rw [LinearMap.pi_apply_eq_sum_univ ψ v]
      simp only [smul_eq_mul]⟩
  have hsum : ∑ k, c k • B k = 0 := by
    ext i j
    have h := hψ (dotMap B (single i j 1)) (LinearMap.mem_range_self _ _)
    simp only [hc, dotMap_apply, dotM_single_one] at h
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have h0 := eq_zero_of_sum_smul_eq_zero B hf c hsum
  refine LinearMap.ext fun v => ?_
  rw [hc v, h0]
  simp

/- ### Covering by six rank-one matrices -/

/-- A subspace inside the span of a set of rank-one matrices whose span has dimension `≤ r` is
covered by `r` rank-one matrices. -/
theorem coveredBy_of_le_span {S : Submodule ℂ Mat} {R : Set Mat} {r : ℕ}
    (hR : ∀ M ∈ R, ∃ a b : Fin 3 → ℂ, M = vecMulVec a b)
    (hS : S ≤ Submodule.span ℂ R) (hr : Module.finrank ℂ (Submodule.span ℂ R) ≤ r) :
    CoveredBy S r := by
  obtain ⟨T, hTR, hspan, hli⟩ := exists_linearIndependent ℂ R
  have hTfin : T.Finite := hli.setFinite
  have : Fintype T := hTfin.fintype
  have hcard : Fintype.card T ≤ r := by
    rw [← finrank_span_eq_card hli, Subtype.range_coe, hspan]
    exact hr
  let e : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  choose a b hab using fun l : Fin (Fintype.card T) => hR _ (hTR (e l).2)
  refine CoveredBy.mono_right hcard ⟨a, b, hS.trans ?_⟩
  rw [← hspan]
  refine Submodule.span_mono ?_
  intro M hM
  refine ⟨e.symm ⟨M, hM⟩, ?_⟩
  simp only
  rw [← hab, Equiv.apply_symm_apply]

/-- The rank-one matrices `vecMulVec a b` with `a ⬝ᵥ (B k *ᵥ b) = 0` for all `k`. -/
def rankOneKer (B : Fin 3 → Mat) : Set Mat :=
  {M | ∃ a b : Fin 3 → ℂ, M = vecMulVec a b ∧ ∀ k, a ⬝ᵥ (B k *ᵥ b) = 0}

theorem coveredBy_six_of_squarefree_colCubic (S : Submodule ℂ Mat) (B : Fin 3 → Mat)
    (hB : ∀ k, B k ∈ ann S) (hsq : Squarefree (colCubic B)) : CoveredBy S 6 := by
  have hf0 : colCubic B ≠ 0 := hsq.ne_zero
  -- the common kernel of the `dotM · (B k)` is spanned by its rank-one elements
  have hker : LinearMap.ker (dotMap B) ≤ Submodule.span ℂ (rankOneKer B) := by
    intro X₀ hX₀
    have hX : ∀ k, dotM X₀ (B k) = 0 := fun k => by
      simpa using congrFun (LinearMap.mem_ker.mp hX₀) k
    refine (Subspace.dualAnnihilator_dualCoannihilator_eq
      (W := Submodule.span ℂ (rankOneKer B))).le ?_
    rw [Submodule.mem_dualCoannihilator]
    intro ψ hψ
    rw [Submodule.mem_dualAnnihilator] at hψ
    obtain ⟨A, hAψ⟩ := exists_dotM_eq ψ
    have hA : ∀ a b : Fin 3 → ℂ, (∀ k, a ⬝ᵥ (B k *ᵥ b) = 0) → a ⬝ᵥ (A *ᵥ b) = 0 := by
      intro a b hab
      rw [← dotM_vecMulVec, ← hAψ]
      exact hψ _ (Submodule.subset_span ⟨a, b, rfl, hab⟩)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
      (mem_span_of_forall_rankOne B hsq A hA)
    rw [hAψ, ← hc, dotM_sum_right]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [dotM_smul_right, hX k, mul_zero]
  have hS : S ≤ LinearMap.ker (dotMap B) := fun X hX => by
    rw [LinearMap.mem_ker]
    funext k
    exact mem_ann.mp (hB k) X hX
  have hRker : Submodule.span ℂ (rankOneKer B) ≤ LinearMap.ker (dotMap B) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, b, rfl, hab⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    funext k
    rw [dotMap_apply, dotM_vecMulVec, hab k, Pi.zero_apply]
  have hdim : Module.finrank ℂ (LinearMap.ker (dotMap B)) = 6 := by
    have h := LinearMap.finrank_range_add_finrank_ker (dotMap B)
    rw [range_dotMap_eq_top B hf0, finrank_top, Module.finrank_fin_fun, Module.finrank_matrix,
      Fintype.card_fin, Module.finrank_self] at h
    omega
  refine coveredBy_of_le_span ?_ (hS.trans hker) ((Submodule.finrank_mono hRker).trans hdim.le)
  rintro M ⟨a, b, rfl, -⟩
  exact ⟨a, b, rfl⟩

theorem coveredBy_six_of_squarefree_colCubic_transpose (S : Submodule ℂ Mat) (B : Fin 3 → Mat)
    (hB : ∀ k, B k ∈ ann S) (hsq : Squarefree (colCubic fun k => (B k)ᵀ)) : CoveredBy S 6 := by
  refine CoveredBy.of_map_transpose
    (coveredBy_six_of_squarefree_colCubic _ (fun k => (B k)ᵀ) (fun k => ?_) hsq)
  rw [mem_ann]
  rintro _ ⟨X, hX, rfl⟩
  show dotM Xᵀ (B k)ᵀ = 0
  rw [dotM_transpose]
  exact mem_ann.mp (hB k) X hX

end TensorRank335

end

/- ## Section: `Pencil` -/

section

/-
# Bertini's theorem for pencils of ternary cubics

Let `f g : ℂ[x₀, x₁, x₂]` be cubic forms (the zero polynomial is allowed). If no member
`f + t g` (`t ∈ ℂ`) of the pencil is squarefree, then `f` and `g` are both divisible by the square
`p ^ 2` of one linear polynomial `p` (`TensorRank335.exists_sq_dvd_of_pencil`). The same holds for
the family `m 3 + ∑ c_k m k` (`TensorRank335.exists_sq_dvd_of_family`).

## Proof

* Degenerate case: `f` and `g` are linearly dependent. Then one member of the pencil is a nonzero
  multiple of a single cubic `h` (or everything vanishes), and a square factor of `h` works.
* Main case: `f` and `g` are independent. For six distinct values `t`, the member `h_t = f + t g`
  is nonzero and has a square factor `p_t ^ 2` with `p_t` linear. If two of the `p_t` divide each
  other, then `p_t ^ 2` divides `h_t - h_s = (t - s) g`, hence `g` and `f`. Otherwise the `p_t` are
  pairwise coprime primes. Each `p_t` divides
  `K_j = f ∂_j g - g ∂_j f = h_t ∂_j g - g ∂_j h_t`, and `K_j` has degree `≤ 5 < 6`, so `K_j = 0`.
  Comparing leading coefficients for a monomial order in `f (X_j ∂_j g) = g (X_j ∂_j f)` shows that
  `f` and `g` have the same leading monomial, and then that `f` is a multiple of `g`, which is a
  contradiction.
* Family version: a nonzero cubic has at most one linear square factor up to association, so the
  square factors obtained from the pencils through a fixed nonzero member all agree.
-/

namespace TensorRank335

open MvPolynomial

namespace Pencil

/-- In `ℂ[x₀, x₁, x₂]`, a polynomial of total degree one is irreducible. -/
theorem irreducible_of_totalDegree_one {p : MvPolynomial (Fin 3) ℂ} (hp : p.totalDegree = 1) :
    Irreducible p := by
  refine MvPolynomial.irreducible_of_totalDegree_eq_one hp fun x hx => ?_
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hp
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp hp0
  rw [isUnit_iff_ne_zero]
  rintro rfl
  exact hd (zero_dvd_iff.mp (hx d))

/-- A nonzero non-squarefree polynomial of total degree at most `3` is divisible by the square
of an irreducible polynomial of total degree `1`. -/
theorem exists_irreducible_sq_dvd {h : MvPolynomial (Fin 3) ℂ} (h0 : h ≠ 0)
    (h3 : h.totalDegree ≤ 3) (hs : ¬ Squarefree h) :
    ∃ p : MvPolynomial (Fin 3) ℂ, Irreducible p ∧ p.totalDegree = 1 ∧ p ^ 2 ∣ h := by
  unfold Squarefree at hs
  push Not at hs
  obtain ⟨x, hx, hxu⟩ := hs
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [mul_zero, zero_dvd_iff] at hx
    exact h0 hx
  obtain ⟨p, hp, hpx⟩ := WfDvdMonoid.exists_irreducible_factor hxu hx0
  have hp2 : p ^ 2 ∣ h := by
    rw [sq]
    exact (mul_dvd_mul hpx hpx).trans hx
  refine ⟨p, hp, ?_, hp2⟩
  have hp0 : p ≠ 0 := hp.ne_zero
  have hdeg := totalDegree_le_of_dvd_of_isDomain hp2 h0
  rw [sq, totalDegree_mul_of_isDomain hp0 hp0] at hdeg
  have hpos : p.totalDegree ≠ 0 := by
    intro hd
    apply hp.not_isUnit
    rw [isUnit_iff_totalDegree_of_isReduced]
    refine ⟨isUnit_iff_ne_zero.mpr fun hc => hp0 ?_, hd⟩
    rw [totalDegree_eq_zero_iff_eq_C] at hd
    rw [hd, hc, map_zero]
  omega

/-- If `p ^ 2 ∣ h`, then `p` divides every partial derivative of `h`. -/
theorem dvd_pderiv_of_sq_dvd {p h : MvPolynomial (Fin 3) ℂ} (hph : p ^ 2 ∣ h) (j : Fin 3) :
    p ∣ pderiv j h := by
  obtain ⟨r, rfl⟩ := hph
  refine ⟨2 * pderiv j p * r + p * pderiv j r, ?_⟩
  rw [sq, pderiv_mul, pderiv_mul]
  ring

/-- The total degree is additive on finite products of nonzero polynomials. -/
theorem totalDegree_finset_prod_eq {ι : Type*} (s : Finset ι) (q : ι → MvPolynomial (Fin 3) ℂ)
    (hq : ∀ i ∈ s, q i ≠ 0) : (∏ i ∈ s, q i).totalDegree = ∑ i ∈ s, (q i).totalDegree := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      totalDegree_mul_of_isDomain (hq a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hq i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hq i (Finset.mem_insert_of_mem hi)]

/-- The coefficient of `x ^ d` in `X j * ∂_j p` is `d j` times the coefficient of `x ^ d` in
`p`. -/
theorem coeff_X_mul_pderiv {σ : Type*} (j : σ) (p : MvPolynomial σ ℂ) (d : σ →₀ ℕ) :
    (X j * pderiv j p).coeff d = (d j : ℂ) * p.coeff d := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, mul_add, MvPolynomial.coeff_add, hp, hq]
  | monomial n a =>
    rw [X_mul_pderiv_monomial, coeff_smul, coeff_monomial]
    split_ifs with hnd
    · subst hnd
      rw [nsmul_eq_mul]
    · simp

theorem support_X_mul_pderiv_subset {σ : Type*} (j : σ) (p : MvPolynomial σ ℂ) :
    (X j * pderiv j p).support ⊆ p.support := by
  intro d hd
  rw [MvPolynomial.mem_support_iff] at hd ⊢
  rw [coeff_X_mul_pderiv] at hd
  exact right_ne_zero_of_mul hd

/-- If `f ∂_j g = g ∂_j f` for all `j` and `f, g ≠ 0`, then `f` and `g` have the same leading
monomial for any monomial order: compare the coefficients of `x ^ (deg f + deg g)` in
`f (X_j ∂_j g) = g (X_j ∂_j f)`. -/
theorem degree_eq_of_forall_mul_pderiv_eq {σ : Type*} (o : MonomialOrder σ)
    {f g : MvPolynomial σ ℂ} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : ∀ j, f * pderiv j g = g * pderiv j f) : o.degree f = o.degree g := by
  ext j
  have e : f * (X j * pderiv j g) = g * (X j * pderiv j f) := by
    rw [show f * (X j * pderiv j g) = X j * (f * pderiv j g) by ring, h j]
    ring
  have key : (f * (X j * pderiv j g)).coeff (o.degree f + o.degree g) =
      (g * (X j * pderiv j f)).coeff (o.degree g + o.degree f) := by
    rw [add_comm (o.degree g) (o.degree f), e]
  rw [MonomialOrder.coeff_mul_of_add_of_degree_le (m := o) le_rfl
      (o.degree_le_degree_of_support_subset (support_X_mul_pderiv_subset j g)),
    MonomialOrder.coeff_mul_of_add_of_degree_le (m := o) le_rfl
      (o.degree_le_degree_of_support_subset (support_X_mul_pderiv_subset j f)),
    coeff_X_mul_pderiv, coeff_X_mul_pderiv] at key
  have hfa : f.coeff (o.degree f) ≠ 0 := o.coeff_degree_ne_zero_iff.mpr hf
  have hgb : g.coeff (o.degree g) ≠ 0 := o.coeff_degree_ne_zero_iff.mpr hg
  have hj : ((o.degree f j : ℕ) : ℂ) = (o.degree g j : ℕ) := by
    apply mul_left_cancel₀ (mul_ne_zero hfa hgb)
    linear_combination -1 * key
  exact_mod_cast hj

/-- If `f ∂_j g = g ∂_j f` for all `j` and `g ≠ 0`, then `f` is a scalar multiple of `g`. -/
theorem exists_eq_C_mul_of_forall_mul_pderiv_eq {σ : Type*} (o : MonomialOrder σ)
    {f g : MvPolynomial σ ℂ} (hg : g ≠ 0) (h : ∀ j, f * pderiv j g = g * pderiv j f) :
    ∃ c : ℂ, f = C c * g := by
  by_cases hf : f = 0
  · exact ⟨0, by rw [hf, map_zero, zero_mul]⟩
  have hdfg : o.degree f = o.degree g := degree_eq_of_forall_mul_pderiv_eq o hf hg h
  have hlg : o.leadingCoeff g ≠ 0 := o.leadingCoeff_ne_zero_iff.mpr hg
  obtain ⟨F, hF⟩ : ∃ F : MvPolynomial σ ℂ,
      F = C (o.leadingCoeff g) * f - C (o.leadingCoeff f) * g := ⟨_, rfl⟩
  have hFw : ∀ j, F * pderiv j g = g * pderiv j F := by
    intro j
    rw [hF, map_sub, pderiv_C_mul, pderiv_C_mul]
    linear_combination C (o.leadingCoeff g) * h j
  by_cases hF0 : F = 0
  · refine ⟨o.leadingCoeff f / o.leadingCoeff g, ?_⟩
    have e : C (o.leadingCoeff g) * f = C (o.leadingCoeff f) * g := by
      rw [← sub_eq_zero, ← hF, hF0]
    calc f = C (o.leadingCoeff g)⁻¹ * (C (o.leadingCoeff g) * f) := by
          rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hlg, map_one, one_mul]
      _ = C (o.leadingCoeff f / o.leadingCoeff g) * g := by
          rw [e, ← mul_assoc, ← map_mul, div_eq_inv_mul]
  · exfalso
    have hdFg : o.degree F = o.degree g := degree_eq_of_forall_mul_pderiv_eq o hF0 hg hFw
    apply hF0
    rw [← o.coeff_degree_eq_zero_iff, hdFg, hF, coeff_sub, coeff_C_mul, coeff_C_mul]
    have e1 : f.coeff (o.degree g) = o.leadingCoeff f := by
      rw [MonomialOrder.leadingCoeff, hdfg]
    have e2 : g.coeff (o.degree g) = o.leadingCoeff g := rfl
    rw [e1, e2]
    ring

/-- A nonzero polynomial of total degree `≤ 3` has at most one linear square factor up to
association: if `p ^ 2 ∣ F` and `q ^ 2 ∣ F` with `p, q` linear, then `p ∣ q`. -/
theorem dvd_of_sq_dvd_of_sq_dvd {F p q : MvPolynomial (Fin 3) ℂ} (hF : F ≠ 0)
    (hF3 : F.totalDegree ≤ 3) (hp : p.totalDegree = 1) (hq : q.totalDegree = 1)
    (hpF : p ^ 2 ∣ F) (hqF : q ^ 2 ∣ F) : p ∣ q := by
  by_contra hpq
  have hpp : Prime p :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp (irreducible_of_totalDegree_one hp)
  have hp0 : p ≠ 0 := hpp.ne_zero
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hq
  have hnd : ¬ p ∣ q ^ 2 := fun hd => hpq (hpp.dvd_of_dvd_pow hd)
  obtain ⟨r, hr⟩ := hqF
  have hpr : p ^ 2 ∣ r := hpp.pow_dvd_of_dvd_mul_left 2 hnd (hr ▸ hpF)
  obtain ⟨s, hs⟩ := hpr
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hF
    rw [hr, hs, mul_zero, mul_zero]
  have hdeg : F.totalDegree =
      q.totalDegree + q.totalDegree + (p.totalDegree + p.totalDegree + s.totalDegree) := by
    rw [hr, hs, sq, sq, totalDegree_mul_of_isDomain (mul_ne_zero hq0 hq0)
      (mul_ne_zero (mul_ne_zero hp0 hp0) hs0), totalDegree_mul_of_isDomain hq0 hq0,
      totalDegree_mul_of_isDomain (mul_ne_zero hp0 hp0) hs0, totalDegree_mul_of_isDomain hp0 hp0]
  omega

theorem sum_C_single_mul (m : Fin 4 → MvPolynomial (Fin 3) ℂ) (i : Fin 3) (a : ℂ) :
    ∑ k : Fin 3, C ((Pi.single i a : Fin 3 → ℂ) k) * m k.castSucc = C a * m i.castSucc := by
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, map_zero, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem sum_C_single_add_mul (m : Fin 4 → MvPolynomial (Fin 3) ℂ) (i j : Fin 3) (a b : ℂ) :
    ∑ k : Fin 3, C ((Pi.single i a + Pi.single j b : Fin 3 → ℂ) k) * m k.castSucc =
      C a * m i.castSucc + C b * m j.castSucc := by
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, sum_C_single_mul]

end Pencil

/-- Bertini for pencils of ternary cubics (char 0). -/
theorem exists_sq_dvd_of_pencil (f g : MvPolynomial (Fin 3) ℂ) (hf : f.IsHomogeneous 3)
    (hg : g.IsHomogeneous 3) (h : ∀ t : ℂ, ¬ Squarefree (f + C t * g)) :
    ∃ p : MvPolynomial (Fin 3) ℂ, p.totalDegree = 1 ∧ p ^ 2 ∣ f ∧ p ^ 2 ∣ g := by
  by_cases hg0 : g = 0
  · subst hg0
    by_cases hf0 : f = 0
    · subst hf0
      exact ⟨X 0, totalDegree_X 0, dvd_zero _, dvd_zero _⟩
    · have hs := h 0
      simp only [map_zero, mul_zero, add_zero] at hs
      obtain ⟨p, -, hp1, hp2⟩ := Pencil.exists_irreducible_sq_dvd hf0 hf.totalDegree_le hs
      exact ⟨p, hp1, hp2, dvd_zero _⟩
  by_cases hdep : ∃ c : ℂ, f = C c * g
  · obtain ⟨c, rfl⟩ := hdep
    have hs := h (1 - c)
    have e : C c * g + C (1 - c) * g = g := by
      rw [← add_mul, ← map_add]
      simp
    rw [e] at hs
    obtain ⟨p, -, hp1, hp2⟩ := Pencil.exists_irreducible_sq_dvd hg0 hg.totalDegree_le hs
    exact ⟨p, hp1, dvd_mul_of_dvd_right hp2 _, hp2⟩
  push Not at hdep
  obtain ⟨t, ht⟩ : ∃ t : Fin 6 → ℂ, Function.Injective t :=
    ⟨(Nat.cast : ℕ → ℂ) ∘ (Fin.val : Fin 6 → ℕ), Nat.cast_injective.comp Fin.val_injective⟩
  have hne : ∀ i, f + C (t i) * g ≠ 0 := by
    intro i hi
    apply hdep (-t i)
    rw [map_neg, neg_mul]
    exact eq_neg_of_add_eq_zero_left hi
  choose p hpirr hpdeg hpdvd using fun i =>
    Pencil.exists_irreducible_sq_dvd (hne i) (hf.add (hg.C_mul (t i))).totalDegree_le (h (t i))
  by_cases hdiv : ∃ i j : Fin 6, i ≠ j ∧ p i ∣ p j
  · obtain ⟨i, j, hij, hdvd⟩ := hdiv
    have h1 : p i ^ 2 ∣ f + C (t i) * g := hpdvd i
    have h2 : p i ^ 2 ∣ f + C (t j) * g := (pow_dvd_pow_of_dvd hdvd 2).trans (hpdvd j)
    have hsub : p i ^ 2 ∣ C (t i - t j) * g := by
      have e : f + C (t i) * g - (f + C (t j) * g) = C (t i - t j) * g := by
        rw [map_sub]
        ring
      rw [← e]
      exact dvd_sub h1 h2
    have htij : t i - t j ≠ 0 := sub_ne_zero.mpr (ht.ne hij)
    have hgdvd : p i ^ 2 ∣ g := by
      have e : C (t i - t j)⁻¹ * (C (t i - t j) * g) = g := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ htij, map_one, one_mul]
      rw [← e]
      exact dvd_mul_of_dvd_right hsub _
    refine ⟨p i, hpdeg i, ?_, hgdvd⟩
    rw [← add_sub_cancel_right f (C (t i) * g)]
    exact dvd_sub h1 (dvd_mul_of_dvd_right hgdvd _)
  · push Not at hdiv
    exfalso
    have hK : ∀ j : Fin 3, f * pderiv j g = g * pderiv j f := by
      intro j
      by_contra hKne
      have hK0 : f * pderiv j g - g * pderiv j f ≠ 0 := sub_ne_zero.mpr hKne
      have hdvdK : ∀ i, p i ∣ f * pderiv j g - g * pderiv j f := by
        intro i
        have e : f * pderiv j g - g * pderiv j f =
            (f + C (t i) * g) * pderiv j g - g * pderiv j (f + C (t i) * g) := by
          rw [map_add, pderiv_C_mul]
          ring
        rw [e]
        exact dvd_sub (dvd_mul_of_dvd_left ((dvd_pow_self (p i) two_ne_zero).trans (hpdvd i)) _)
          (dvd_mul_of_dvd_right (Pencil.dvd_pderiv_of_sq_dvd (hpdvd i) j) _)
      have hprod : ∏ i, p i ∣ f * pderiv j g - g * pderiv j f := by
        refine Fintype.prod_dvd_of_isRelPrime ?_ hdvdK
        intro i i' hii'
        exact (hpirr i).isRelPrime_iff_not_dvd.mpr (hdiv i i' hii')
      have hle := totalDegree_le_of_dvd_of_isDomain hprod hK0
      rw [Pencil.totalDegree_finset_prod_eq _ _ (fun i _ => (hpirr i).ne_zero)] at hle
      simp only [hpdeg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        mul_one] at hle
      have h5 : (f * pderiv j g - g * pderiv j f).totalDegree ≤ 3 + (3 - 1) :=
        ((hf.mul (hg.pderiv (i := j))).sub (hg.mul (hf.pderiv (i := j)))).totalDegree_le
      omega
    obtain ⟨c, hc⟩ :=
      Pencil.exists_eq_C_mul_of_forall_mul_pderiv_eq MonomialOrder.degLex hg0 hK
    exact hdep c hc

/-- the family version used later (note: the coefficient of `m 3` is fixed to 1) -/
theorem exists_sq_dvd_of_family (m : Fin 4 → MvPolynomial (Fin 3) ℂ)
    (hm : ∀ k, (m k).IsHomogeneous 3)
    (h : ∀ c : Fin 3 → ℂ, ¬ Squarefree (m 3 + ∑ k : Fin 3, C (c k) * m k.castSucc)) :
    ∃ p : MvPolynomial (Fin 3) ℂ, p.totalDegree = 1 ∧ ∀ k, p ^ 2 ∣ m k := by
  -- If `F ≠ 0` is a cubic such that no `F + t m k` is squarefree, then a square factor of `F`
  -- works for every `m k`.
  have glue : ∀ F : MvPolynomial (Fin 3) ℂ, F ≠ 0 → F.IsHomogeneous 3 →
      (∀ k t, ¬ Squarefree (F + C t * m k)) →
      ∃ p : MvPolynomial (Fin 3) ℂ, p.totalDegree = 1 ∧ ∀ k, p ^ 2 ∣ m k := by
    intro F hF0 hF3 hk
    have hFs : ¬ Squarefree F := by
      have := hk 0 0
      rwa [map_zero, zero_mul, add_zero] at this
    obtain ⟨p, -, hp1, hp2⟩ := Pencil.exists_irreducible_sq_dvd hF0 hF3.totalDegree_le hFs
    refine ⟨p, hp1, fun k => ?_⟩
    obtain ⟨q, hq1, hqF, hqk⟩ := exists_sq_dvd_of_pencil F (m k) hF3 (hm k) (hk k)
    exact (pow_dvd_pow_of_dvd
      (Pencil.dvd_of_sq_dvd_of_sq_dvd hF0 hF3.totalDegree_le hp1 hq1 hp2 hqF) 2).trans hqk
  by_cases h3 : m 3 = 0
  · by_cases hall : ∀ i : Fin 3, m i.castSucc = 0
    · refine ⟨X 0, totalDegree_X 0, fun k => ?_⟩
      induction k using Fin.lastCases with
      | last =>
        rw [show m (Fin.last 3) = 0 from h3]
        exact dvd_zero _
      | cast j =>
        rw [hall j]
        exact dvd_zero _
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      refine glue (m i.castSucc) hi (hm _) (fun k t => ?_)
      induction k using Fin.lastCases with
      | last =>
        have e : m i.castSucc + C t * m (Fin.last 3) = m i.castSucc := by
          rw [show m (Fin.last 3) = 0 from h3, mul_zero, add_zero]
        rw [e]
        have := h (Pi.single i 1)
        rwa [Pencil.sum_C_single_mul, h3, zero_add, map_one, one_mul] at this
      | cast j =>
        have := h (Pi.single i 1 + Pi.single j t)
        rwa [Pencil.sum_C_single_add_mul, h3, zero_add, map_one, one_mul] at this
  · refine glue (m 3) h3 (hm 3) (fun k t => ?_)
    induction k using Fin.lastCases with
    | last =>
      intro hsq
      apply h 0
      have e : m 3 + C t * m (Fin.last 3) = C (1 + t) * m 3 := by
        rw [show m (Fin.last 3) = m 3 from rfl, map_add, map_one, add_mul, one_mul]
      rw [e] at hsq
      simpa using hsq.of_mul_right
    | cast j =>
      have := h (Pi.single j t)
      rwa [Pencil.sum_C_single_mul] at this

end TensorRank335

end

/- ## Section: `Syzygy` -/

section

/-
# Column cubics of the hyperplanes of a four-dimensional space

Let `B : Fin 4 → Mat` span a four-dimensional space `V`. The column cubics of the hyperplanes of
`V` form the linear system spanned by the four cubics `mfam B`, and these satisfy the syzygy
`∑_{k<3} mfam B k • (B k *ᵥ b) = mfam B 3 • (B 3 *ᵥ b)`.

If all four cubics are divisible by `p ^ 2` for a linear `p` and not all vanish, dividing the
syzygy by `p ^ 2` produces a nonzero linear map `Φ` with `Φ b *ᵥ b = 0`, and every such map is
`b ↦ N * crossMat b` (`exists_eq_mul_crossMat`). If all four cubics vanish, every `b` is killed
by some nonzero `a` (`exists_left_kernel_of_mfam_eq_zero`).
-/

namespace TensorRank335

open Matrix MvPolynomial

/-- The `3 × 3` minor of `Kmat B` on the columns `a, b, c`. -/
noncomputable def c3 (B : Fin 4 → Mat) (a b c : Fin 4) : MvPolynomial (Fin 3) ℂ :=
  Kmat B 0 a * Kmat B 1 b * Kmat B 2 c - Kmat B 0 a * Kmat B 1 c * Kmat B 2 b
    - Kmat B 0 b * Kmat B 1 a * Kmat B 2 c + Kmat B 0 b * Kmat B 1 c * Kmat B 2 a
    + Kmat B 0 c * Kmat B 1 a * Kmat B 2 b - Kmat B 0 c * Kmat B 1 b * Kmat B 2 a

/-- The four column cubics attached to a family `B : Fin 4 → Mat`. -/
noncomputable def mfam (B : Fin 4 → Mat) : Fin 4 → MvPolynomial (Fin 3) ℂ
  | 0 => c3 B 3 1 2
  | 1 => c3 B 0 3 2
  | 2 => c3 B 0 1 3
  | 3 => c3 B 0 1 2

theorem Kmat_apply {n : ℕ} (B : Fin n → Mat) (i : Fin 3) (k : Fin n) :
    Kmat B i k = ∑ j, C (B k i j) * X j := rfl

-- `isHomogeneous_Kmat` is proved in the section `ReflexR` above.

theorem isHomogeneous_colCubic (B : Fin 3 → Mat) : (colCubic B).IsHomogeneous 3 := by
  rw [colCubic, det_fin_three]
  have h := isHomogeneous_Kmat B
  refine (((((((h 0 0).mul (h 1 1)).mul (h 2 2)).sub (((h 0 0).mul (h 1 2)).mul (h 2 1))).sub
    (((h 0 1).mul (h 1 0)).mul (h 2 2))).add (((h 0 1).mul (h 1 2)).mul (h 2 0))).add
    (((h 0 2).mul (h 1 0)).mul (h 2 1))).sub (((h 0 2).mul (h 1 1)).mul (h 2 0))

theorem isHomogeneous_c3 (B : Fin 4 → Mat) (a b c : Fin 4) : (c3 B a b c).IsHomogeneous 3 := by
  have h := isHomogeneous_Kmat B
  unfold c3
  refine (((((((h 0 a).mul (h 1 b)).mul (h 2 c)).sub (((h 0 a).mul (h 1 c)).mul (h 2 b))).sub
    (((h 0 b).mul (h 1 a)).mul (h 2 c))).add (((h 0 b).mul (h 1 c)).mul (h 2 a))).add
    (((h 0 c).mul (h 1 a)).mul (h 2 b))).sub (((h 0 c).mul (h 1 b)).mul (h 2 a))

theorem isHomogeneous_mfam (B : Fin 4 → Mat) (k : Fin 4) : (mfam B k).IsHomogeneous 3 := by
  fin_cases k <;> exact isHomogeneous_c3 _ _ _ _

theorem Kmat_add_smul (B : Fin 4 → Mat) (c : Fin 3 → ℂ) (i j : Fin 3) :
    Kmat (fun j => B j.castSucc + c j • B 3) i j = Kmat B i j.castSucc + C (c j) * Kmat B i 3 := by
  simp only [Kmat_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
    add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

theorem mfam_zero (B : Fin 4 → Mat) : mfam B (0 : Fin 3).castSucc = c3 B 3 1 2 := rfl
theorem mfam_one (B : Fin 4 → Mat) : mfam B (1 : Fin 3).castSucc = c3 B 0 3 2 := rfl
theorem mfam_two (B : Fin 4 → Mat) : mfam B (2 : Fin 3).castSucc = c3 B 0 1 3 := rfl
theorem mfam_three (B : Fin 4 → Mat) : mfam B 3 = c3 B 0 1 2 := rfl

theorem Kmat_castSucc_zero (B : Fin 4 → Mat) (i : Fin 3) :
    Kmat B i (0 : Fin 3).castSucc = Kmat B i 0 := rfl
theorem Kmat_castSucc_one (B : Fin 4 → Mat) (i : Fin 3) :
    Kmat B i (1 : Fin 3).castSucc = Kmat B i 1 := rfl
theorem Kmat_castSucc_two (B : Fin 4 → Mat) (i : Fin 3) :
    Kmat B i (2 : Fin 3).castSucc = Kmat B i 2 := rfl

/-- The column cubic of the hyperplane spanned by `B j + c j • B 3`. -/
theorem colCubic_hyperplane (B : Fin 4 → Mat) (c : Fin 3 → ℂ) :
    colCubic (fun j => B j.castSucc + c j • B 3) =
      mfam B 3 + ∑ k : Fin 3, C (c k) * mfam B k.castSucc := by
  have hK : Kmat (fun j => B j.castSucc + c j • B 3) =
      Matrix.of fun i j => Kmat B i j.castSucc + C (c j) * Kmat B i 3 :=
    Matrix.ext fun i j => Kmat_add_smul B c i j
  rw [colCubic, hK, det_fin_three, Fin.sum_univ_three, mfam_zero, mfam_one, mfam_two,
    mfam_three]
  simp only [Matrix.of_apply, Kmat_castSucc_zero, Kmat_castSucc_one, Kmat_castSucc_two, c3]
  ring

private theorem syzygy_row (B : Fin 4 → Mat) (i : Fin 3) (hi : i = 0 ∨ i = 1 ∨ i = 2) :
    c3 B 3 1 2 * Kmat B i 0 + c3 B 0 3 2 * Kmat B i 1 + c3 B 0 1 3 * Kmat B i 2 =
      c3 B 0 1 2 * Kmat B i 3 := by
  rcases hi with rfl | rfl | rfl <;> simp only [c3] <;> ring

/-- The syzygy between the four column cubics. -/
theorem syzygy (B : Fin 4 → Mat) (i : Fin 3) :
    ∑ k : Fin 3, mfam B k.castSucc * Kmat B i k.castSucc = mfam B 3 * Kmat B i 3 := by
  rw [Fin.sum_univ_three, mfam_zero, mfam_one, mfam_two, mfam_three, Kmat_castSucc_zero,
    Kmat_castSucc_one, Kmat_castSucc_two]
  exact syzygy_row B i (by fin_cases i <;> simp)

/- ### Linear maps with `Φ b *ᵥ b = 0` -/

/-- A linear family `b ↦ ∑ j, b j • Φ j` with `Φ b *ᵥ b = 0` is `b ↦ N * crossMat b`. -/
theorem exists_eq_mul_crossMat (Φ : Fin 3 → Mat)
    (h : ∀ b : Fin 3 → ℂ, (∑ j, b j • Φ j) *ᵥ b = 0) :
    ∃ N : Mat, ∀ b : Fin 3 → ℂ, ∑ j, b j • Φ j = N * crossMat b := by
  have hdiag : ∀ j i, Φ j i j = 0 := by
    intro j i
    have := congrFun (h (Pi.single j 1)) i
    fin_cases j <;>
      simpa [Fin.sum_univ_three, mulVec, dotProduct, Pi.single_apply, Matrix.sum_apply] using this
  have hsym : ∀ j k i, Φ j i k + Φ k i j = 0 := by
    intro j k i
    have h1 := congrFun (h (Pi.single j 1 + Pi.single k 1)) i
    have hj := hdiag j i
    have hk := hdiag k i
    by_cases hjk : j = k
    · subst hjk; simp [hj]
    · simp only [mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply, Pi.add_apply,
        Pi.single_apply, Fin.sum_univ_three] at h1
      fin_cases j <;> fin_cases k <;> simp_all <;> linear_combination h1
  refine ⟨Matrix.of fun i l => ![Φ 1 i 2, Φ 2 i 0, Φ 0 i 1] l, fun b => ?_⟩
  ext i k
  have e01 := hsym 0 1 i
  have e02 := hsym 0 2 i
  have e12 := hsym 1 2 i
  have d0 := hdiag 0 i
  have d1 := hdiag 1 i
  have d2 := hdiag 2 i
  fin_cases k
  · simp [crossMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.sum_apply]
    linear_combination (b 0) * d0 + (b 1) * e01
  · simp [crossMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.sum_apply]
    linear_combination (b 1) * d1 + (b 2) * e12
  · simp [crossMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.sum_apply]
    linear_combination (b 0) * e02 + (b 2) * d2

end TensorRank335

end

/- ## Section: `SyzygyN` -/

section

/-
# Degenerate linear systems of column cubics

For `B : Fin 4 → Mat` linearly independent:

* if every `mfam B k` is divisible by `p ^ 2` for a linear `p` and some `mfam B k ≠ 0`, then the
  span of `B` contains `N * crossMat b` for all `b`, for some `N ≠ 0`
  (`exists_crossMat_of_sq_dvd`);
* if every `mfam B k` vanishes, then every `b` is killed by a nonzero `a`:
  `a ⬝ᵥ (B k *ᵥ b) = 0` for all `k` (`exists_left_kernel_of_mfam_eq_zero`).
-/

namespace TensorRank335

open Matrix MvPolynomial

theorem eval_c3 (B : Fin 4 → Mat) (b : Fin 3 → ℂ) (x y z : Fin 4) :
    eval b (c3 B x y z) = (B x *ᵥ b) ⬝ᵥ ((B y *ᵥ b) ⨯₃ (B z *ᵥ b)) := by
  simp only [c3, map_sub, map_add, map_mul, eval_Kmat, cross_apply, dotProduct,
    Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

theorem tp_perm_zero {u v w : Fin 3 → ℂ} (h : u ⬝ᵥ v ⨯₃ w = 0) : v ⬝ᵥ w ⨯₃ u = 0 := by
  rw [← triple_product_permutation]; exact h

theorem tp_swap_zero {u v w : Fin 3 → ℂ} (h : u ⬝ᵥ v ⨯₃ w = 0) : u ⬝ᵥ w ⨯₃ v = 0 := by
  rw [← cross_anticomm, dotProduct_neg, h, neg_zero]

theorem fin4_forall {P : Fin 4 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) :
    ∀ k, P k := by
  intro k; fin_cases k
  exacts [h0, h1, h2, h3]

/-- `a = u ⨯₃ w` is orthogonal to `u`, `w`, and every `x` with `x ⬝ᵥ u ⨯₃ w = 0`. -/
theorem cross_dot_eq_zero {u w x : Fin 3 → ℂ} (h : x ⬝ᵥ u ⨯₃ w = 0) : (u ⨯₃ w) ⬝ᵥ x = 0 := by
  rw [dotProduct_comm]; exact h

/-- If all four column cubics vanish, every `b` is killed by a nonzero `a`. -/
theorem exists_left_kernel_of_mfam_eq_zero (B : Fin 4 → Mat) (h : ∀ k, mfam B k = 0)
    (b : Fin 3 → ℂ) : ∃ a : Fin 3 → ℂ, a ≠ 0 ∧ ∀ k, a ⬝ᵥ (B k *ᵥ b) = 0 := by
  set v : Fin 4 → Fin 3 → ℂ := fun k => B k *ᵥ b with hv
  have hev : ∀ k (x y z : Fin 4), mfam B k = c3 B x y z → v x ⬝ᵥ v y ⨯₃ v z = 0 := by
    intro k x y z hk
    have := congrArg (eval b) (h k)
    rw [map_zero, hk, eval_c3] at this
    exact this
  have t0 : v 3 ⬝ᵥ v 1 ⨯₃ v 2 = 0 := hev 0 3 1 2 rfl
  have t1 : v 0 ⬝ᵥ v 3 ⨯₃ v 2 = 0 := hev 1 0 3 2 rfl
  have t2 : v 0 ⬝ᵥ v 1 ⨯₃ v 3 = 0 := hev 2 0 1 3 rfl
  have t3 : v 0 ⬝ᵥ v 1 ⨯₃ v 2 = 0 := hev 3 0 1 2 rfl
  have self1 : ∀ x y : Fin 3 → ℂ, (x ⨯₃ y) ⬝ᵥ x = 0 := fun x y => by
    rw [dotProduct_comm]; exact dot_self_cross x y
  have self2 : ∀ x y : Fin 3 → ℂ, (x ⨯₃ y) ⬝ᵥ y = 0 := fun x y => by
    rw [dotProduct_comm]; exact dot_cross_self x y
  have out : ∀ a : Fin 3 → ℂ, a ≠ 0 → (∀ k, a ⬝ᵥ v k = 0) →
      ∃ a : Fin 3 → ℂ, a ≠ 0 ∧ ∀ k, a ⬝ᵥ (B k *ᵥ b) = 0 := fun a ha hk => ⟨a, ha, hk⟩
  by_cases h01 : v 0 ⨯₃ v 1 ≠ 0
  · refine out _ h01 (fin4_forall (self1 _ _) (self2 _ _) ?_ ?_)
    · exact cross_dot_eq_zero (tp_perm_zero (tp_perm_zero t3))
    · exact cross_dot_eq_zero (tp_perm_zero (tp_perm_zero t2))
  by_cases h02 : v 0 ⨯₃ v 2 ≠ 0
  · refine out _ h02 (fin4_forall (self1 _ _) ?_ (self2 _ _) ?_)
    · exact cross_dot_eq_zero (tp_perm_zero (tp_perm_zero (tp_swap_zero t3)))
    · exact cross_dot_eq_zero (tp_perm_zero (tp_perm_zero (tp_swap_zero t1)))
  by_cases h03 : v 0 ⨯₃ v 3 ≠ 0
  · refine out _ h03 (fin4_forall (self1 _ _) ?_ ?_ (self2 _ _))
    · exact cross_dot_eq_zero (tp_perm_zero (tp_perm_zero (tp_swap_zero t2)))
    · exact cross_dot_eq_zero (tp_perm_zero (tp_perm_zero t1))
  by_cases h12 : v 1 ⨯₃ v 2 ≠ 0
  · refine out _ h12 (fin4_forall ?_ (self1 _ _) (self2 _ _) ?_)
    · exact cross_dot_eq_zero t3
    · exact cross_dot_eq_zero t0
  by_cases h13 : v 1 ⨯₃ v 3 ≠ 0
  · refine out _ h13 (fin4_forall ?_ (self1 _ _) ?_ (self2 _ _))
    · exact cross_dot_eq_zero t2
    · exact cross_dot_eq_zero (tp_perm_zero (tp_perm_zero (tp_swap_zero (tp_perm_zero t0))))
  by_cases h23 : v 2 ⨯₃ v 3 ≠ 0
  · refine out _ h23 (fin4_forall ?_ ?_ (self1 _ _) (self2 _ _))
    · exact cross_dot_eq_zero (tp_swap_zero t1)
    · exact cross_dot_eq_zero (tp_perm_zero t0)
  simp only [ne_eq, not_not] at h01 h02 h03 h12 h13 h23
  -- all pairwise cross products vanish; pick a nonzero `w = v k₀`
  have anti : ∀ x y : Fin 3 → ℂ, x ⨯₃ y = 0 → y ⨯₃ x = 0 := fun x y hxy => by
    rw [← cross_anticomm, hxy, neg_zero]
  -- `a := w ⨯₃ e_m` is orthogonal to every `x` with `x ⨯₃ w = 0`
  have perp : ∀ w e x : Fin 3 → ℂ, x ⨯₃ w = 0 → (w ⨯₃ e) ⬝ᵥ x = 0 := by
    intro w e x hx
    rw [dotProduct_comm, triple_product_permutation, triple_product_permutation, hx,
      dotProduct_zero]
  have exists_e : ∀ w : Fin 3 → ℂ, w ≠ 0 → ∃ e : Fin 3 → ℂ, w ⨯₃ e ≠ 0 := by
    intro w hw
    by_contra hcon
    push Not at hcon
    apply hw
    have e0 := hcon (Pi.single 0 1)
    have e1 := hcon (Pi.single 1 1)
    rw [cross_apply] at e0 e1
    ext i
    fin_cases i
    · have := congrFun e1 2; simpa using this
    · have := congrFun e0 2; simpa using this.symm
    · have := congrFun e0 1; simpa using this
  have cself : ∀ x : Fin 3 → ℂ, x ⨯₃ x = 0 := cross_self
  by_cases hv0 : v 0 ≠ 0
  · obtain ⟨e, he⟩ := exists_e _ hv0
    exact out _ he (fin4_forall (perp _ _ _ (cself _)) (perp _ _ _ (anti _ _ h01))
      (perp _ _ _ (anti _ _ h02)) (perp _ _ _ (anti _ _ h03)))
  by_cases hv1 : v 1 ≠ 0
  · obtain ⟨e, he⟩ := exists_e _ hv1
    exact out _ he (fin4_forall (perp _ _ _ h01) (perp _ _ _ (cself _))
      (perp _ _ _ (anti _ _ h12)) (perp _ _ _ (anti _ _ h13)))
  by_cases hv2 : v 2 ≠ 0
  · obtain ⟨e, he⟩ := exists_e _ hv2
    exact out _ he (fin4_forall (perp _ _ _ h02) (perp _ _ _ h12) (perp _ _ _ (cself _))
      (perp _ _ _ (anti _ _ h23)))
  by_cases hv3 : v 3 ≠ 0
  · obtain ⟨e, he⟩ := exists_e _ hv3
    exact out _ he (fin4_forall (perp _ _ _ h03) (perp _ _ _ h13) (perp _ _ _ h23)
      (perp _ _ _ (cself _)))
  simp only [ne_eq, not_not] at hv0 hv1 hv2 hv3
  refine out (Pi.single 0 1) (by simp) (fin4_forall ?_ ?_ ?_ ?_) <;>
    simp [hv0, hv1, hv2, hv3]

/- ### The case of a common square factor -/

/-- A polynomial of total degree at most one is affine. -/
theorem exists_affine_of_totalDegree_le_one (q : MvPolynomial (Fin 3) ℂ)
    (hq : q.totalDegree ≤ 1) : ∃ (c : ℂ) (a : Fin 3 → ℂ), q = C c + ∑ j, C (a j) * X j := by
  have hsum : q = homogeneousComponent 0 q + homogeneousComponent 1 q := by
    conv_lhs => rw [← sum_homogeneousComponent q]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with h0 | h1
    · rw [h0, homogeneousComponent_eq_zero 1 q (by omega)]
      simp
    · rw [h1]
      simp [Finset.sum_range_succ]
  have h1mem : homogeneousComponent 1 q ∈ homogeneousSubmodule (Fin 3) ℂ 1 :=
    homogeneousComponent_mem 1 q
  rw [homogeneousSubmodule_one_eq_span_X, Submodule.mem_span_range_iff_exists_fun] at h1mem
  obtain ⟨a, ha⟩ := h1mem
  refine ⟨q.coeff 0, a, ?_⟩
  nth_rewrite 1 [hsum]
  rw [homogeneousComponent_zero, ← ha]
  simp [smul_eq_C_mul]

/-- If every `mfam B k` is divisible by `p ^ 2` (`p` linear) and some `mfam B k ≠ 0`, the span of
`B` contains `N * crossMat b` for all `b`, for some `N ≠ 0`. -/
theorem exists_crossMat_of_sq_dvd (B : Fin 4 → Mat) (hB : LinearIndependent ℂ B)
    (p : MvPolynomial (Fin 3) ℂ) (hp : p.totalDegree = 1) (hdvd : ∀ k, p ^ 2 ∣ mfam B k)
    (hne : ∃ k, mfam B k ≠ 0) :
    ∃ N : Mat, N ≠ 0 ∧ ∀ b, N * crossMat b ∈ Submodule.span ℂ (Set.range B) := by
  choose μ hμ using hdvd
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp0
  have hdeg : ∀ k, (μ k).totalDegree ≤ 1 := by
    intro k
    by_cases hk : μ k = 0
    · simp [hk]
    have hm : mfam B k ≠ 0 := by rw [hμ k]; exact mul_ne_zero hp2 hk
    have h3 := (isHomogeneous_mfam B k).totalDegree hm
    rw [hμ k, totalDegree_mul_of_isDomain hp2 hk, pow_two,
      totalDegree_mul_of_isDomain hp0 hp0, hp] at h3
    omega
  have hsyz : ∀ i, ∑ k : Fin 3, μ k.castSucc * Kmat B i k.castSucc = μ 3 * Kmat B i 3 := by
    intro i
    have h := syzygy B i
    simp only [hμ] at h
    apply mul_left_cancel₀ hp2
    rw [Finset.mul_sum]
    simpa [mul_assoc] using h
  choose c a hca using fun k => exists_affine_of_totalDegree_le_one (μ k) (hdeg k)
  have hev : ∀ (b : Fin 3 → ℂ) (i : Fin 3),
      ∑ k : Fin 3, (c k.castSucc + a k.castSucc ⬝ᵥ b) * (B k.castSucc *ᵥ b) i =
        (c 3 + a 3 ⬝ᵥ b) * (B 3 *ᵥ b) i := by
    intro b i
    have := congrArg (eval b) (hsyz i)
    simp only [map_sum, map_mul, eval_Kmat, hca, map_add, eval_C, eval_X] at this
    simpa [dotProduct] using this
  have hQ : ∀ (b : Fin 3 → ℂ) (i : Fin 3),
      ∑ k : Fin 3, (a k.castSucc ⬝ᵥ b) * (B k.castSucc *ᵥ b) i = (a 3 ⬝ᵥ b) * (B 3 *ᵥ b) i := by
    intro b i
    have h1 := hev b i
    have h2 := hev ((2 : ℂ) • b) i
    simp only [dotProduct_smul, mulVec_smul, Pi.smul_apply, smul_eq_mul] at h2
    rw [Fin.sum_univ_three] at h1 h2 ⊢
    linear_combination (h2 - 2 * h1) / 2
  have hL : ∀ (b : Fin 3 → ℂ) (i : Fin 3),
      ∑ k : Fin 3, c k.castSucc * (B k.castSucc *ᵥ b) i = c 3 * (B 3 *ᵥ b) i := by
    intro b i
    have h1 := hev b i
    have hq := hQ b i
    rw [Fin.sum_univ_three] at h1 hq ⊢
    linear_combination h1 - hq
  set Φ : Fin 3 → Mat := fun j => ∑ k : Fin 3, a k.castSucc j • B k.castSucc - a 3 j • B 3
    with hΦ
  have hΦb : ∀ b : Fin 3 → ℂ, (∑ j, b j • Φ j) *ᵥ b = 0 := by
    intro b
    ext i
    have := hQ b i
    simp only [hΦ, Fin.sum_univ_three, dotProduct, mulVec, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sub_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    linear_combination this
  obtain ⟨N, hN⟩ := exists_eq_mul_crossMat Φ hΦb
  -- linear independence of `B`, in coordinates
  have hind : ∀ g : Fin 4 → ℂ, ∑ k, g k • B k = 0 → ∀ k, g k = 0 :=
    Fintype.linearIndependent_iff.mp hB
  refine ⟨N, ?_, fun b => ?_⟩
  · rintro rfl
    have hΦ0 : ∀ j, Φ j = 0 := by
      intro j
      have := hN (Pi.single j 1)
      rw [zero_mul] at this
      fin_cases j <;> simpa [Fin.sum_univ_three] using this
    have ha0 : ∀ k j, a k j = 0 := by
      intro k j
      have h0 := hind ![a 0 j, a 1 j, a 2 j, -a 3 j] (by
        have := hΦ0 j
        simp only [hΦ, Fin.sum_univ_three, Fin.castSucc_zero, Fin.castSucc_one,
          show (2 : Fin 3).castSucc = (2 : Fin 4) from rfl] at this
        rw [Fin.sum_univ_four]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
        rw [neg_smul, ← sub_eq_add_neg]
        exact this)
      fin_cases k
      · exact h0 0
      · exact h0 1
      · exact h0 2
      · simpa using h0 3
    have hc0 : ∀ k, c k = 0 := by
      have hM : ∑ k : Fin 3, c k.castSucc • B k.castSucc - c 3 • B 3 = 0 := by
        ext i j
        have := hL (Pi.single j 1) i
        simp only [Fin.sum_univ_three, mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one,
          mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
        simp only [Fin.sum_univ_three, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
          smul_eq_mul, Matrix.zero_apply]
        linear_combination this
      have h0 := hind ![c 0, c 1, c 2, -c 3] (by
        simp only [Fin.sum_univ_three, Fin.castSucc_zero, Fin.castSucc_one,
          show (2 : Fin 3).castSucc = (2 : Fin 4) from rfl] at hM
        rw [Fin.sum_univ_four]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
        rw [neg_smul, ← sub_eq_add_neg]
        exact hM)
      intro k
      fin_cases k
      · exact h0 0
      · exact h0 1
      · exact h0 2
      · simpa using h0 3
    obtain ⟨k, hk⟩ := hne
    apply hk
    rw [hμ k, hca k, hc0 k]
    simp [ha0]
  · rw [← hN b]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    simp only [hΦ]
    refine Submodule.sub_mem _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, rfl⟩)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

end TensorRank335

end

/- ## Section: `Nilpotent3` -/

section

/-
# Spaces of nilpotent `3 × 3` matrices

We prove Gerstenhaber's bound for `3 × 3` complex matrices: a linear space of nilpotent matrices
has dimension at most `3`. As an application, a subspace `S` of dimension at most five that
contains four linearly independent rank-one matrices lies in the span of six rank-one matrices.

## Nilpotent bound

Instead of nilpotency we work with the polynomial conditions `NilCond A`:
`tr A = 0`, `tr (A * A) = 0`, `det A = 0` (all implied by nilpotency).

* If some `A ∈ N` has `A * A ≠ 0`, then (Cayley–Hamilton) `A * A * A = 0` and `A` is conjugate to
  the Jordan block `Jmat = E₀₁ + E₁₂` (basis `A² v, A v, v`). After conjugation `Jmat ∈ N`; the
  conditions for `B + t • Jmat` force `B₂₀ = 0`, `B₂₁ = -B₁₀`, `tr B = 0` and
  `B₁₀ * (2 B₀₀ + B₁₁) = 0`. Either `B₁₀ = 0` on `N` (then `N` is strictly upper triangular), or
  `2 B₀₀ + B₁₁ = 0` on `N` and `B ↦ (B₀₀, B₁₀, B₀₁)` is injective on `N`.
* Otherwise `A * A = 0` on `N`, so every element has vanishing adjugate, hence rank at most one,
  and a linear space of such matrices has a common row or a common column space.

## Main results

* `TensorRank335.finrank_le_three_of_isNilpotent`
* `TensorRank335.coveredBy_six_of_four_rankOne`
-/

namespace TensorRank335

open Matrix

/- ### Polynomial conditions for nilpotency -/

/-- The conditions `tr A = 0`, `tr A² = 0`, `det A = 0`, which characterize nilpotent `3 × 3`
matrices. -/
def NilCond (A : Mat) : Prop :=
  trace A = 0 ∧ trace (A * A) = 0 ∧ det A = 0

theorem nilCond_of_isNilpotent {A : Mat} (h : IsNilpotent A) : NilCond A := by
  refine ⟨(isNilpotent_trace_of_isNilpotent h).eq_zero,
    (isNilpotent_trace_of_isNilpotent ((Commute.refl A).isNilpotent_mul_right h)).eq_zero, ?_⟩
  obtain ⟨n, hn⟩ := h
  exact (show IsNilpotent (det A) from ⟨n, by rw [← det_pow, hn, det_zero]⟩).eq_zero

theorem NilCond.conj {Q A : Mat} (hQ : IsUnit Q.det) (h : NilCond A) :
    NilCond (Q⁻¹ * A * Q) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hmul : ∀ B : Mat, trace (Q⁻¹ * B * Q) = trace B := fun B => by
    rw [trace_mul_comm, ← Matrix.mul_assoc, mul_nonsing_inv _ hQ, Matrix.one_mul]
  refine ⟨by rw [hmul, h1], ?_, ?_⟩
  · have : Q⁻¹ * A * Q * (Q⁻¹ * A * Q) = Q⁻¹ * (A * A) * Q := by
      simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hQ]
    rw [this, hmul, h2]
  · rw [det_conj' ((isUnit_iff_isUnit_det Q).mpr hQ), h3]

theorem NilCond.expand {M : Mat} (h : NilCond M) :
    M 0 0 + M 1 1 + M 2 2 = 0 ∧
    M 0 0 * M 0 0 + M 0 1 * M 1 0 + M 0 2 * M 2 0 + (M 1 0 * M 0 1 + M 1 1 * M 1 1 + M 1 2 * M 2 1) +
      (M 2 0 * M 0 2 + M 2 1 * M 1 2 + M 2 2 * M 2 2) = 0 ∧
    M 0 0 * M 1 1 * M 2 2 - M 0 0 * M 1 2 * M 2 1 - M 0 1 * M 1 0 * M 2 2 + M 0 1 * M 1 2 * M 2 0 +
      M 0 2 * M 1 0 * M 2 1 - M 0 2 * M 1 1 * M 2 0 = 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [trace, diag_apply, Fin.sum_univ_three, mul_apply] at h1 h2
  rw [det_fin_three] at h3
  exact ⟨h1, h2, h3⟩

/-- Cayley–Hamilton for `3 × 3` matrices. -/
theorem cayley_hamilton3 (A : Mat) :
    A * A * A = trace A • (A * A) - ((trace A ^ 2 - trace (A * A)) / 2) • A +
      det A • (1 : Mat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_three, trace, det_fin_three, one_apply] <;> ring

theorem adjugate_eq3 (A : Mat) :
    adjugate A = A * A - trace A • A + ((trace A ^ 2 - trace (A * A)) / 2) • (1 : Mat) := by
  ext i j
  rw [adjugate_fin_three]
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_three, trace, one_apply] <;> ring

theorem NilCond.cube {A : Mat} (h : NilCond A) : A * A * A = 0 := by
  rw [cayley_hamilton3, h.1, h.2.1, h.2.2]
  simp

theorem det_one_add_smul_three (t : ℂ) (M : Mat) :
    det (1 + t • M) = 1 + t * trace M + t ^ 2 * ((trace M ^ 2 - trace (M * M)) / 2) +
      t ^ 3 * det M := by
  simp [det_fin_three, trace, mul_apply, Fin.sum_univ_three, one_apply]
  ring

/- ### Dimension bounds via evaluation at three entries -/

/-- Evaluation at the three entries `(r m, c m)`. -/
def evalL (r c : Fin 3 → Fin 3) : Mat →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun B m := B (r m) (c m)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_le_three_of_eval (N : Submodule ℂ Mat) (r c : Fin 3 → Fin 3)
    (h : ∀ B ∈ N, (∀ m, B (r m) (c m) = 0) → B = 0) : Module.finrank ℂ N ≤ 3 := by
  have hinj : Function.Injective ((evalL r c).comp N.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (h x x.2 fun m => congrFun hx m)
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

/- ### Spaces of matrices of rank at most one -/

theorem minor_eq_of_adjugate_eq_zero {M : Mat} (h : adjugate M = 0) (i j k l : Fin 3) :
    M i j * M k l = M i l * M k j := by
  rw [adjugate_fin_three] at h
  have e : ∀ a b, (!![M 1 1 * M 2 2 - M 1 2 * M 2 1,
      -(M 0 1 * M 2 2) + M 0 2 * M 2 1,
      M 0 1 * M 1 2 - M 0 2 * M 1 1;
      -(M 1 0 * M 2 2) + M 1 2 * M 2 0,
      M 0 0 * M 2 2 - M 0 2 * M 2 0,
      -(M 0 0 * M 1 2) + M 0 2 * M 1 0;
      M 1 0 * M 2 1 - M 1 1 * M 2 0,
      -(M 0 0 * M 2 1) + M 0 1 * M 2 0,
      M 0 0 * M 1 1 - M 0 1 * M 1 0] : Mat) a b = 0 := fun a b => by rw [h]; rfl
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  have e22 := e 2 2
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
    cons_val_fin_one, head_cons, head_fin_const, tail_cons] at e00 e01 e02 e10 e11 e12 e20 e21 e22
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    (try simp only [Fin.reduceFinMk, Fin.isValue]) <;>
    first
    | ring1
    | linear_combination e00 | linear_combination -e00
    | linear_combination e01 | linear_combination -e01
    | linear_combination e02 | linear_combination -e02
    | linear_combination e10 | linear_combination -e10
    | linear_combination e11 | linear_combination -e11
    | linear_combination e12 | linear_combination -e12
    | linear_combination e20 | linear_combination -e20
    | linear_combination e21 | linear_combination -e21
    | linear_combination e22 | linear_combination -e22

theorem minor_eq_of_sq_eq_zero {M : Mat} (h : NilCond M) (hsq : M * M = 0) (i j k l : Fin 3) :
    M i j * M k l = M i l * M k j := by
  apply minor_eq_of_adjugate_eq_zero
  rw [adjugate_eq3, hsq, h.1]
  simp

/-- A linear space of `3 × 3` matrices all of whose `2 × 2` minors vanish has dimension at most
three: its elements share a row space or a column space. -/
theorem finrank_le_three_of_minors (N : Submodule ℂ Mat)
    (hN : ∀ M ∈ N, ∀ i j k l, M i j * M k l = M i l * M k j) : Module.finrank ℂ N ≤ 3 := by
  by_cases hA : ∃ A ∈ N, A ≠ 0
  swap
  · push Not at hA
    rw [(Submodule.eq_bot_iff N).mpr hA, finrank_bot]
    norm_num
  obtain ⟨A, hAN, hA0⟩ := hA
  obtain ⟨i₀, j₀, hα⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hA0 (Matrix.ext hcon)
  have key : ∀ B ∈ N, (∀ k l, A i₀ j₀ * B k l = A k j₀ * B i₀ l) ∨
      (∀ k l, A i₀ j₀ * B k l = B k j₀ * A i₀ l) := by
    intro B hB
    have hAB := N.add_mem hAN hB
    have hxy : ∀ k l, (A i₀ j₀ * B k j₀ - B i₀ j₀ * A k j₀) *
        (A i₀ j₀ * B i₀ l - B i₀ j₀ * A i₀ l) = 0 := by
      intro k l
      have mA := hN A hAN i₀ j₀ k l
      have mB := hN B hB i₀ j₀ k l
      have mAB := hN _ hAB i₀ j₀ k l
      simp only [Matrix.add_apply] at mAB
      linear_combination (-(A i₀ j₀) ^ 2 - A i₀ j₀ * B i₀ j₀) * mB + A i₀ j₀ * B i₀ j₀ * mAB +
        (-(A i₀ j₀) * B i₀ j₀ - B i₀ j₀ ^ 2) * mA
    by_cases hx : ∀ k, A i₀ j₀ * B k j₀ - B i₀ j₀ * A k j₀ = 0
    · left
      intro k l
      have mA := hN A hAN i₀ j₀ k l
      have mB := hN B hB i₀ j₀ k l
      have mAB := hN _ hAB i₀ j₀ k l
      simp only [Matrix.add_apply] at mAB
      have : A i₀ j₀ * (A i₀ j₀ * B k l - A k j₀ * B i₀ l) = 0 := by
        linear_combination A i₀ l * hx k + A i₀ j₀ * (mAB - mA - mB) - B i₀ j₀ * mA
      have := (mul_eq_zero.mp this).resolve_left hα
      linear_combination this
    · right
      push Not at hx
      obtain ⟨k₁, hk₁⟩ := hx
      have hy : ∀ l, A i₀ j₀ * B i₀ l - B i₀ j₀ * A i₀ l = 0 := fun l =>
        (mul_eq_zero.mp (hxy k₁ l)).resolve_left hk₁
      intro k l
      have mA := hN A hAN i₀ j₀ k l
      have mB := hN B hB i₀ j₀ k l
      have mAB := hN _ hAB i₀ j₀ k l
      simp only [Matrix.add_apply] at mAB
      have : A i₀ j₀ * (A i₀ j₀ * B k l - B k j₀ * A i₀ l) = 0 := by
        linear_combination A k j₀ * hy l + A i₀ j₀ * (mAB - mA - mB) - B i₀ j₀ * mA
      have := (mul_eq_zero.mp this).resolve_left hα
      linear_combination this
  have hU : (∀ B ∈ N, ∀ k l, A i₀ j₀ * B k l = A k j₀ * B i₀ l) ∨
      (∀ B ∈ N, ∀ k l, A i₀ j₀ * B k l = B k j₀ * A i₀ l) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨B, hB, k, l, hBkl⟩, ⟨C, hC, k', l', hCkl⟩⟩ := hcon
    have hB2 := (key B hB).resolve_left (fun h => hBkl (h k l))
    have hC1 := (key C hC).resolve_right (fun h => hCkl (h k' l'))
    rcases key (B + C) (N.add_mem hB hC) with h | h
    · apply hBkl
      have e1 := h k l
      have e2 := hC1 k l
      simp only [Matrix.add_apply] at e1
      linear_combination e1 - e2
    · apply hCkl
      have e1 := h k' l'
      have e2 := hB2 k' l'
      simp only [Matrix.add_apply] at e1
      linear_combination e1 - e2
  rcases hU with h | h
  · apply finrank_le_three_of_eval N (fun _ => i₀) id
    intro B hB hz
    have hz' : ∀ m, B i₀ m = 0 := hz
    ext k l
    have e := h B hB k l
    rw [hz' l] at e
    simpa [hα] using e
  · apply finrank_le_three_of_eval N id (fun _ => j₀)
    intro B hB hz
    have hz' : ∀ m, B m j₀ = 0 := hz
    ext k l
    have e := h B hB k l
    rw [hz' k] at e
    simpa [hα] using e

/- ### Spaces containing the Jordan block -/

/-- The nilpotent Jordan block `E₀₁ + E₁₂`. -/
def Jmat : Mat :=
  !![0, 1, 0; 0, 0, 1; 0, 0, 0]

@[simp] theorem Jmat_00 : Jmat 0 0 = 0 := rfl
@[simp] theorem Jmat_01 : Jmat 0 1 = 1 := rfl
@[simp] theorem Jmat_02 : Jmat 0 2 = 0 := rfl
@[simp] theorem Jmat_10 : Jmat 1 0 = 0 := rfl
@[simp] theorem Jmat_11 : Jmat 1 1 = 0 := rfl
@[simp] theorem Jmat_12 : Jmat 1 2 = 1 := rfl
@[simp] theorem Jmat_20 : Jmat 2 0 = 0 := rfl
@[simp] theorem Jmat_21 : Jmat 2 1 = 0 := rfl
@[simp] theorem Jmat_22 : Jmat 2 2 = 0 := rfl

theorem facts_of_Jmat {N : Submodule ℂ Mat} (hN : ∀ M ∈ N, NilCond M) (hJ : Jmat ∈ N) {M : Mat}
    (hM : M ∈ N) :
    M 2 0 = 0 ∧ M 2 1 = -M 1 0 ∧ M 2 2 = -M 0 0 - M 1 1 ∧ M 1 0 * (2 * M 0 0 + M 1 1) = 0 := by
  obtain ⟨t0, s0, d0⟩ := (hN M hM).expand
  obtain ⟨-, s1, d1⟩ := (hN (M + Jmat) (N.add_mem hM hJ)).expand
  obtain ⟨-, -, d2⟩ := (hN (M - Jmat) (N.sub_mem hM hJ)).expand
  simp only [Matrix.add_apply, Matrix.sub_apply, Jmat_00, Jmat_01, Jmat_02, Jmat_10, Jmat_11,
    Jmat_12, Jmat_20, Jmat_21, Jmat_22] at s1 d1 d2
  have f1 : M 2 0 = 0 := by linear_combination (d1 + d2 - 2 * d0) / 2
  have f2 : M 2 1 = -M 1 0 := by linear_combination (s1 - s0) / 2
  have f3 : M 2 2 = -M 0 0 - M 1 1 := by linear_combination t0
  refine ⟨f1, f2, f3, ?_⟩
  linear_combination (d1 - d2) / 2 + M 0 0 * f2 + M 1 0 * f3 - (M 0 1 + M 1 2) * f1

theorem finrank_le_three_of_Jmat_mem (N : Submodule ℂ Mat) (hN : ∀ M ∈ N, NilCond M)
    (hJ : Jmat ∈ N) : Module.finrank ℂ N ≤ 3 := by
  have F := fun M (hM : M ∈ N) => facts_of_Jmat hN hJ hM
  by_cases hs : ∀ M ∈ N, M 1 0 = 0
  · -- every element is upper triangular, hence strictly upper triangular
    apply finrank_le_three_of_eval N ![0, 0, 1] ![1, 2, 2]
    intro M hM hz
    have h01 : M 0 1 = 0 := hz 0
    have h02 : M 0 2 = 0 := hz 1
    have h12 : M 1 2 = 0 := hz 2
    have h10 := hs M hM
    obtain ⟨f1, f2, f3, -⟩ := F M hM
    have h21 : M 2 1 = 0 := by rw [f2, h10, neg_zero]
    obtain ⟨-, s0, d0⟩ := (hN M hM).expand
    rw [f1, h21, f3, h01, h02, h12, h10] at s0 d0
    have hq : M 0 0 ^ 2 + M 0 0 * M 1 1 + M 1 1 ^ 2 = 0 := by linear_combination s0 / 2
    have hc : M 0 0 * M 1 1 * (M 0 0 + M 1 1) = 0 := by linear_combination -d0
    have hsum : (M 0 0 + M 1 1) ^ 3 = 0 := by linear_combination (M 0 0 + M 1 1) * hq + hc
    have hsum' : M 0 0 + M 1 1 = 0 := pow_eq_zero_iff (by norm_num) |>.mp hsum
    have hx : M 0 0 = 0 := by
      have : M 0 0 ^ 2 = 0 := by linear_combination hq - M 1 1 * hsum'
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    have hy : M 1 1 = 0 := by linear_combination hsum' - hx
    have h22 : M 2 2 = 0 := by rw [f3, hx, hy]; ring
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hx, hy, h01, h02, h12, h10, f1, h21, h22]
  · push Not at hs
    obtain ⟨B₁, hB₁, hs₁⟩ := hs
    have hb : 2 * B₁ 0 0 + B₁ 1 1 = 0 := (mul_eq_zero.mp (F B₁ hB₁).2.2.2).resolve_left hs₁
    have h2xy : ∀ M ∈ N, 2 * M 0 0 + M 1 1 = 0 := by
      intro M hM
      have e1 := (F (B₁ + M) (N.add_mem hB₁ hM)).2.2.2
      have e2 := (F (B₁ + (2 : ℂ) • M) (N.add_mem hB₁ (N.smul_mem 2 hM))).2.2.2
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at e1 e2
      by_contra hne
      have k1 : B₁ 1 0 + M 1 0 = 0 := by
        have : (B₁ 1 0 + M 1 0) * (2 * M 0 0 + M 1 1) = 0 := by
          linear_combination e1 - (B₁ 1 0 + M 1 0) * hb
        exact (mul_eq_zero.mp this).resolve_right hne
      have k2 : B₁ 1 0 + 2 * M 1 0 = 0 := by
        have : (B₁ 1 0 + 2 * M 1 0) * (2 * M 0 0 + M 1 1) = 0 := by
          linear_combination (e2 - (B₁ 1 0 + 2 * M 1 0) * hb) / 2
        exact (mul_eq_zero.mp this).resolve_right hne
      exact hs₁ (by linear_combination 2 * k1 - k2)
    -- `B ↦ (B₀₀, B₁₀, B₀₁)` is injective on `N`
    apply finrank_le_three_of_eval N ![0, 1, 0] ![0, 0, 1]
    intro M hM hz
    have h00 : M 0 0 = 0 := hz 0
    have h10 : M 1 0 = 0 := hz 1
    have h01 : M 0 1 = 0 := hz 2
    obtain ⟨f1, f2, f3, -⟩ := F M hM
    have h11 : M 1 1 = 0 := by linear_combination h2xy M hM - 2 * h00
    have h21 : M 2 1 = 0 := by rw [f2, h10, neg_zero]
    have h22 : M 2 2 = 0 := by rw [f3, h00, h11]; ring
    obtain ⟨g1, g2, -, -⟩ := F B₁ hB₁
    obtain ⟨-, sB, dB⟩ := (hN B₁ hB₁).expand
    obtain ⟨-, sBM, dBM⟩ := (hN _ (N.add_mem hB₁ hM)).expand
    simp only [Matrix.add_apply] at sBM dBM
    rw [h00, h10, h01, h11, f1, h21, h22] at sBM dBM
    have hr : M 1 2 = 0 := by
      have : B₁ 1 0 * M 1 2 = 0 := by
        linear_combination -(sBM - sB) / 2 + M 0 2 * g1 + M 1 2 * g2
      exact (mul_eq_zero.mp this).resolve_left hs₁
    have hq : M 0 2 = 0 := by
      have : B₁ 1 0 ^ 2 * M 0 2 = 0 := by
        linear_combination M 0 2 * B₁ 1 0 * g2 - M 0 2 * B₁ 1 1 * g1 - (dBM - dB) +
          (-B₁ 0 0 * B₁ 2 1 + B₁ 0 1 * B₁ 2 0) * hr
      exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hs₁)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h01, h11, f1, h21, h22, hr, hq]

/- ### Conjugating a rank-two nilpotent matrix to the Jordan block -/

theorem mul_cols_eq_cols_mul_Jmat (A : Mat) (w₀ w₁ w₂ : Fin 3 → ℂ) (h0 : A *ᵥ w₀ = 0)
    (h1 : A *ᵥ w₁ = w₀) (h2 : A *ᵥ w₂ = w₁) :
    A * (of ![w₀, w₁, w₂])ᵀ = (of ![w₀, w₁, w₂])ᵀ * Jmat := by
  ext r c
  have e0 := congrFun h0 r
  have e1 := congrFun h1 r
  have e2 := congrFun h2 r
  simp only [mulVec, dotProduct, Fin.sum_univ_three, Pi.zero_apply] at e0 e1 e2
  fin_cases c
  · simp [mul_apply, Fin.sum_univ_three]
    linear_combination e0
  · simp [mul_apply, Fin.sum_univ_three]
    linear_combination e1
  · simp [mul_apply, Fin.sum_univ_three]
    linear_combination e2

theorem det_cols_ne_zero (A : Mat) (w₀ w₁ w₂ : Fin 3 → ℂ) (hw : w₀ ≠ 0) (h0 : A *ᵥ w₀ = 0)
    (h1 : A *ᵥ w₁ = w₀) (h2 : A *ᵥ w₂ = w₁) : det (of ![w₀, w₁, w₂])ᵀ ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hc⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  have hQc : (of ![w₀, w₁, w₂])ᵀ *ᵥ c = c 0 • w₀ + c 1 • w₁ + c 2 • w₂ := by
    ext r
    simp [mulVec, dotProduct, Fin.sum_univ_three]
    ring
  rw [hQc] at hc
  have e1 : A *ᵥ (c 0 • w₀ + c 1 • w₁ + c 2 • w₂) = c 1 • w₀ + c 2 • w₁ := by
    rw [mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul, h0, h1, h2, smul_zero,
      zero_add]
  have e2 : A *ᵥ (c 1 • w₀ + c 2 • w₁) = c 2 • w₀ := by
    rw [mulVec_add, mulVec_smul, mulVec_smul, h0, h1, smul_zero, zero_add]
  rw [hc, mulVec_zero] at e1
  rw [← e1, mulVec_zero] at e2
  have hc2 : c 2 = 0 := (smul_eq_zero.mp e2.symm).resolve_right hw
  rw [hc2, zero_smul, add_zero] at e1
  have hc1 : c 1 = 0 := (smul_eq_zero.mp e1.symm).resolve_right hw
  rw [hc1, hc2, zero_smul, zero_smul, add_zero, add_zero] at hc
  have hc0' : c 0 = 0 := (smul_eq_zero.mp hc).resolve_right hw
  apply hc0
  ext i
  fin_cases i <;> simp [hc0', hc1, hc2]

theorem exists_conj_eq_Jmat {A : Mat} (h : NilCond A) (hA : A * A ≠ 0) :
    ∃ Q : Mat, IsUnit Q.det ∧ Q⁻¹ * A * Q = Jmat := by
  obtain ⟨i, j, hij⟩ : ∃ i j, (A * A) i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hA (Matrix.ext hcon)
  have hw0 : A *ᵥ (A *ᵥ Pi.single j 1) ≠ 0 := by
    intro h0
    apply hij
    have : ((A * A) *ᵥ Pi.single j 1) i = 0 := by
      rw [← mulVec_mulVec, h0]
      rfl
    rwa [mulVec_single_one] at this
  have h0 : A *ᵥ (A *ᵥ (A *ᵥ Pi.single j 1)) = 0 := by
    rw [mulVec_mulVec, mulVec_mulVec, h.cube, zero_mulVec]
  have hQ := isUnit_iff_ne_zero.mpr (det_cols_ne_zero A _ _ (Pi.single j 1) hw0 h0 rfl rfl)
  refine ⟨_, hQ, ?_⟩
  rw [Matrix.mul_assoc, mul_cols_eq_cols_mul_Jmat A _ _ _ h0 rfl rfl,
    nonsing_inv_mul_cancel_left _ _ hQ]

/- ### Gerstenhaber's bound -/

theorem finrank_le_three_of_nilCond (N : Submodule ℂ Mat) (hN : ∀ A ∈ N, NilCond A) :
    Module.finrank ℂ N ≤ 3 := by
  by_cases h : ∃ A ∈ N, A * A ≠ 0
  · obtain ⟨A, hA, hAA⟩ := h
    obtain ⟨Q, hQ, hQA⟩ := exists_conj_eq_Jmat (hN A hA) hAA
    have hN' : ∀ M ∈ N.map (lrMul Q⁻¹ Q), NilCond M := by
      rintro _ ⟨B, hB, rfl⟩
      exact (hN B hB).conj hQ
    have hJ : Jmat ∈ N.map (lrMul Q⁻¹ Q) := ⟨A, hA, hQA⟩
    have hle : N ≤ (N.map (lrMul Q⁻¹ Q)).map (lrMul Q Q⁻¹) := by
      intro B hB
      refine ⟨Q⁻¹ * B * Q, ⟨B, hB, rfl⟩, ?_⟩
      simp only [lrMul_apply, Matrix.mul_assoc, mul_nonsing_inv _ hQ, Matrix.mul_one,
        mul_nonsing_inv_cancel_left _ _ hQ]
    calc Module.finrank ℂ N
        ≤ Module.finrank ℂ ((N.map (lrMul Q⁻¹ Q)).map (lrMul Q Q⁻¹)) :=
          Submodule.finrank_mono hle
      _ ≤ Module.finrank ℂ (N.map (lrMul Q⁻¹ Q)) := Submodule.finrank_map_le _ _
      _ ≤ 3 := finrank_le_three_of_Jmat_mem _ hN' hJ
  · push Not at h
    exact finrank_le_three_of_minors N fun M hM => minor_eq_of_sq_eq_zero (hN M hM) (h M hM)

/-- Gerstenhaber's bound for `3 × 3` matrices. -/
theorem finrank_le_three_of_isNilpotent (N : Submodule ℂ Mat) (h : ∀ A ∈ N, IsNilpotent A) :
    Module.finrank ℂ N ≤ 3 :=
  finrank_le_three_of_nilCond N fun A hA => nilCond_of_isNilpotent (h A hA)

/- ### Covering by six rank-one matrices -/

theorem coeffs_eq_zero_of_forall_ne {a b c : ℂ}
    (h : ∀ t : ℂ, 1 + t * a + t ^ 2 * b + t ^ 3 * c ≠ 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  classical
  let p : Polynomial ℂ := Polynomial.C c * Polynomial.X ^ 3 + Polynomial.C b * Polynomial.X ^ 2 +
    Polynomial.C a * Polynomial.X + Polynomial.C 1
  have hdeg : p.degree ≤ 0 := by
    by_contra hd
    push Not at hd
    obtain ⟨z, hz⟩ := Complex.exists_root hd
    apply h z
    have hz' : Polynomial.eval z p = 0 := hz
    simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X] at hz'
    linear_combination hz'
  have hc3 : p.coeff 3 = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (lt_of_le_of_lt hdeg (by norm_num))
  have hc2 : p.coeff 2 = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (lt_of_le_of_lt hdeg (by norm_num))
  have hc1 : p.coeff 1 = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (lt_of_le_of_lt hdeg (by norm_num))
  simp [p, Polynomial.coeff_one, Polynomial.coeff_C, Polynomial.coeff_X_pow] at hc1 hc2 hc3
  exact ⟨hc1, hc2, hc3⟩

/-- A singular `3 × 3` matrix is a sum of two matrices of rank at most one. -/
theorem exists_two_rankOne_of_det_eq_zero {X : Mat} (h : det X = 0) :
    ∃ u v : Fin 2 → Fin 3 → ℂ, X = ∑ j, vecMulVec (u j) (v j) := by
  obtain ⟨w, hw0, hw⟩ := exists_vecMul_eq_zero_iff.mpr h
  obtain ⟨k, hk⟩ : ∃ k, w k ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hw0 (funext hc)
  let u' : Fin 3 → Fin 3 → ℂ := fun i r =>
    (if r = i then 1 else 0) - (if r = k then w i / w k else 0)
  have hX : X = ∑ i, vecMulVec (u' i) (X i) := by
    ext r c
    have hc : ∑ i, w i * X i c = 0 := by
      have := congrFun hw c
      simpa [vecMul, dotProduct] using this
    simp only [Matrix.sum_apply, vecMulVec_apply, u', sub_mul, Finset.sum_sub_distrib, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    by_cases hr : r = k
    · subst hr
      simp only [if_true]
      have : ∑ i, w i / w r * X i c = 0 := by
        simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, hc, zero_div]
      rw [this, sub_zero]
    · simp [hr]
  have hk0 : u' k = 0 := by
    ext r
    simp only [u', Pi.zero_apply]
    by_cases hr : r = k
    · simp [hr, div_self hk]
    · simp [hr]
  refine ⟨fun j => u' (k.succAbove j), fun j => X (k.succAbove j), ?_⟩
  conv_lhs => rw [hX, Fin.sum_univ_succAbove _ k, hk0]
  simp

/-- A subspace of dimension ≤ 5 containing four linearly independent rank-one matrices is covered
by six. -/
theorem coveredBy_six_of_four_rankOne (S : Submodule ℂ Mat) (hS : Module.finrank ℂ S ≤ 5)
    (a b : Fin 4 → Fin 3 → ℂ) (hmem : ∀ l, Matrix.vecMulVec (a l) (b l) ∈ S)
    (hli : LinearIndependent ℂ fun l => Matrix.vecMulVec (a l) (b l)) : CoveredBy S 6 := by
  set span4 := Submodule.span ℂ (Set.range fun l => vecMulVec (a l) (b l))
  have hspanS : span4 ≤ S := Submodule.span_le.mpr (by rintro _ ⟨l, rfl⟩; exact hmem l)
  have hspan4 : Module.finrank ℂ span4 = 4 := by rw [finrank_span_eq_card hli, Fintype.card_fin]
  by_cases hle : S ≤ span4
  · exact CoveredBy.mono_right (by norm_num) ⟨a, b, hle⟩
  obtain ⟨X, hXS, hXspan⟩ := SetLike.not_le_iff_exists.mp hle
  have hS_le : S ≤ span4 ⊔ Submodule.span ℂ {X} := by
    have hle' : span4 ⊔ Submodule.span ℂ {X} ≤ S :=
      sup_le hspanS ((Submodule.span_singleton_le_iff_mem X S).mpr hXS)
    have hlt : span4 < span4 ⊔ Submodule.span ℂ {X} :=
      lt_of_le_of_ne le_sup_left fun h =>
        hXspan (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self X))
    have h5 : 4 < Module.finrank ℂ ↥(span4 ⊔ Submodule.span ℂ {X}) :=
      hspan4 ▸ Submodule.finrank_lt_finrank_of_lt hlt
    exact (Submodule.eq_of_le_of_finrank_le hle' (hS.trans (Nat.succ_le_of_lt h5))).ge
  by_cases hdet : ∃ σ ∈ span4, det (X + σ) = 0
  · -- a singular element `X + σ` is a sum of two rank-one matrices
    obtain ⟨σ, hσ, hd⟩ := hdet
    obtain ⟨u, v, huv⟩ := exists_two_rankOne_of_det_eq_zero hd
    set a' : Fin 6 → Fin 3 → ℂ := ![a 0, a 1, a 2, a 3, u 0, u 1]
    set b' : Fin 6 → Fin 3 → ℂ := ![b 0, b 1, b 2, b 3, v 0, v 1]
    set T := Submodule.span ℂ (Set.range fun l => vecMulVec (a' l) (b' l))
    have hT : ∀ l, vecMulVec (a' l) (b' l) ∈ T := fun l => Submodule.subset_span ⟨l, rfl⟩
    have hspanT : span4 ≤ T := by
      rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      fin_cases l
      · exact hT 0
      · exact hT 1
      · exact hT 2
      · exact hT 3
    have hXσ : X + σ ∈ T := by
      rw [huv, Fin.sum_univ_two]
      exact T.add_mem (hT 4) (hT 5)
    refine ⟨a', b', hS_le.trans (sup_le hspanT ?_)⟩
    rw [Submodule.span_singleton_le_iff_mem]
    simpa using T.sub_mem hXσ (hspanT hσ)
  · -- otherwise `X⁻¹ span4` is a four-dimensional space of nilpotent matrices
    push Not at hdet
    exfalso
    have hX0 : det X ≠ 0 := by simpa using hdet 0 span4.zero_mem
    have hXu : IsUnit X.det := isUnit_iff_ne_zero.mpr hX0
    have hN : ∀ M ∈ span4.map (lrMul X⁻¹ 1), NilCond M := by
      rintro _ ⟨σ, hσ, rfl⟩
      have key : ∀ t : ℂ, 1 + t * trace (lrMul X⁻¹ 1 σ) +
          t ^ 2 * ((trace (lrMul X⁻¹ 1 σ) ^ 2 - trace (lrMul X⁻¹ 1 σ * lrMul X⁻¹ 1 σ)) / 2) +
          t ^ 3 * det (lrMul X⁻¹ 1 σ) ≠ 0 := by
        intro t
        have h1 := hdet (t • σ) (span4.smul_mem t hσ)
        have h2 : X + t • σ = X * (1 + t • lrMul X⁻¹ 1 σ) := by
          simp only [lrMul_apply, Matrix.mul_one, Matrix.mul_add, Matrix.mul_smul,
            mul_nonsing_inv_cancel_left _ _ hXu]
        rw [h2, det_mul, det_one_add_smul_three] at h1
        exact right_ne_zero_of_mul h1
      obtain ⟨h1, h2, h3⟩ := coeffs_eq_zero_of_forall_ne key
      refine ⟨h1, ?_, h3⟩
      rw [h1] at h2
      linear_combination -2 * h2
    have h3 := finrank_le_three_of_nilCond _ hN
    have h4 : span4 ≤ (span4.map (lrMul X⁻¹ 1)).map (lrMul X 1) := by
      intro σ hσ
      refine ⟨lrMul X⁻¹ 1 σ, ⟨σ, hσ, rfl⟩, ?_⟩
      simp only [lrMul_apply, Matrix.mul_one]
      exact mul_nonsing_inv_cancel_left _ _ hXu
    have h6 : Module.finrank ℂ span4 ≤ 3 :=
      ((Submodule.finrank_mono h4).trans (Submodule.finrank_map_le _ _)).trans h3
    omega

end TensorRank335

end

/- ## Section: `Degenerate` -/

section

/-
# Degenerate cases: symmetry conditions and four rank-one matrices

This file handles the degenerate situations left over by Lemma R in the proof of the universal
bound. Throughout, `S` is a subspace of `3 × 3` complex matrices.

* `TensorRank335.coveredBy_six_of_symm_of_det_ne_zero` (D1): if `(Nᵀ * X).IsSymm` for all
  `X ∈ S` and `N` is invertible, then `Nᵀ S` consists of symmetric matrices, which are spanned
  by the six rank-one matrices `eᵢ eᵢᵀ`, `(eᵢ + eⱼ)(eᵢ + eⱼ)ᵀ`.
* `TensorRank335.coveredBy_six_of_symm_of_rank_two` (D2): the same when `N` has rank two. With
  the normal form `N * Q = R * diag(1, 1, 0)` (`Degenerate.exists_mul_eq_mul_D2`) the condition
  becomes `X₀₁ = X₁₀`, `X₀₂ = X₁₂ = 0` for `X ∈ Rᵀ S Q`.
* `TensorRank335.coveredBy_six_of_symm_symm_rank_one` (D3): `(Nᵀ * X).IsSymm` and
  `(X * N').IsSymm` for rank-one `N = u vᵀ`, `N' = u' v'ᵀ`. These say `uᵀ X ∥ vᵀ` and
  `X u' ∥ v'`; after a change of bases (`Degenerate.exists_isUnit_row_zero_mulVec`) the first row
  and the first column of every element are supported in one position each, so `S` lies in the
  span of six matrix units.
* `TensorRank335.fourRankOne_or_row`, `TensorRank335.fourRankOne_of_row_of_forall_left`,
  `TensorRank335.fourRankOne_of_row_of_symm` (D4): criteria for `S` to contain four linearly
  independent rank-one matrices (`TensorRank335.FourRankOne`).

The normal forms are derived from the diagonalisation of a matrix by transvections
(`Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal`):
`Degenerate.exists_eq_vecMulVec_of_adjugate_eq_zero` (a nonzero matrix with vanishing adjugate
has rank one) and `Degenerate.exists_mul_eq_mul_D2` (rank two).
-/

namespace TensorRank335

open Matrix

/-- `S` contains four linearly independent rank-one matrices. -/
def FourRankOne (S : Submodule ℂ Mat) : Prop :=
  ∃ a b : Fin 4 → Fin 3 → ℂ, (∀ l, vecMulVec (a l) (b l) ∈ S) ∧
    LinearIndependent ℂ fun l => vecMulVec (a l) (b l)

namespace Degenerate

/- ### Generalities -/

theorem coveredBy_of_forall_exists {S : Submodule ℂ Mat} {r : ℕ} (a b : Fin r → Fin 3 → ℂ)
    (h : ∀ X ∈ S, ∃ c : Fin r → ℂ, ∑ l, c l • vecMulVec (a l) (b l) = X) : CoveredBy S r :=
  ⟨a, b, fun X hX => (Submodule.mem_span_range_iff_exists_fun ℂ).mpr (h X hX)⟩

theorem isUnit_of_det_ne_zero {M : Mat} (h : M.det ≠ 0) : IsUnit M :=
  (isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr h)

theorem isSymm_transpose_mul_mul {M : Mat} (hM : M.IsSymm) (Q : Mat) : (Qᵀ * M * Q).IsSymm := by
  show (Qᵀ * M * Q)ᵀ = Qᵀ * M * Q
  rw [transpose_mul, transpose_mul, transpose_transpose, hM.eq, Matrix.mul_assoc]

theorem single_zero_vecMul (M : Mat) : Pi.single 0 1 ᵥ* M = M 0 :=
  single_one_vecMul 0 M

theorem inv_lrMul_lrMul {P Q : Mat} (hP : IsUnit P) (hQ : IsUnit Q) (X : Mat) :
    lrMul P⁻¹ Q⁻¹ (lrMul P Q X) = X := by
  have hPd := (isUnit_iff_isUnit_det P).mp hP
  have hQd := (isUnit_iff_isUnit_det Q).mp hQ
  simp only [lrMul_apply]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hPd, Matrix.one_mul,
    Matrix.mul_assoc, mul_nonsing_inv _ hQd, Matrix.mul_one]

theorem lrMul_injective {P Q : Mat} (hP : IsUnit P) (hQ : IsUnit Q) :
    Function.Injective (lrMul P Q) := fun X Y h => by
  rw [← inv_lrMul_lrMul hP hQ X, h, inv_lrMul_lrMul hP hQ Y]

/- ### Symmetric matrices -/

/-- The vectors `e₀, e₁, e₂, e₀ + e₁, e₀ + e₂, e₁ + e₂`. -/
def symVec : Fin 6 → Fin 3 → ℂ :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 0], ![1, 0, 1], ![0, 1, 1]]

/-- A space of symmetric matrices is covered by `eᵢ eᵢᵀ` and `(eᵢ + eⱼ)(eᵢ + eⱼ)ᵀ`. -/
theorem coveredBy_six_of_forall_isSymm (S : Submodule ℂ Mat) (hS : ∀ X ∈ S, X.IsSymm) :
    CoveredBy S 6 := by
  refine coveredBy_of_forall_exists symVec symVec fun X hX => ?_
  have h := IsSymm.ext_iff.mp (hS X hX)
  have h01 := h 0 1
  have h02 := h 0 2
  have h12 := h 1 2
  refine ⟨![X 0 0 - X 0 1 - X 0 2, X 1 1 - X 0 1 - X 1 2, X 2 2 - X 0 2 - X 1 2, X 0 1, X 0 2,
    X 1 2], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symVec, Fin.sum_univ_six] <;>
    first
    | ring
    | linear_combination h01
    | linear_combination (-1 : ℂ) * h01
    | linear_combination h02
    | linear_combination (-1 : ℂ) * h02
    | linear_combination h12
    | linear_combination (-1 : ℂ) * h12

/- ### The rank-two normal form -/

/-- `diag(1, 1, 0)`. -/
def D2 : Mat := diagonal ![1, 1, 0]

theorem coveredBy_six_of_D2 (S : Submodule ℂ Mat) (hS : ∀ X ∈ S, (D2 * X).IsSymm) :
    CoveredBy S 6 := by
  refine coveredBy_of_forall_exists
    ![![1, 0, 0], ![0, 1, 0], ![1, 1, 0], ![0, 0, 1], ![0, 0, 1], ![0, 0, 1]]
    ![![1, 0, 0], ![0, 1, 0], ![1, 1, 0], ![1, 0, 0], ![0, 1, 0], ![0, 0, 1]] fun X hX => ?_
  have h := IsSymm.ext_iff.mp (hS X hX)
  have h01 : X 1 0 = X 0 1 := by
    have := h 0 1
    simp only [D2, diagonal_mul] at this
    simpa using this
  have h02 : X 0 2 = 0 := by
    have := h 0 2
    simp only [D2, diagonal_mul] at this
    simpa using this.symm
  have h12 : X 1 2 = 0 := by
    have := h 1 2
    simp only [D2, diagonal_mul] at this
    simpa using this.symm
  refine ⟨![X 0 0 - X 0 1, X 1 1 - X 0 1, X 0 1, X 2 0, X 2 1, X 2 2], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_six, h01, h02, h12]

theorem exists_isUnit_mul_mul_eq_diagonal (N : Mat) :
    ∃ P Q : Mat, ∃ d : Fin 3 → ℂ, IsUnit P ∧ IsUnit Q ∧ P * N * Q = diagonal d := by
  obtain ⟨L, L', d, h⟩ := Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal N
  refine ⟨_, _, d, ?_, ?_, h⟩ <;>
    exact (isUnit_iff_isUnit_det _).mpr
      (by rw [TransvectionStruct.det_toMatrix_prod]; exact isUnit_one)

theorem isUnit_adjugate_of_isUnit {P : Mat} (hP : IsUnit P) : IsUnit P.adjugate := by
  rw [isUnit_iff_isUnit_det, det_adjugate]
  exact ((isUnit_iff_isUnit_det P).mp hP).pow _

theorem adjugate_mul_mul_eq_zero_iff {P Q N : Mat} (hP : IsUnit P) (hQ : IsUnit Q) :
    (P * N * Q).adjugate = 0 ↔ N.adjugate = 0 := by
  rw [adjugate_mul_distrib, adjugate_mul_distrib, (isUnit_adjugate_of_isUnit hQ).mul_right_eq_zero,
    (isUnit_adjugate_of_isUnit hP).mul_left_eq_zero]

theorem adjugate_diagonal_three (d : Fin 3 → ℂ) :
    (diagonal d).adjugate = diagonal ![d 1 * d 2, d 0 * d 2, d 0 * d 1] := by
  rw [adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- A nonzero `3 × 3` matrix with vanishing adjugate has rank one. -/
theorem exists_eq_vecMulVec_of_adjugate_eq_zero {N : Mat} (hN : N ≠ 0) (h : N.adjugate = 0) :
    ∃ u v : Fin 3 → ℂ, u ≠ 0 ∧ v ≠ 0 ∧ N = vecMulVec u v := by
  obtain ⟨P, Q, d, hP, hQ, hPNQ⟩ := exists_isUnit_mul_mul_eq_diagonal N
  have hPd := (isUnit_iff_isUnit_det P).mp hP
  have hQd := (isUnit_iff_isUnit_det Q).mp hQ
  have hd0 : diagonal d ≠ 0 := by
    rw [← hPNQ]
    intro h0
    rw [hQ.mul_left_eq_zero, hP.mul_right_eq_zero] at h0
    exact hN h0
  have hadjd : (diagonal d).adjugate = 0 := by
    rw [← hPNQ, adjugate_mul_mul_eq_zero_iff hP hQ]
    exact h
  rw [adjugate_diagonal_three] at hadjd
  have e0 : d 1 * d 2 = 0 := by simpa using congrFun (congrFun hadjd 0) 0
  have e1 : d 0 * d 2 = 0 := by simpa using congrFun (congrFun hadjd 1) 1
  have e2 : d 0 * d 1 = 0 := by simpa using congrFun (congrFun hadjd 2) 2
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hd0 (by ext a b; simp [diagonal_apply, hc])
  have hzero : ∀ a, a ≠ i → d a = 0 := by
    intro a hai
    fin_cases i <;> fin_cases a <;>
      first
      | exact absurd rfl hai
      | exact (mul_eq_zero.mp e0).resolve_left hi
      | exact (mul_eq_zero.mp e0).resolve_right hi
      | exact (mul_eq_zero.mp e1).resolve_left hi
      | exact (mul_eq_zero.mp e1).resolve_right hi
      | exact (mul_eq_zero.mp e2).resolve_left hi
      | exact (mul_eq_zero.mp e2).resolve_right hi
  have hdiag : diagonal d = vecMulVec (Pi.single i (d i)) (Pi.single i 1) := by
    ext a b
    rw [diagonal_apply, vecMulVec_apply]
    by_cases hab : a = b
    · subst hab
      by_cases hai : a = i
      · subst hai
        simp
      · simp [hai, hzero a hai]
    · rw [if_neg hab]
      simp only [Pi.single_apply]
      split_ifs with h1 h2 <;> simp_all
  refine ⟨P⁻¹ *ᵥ Pi.single i (d i), Pi.single i 1 ᵥ* Q⁻¹, ?_, ?_, ?_⟩
  · intro h0
    apply hi
    have := congrArg (P *ᵥ ·) h0
    simp only [mulVec_mulVec, mul_nonsing_inv _ hPd, one_mulVec, mulVec_zero] at this
    simpa using congrFun this i
  · intro h0
    have := congrArg (· ᵥ* Q) h0
    simp only [vecMul_vecMul, nonsing_inv_mul _ hQd, vecMul_one, zero_vecMul] at this
    simpa using congrFun this i
  · rw [← vecMulVec_mul, ← mul_vecMulVec, ← hdiag, ← hPNQ, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      nonsing_inv_mul _ hPd, Matrix.one_mul, Matrix.mul_assoc, mul_nonsing_inv _ hQd,
      Matrix.mul_one]

/-- The permutation matrix of the transposition `(0 2)`. -/
def W02 : Mat := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

/-- The permutation matrix of the transposition `(1 2)`. -/
def W12 : Mat := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

theorem isUnit_W02 : IsUnit W02 := isUnit_of_det_ne_zero (by simp [W02, det_fin_three])

theorem isUnit_W12 : IsUnit W12 := isUnit_of_det_ne_zero (by simp [W12, det_fin_three])

theorem W02_mul_diagonal_mul_W02 (v : Fin 3 → ℂ) :
    W02 * diagonal v * W02 = diagonal ![v 2, v 1, v 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [W02, Matrix.mul_apply, Fin.sum_univ_three, vecMul_diagonal]

theorem W12_mul_diagonal_mul_W12 (v : Fin 3 → ℂ) :
    W12 * diagonal v * W12 = diagonal ![v 0, v 2, v 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [W12, Matrix.mul_apply, Fin.sum_univ_three, vecMul_diagonal]

theorem isUnit_diagonal_three {v : Fin 3 → ℂ} (h0 : v 0 ≠ 0) (h1 : v 1 ≠ 0) (h2 : v 2 ≠ 0) :
    IsUnit (diagonal v) :=
  isUnit_of_det_ne_zero (by simp [det_diagonal, Fin.prod_univ_three, h0, h1, h2])

theorem exists_isUnit_mul_diagonal_mul_eq_D2 {d : Fin 3 → ℂ} (hdd : d 0 * d 1 * d 2 = 0)
    (hadj : ¬ (d 1 * d 2 = 0 ∧ d 0 * d 2 = 0 ∧ d 0 * d 1 = 0)) :
    ∃ P Q : Mat, IsUnit P ∧ IsUnit Q ∧ P * diagonal d * Q = D2 := by
  rcases mul_eq_zero.mp hdd with h01 | h2
  · rcases mul_eq_zero.mp h01 with h0 | h1
    · have h1 : d 1 ≠ 0 := fun h1 => hadj ⟨by simp [h1], by simp [h0], by simp [h0]⟩
      have h2 : d 2 ≠ 0 := fun h2 => hadj ⟨by simp [h2], by simp [h0], by simp [h0]⟩
      refine ⟨W02 * diagonal ![1, (d 1)⁻¹, (d 2)⁻¹], W02,
        isUnit_W02.mul (isUnit_diagonal_three (by simp) (by simp [h1]) (by simp [h2])),
        isUnit_W02, ?_⟩
      rw [Matrix.mul_assoc W02, diagonal_mul_diagonal, W02_mul_diagonal_mul_W02, D2]
      congr 1
      funext i
      fin_cases i <;> simp [h0, h1, h2]
    · have h0 : d 0 ≠ 0 := fun h0 => hadj ⟨by simp [h1], by simp [h0], by simp [h0]⟩
      have h2 : d 2 ≠ 0 := fun h2 => hadj ⟨by simp [h2], by simp [h2], by simp [h1]⟩
      refine ⟨W12 * diagonal ![(d 0)⁻¹, 1, (d 2)⁻¹], W12,
        isUnit_W12.mul (isUnit_diagonal_three (by simp [h0]) (by simp) (by simp [h2])),
        isUnit_W12, ?_⟩
      rw [Matrix.mul_assoc W12, diagonal_mul_diagonal, W12_mul_diagonal_mul_W12, D2]
      congr 1
      funext i
      fin_cases i <;> simp [h0, h1, h2]
  · have h0 : d 0 ≠ 0 := fun h0 => hadj ⟨by simp [h2], by simp [h0], by simp [h0]⟩
    have h1 : d 1 ≠ 0 := fun h1 => hadj ⟨by simp [h1], by simp [h2], by simp [h1]⟩
    refine ⟨diagonal ![(d 0)⁻¹, (d 1)⁻¹, 1], 1,
      isUnit_diagonal_three (by simp [h0]) (by simp [h1]) (by simp), isUnit_one, ?_⟩
    rw [Matrix.mul_one, diagonal_mul_diagonal, D2]
    congr 1
    funext i
    fin_cases i <;> simp [h0, h1, h2]

/-- **Normal form of a rank-two matrix**: `N * Q = R * diag(1, 1, 0)` with `R`, `Q` invertible. -/
theorem exists_mul_eq_mul_D2 {N : Mat} (hdet : N.det = 0) (hadj : N.adjugate ≠ 0) :
    ∃ R Q : Mat, IsUnit R ∧ IsUnit Q ∧ N * Q = R * D2 := by
  obtain ⟨P, Q, d, hP, hQ, hPNQ⟩ := exists_isUnit_mul_mul_eq_diagonal N
  have hdd : d 0 * d 1 * d 2 = 0 := by
    have h := congrArg det hPNQ
    rw [det_mul, det_mul, hdet, mul_zero, zero_mul, det_diagonal, Fin.prod_univ_three] at h
    exact h.symm
  have hadjd : ¬ (d 1 * d 2 = 0 ∧ d 0 * d 2 = 0 ∧ d 0 * d 1 = 0) := by
    rintro ⟨e0, e1, e2⟩
    apply hadj
    rw [← adjugate_mul_mul_eq_zero_iff hP hQ, hPNQ, adjugate_diagonal_three, e0, e1, e2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  obtain ⟨P₁, Q₁, hP₁, hQ₁, h₁⟩ := exists_isUnit_mul_diagonal_mul_eq_D2 hdd hadjd
  have hu : IsUnit (P₁ * P) := hP₁.mul hP
  refine ⟨(P₁ * P)⁻¹, Q * Q₁, isUnit_nonsing_inv_iff.mpr hu, hQ.mul hQ₁, ?_⟩
  rw [← h₁, ← hPNQ]
  have e : P₁ * (P * N * Q) * Q₁ = (P₁ * P) * (N * (Q * Q₁)) := by simp only [Matrix.mul_assoc]
  rw [e, nonsing_inv_mul_cancel_left _ _ ((isUnit_iff_isUnit_det _).mp hu)]

/- ### Matrix units -/

/-- A space of matrices supported on the positions `p l` is covered by the corresponding
matrix units. -/
theorem coveredBy_of_support {S : Submodule ℂ Mat} {r : ℕ} (p : Fin r → Fin 3 × Fin 3)
    (h : ∀ X ∈ S, ∀ i j, X i j ≠ 0 → ∃ l, p l = (i, j)) : CoveredBy S r := by
  refine ⟨fun l => Pi.single (p l).1 1, fun l => Pi.single (p l).2 1, fun X hX => ?_⟩
  rw [matrix_eq_sum_single X]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  by_cases hij : X i j = 0
  · rw [hij, single_zero]
    exact Submodule.zero_mem _
  · obtain ⟨l, hl⟩ := h X hX i j hij
    have hmem : single i j (1 : ℂ) ∈ Submodule.span ℂ
        (Set.range fun l => vecMulVec (Pi.single (p l).1 (1 : ℂ)) (Pi.single (p l).2 1)) :=
      Submodule.subset_span
        ⟨l, by simp only [hl]; exact (single_eq_single_vecMulVec_single i j).symm⟩
    have e : single i j (X i j) = X i j • single i j (1 : ℂ) := by
      rw [smul_single, smul_eq_mul, mul_one]
    rw [e]
    exact Submodule.smul_mem _ _ hmem

/- ### Symmetry conditions for rank-one matrices -/

theorem exists_smul_of_isSymm_vecMulVec {x y : Fin 3 → ℂ} (hx : x ≠ 0)
    (h : (vecMulVec x y).IsSymm) : ∃ c : ℂ, y = c • x := by
  obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx (funext hc)
  refine ⟨y k / x k, funext fun i => ?_⟩
  have hik := IsSymm.ext_iff.mp h i k
  simp only [vecMulVec_apply] at hik
  rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hk]
  linear_combination hik

theorem exists_smul_of_isSymm_transpose_mul {u v : Fin 3 → ℂ} {X : Mat} (hv : v ≠ 0)
    (h : ((vecMulVec u v)ᵀ * X).IsSymm) : ∃ c : ℂ, u ᵥ* X = c • v := by
  rw [transpose_vecMulVec, vecMulVec_mul] at h
  exact exists_smul_of_isSymm_vecMulVec hv h

theorem exists_smul_of_isSymm_mul {u v : Fin 3 → ℂ} {X : Mat} (hv : v ≠ 0)
    (h : (X * vecMulVec u v).IsSymm) : ∃ c : ℂ, X *ᵥ u = c • v := by
  rw [mul_vecMulVec] at h
  have h' : (vecMulVec v (X *ᵥ u)).IsSymm := by
    rw [← transpose_vecMulVec]
    exact h.transpose
  exact exists_smul_of_isSymm_vecMulVec hv h'

/- ### Invertible matrices with a prescribed first row -/

theorem exists_isUnit_row_zero {x : Fin 3 → ℂ} (hx : x ≠ 0) : ∃ R : Mat, IsUnit R ∧ R 0 = x := by
  by_cases h0 : x 0 = 0
  · by_cases h1 : x 1 = 0
    · have h2 : x 2 ≠ 0 := by
        intro h2
        apply hx
        funext i
        fin_cases i <;> simp [h0, h1, h2]
      refine ⟨!![x 0, x 1, x 2; 1, 0, 0; 0, 1, 0], isUnit_of_det_ne_zero ?_, ?_⟩
      · simp [det_fin_three, h2]
      · funext j
        fin_cases j <;> rfl
    · refine ⟨!![x 0, x 1, x 2; 1, 0, 0; 0, 0, 1], isUnit_of_det_ne_zero ?_, ?_⟩
      · simp [det_fin_three, h1]
      · funext j
        fin_cases j <;> rfl
  · refine ⟨!![x 0, x 1, x 2; 0, 1, 0; 0, 0, 1], isUnit_of_det_ne_zero ?_, ?_⟩
    · simp [det_fin_three, h0]
    · funext j
      fin_cases j <;> rfl

theorem exists_isUnit_fix_row_zero (z : Fin 3 → ℂ) :
    ∃ T : Mat, IsUnit T ∧ T 0 = Pi.single 0 1 ∧ ∃ c : ℂ, ∃ j : Fin 3,
      T *ᵥ z = c • Pi.single j 1 := by
  by_cases h0 : z 0 = 0
  · by_cases h1 : z 1 = 0
    · refine ⟨1, isUnit_one, ?_, z 2, 2, ?_⟩
      · funext j
        fin_cases j <;> simp [one_apply]
      · funext i
        fin_cases i <;> simp [h0, h1]
    · refine ⟨!![1, 0, 0; 0, 1, 0; 0, -(z 2 / z 1), 1], isUnit_of_det_ne_zero ?_, ?_, z 1, 1, ?_⟩
      · simp [det_fin_three]
      · funext j
        fin_cases j <;> simp
      · funext i
        fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three, h0, h1]
  · refine ⟨!![1, 0, 0; -(z 1 / z 0), 1, 0; -(z 2 / z 0), 0, 1], isUnit_of_det_ne_zero ?_, ?_,
      z 0, 0, ?_⟩
    · simp [det_fin_three]
    · funext j
      fin_cases j <;> simp
    · funext i
      fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three, h0]

theorem mul_row_zero {T : Mat} (R : Mat) (hT : T 0 = Pi.single 0 1) : (T * R) 0 = R 0 := by
  funext k
  rw [mul_apply]
  simp [hT, Pi.single_apply]

/-- An invertible matrix with first row `x` mapping `w` to a multiple of a basis vector. -/
theorem exists_isUnit_row_zero_mulVec {x : Fin 3 → ℂ} (hx : x ≠ 0) (w : Fin 3 → ℂ) :
    ∃ R : Mat, IsUnit R ∧ R 0 = x ∧ ∃ c : ℂ, ∃ j : Fin 3, R *ᵥ w = c • Pi.single j 1 := by
  obtain ⟨R₀, hR₀, hR₀0⟩ := exists_isUnit_row_zero hx
  obtain ⟨T, hT, hT0, c, j, hTz⟩ := exists_isUnit_fix_row_zero (R₀ *ᵥ w)
  exact ⟨T * R₀, hT.mul hR₀, by rw [mul_row_zero R₀ hT0, hR₀0], c, j,
    by rw [← mulVec_mulVec, hTz]⟩

/- ### Four rank-one matrices -/

/-- `X ↦ X 0`, the first row. -/
def row0 : Mat →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun X := X 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem exists_quad_zero (A B C : ℂ) :
    ∃ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) ∧ A * s * s + B * s * t + C * t * t = 0 := by
  by_cases hA : A = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, by simp [hA]⟩
  · obtain ⟨r, hr⟩ := IsAlgClosed.exists_eq_mul_self (discrim A B C)
    have hs := (quadratic_eq_zero_iff hA hr ((-B + r) / (2 * A))).mpr (Or.inl rfl)
    exact ⟨(-B + r) / (2 * A), 1, Or.inr one_ne_zero, by linear_combination hs⟩

/-- A pencil of `2 × 2` matrices (the lower right blocks) contains a singular member. -/
theorem exists_singular_comb (Z₀ Z₁ : Mat) :
    ∃ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) ∧
      (s • Z₀ + t • Z₁) 1 1 * (s • Z₀ + t • Z₁) 2 2 -
        (s • Z₀ + t • Z₁) 1 2 * (s • Z₀ + t • Z₁) 2 1 = 0 := by
  obtain ⟨s, t, hst, h⟩ := exists_quad_zero (Z₀ 1 1 * Z₀ 2 2 - Z₀ 1 2 * Z₀ 2 1)
    (Z₀ 1 1 * Z₁ 2 2 + Z₁ 1 1 * Z₀ 2 2 - Z₀ 1 2 * Z₁ 2 1 - Z₁ 1 2 * Z₀ 2 1)
    (Z₁ 1 1 * Z₁ 2 2 - Z₁ 1 2 * Z₁ 2 1)
  refine ⟨s, t, hst, ?_⟩
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination h

theorem adjugate_eq_zero_of_block {Z : Mat} (h0 : Z 0 = 0) (hc : ∀ i, Z i 0 = 0)
    (hdet : Z 1 1 * Z 2 2 - Z 1 2 * Z 2 1 = 0) : Z.adjugate = 0 := by
  have e : ∀ j, Z 0 j = 0 := fun j => congrFun h0 j
  rw [adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e, hc, hdet]

end Degenerate

open Degenerate

/-- `FourRankOne` is invariant under `X ↦ P * X * Q` for invertible `P`, `Q`. -/
theorem FourRankOne.of_map_lrMul {S : Submodule ℂ Mat} {P Q : Mat} (hP : IsUnit P)
    (hQ : IsUnit Q) (h : FourRankOne (S.map (lrMul P Q))) : FourRankOne S := by
  obtain ⟨a, b, hab, hli⟩ := h
  have hvec : ∀ l, lrMul P⁻¹ Q⁻¹ (vecMulVec (a l) (b l)) =
      vecMulVec (P⁻¹ *ᵥ a l) (b l ᵥ* Q⁻¹) := fun l => by
    rw [lrMul_apply, mul_vecMulVec, vecMulVec_mul]
  refine ⟨fun l => P⁻¹ *ᵥ a l, fun l => b l ᵥ* Q⁻¹, fun l => ?_, ?_⟩
  · obtain ⟨X, hX, hXe⟩ := hab l
    show vecMulVec (P⁻¹ *ᵥ a l) (b l ᵥ* Q⁻¹) ∈ S
    rw [← hvec, ← hXe, inv_lrMul_lrMul hP hQ]
    exact hX
  · have hker : LinearMap.ker (lrMul P⁻¹ Q⁻¹) = ⊥ := LinearMap.ker_eq_bot.mpr
      (lrMul_injective (isUnit_nonsing_inv_iff.mpr hP) (isUnit_nonsing_inv_iff.mpr hQ))
    have hfun : (fun l => vecMulVec (P⁻¹ *ᵥ a l) (b l ᵥ* Q⁻¹)) =
        ⇑(lrMul P⁻¹ Q⁻¹) ∘ fun l => vecMulVec (a l) (b l) := by
      funext l
      exact (hvec l).symm
    show LinearIndependent ℂ fun l => vecMulVec (P⁻¹ *ᵥ a l) (b l ᵥ* Q⁻¹)
    rw [hfun]
    exact hli.map' _ hker

/-- **D1.** If `(Nᵀ * X).IsSymm` for all `X ∈ S` with `N` invertible, then `S` is covered by six
rank-one matrices. -/
theorem coveredBy_six_of_symm_of_det_ne_zero (S : Submodule ℂ Mat) (N : Mat) (hdet : N.det ≠ 0)
    (hS : ∀ X ∈ S, (Nᵀ * X).IsSymm) : CoveredBy S 6 := by
  refine CoveredBy.of_map_lrMul ((isUnit_transpose N).mpr (isUnit_of_det_ne_zero hdet)) isUnit_one
    (coveredBy_six_of_forall_isSymm _ ?_)
  rintro _ ⟨X, hX, rfl⟩
  rw [lrMul_apply, Matrix.mul_one]
  exact hS X hX

/-- **D2.** The same as D1 when `N` has rank two. -/
theorem coveredBy_six_of_symm_of_rank_two (S : Submodule ℂ Mat) (N : Mat) (hdet : N.det = 0)
    (hadj : N.adjugate ≠ 0) (hS : ∀ X ∈ S, (Nᵀ * X).IsSymm) : CoveredBy S 6 := by
  obtain ⟨R, Q, hR, hQ, hNQ⟩ := exists_mul_eq_mul_D2 hdet hadj
  refine CoveredBy.of_map_lrMul ((isUnit_transpose R).mpr hR) hQ (coveredBy_six_of_D2 _ ?_)
  rintro _ ⟨X, hX, rfl⟩
  have hD : D2ᵀ = D2 := diagonal_transpose _
  have key : D2 * (Rᵀ * X * Q) = Qᵀ * (Nᵀ * X) * Q := by
    calc D2 * (Rᵀ * X * Q) = (R * D2)ᵀ * X * Q := by
          rw [transpose_mul, hD]
          simp only [Matrix.mul_assoc]
      _ = (N * Q)ᵀ * X * Q := by rw [hNQ]
      _ = Qᵀ * (Nᵀ * X) * Q := by
          rw [transpose_mul]
          simp only [Matrix.mul_assoc]
  rw [lrMul_apply, key]
  exact isSymm_transpose_mul_mul (hS X hX) Q

/-- **D3.** If `(Nᵀ * X).IsSymm` and `(X * N').IsSymm` for all `X ∈ S`, with `N` and `N'` of rank
one, then `S` is covered by six matrix units after a change of bases. -/
theorem coveredBy_six_of_symm_symm_rank_one (S : Submodule ℂ Mat) (N N' : Mat) (hN : N ≠ 0)
    (hN' : N' ≠ 0) (hadj : N.adjugate = 0) (hadj' : N'.adjugate = 0)
    (hS : ∀ X ∈ S, (Nᵀ * X).IsSymm ∧ (X * N').IsSymm) : CoveredBy S 6 := by
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_eq_vecMulVec_of_adjugate_eq_zero hN hadj
  obtain ⟨u', v', hu', hv', rfl⟩ := exists_eq_vecMulVec_of_adjugate_eq_zero hN' hadj'
  obtain ⟨A, hA, hA0, c₁, i₁, hAv'⟩ := exists_isUnit_row_zero_mulVec hu v'
  obtain ⟨B, hB, hB0, c₂, j₂, hBv⟩ := exists_isUnit_row_zero_mulVec hu' v
  refine CoveredBy.of_map_lrMul hA ((isUnit_transpose B).mpr hB)
    (coveredBy_of_support ![(0, j₂), (i₁, 0), (1, 1), (1, 2), (2, 1), (2, 2)] ?_)
  rintro _ ⟨X, hX, rfl⟩ i j hij
  obtain ⟨c, hc⟩ := exists_smul_of_isSymm_transpose_mul hv (hS X hX).1
  obtain ⟨d, hd⟩ := exists_smul_of_isSymm_mul hv' (hS X hX).2
  rw [lrMul_apply] at hij
  have hrow : (A * X * Bᵀ) 0 = (c * c₂) • Pi.single j₂ 1 := by
    rw [← single_zero_vecMul (A * X * Bᵀ), ← vecMul_vecMul, ← vecMul_vecMul, single_zero_vecMul,
      hA0, hc, smul_vecMul, vecMul_transpose, hBv, smul_smul]
  have hcol : (A * X * Bᵀ) *ᵥ Pi.single 0 1 = (d * c₁) • Pi.single i₁ 1 := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, single_zero_vecMul, hB0, hd,
      mulVec_smul, hAv', smul_smul]
  have hr : ∀ k, (A * X * Bᵀ) 0 k ≠ 0 → j₂ = k := by
    intro k hk
    by_contra hne
    apply hk
    rw [hrow, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hne), smul_zero]
  have hc0 : ∀ k, (A * X * Bᵀ) k 0 ≠ 0 → i₁ = k := by
    intro k hk
    by_contra hne
    apply hk
    have := congrFun hcol k
    rw [mulVec_single_one, col_apply] at this
    rw [this, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hne), smul_zero]
  fin_cases i <;> fin_cases j
  · exact ⟨0, by simp [hr _ hij]⟩
  · exact ⟨0, by simp [hr _ hij]⟩
  · exact ⟨0, by simp [hr _ hij]⟩
  · exact ⟨1, by simp [hc0 _ hij]⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨1, by simp [hc0 _ hij]⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩

/-- **D4, first piece.** If every `b` is the row vector of a rank-one element `a bᵀ` of `S`, then
either `S` contains four independent rank-one matrices, or it contains a whole "row space"
`{y wᵀ | w}`. -/
theorem fourRankOne_or_row (S : Submodule ℂ Mat)
    (h : ∀ b : Fin 3 → ℂ, ∃ a, a ≠ 0 ∧ vecMulVec a b ∈ S) :
    FourRankOne S ∨ ∃ y : Fin 3 → ℂ, y ≠ 0 ∧ ∀ w, vecMulVec y w ∈ S := by
  choose a ha haS using h
  let B : Fin 4 → Fin 3 → ℂ := ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, 1]
  by_cases hli : LinearIndependent ℂ fun l => vecMulVec (a (B l)) (B l)
  · exact Or.inl ⟨fun l => a (B l), B, fun l => haS _, hli⟩
  right
  obtain ⟨g, hg, l₀, hl₀⟩ := Fintype.not_linearIndependent_iff.mp hli
  have col : ∀ i k, (∑ l, g l • vecMulVec (a (B l)) (B l)) i k = 0 := fun i k => by
    rw [hg]
    rfl
  have c0 : ∀ i, g 0 * a (Pi.single 0 1) i + g 3 * a 1 i = 0 := fun i => by
    have := col i 0
    simp [Fin.sum_univ_four, B, vecMulVec_apply] at this
    linear_combination this
  have c1 : ∀ i, g 1 * a (Pi.single 1 1) i + g 3 * a 1 i = 0 := fun i => by
    have := col i 1
    simp [Fin.sum_univ_four, B, vecMulVec_apply] at this
    linear_combination this
  have c2 : ∀ i, g 2 * a (Pi.single 2 1) i + g 3 * a 1 i = 0 := fun i => by
    have := col i 2
    simp [Fin.sum_univ_four, B, vecMulVec_apply] at this
    linear_combination this
  have hvz : ∀ {x : Fin 3 → ℂ} {c : ℂ}, x ≠ 0 → (∀ i, c * x i = 0) → c = 0 := by
    intro x c hx hc
    obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hx (funext hn)
    exact (mul_eq_zero.mp (hc k)).resolve_right hk
  have hg3 : g 3 ≠ 0 := by
    intro h3
    have g0 : g 0 = 0 := hvz (ha _) fun i => by simpa [h3] using c0 i
    have g1 : g 1 = 0 := hvz (ha _) fun i => by simpa [h3] using c1 i
    have g2 : g 2 = 0 := hvz (ha _) fun i => by simpa [h3] using c2 i
    apply hl₀
    fin_cases l₀ <;> assumption
  have key : ∀ (x : Fin 3 → ℂ) (gx : ℂ) (w : Fin 3 → ℂ), (∀ i, gx * x i + g 3 * a 1 i = 0) →
      vecMulVec x w ∈ S → vecMulVec (a 1) w ∈ S := by
    intro x gx w hx hmem
    have e : vecMulVec (a 1) w = (-gx / g 3) • vecMulVec x w := by
      ext i j
      rw [vecMulVec_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, div_mul_eq_mul_div,
        eq_div_iff hg3]
      linear_combination (w j) * hx i
    rw [e]
    exact S.smul_mem _ hmem
  have h0 := key _ _ (Pi.single 0 1) c0 (haS _)
  have h1 := key _ _ (Pi.single 1 1) c1 (haS _)
  have h2 := key _ _ (Pi.single 2 1) c2 (haS _)
  refine ⟨a 1, ha 1, fun w => ?_⟩
  have e : vecMulVec (a 1) w = w 0 • vecMulVec (a 1) (Pi.single 0 1) +
      w 1 • vecMulVec (a 1) (Pi.single 1 1) + w 2 • vecMulVec (a 1) (Pi.single 2 1) := by
    ext i j
    fin_cases j <;> simp [vecMulVec_apply] <;> ring
  rw [e]
  exact S.add_mem (S.add_mem (S.smul_mem _ h0) (S.smul_mem _ h1)) (S.smul_mem _ h2)

/-- **D4, second piece.** A row space `{y wᵀ | w} ⊆ S`, together with a rank-one element `a bᵀ`
of `S` for every `a`, gives four independent rank-one matrices. -/
theorem fourRankOne_of_row_of_forall_left (S : Submodule ℂ Mat) (y : Fin 3 → ℂ) (hy : y ≠ 0)
    (hrow : ∀ w, vecMulVec y w ∈ S) (h : ∀ a : Fin 3 → ℂ, ∃ b, b ≠ 0 ∧ vecMulVec a b ∈ S) :
    FourRankOne S := by
  obtain ⟨a, ha⟩ : ∃ a : Fin 3 → ℂ, ∀ s : ℂ, a ≠ s • y := by
    by_cases hy12 : y 1 = 0 ∧ y 2 = 0
    · refine ⟨Pi.single 1 1, fun s hs => ?_⟩
      have := congrFun hs 1
      simp [hy12.1] at this
    · refine ⟨Pi.single 0 1, fun s hs => hy12 ?_⟩
      have e0 := congrFun hs 0
      have e1 := congrFun hs 1
      have e2 := congrFun hs 2
      rw [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same] at e0
      rw [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne (show (1 : Fin 3) ≠ 0 by decide)] at e1
      rw [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne (show (2 : Fin 3) ≠ 0 by decide)] at e2
      have hs0 : s ≠ 0 := by
        rintro rfl
        rw [zero_mul] at e0
        exact one_ne_zero e0
      exact ⟨(mul_eq_zero.mp e1.symm).resolve_left hs0, (mul_eq_zero.mp e2.symm).resolve_left hs0⟩
  obtain ⟨b, hb, habS⟩ := h a
  refine ⟨![y, y, y, a], ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, b], ?_, ?_⟩
  · intro l
    fin_cases l <;> simp [hrow, habS]
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsum : vecMulVec y ![g 0, g 1, g 2] + g 3 • vecMulVec a b = 0 := by
      rw [← hg, Fin.sum_univ_four]
      ext i j
      fin_cases j <;> simp [vecMulVec_apply] <;> ring
    have hg3 : g 3 = 0 := by
      by_contra h3
      obtain ⟨k, hk⟩ : ∃ k, b k ≠ 0 := by
        by_contra hn
        push Not at hn
        exact hb (funext hn)
      apply ha (-(![g 0, g 1, g 2] k) / (g 3 * b k))
      funext i
      have := congrFun (congrFun hsum i) k
      simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
        Matrix.zero_apply] at this
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff (mul_ne_zero h3 hk)]
      linear_combination this
    have hc : (![g 0, g 1, g 2] : Fin 3 → ℂ) = 0 := by
      by_contra hc
      rw [hg3, zero_smul, add_zero] at hsum
      exact vecMulVec_ne_zero hy hc hsum
    intro l
    fin_cases l
    · simpa using congrFun hc 0
    · simpa using congrFun hc 1
    · simpa using congrFun hc 2
    · exact hg3

namespace Degenerate

/-- The normalized situation of `fourRankOne_of_row_of_symm`: `S` contains the whole first row
`e₀ wᵀ` and the first column of every element of `S` is a multiple of `e₀`. -/
theorem fourRankOne_of_normalized (S : Submodule ℂ Mat) (hS5 : Module.finrank ℂ S = 5)
    (hrow : ∀ w, vecMulVec (Pi.single 0 1) w ∈ S) (hcol : ∀ X ∈ S, ∀ i, i ≠ 0 → X i 0 = 0) :
    FourRankOne S := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (row0.domRestrict S)
  have hle : Module.finrank ℂ (LinearMap.range (row0.domRestrict S)) ≤ 3 :=
    (Submodule.finrank_le _).trans (Module.finrank_fin_fun ℂ).le
  have hK : 1 < Module.finrank ℂ (LinearMap.ker (row0.domRestrict S)) := by omega
  obtain ⟨x, hx⟩ := (Module.finrank_pos_iff_exists_ne_zero
    (M := LinearMap.ker (row0.domRestrict S))).mp (zero_lt_one.trans hK)
  obtain ⟨y, hxy⟩ := exists_linearIndependent_pair_of_one_lt_finrank hK hx
  have hx0 : ((x : S) : Mat) 0 = 0 := LinearMap.mem_ker.mp x.2
  have hy0 : ((y : S) : Mat) 0 = 0 := LinearMap.mem_ker.mp y.2
  have ex : ∀ j, ((x : S) : Mat) 0 j = 0 := fun j => congrFun hx0 j
  have ey : ∀ j, ((y : S) : Mat) 0 j = 0 := fun j => congrFun hy0 j
  obtain ⟨s, t, hst, hdet⟩ := exists_singular_comb ((x : S) : Mat) ((y : S) : Mat)
  obtain ⟨Z, hZ⟩ : ∃ Z : Mat, Z = s • ((x : S) : Mat) + t • ((y : S) : Mat) := ⟨_, rfl⟩
  rw [← hZ] at hdet
  have hZS : Z ∈ S := hZ ▸ S.add_mem (S.smul_mem _ (x : S).2) (S.smul_mem _ (y : S).2)
  have hZ0 : Z 0 = 0 := by
    rw [hZ]
    funext j
    simp [ex, ey]
  have hZc : ∀ i, Z i 0 = 0 := by
    intro i
    by_cases hi : i = 0
    · rw [hi, hZ0]
      rfl
    · exact hcol Z hZS i hi
  have hZne : Z ≠ 0 := by
    intro h0
    have h' : s • x + t • y = 0 := by
      apply Subtype.ext
      apply Subtype.ext
      simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_zero]
      rw [← hZ]
      exact h0
    obtain ⟨hs, ht⟩ := LinearIndependent.pair_iff.mp hxy s t h'
    rcases hst with h | h <;> contradiction
  obtain ⟨a, b, -, -, hab⟩ := exists_eq_vecMulVec_of_adjugate_eq_zero hZne
    (adjugate_eq_zero_of_block hZ0 hZc hdet)
  refine ⟨![Pi.single 0 1, Pi.single 0 1, Pi.single 0 1, a],
    ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, b], ?_, ?_⟩
  · intro l
    fin_cases l
    · exact hrow _
    · exact hrow _
    · exact hrow _
    · show vecMulVec a b ∈ S
      rw [← hab]
      exact hZS
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have hZ0j : ∀ j, a 0 * b j = 0 := fun j => by
      have := congrFun hZ0 j
      rw [hab] at this
      exact this
    have e := fun j => congrFun (congrFun hg 0) j
    have g0 : g 0 = 0 := by simpa [Fin.sum_univ_four, vecMulVec_apply, hZ0j] using e 0
    have g1 : g 1 = 0 := by simpa [Fin.sum_univ_four, vecMulVec_apply, hZ0j] using e 1
    have g2 : g 2 = 0 := by simpa [Fin.sum_univ_four, vecMulVec_apply, hZ0j] using e 2
    have g3 : g 3 = 0 := by
      rw [Fin.sum_univ_four, g0, g1, g2] at hg
      have : g 3 • Z = 0 := by simpa [hab] using hg
      exact (smul_eq_zero.mp this).resolve_right hZne
    intro l
    fin_cases l <;> assumption

end Degenerate

/-- **D4, third piece.** A row space `{y wᵀ | w} ⊆ S` in a five-dimensional `S` satisfying
`(X * N').IsSymm` with `N'` of rank one gives four independent rank-one matrices. -/
theorem fourRankOne_of_row_of_symm (S : Submodule ℂ Mat) (hS5 : Module.finrank ℂ S = 5)
    (y : Fin 3 → ℂ) (hy : y ≠ 0) (hrow : ∀ w, vecMulVec y w ∈ S) (N' : Mat) (hN' : N' ≠ 0)
    (hadj' : N'.adjugate = 0) (hS : ∀ X ∈ S, (X * N').IsSymm) : FourRankOne S := by
  obtain ⟨u', v', hu', hv', rfl⟩ := exists_eq_vecMulVec_of_adjugate_eq_zero hN' hadj'
  obtain ⟨k, hk⟩ : ∃ k, u' k ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hu' (funext hn)
  obtain ⟨e, he⟩ : ∃ e : ℂ, v' = e • y := by
    have h := hS _ (hrow (Pi.single k 1))
    have hrk : Pi.single k 1 ᵥ* vecMulVec u' v' = u' k • v' := by
      rw [single_one_vecMul]
      funext j
      exact vecMulVec_apply u' v' k j
    rw [vecMulVec_mul, hrk] at h
    obtain ⟨c, hc⟩ := exists_smul_of_isSymm_vecMulVec hy h
    refine ⟨c / u' k, funext fun j => ?_⟩
    have := congrFun hc j
    simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [div_mul_eq_mul_div, eq_div_iff hk]
    linear_combination this
  obtain ⟨R₁, hR₁, hR₁0⟩ := exists_isUnit_row_zero hy
  obtain ⟨R₂, hR₂, hR₂0⟩ := exists_isUnit_row_zero hu'
  have hR₁t : IsUnit R₁ᵀ := (isUnit_transpose _).mpr hR₁
  have hP : IsUnit (R₁ᵀ)⁻¹ := isUnit_nonsing_inv_iff.mpr hR₁t
  have hQ : IsUnit R₂ᵀ := (isUnit_transpose _).mpr hR₂
  have hPy : (R₁ᵀ)⁻¹ *ᵥ y = Pi.single 0 1 := by
    have h1 : R₁ᵀ *ᵥ Pi.single 0 1 = y := by rw [mulVec_transpose, single_zero_vecMul, hR₁0]
    rw [← h1, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hR₁t), one_mulVec]
  have hQe : R₂ᵀ *ᵥ Pi.single 0 1 = u' := by rw [mulVec_transpose, single_zero_vecMul, hR₂0]
  refine FourRankOne.of_map_lrMul hP hQ (fourRankOne_of_normalized _ ?_ ?_ ?_)
  · rw [← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (lrMul_injective hP hQ) S)]
    exact hS5
  · intro w
    refine ⟨vecMulVec y (w ᵥ* (R₂ᵀ)⁻¹), hrow _, ?_⟩
    rw [lrMul_apply, mul_vecMulVec, vecMulVec_mul, hPy, vecMul_vecMul,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hQ), vecMul_one]
  · rintro _ ⟨X, hX, rfl⟩ i hi
    obtain ⟨d, hd⟩ := exists_smul_of_isSymm_mul hv' (hS X hX)
    have hcolX : lrMul (R₁ᵀ)⁻¹ R₂ᵀ X *ᵥ Pi.single 0 1 = (d * e) • Pi.single 0 1 := by
      rw [lrMul_apply, ← mulVec_mulVec, ← mulVec_mulVec, hQe, hd, he, smul_smul, mulVec_smul,
        hPy]
    have := congrFun hcolX i
    rw [mulVec_single_one, col_apply] at this
    rw [this, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero]

end TensorRank335

end

/- ## Section: `Upper` -/

section

/-
# The one-sided dichotomy for five-dimensional spaces

For a five-dimensional subspace `S` of `3 × 3` matrices we choose a basis `B` of its annihilator
and look at the linear system of column cubics of the hyperplanes of `ann S`
(`TensorRank335.mfam`). Exactly one of the following happens (`TensorRank335.sideInfo`):

* some hyperplane has a squarefree column cubic, and then `S` is covered by six rank-one
  matrices (Lemma R, `coveredBy_six_of_squarefree_colCubic`);
* all column cubics vanish, and then every `b` is the column vector of a rank-one matrix of `S`;
* all column cubics share a square linear factor, and then `(Nᵀ * X).IsSymm` for all `X ∈ S`,
  for some `N ≠ 0`.
-/

namespace TensorRank335

open Matrix MvPolynomial Module

/- ### The annihilator -/

theorem mem_of_forall_ann (S : Submodule ℂ Mat) (X : Mat) (h : ∀ B ∈ ann S, dotM X B = 0) :
    X ∈ S := by
  by_contra hX
  obtain ⟨φ, hφX, hφS⟩ := Submodule.exists_le_ker_of_notMem hX
  obtain ⟨A, hA⟩ := exists_dotM_eq φ
  have hAS : A ∈ ann S := fun Y hY => by
    rw [← hA]
    exact hφS hY
  exact hφX (by rw [hA]; exact h A hAS)

theorem finrank_mat : finrank ℂ Mat = 9 := by
  simp [Module.finrank_matrix]

/-- Restriction of `dotM · B` to `S`. -/
noncomputable def annRestrict (S : Submodule ℂ Mat) : Mat →ₗ[ℂ] Module.Dual ℂ S where
  toFun B := (dotMLeft B).domRestrict S
  map_add' B C := by ext X; simp [dotM_add_right]
  map_smul' c B := by ext X; simp [dotM_smul_right]

theorem finrank_ann (S : Submodule ℂ Mat) : finrank ℂ (ann S) + finrank ℂ S = 9 := by
  have hker : LinearMap.ker (annRestrict S) = ann S := by
    ext B
    simp only [LinearMap.mem_ker, mem_ann]
    constructor
    · intro h X hX
      have := congrArg (fun φ => φ ⟨X, hX⟩) h
      simpa [annRestrict] using this
    · intro h
      ext ⟨X, hX⟩
      simpa [annRestrict] using h X hX
  have hsurj : LinearMap.range (annRestrict S) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro ψ
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ψ
    obtain ⟨A, hA⟩ := exists_dotM_eq g
    refine ⟨A, ?_⟩
    ext ⟨X, hX⟩
    have := congrArg (fun φ => φ ⟨X, hX⟩) hg
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    simp [annRestrict, ← this, hA]
  have := LinearMap.finrank_range_add_finrank_ker (annRestrict S)
  rw [hsurj, hker, finrank_top, Subspace.dual_finrank_eq, finrank_mat] at this
  omega

/- ### Symmetry from cross matrices -/

theorem dotM_mul_left (N X C : Mat) : dotM X (N * C) = dotM (Nᵀ * X) C := by
  have := dotM_mul_mul Nᵀ 1 X C
  simp only [mul_one, transpose_transpose, transpose_one] at this
  exact this.symm

theorem isSymm_of_forall_dotM_crossMat {Y : Mat} (h : ∀ b, dotM Y (crossMat b) = 0) :
    Y.IsSymm := by
  have h0 := h (Pi.single 0 1)
  have h1 := h (Pi.single 1 1)
  have h2 := h (Pi.single 2 1)
  simp [dotM, crossMat, Fin.sum_univ_three] at h0 h1 h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transpose_apply] <;>
    first | linear_combination h0 | linear_combination -h0 | linear_combination h1 |
      linear_combination -h1 | linear_combination h2 | linear_combination -h2

theorem isSymm_of_crossMat_mem_ann {S : Submodule ℂ Mat} {N : Mat}
    (h : ∀ b, N * crossMat b ∈ ann S) : ∀ X ∈ S, (Nᵀ * X).IsSymm := by
  intro X hX
  refine isSymm_of_forall_dotM_crossMat fun b => ?_
  rw [← dotM_mul_left]
  exact h b X hX

/- ### The one-sided dichotomy -/

theorem sideInfo (S : Submodule ℂ Mat) (hS : finrank ℂ S = 5) :
    CoveredBy S 6 ∨ (∀ b : Fin 3 → ℂ, ∃ a, a ≠ 0 ∧ vecMulVec a b ∈ S) ∨
      ∃ N : Mat, N ≠ 0 ∧ ∀ X ∈ S, (Nᵀ * X).IsSymm := by
  have h4 : finrank ℂ (ann S) = 4 := by have := finrank_ann S; omega
  let bas := Module.finBasisOfFinrankEq ℂ (ann S) h4
  set B : Fin 4 → Mat := fun k => (bas k : Mat) with hBdef
  have hBmem : ∀ k, B k ∈ ann S := fun k => (bas k).2
  have hBli : LinearIndependent ℂ B :=
    bas.linearIndependent.map' (ann S).subtype (Submodule.ker_subtype _)
  have hBspan : ann S ≤ Submodule.span ℂ (Set.range B) := by
    intro B' hB'
    have hrepr := bas.sum_repr ⟨B', hB'⟩
    have : B' = ∑ k, bas.repr ⟨B', hB'⟩ k • B k := by
      have h := congrArg Subtype.val hrepr
      rw [Submodule.coe_sum] at h
      simp only [Submodule.coe_smul] at h
      exact h.symm
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  by_cases hsq : ∃ c : Fin 3 → ℂ,
      Squarefree (mfam B 3 + ∑ k : Fin 3, C (c k) * mfam B k.castSucc)
  · obtain ⟨c, hc⟩ := hsq
    left
    refine coveredBy_six_of_squarefree_colCubic S (fun j => B j.castSucc + c j • B 3)
      (fun j => (ann S).add_mem (hBmem _) ((ann S).smul_mem _ (hBmem 3))) ?_
    rw [colCubic_hyperplane]
    exact hc
  push Not at hsq
  obtain ⟨p, hp, hpdvd⟩ := exists_sq_dvd_of_family (mfam B) (isHomogeneous_mfam B) hsq
  by_cases hz : ∀ k, mfam B k = 0
  · right; left
    intro b
    obtain ⟨a, ha, hab⟩ := exists_left_kernel_of_mfam_eq_zero B hz b
    refine ⟨a, ha, mem_of_forall_ann S _ fun B' hB' => ?_⟩
    have hle : Submodule.span ℂ (Set.range B) ≤ LinearMap.ker (dotMLeft (vecMulVec a b)) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, dotMLeft_apply]
      rw [dotM_comm, dotM_vecMulVec]
      exact hab k
    have := hle (hBspan hB')
    simp only [LinearMap.mem_ker, dotMLeft_apply] at this
    rw [dotM_comm]
    exact this
  · right; right
    push Not at hz
    obtain ⟨N, hN0, hNmem⟩ := exists_crossMat_of_sq_dvd B hBli p hp hpdvd hz
    refine ⟨N, hN0, isSymm_of_crossMat_mem_ann fun b => ?_⟩
    have hle : Submodule.span ℂ (Set.range B) ≤ ann S := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hBmem k
    exact hle (hNmem b)

/- ### Transposes and dimension -/

/-- The transpose of a subspace. -/
noncomputable def trS (S : Submodule ℂ Mat) : Submodule ℂ Mat :=
  S.map (Matrix.transposeLinearEquiv (Fin 3) (Fin 3) ℂ ℂ).toLinearMap

theorem mem_trS {S : Submodule ℂ Mat} {X : Mat} : X ∈ trS S ↔ Xᵀ ∈ S := by
  constructor
  · rintro ⟨Y, hY, rfl⟩
    simpa using hY
  · intro h
    exact ⟨Xᵀ, h, by simp⟩

theorem finrank_trS (S : Submodule ℂ Mat) : finrank ℂ (trS S) = finrank ℂ S :=
  LinearEquiv.finrank_map_eq _ S

theorem CoveredBy.of_trS {S : Submodule ℂ Mat} {r : ℕ} (h : CoveredBy (trS S) r) :
    CoveredBy S r :=
  CoveredBy.of_map_transpose h

theorem vecMulVec_mem_trS {S : Submodule ℂ Mat} {a b : Fin 3 → ℂ} :
    vecMulVec a b ∈ trS S ↔ vecMulVec b a ∈ S := by
  rw [mem_trS, transpose_vecMulVec]

theorem isSymm_mul_iff_trS {S : Submodule ℂ Mat} {N : Mat} :
    (∀ Y ∈ trS S, (Nᵀ * Y).IsSymm) ↔ ∀ X ∈ S, (X * N).IsSymm := by
  constructor
  · intro h X hX
    have := h Xᵀ (by rw [mem_trS, transpose_transpose]; exact hX)
    have h2 : (X * N) = (Nᵀ * Xᵀ)ᵀ := by simp [transpose_mul]
    rw [h2]
    exact this.transpose
  · intro h Y hY
    have := h Yᵀ (mem_trS.mp hY)
    have h2 : Nᵀ * Y = (Yᵀ * N)ᵀ := by simp [transpose_mul]
    rw [h2]
    exact this.transpose

theorem isSymm_mul_iff_trS' {S : Submodule ℂ Mat} {N : Mat} :
    (∀ Y ∈ trS S, (Y * N).IsSymm) ↔ ∀ X ∈ S, (Nᵀ * X).IsSymm := by
  constructor
  · intro h X hX
    have := h Xᵀ (by rw [mem_trS, transpose_transpose]; exact hX)
    have h2 : Nᵀ * X = (Xᵀ * N)ᵀ := by simp [transpose_mul]
    rw [h2]
    exact this.transpose
  · intro h Y hY
    have := h Yᵀ (mem_trS.mp hY)
    have h2 : Y * N = (Nᵀ * Yᵀ)ᵀ := by simp [transpose_mul]
    rw [h2]
    exact this.transpose

theorem exists_le_finrank_eq_add (S : Submodule ℂ Mat) (d : ℕ) (hd : finrank ℂ S + d ≤ 9) :
    ∃ S' : Submodule ℂ Mat, S ≤ S' ∧ finrank ℂ S' = finrank ℂ S + d := by
  induction d generalizing S with
  | zero => exact ⟨S, le_rfl, rfl⟩
  | succ d ih =>
    have hne : ∃ X, X ∉ S := by
      by_contra h
      push Not at h
      have htop : S = ⊤ := eq_top_iff.mpr fun X _ => h X
      rw [htop, finrank_top, finrank_mat] at hd
      omega
    obtain ⟨X, hX⟩ := hne
    have hX0 : X ≠ 0 := fun h => hX (h ▸ S.zero_mem)
    have hdisj : S ⊓ Submodule.span ℂ {X} = ⊥ :=
      disjoint_iff.mp ((Submodule.disjoint_span_singleton' hX0).mpr hX)
    have h1 : finrank ℂ ↥(S ⊔ Submodule.span ℂ {X}) = finrank ℂ S + 1 := by
      have := Submodule.finrank_sup_add_finrank_inf_eq S (Submodule.span ℂ {X})
      rw [hdisj, finrank_bot, finrank_span_singleton hX0] at this
      omega
    obtain ⟨S', hS', hdim⟩ := ih (S ⊔ Submodule.span ℂ {X}) (by omega)
    exact ⟨S', le_sup_left.trans hS', by omega⟩

theorem exists_le_finrank_eq_five (S : Submodule ℂ Mat) (hS : finrank ℂ S ≤ 5) :
    ∃ S' : Submodule ℂ Mat, S ≤ S' ∧ finrank ℂ S' = 5 := by
  obtain ⟨S', h1, h2⟩ := exists_le_finrank_eq_add S (5 - finrank ℂ S) (by omega)
  exact ⟨S', h1, by omega⟩

end TensorRank335

end

/- ## Section: `Main` -/

section

/-
# The maximal rank of complex `3 × 3 × 5` tensors is six

Every subspace `S` of `3 × 3` complex matrices of dimension at most five lies in the span of six
rank-one matrices (`TensorRank335.coveredBy_six_of_finrank_le_five`). With the bridge
`cprank_le_iff` this gives `T.cprank ≤ 6` for every `T : Holor ℂ [3, 3, 5]`, and the explicit
tensor `T₀` of rank six
(`cprank_T₀`) shows that the bound is attained:

* `TensorRank335.isMaxRank_three_three_five_eq_six : IsMaxRank [3, 3, 5] 6`,
* `Arxiv.«0805.3777».isMaxRank_three_three_five_solution`, the Formal Conjectures statement
  `Arxiv.«0805.3777».isMaxRank_three_three_five` with the answer `6` filled in.

## Structure of the upper bound

For a five-dimensional `S`, `sideInfo` (applied to `S` and to its transpose) either finishes by
Lemma R or leaves one of two degenerate situations on each side: every vector is the column
(resp. row) vector of a rank-one element of `S`, or `S ⊆ {X | (Nᵀ X).IsSymm}` (resp.
`{X | (X N).IsSymm}`) for some `N ≠ 0`. `degenerate_combine` settles every combination, using the
normal forms of `Degenerate.lean` and the four-rank-one criterion of `Nilpotent3.lean`.
-/

namespace TensorRank335

open Matrix Module

theorem coveredBy_six_of_fourRankOne {S : Submodule ℂ Mat} (hS : finrank ℂ S ≤ 5)
    (h : FourRankOne S) : CoveredBy S 6 := by
  obtain ⟨a, b, hmem, hli⟩ := h
  exact coveredBy_six_of_four_rankOne S hS a b hmem hli

theorem degenerate_combine (S : Submodule ℂ Mat) (hS : finrank ℂ S = 5)
    (hb : (∀ b : Fin 3 → ℂ, ∃ a, a ≠ 0 ∧ vecMulVec a b ∈ S) ∨
      ∃ N : Mat, N ≠ 0 ∧ ∀ X ∈ S, (Nᵀ * X).IsSymm)
    (ha : (∀ b : Fin 3 → ℂ, ∃ a, a ≠ 0 ∧ vecMulVec a b ∈ trS S) ∨
      ∃ N : Mat, N ≠ 0 ∧ ∀ Y ∈ trS S, (Nᵀ * Y).IsSymm) :
    CoveredBy S 6 := by
  have hT : finrank ℂ (trS S) = 5 := by rw [finrank_trS]; exact hS
  have hleft : (∀ b : Fin 3 → ℂ, ∃ a, a ≠ 0 ∧ vecMulVec a b ∈ trS S) →
      ∀ a : Fin 3 → ℂ, ∃ b, b ≠ 0 ∧ vecMulVec a b ∈ S := by
    intro h a
    obtain ⟨b, hb, hmem⟩ := h a
    exact ⟨b, hb, vecMulVec_mem_trS.mp hmem⟩
  rcases hb with hZb | ⟨N, hN0, hN⟩
  · rcases fourRankOne_or_row S hZb with hF | ⟨y, hy, hrow⟩
    · exact coveredBy_six_of_fourRankOne hS.le hF
    rcases ha with hZa | ⟨N', hN'0, hN'⟩
    · exact coveredBy_six_of_fourRankOne hS.le
        (fourRankOne_of_row_of_forall_left S y hy hrow (hleft hZa))
    by_cases hdet' : N'.det ≠ 0
    · exact (coveredBy_six_of_symm_of_det_ne_zero (trS S) N' hdet' hN').of_trS
    push Not at hdet'
    by_cases hadj' : N'.adjugate ≠ 0
    · exact (coveredBy_six_of_symm_of_rank_two (trS S) N' hdet' hadj' hN').of_trS
    push Not at hadj'
    exact coveredBy_six_of_fourRankOne hS.le
      (fourRankOne_of_row_of_symm S hS y hy hrow N' hN'0 hadj' (isSymm_mul_iff_trS.mp hN'))
  · by_cases hdet : N.det ≠ 0
    · exact coveredBy_six_of_symm_of_det_ne_zero S N hdet hN
    push Not at hdet
    by_cases hadj : N.adjugate ≠ 0
    · exact coveredBy_six_of_symm_of_rank_two S N hdet hadj hN
    push Not at hadj
    rcases ha with hZa | ⟨N', hN'0, hN'⟩
    · rcases fourRankOne_or_row (trS S) hZa with hF | ⟨y', hy', hrow'⟩
      · exact (coveredBy_six_of_fourRankOne hT.le hF).of_trS
      exact (coveredBy_six_of_fourRankOne hT.le (fourRankOne_of_row_of_symm (trS S) hT y' hy'
        hrow' N hN0 hadj (isSymm_mul_iff_trS'.mpr hN))).of_trS
    by_cases hdet' : N'.det ≠ 0
    · exact (coveredBy_six_of_symm_of_det_ne_zero (trS S) N' hdet' hN').of_trS
    push Not at hdet'
    by_cases hadj' : N'.adjugate ≠ 0
    · exact (coveredBy_six_of_symm_of_rank_two (trS S) N' hdet' hadj' hN').of_trS
    push Not at hadj'
    exact coveredBy_six_of_symm_symm_rank_one S N N' hN0 hN'0 hadj hadj'
      fun X hX => ⟨hN X hX, isSymm_mul_iff_trS.mp hN' X hX⟩

theorem coveredBy_six_of_finrank_eq_five (S : Submodule ℂ Mat) (hS : finrank ℂ S = 5) :
    CoveredBy S 6 := by
  rcases sideInfo S hS with h | hb
  · exact h
  rcases sideInfo (trS S) (by rw [finrank_trS]; exact hS) with h' | ha
  · exact h'.of_trS
  exact degenerate_combine S hS hb ha

/-- **Universal bound.** A subspace of `3 × 3` matrices of dimension at most five lies in the span
of six rank-one matrices. -/
theorem coveredBy_six_of_finrank_le_five (S : Submodule ℂ Mat) (hS : finrank ℂ S ≤ 5) :
    CoveredBy S 6 := by
  obtain ⟨S', hle, h5⟩ := exists_le_finrank_eq_five S hS
  exact (coveredBy_six_of_finrank_eq_five S' h5).mono hle

/-- Every complex `3 × 3 × 5` tensor has rank at most six. -/
theorem cprank_le_six (T : Holor ℂ [3, 3, 5]) : T.cprank ≤ 6 :=
  cprank_le_of_forall_coveredBy coveredBy_six_of_finrank_le_five T

/-- **The maximal rank of a complex `3 × 3 × 5` tensor is six.** -/
theorem isMaxRank_three_three_five_eq_six : Arxiv.«0805.3777».IsMaxRank [3, 3, 5] 6 :=
  ⟨⟨T₀, cprank_T₀⟩, by rintro _ ⟨T, rfl⟩; exact cprank_le_six T⟩

end TensorRank335

end

/- ## Section: `Formal Conjectures target` -/

/-- Exact Formal Conjectures target `Arxiv.«0805.3777».isMaxRank_three_three_five`, with the
answer `6`. -/
theorem TensorRank335.isMaxRank_three_three_five_solved :
    Arxiv.«0805.3777».IsMaxRank [3, 3, 5] answer(6) :=
  TensorRank335.isMaxRank_three_three_five_eq_six

/-- The Formal Conjectures theorem `Arxiv.«0805.3777».isMaxRank_three_three_five_bounds`. -/
theorem TensorRank335.isMaxRank_three_three_five_bounds_solved {R : ℕ}
    (hR : Arxiv.«0805.3777».IsMaxRank [3, 3, 5] R) : 6 ≤ R ∧ R ≤ 7 := by
  have := hR.unique TensorRank335.isMaxRank_three_three_five_eq_six
  omega

#print axioms TensorRank335.isMaxRank_three_three_five_solved
#print axioms TensorRank335.isMaxRank_three_three_five_bounds_solved
