import zkLean
import zkLean.Formalism
import zkLeanExamples.Sha3.Circuit
import zkLeanExamples.Sha3.Circuit.State
import zkLeanExamples.Sha3.Proof.Iota
import zkLeanExamples.Sha3.Proof.Shift
import zkLeanExamples.Sha3.Proof.Xor
import zkLeanExamples.Sha3.Spec

open Std Do

/-!
# Vector.ofFnM Hoare Triple Specification

This section provides a Hoare triple specification for `Vector.ofFnM` that allows
reasoning about monadic vector construction in a compositional way.

The key insight is that `Vector.ofFnM f` can be decomposed using `ofFnM_succ'`:
- First compute `f 0` to get the first element
- Then recursively compute the rest with indices shifted by 1
- Combine the results

We provide a spec that says: if for each index i, running `f i` in a state where
a precondition `P` holds produces a result satisfying `Q i`, and these operations
compose correctly, then `Vector.ofFnM f` produces a vector where each element
satisfies its corresponding property.
-/

-- Helper: getElem for cast-append-singleton pattern
@[simp]
theorem vector_cast_append_getElem_zero {α : Type} (a : α) (v : Vector α k) :
    (Vector.cast (Nat.add_comm 1 k) (#v[a] ++ v))[(0 : Fin (k + 1))] = a := by
  have h1 : (Vector.cast (Nat.add_comm 1 k) (#v[a] ++ v))[(0 : Fin (k + 1))] =
            (#v[a] ++ v)[(0 : Nat)] := Vector.getElem_cast (by omega)
  have h2 : (#v[a] ++ v)[(0 : Nat)] = #v[a][(0 : Nat)] := Vector.getElem_append_left (by omega)
  have h3 : #v[a][(0 : Nat)] = a := Vector.getElem_singleton (by omega)
  rw [h1, h2, h3]

@[simp]
theorem vector_cast_append_getElem_succ {α : Type} (a : α) (v : Vector α k) (i : Fin k) :
    (Vector.cast (Nat.add_comm 1 k) (#v[a] ++ v))[(i.succ : Fin (k + 1))] = v[i] := by
  have h1 : (Vector.cast (Nat.add_comm 1 k) (#v[a] ++ v))[(i.succ : Fin (k + 1))] =
            (#v[a] ++ v)[(i.val + 1 : Nat)] := Vector.getElem_cast (by omega)
  have h2 : (#v[a] ++ v)[(i.val + 1 : Nat)] = v[(i.val : Nat)] := by
    rw [Vector.getElem_append_right (by omega) (by omega)]
    simp only [Nat.add_sub_cancel]
  -- v[↑i] = v[i] by Fin.getElem_fin (which is rfl)
  rw [h1, h2, Fin.getElem_fin]

namespace Std.Do
@[spec]
theorem Spec.Vector_ofFnM {n : Nat} {α : Type}
  (inv : Prop)
  (f : Fin n → ZKBuilder f α)
  (postStep : Fin n → α → Prop)
  (hStep : ∀ (i : Fin n),
    ⦃ λ _e => ⌜inv⌝ ⦄
    f i
    ⦃ ⇓? s _e => ⌜postStep i s ∧ inv⌝ ⦄
  ) :
    ⦃ λ _e => ⌜inv⌝ ⦄
    Vector.ofFnM fun (x : Fin n) => f x
    ⦃ ⇓? v _e => ⌜inv ∧ ∀ (i : Fin n), postStep i v[i]⌝ ⦄
  := by
    induction n with
    | zero =>
      -- Base case: Vector.ofFnM f = pure #v[]
      simp only [Vector.ofFnM_zero]
      -- Use Triple.pure: need to show precond entails postcond applied to #v[]
      apply Triple.pure
      -- Goal: ⌜inv⌝ ⊢ₛ ⌜inv ∧ ∀ i : Fin 0, postStep i #v[][i]⌝
      apply SPred.pure_elim' (fun h_inv => ?_)
      apply SPred.pure_intro
      exact ⟨h_inv, fun i => i.elim0⟩
    | succ k ih =>
      -- Inductive case: use ofFnM_succ'
      rw [Vector.ofFnM_succ']
      mintro h_inv ∀e
      mpure h_inv
      -- First: run f 0
      mspec (hStep 0)
      mrename_i h0
      mpure h0
      -- Second: run recursive ofFnM
      have ih_inst := ih (f := fun i => f i.succ) (postStep := fun i => postStep i.succ)
        (fun i => hStep i.succ)
      mspec ih_inst
      mrename_i h_rest
      mpure h_rest
      -- Final: pure step to construct result
      mintro ∀e'
      mpure_intro
      obtain ⟨h_inv', h_all⟩ := h_rest
      obtain ⟨h_post0, _⟩ := h0
      constructor
      · exact h_inv'
      · intro i
        -- The result vector is ((#v[first_elem] ++ rest_vec).cast ...)
        -- For i=0, the element is first_elem which satisfies h_post0
        -- For i>0, the element is rest_vec[i-1] which satisfies h_all
        cases i using Fin.cases with
        | zero =>
          -- Use helper lemma for zero case
          simp only [vector_cast_append_getElem_zero]
          exact h_post0
        | succ i' =>
          -- Use helper lemma for succ case
          simp only [vector_cast_append_getElem_succ]
          exact h_all i'
end Std.Do

/-!
# Theta Soundness Proof

The theta step of Keccak involves three Vector.ofFnM operations:
1. Compute column parity: c[x] = s[x,0] ⊕ s[x,1] ⊕ s[x,2] ⊕ s[x,3] ⊕ s[x,4]
2. Compute d values: d[x] = c[x-1] ⊕ rotl(c[x+1], 1)
3. Apply to state: s'[x,y] = s[x,y] ⊕ d[x]
-/

-- Helper: converting between lane access styles
theorem state_get_lane_eq (s : State) (s_bv : SHA3.State) (x y : Fin 5)
    (h : eqState s s_bv) : eqF (s.get x y) s_bv.lanes[y.val * 5 + x.val] := by
  have := eqState_implies_lane_eq s s_bv ⟨y.val * 5 + x.val, by omega⟩ h
  unfold State.get
  simp at this ⊢
  exact this

-- Step lemmas for Spec.Vector_ofFnM: with inv=True and postStep ∧ inv postcondition

-- Step lemma for c computation
-- Takes h_eq as explicit parameter since it's a pure fact from outer scope
theorem c_step_soundness (s : State) (s_bv : SHA3.State) (x : Fin 5)
    (h_eq : eqState s s_bv)
    (cBV_fn : Fin 5 → BitVec 64)
    (hcBV : ∀ x, cBV_fn x = s_bv.get x 0 ^^^ s_bv.get x 1 ^^^ s_bv.get x 2 ^^^ s_bv.get x 3 ^^^ s_bv.get x 4) :
  ⦃ λ _e => ⌜True⌝ ⦄
  (do xor64 (← xor64 (← xor64 (← xor64 (s.get x 0) (s.get x 1)) (s.get x 2)) (s.get x 3)) (s.get x 4))
  ⦃ ⇓? o _e => ⌜eqF o (cBV_fn x) ∧ True⌝ ⦄ := by
  mintro _ ∀e'
  -- xor64 (s.get x 0) (s.get x 1)
  mspec (xor64.soundness (bv1 := s_bv.get x 0) (bv2 := s_bv.get x 1) _ _)
  · simp; exact ⟨state_get_lane_eq s s_bv x 0 h_eq, state_get_lane_eq s s_bv x 1 h_eq⟩
  mrename_i h1; mpure h1
  -- xor64 _ (s.get x 2)
  mspec (xor64.soundness (bv1 := s_bv.get x 0 ^^^ s_bv.get x 1) (bv2 := s_bv.get x 2) _ _)
  · simp; exact ⟨h1, state_get_lane_eq s s_bv x 2 h_eq⟩
  mrename_i h2; mpure h2
  -- xor64 _ (s.get x 3)
  mspec (xor64.soundness (bv1 := s_bv.get x 0 ^^^ s_bv.get x 1 ^^^ s_bv.get x 2) (bv2 := s_bv.get x 3) _ _)
  · simp; exact ⟨h2, state_get_lane_eq s s_bv x 3 h_eq⟩
  mrename_i h3; mpure h3
  -- xor64 _ (s.get x 4)
  mspec (xor64.soundness (bv1 := s_bv.get x 0 ^^^ s_bv.get x 1 ^^^ s_bv.get x 2 ^^^ s_bv.get x 3) (bv2 := s_bv.get x 4) _ _)
  · simp; exact ⟨h3, state_get_lane_eq s s_bv x 4 h_eq⟩
  mrename_i h4; mpure h4
  -- Final step: produce postStep ∧ inv
  mintro ∀e''
  mpure_intro
  rw [hcBV]
  exact ⟨h4, trivial⟩

-- Step lemma for d computation
theorem d_step_soundness (cF : Vector (ZKExpr f) 5) (cBV : Vector (BitVec 64) 5) (x : Fin 5)
    (h_c : ∀ i : Fin 5, eqF (cF.get i) (cBV.get i))
    (dBV_fn : Fin 5 → BitVec 64)
    (hdBV : ∀ x, dBV_fn x = cBV[(x.val + 4) % 5] ^^^ (cBV[(x.val + 1) % 5]).rotateLeft 1) :
  ⦃ λ _e => ⌜True⌝ ⦄
  (do xor64 (cF.get ⟨(x.val + 4) % 5, by omega⟩) (← rotateLeft64 (cF.get ⟨(x.val + 1) % 5, by omega⟩) 1))
  ⦃ ⇓? o _e => ⌜eqF o (dBV_fn x) ∧ True⌝ ⦄ := by
  have h1_lt : (x.val + 1) % 5 < 5 := Nat.mod_lt _ (by omega)
  have h4_lt : (x.val + 4) % 5 < 5 := Nat.mod_lt _ (by omega)
  mintro _ ∀e'
  -- First step: rotateLeft64
  have hc1 : eqF (cF.get ⟨(x.val + 1) % 5, h1_lt⟩) (cBV.get ⟨(x.val + 1) % 5, h1_lt⟩) :=
    h_c ⟨(x.val + 1) % 5, h1_lt⟩
  have hc4 : eqF (cF.get ⟨(x.val + 4) % 5, h4_lt⟩) (cBV.get ⟨(x.val + 4) % 5, h4_lt⟩) :=
    h_c ⟨(x.val + 4) % 5, h4_lt⟩
  mspec (rotateLeft64.soundness (bv1 := cBV.get ⟨(x.val + 1) % 5, h1_lt⟩) (bv2 := 1) _ _)
  · simp; exact ⟨hc1, rfl⟩
  mrename_i h_rot; mpure h_rot
  -- Second step: xor64
  mspec (xor64.soundness (bv1 := cBV.get ⟨(x.val + 4) % 5, h4_lt⟩) (bv2 := (cBV.get ⟨(x.val + 1) % 5, h1_lt⟩).rotateLeft 1) _ _)
  · simp; exact ⟨hc4, h_rot⟩
  mrename_i hdx; mpure hdx
  -- Final step
  mintro ∀e''
  mpure_intro
  constructor
  · simp only [hdBV]
    exact hdx
  · trivial

-- Step lemma for lanes computation
theorem lanes_step_soundness (s : State) (s_bv : SHA3.State)
    (dF : Vector (ZKExpr f) 5) (dBV : Vector (BitVec 64) 5)
    (i : Fin 25) (h_s : eqState s s_bv) (h_d : ∀ j : Fin 5, eqF (dF.get j) (dBV.get j))
    (laneBV_fn : Fin 25 → BitVec 64)
    (hlaneBV : ∀ i, laneBV_fn i = s_bv.get ⟨i.val % 5, by omega⟩ ⟨i.val / 5, by omega⟩ ^^^ dBV[i.val % 5]) :
  ⦃ λ _e => ⌜True⌝ ⦄
  (let x := i.val % 5
   let y := i.val / 5
   xor64 (s.get ⟨x, by omega⟩ ⟨y, by omega⟩) dF[x])
  ⦃ ⇓? o _e => ⌜eqF o (laneBV_fn i) ∧ True⌝ ⦄ := by
  have hx_lt : i.val % 5 < 5 := Nat.mod_lt _ (by omega)
  have hy_lt : i.val / 5 < 5 := Nat.div_lt_of_lt_mul (by omega)
  mintro _ ∀e'
  -- Single step: xor64
  have hs_lane : eqF (s.get ⟨i.val % 5, hx_lt⟩ ⟨i.val / 5, hy_lt⟩) s_bv.lanes[i] := by
    have := state_get_lane_eq s s_bv ⟨i.val % 5, hx_lt⟩ ⟨i.val / 5, hy_lt⟩ h_s
    simp only [eqF] at this ⊢
    have idx_eq : (i.val / 5) * 5 + i.val % 5 = i.val := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod i.val 5
    simp only [idx_eq] at this
    exact this
  have hd_elem : eqF dF[i.val % 5] (dBV.get ⟨i.val % 5, hx_lt⟩) := by
    have := h_d ⟨i.val % 5, hx_lt⟩
    simp only [Vector.get_eq_getElem] at this
    simp only [eqF] at this ⊢
    exact this
  mspec (xor64.soundness (bv1 := s_bv.lanes[i]) (bv2 := dBV.get ⟨i.val % 5, hx_lt⟩) _ _)
  · simp; exact ⟨hs_lane, hd_elem⟩
  mrename_i hli; mpure hli
  mintro ∀e''
  mpure_intro
  constructor
  · -- eqF li (laneBV_fn i)
    simp only [hlaneBV, Vector.get_eq_getElem] at hli ⊢
    simp only [eqF] at hli ⊢
    have lanes_eq : s_bv.lanes[i] = s_bv.get ⟨i.val % 5, hx_lt⟩ ⟨i.val / 5, hy_lt⟩ := by
      simp only [SHA3.State.get]
      have idx_eq : (i.val / 5) * 5 + i.val % 5 = i.val := by
        rw [Nat.mul_comm]; exact Nat.div_add_mod i.val 5
      simp only [idx_eq, Fin.getElem_fin]
    rw [lanes_eq] at hli
    exact hli
  · trivial

-- Helper: Build eqState from element-wise eqF
theorem eqState_of_lanes_eq (lanes : Vector (ZKExpr f) 25) (lanes_bv : Vector (BitVec 64) 25)
    (h : ∀ i : Fin 25, eqF lanes[i] lanes_bv[i]) :
    eqState { lanes := lanes } { lanes := lanes_bv } := by
  unfold eqState
  simp only [Vector.all_iff_forall]
  intro i hi
  simp only [Vector.getElem_zip, eqF]
  exact h ⟨i, hi⟩

-- Main theta soundness theorem
-- Note: The theta circuit uses Vector.ofFnM which is a recursive combinator.
-- The proof requires integrating the Spec.Vector_ofFnM theorem with the mspec
-- tactic framework.
--
-- The proof structure is:
-- 1. Apply Spec.Vector_ofFnM for the c vector computation
-- 2. Apply Spec.Vector_ofFnM for the d vector computation
-- 3. Apply Spec.Vector_ofFnM for the lanes vector computation
-- 4. Combine the results to show eqState holds for the final state
--
-- The helper lemmas prove the soundness of individual element computations. The Spec.Vector_ofFnM theorem lifts these to the full vector computations.
def theta.soundness (s0 : State) :
  ⦃ λ _e => ⌜eqState s0 s0_bv⌝ ⦄
  theta s0
  ⦃ ⇓? s1 _e => ⌜eqState s1 (SHA3.theta s0_bv)⌝ ⦄
  := by
  mintro h_eq ∀e
  unfold theta SHA3.theta
  mpure h_eq

  -- Step 1: Compute c vector
  -- Define spec values for c
  let cBV_fn : Fin 5 → BitVec 64 := fun x =>
    s0_bv.get x 0 ^^^ s0_bv.get x 1 ^^^ s0_bv.get x 2 ^^^ s0_bv.get x 3 ^^^ s0_bv.get x 4
  let cBV : Vector (BitVec 64) 5 := Vector.ofFn cBV_fn

  -- Apply Spec.Vector_ofFnM for c using c_step_soundness
  mspec (Spec.Vector_ofFnM
    (inv := True)
    (f := fun x => do xor64 (← xor64 (← xor64 (← xor64 (s0.get x 0) (s0.get x 1)) (s0.get x 2)) (s0.get x 3)) (s0.get x 4))
    (postStep := fun x cx => eqF cx (cBV_fn x))
    (fun x => c_step_soundness s0 s0_bv x h_eq cBV_fn (fun _ => rfl)))
  rename_i cF
  mrename_i hC'
  mpure hC'
  have hC : ∀ i : Fin 5, eqF cF[i] (cBV_fn i) := hC'.2

  -- Step 2: Compute d vector
  let dBV_fn : Fin 5 → BitVec 64 := fun x =>
    cBV[(x.val + 4) % 5] ^^^ (cBV[(x.val + 1) % 5]).rotateLeft 1
  let dBV : Vector (BitVec 64) 5 := Vector.ofFn dBV_fn

  -- Need hypothesis about cF for d_body_soundness
  have hC_get : ∀ i : Fin 5, eqF (cF.get i) (cBV.get i) := fun i => by
    unfold cBV
    simp [Vector.get_eq_getElem, Vector.getElem_ofFn]
    apply (hC i)

  -- Apply Spec.Vector_ofFnM for d using d_step_soundness
  mspec (Spec.Vector_ofFnM
    (inv := True)
    (f := fun x => do xor64 (cF.get ⟨(x.val + 4) % 5, by omega⟩) (← rotateLeft64 (cF.get ⟨(x.val + 1) % 5, by omega⟩) 1))
    (postStep := fun x dx => eqF dx (dBV_fn x))
    (fun x => d_step_soundness cF cBV x hC_get dBV_fn (fun _ => rfl)))
  rename_i dF
  mrename_i hD'
  mpure hD'
  have hD : ∀ i : Fin 5, eqF dF[i] (dBV_fn i) := hD'.2

  -- Step 3: Compute lanes vector
  let laneBV_fn : Fin 25 → BitVec 64 := fun i =>
    let x := i.val % 5
    let y := i.val / 5
    s0_bv.get ⟨x, by omega⟩ ⟨y, by omega⟩ ^^^ dBV[x]
  let laneBV : Vector (BitVec 64) 25 := Vector.ofFn laneBV_fn

  have hD_get : ∀ i : Fin 5, eqF (dF.get i) (dBV.get i) := fun i => by
    unfold dBV
    simp [Vector.get_eq_getElem, Vector.getElem_ofFn]
    apply (hD i)

  -- Apply Spec.Vector_ofFnM for lanes using lanes_step_soundness
  mspec (Spec.Vector_ofFnM
    (inv := True)
    (f := fun i =>
      let x := i.val % 5
      let y := i.val / 5
      xor64 (s0.get ⟨x, by omega⟩ ⟨y, by omega⟩) dF[x])
    (postStep := fun i li => eqF li (laneBV_fn i))
    (fun i => lanes_step_soundness s0 s0_bv dF dBV i h_eq hD_get laneBV_fn (fun _ => rfl)))
  rename_i laneF
  mrename_i hLane'
  mpure hLane'

  -- Final step: pure { lanes := laneF }
  mintro ∀e'
  mpure_intro

  -- Prove eqState for the result
  apply eqState_of_lanes_eq
  intro i
  have h_lane_i := hLane'.2 i
  apply (eqFhelper h_lane_i)

  unfold laneBV_fn
  simp [dBV, dBV_fn, cBV, cBV_fn]
  fin_cases i
  <;> simp
