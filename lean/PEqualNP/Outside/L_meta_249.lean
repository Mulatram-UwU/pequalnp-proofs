import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_249 : ∀ (N k : ℕ) (E : Fin N → Fin N → Prop) (pos : Fin N → ℕ), 1 ≤ k → ((∀ u v : Fin N, E u v → E v u) ∧ (∀ u v : Fin N, E u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧ ∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) → (∀ (L : ℕ) (w : ℕ → Fin N), pos (w 0) = 0 → pos (w L) = 0 → w 0 ≠ w L → (∀ i : ℕ, i < L → E (w i) (w (i + 1))) → 2 * k + 1 ≤ L) ∧ ∀ v a b c : Fin N, E v a → E v b → E v c → a ≠ b → a ≠ c → b ≠ c → pos v = 0 := by
  intro N k E pos hk H
  obtain ⟨hsymm, H1, H2⟩ := H
  constructor
  · intro L w hw0 hwL hne hadj
    let u := w 0
    have hu : pos u = 0 := hw0
    have H2' : ∀ x : Fin N, ∃ a b : Fin N, pos x ≠ 0 →
        ((∀ y : Fin N, E x y ↔ y = a ∨ y = b) ∧ pos a + 1 = pos x ∧
          pos b = (pos x + 1) % (2 * k + 1)) := by
      intro x
      by_cases hx : pos x ≠ 0
      · obtain ⟨_, a, b, h⟩ := H2 x hx
        exact ⟨a, b, fun _ => h⟩
      · exact ⟨x, x, fun h => absurd h hx⟩
    choose A B hAB using H2'
    have hle : ∀ x, pos x ≠ 0 → pos x ≤ 2 * k := fun x hx => (H2 x hx).1
    have nbr : ∀ x y, pos x ≠ 0 → E x y → y = A x ∨ y = B x :=
      fun x y hx h => ((hAB x hx).1 y).1 h
    have hA : ∀ x, pos x ≠ 0 → pos (A x) + 1 = pos x := fun x hx => (hAB x hx).2.1
    have hB : ∀ x, pos x ≠ 0 → pos (B x) = (pos x + 1) % (2 * k + 1) :=
      fun x hx => (hAB x hx).2.2
    have back_A : ∀ y, pos y ≠ 0 → pos y < 2 * k → A (B y) = y := by
      intro y hy hlt
      have h1 := hB y hy
      rw [Nat.mod_eq_of_lt (by omega : pos y + 1 < 2 * k + 1)] at h1
      have hz : pos (B y) ≠ 0 := by omega
      have hyz : E y (B y) := ((hAB y hy).1 (B y)).2 (Or.inr rfl)
      rcases nbr (B y) y hz (hsymm y (B y) hyz) with h | h
      · exact h.symm
      · exfalso
        have h2 := hB (B y) hz
        rw [← h, h1] at h2
        by_cases h3 : pos y + 1 + 1 < 2 * k + 1
        · rw [Nat.mod_eq_of_lt h3] at h2
          omega
        · have h4 : pos y + 1 + 1 = 2 * k + 1 := by omega
          rw [h4, Nat.mod_self] at h2
          exact hy h2
    have back_B : ∀ y, pos y ≠ 0 → 2 ≤ pos y → B (A y) = y := by
      intro y hy h2
      have h1 := hA y hy
      have hz : pos (A y) ≠ 0 := by omega
      have hyz : E y (A y) := ((hAB y hy).1 (A y)).2 (Or.inl rfl)
      rcases nbr (A y) y hz (hsymm y (A y) hyz) with h | h
      · exfalso
        have h3 := hA (A y) hz
        rw [← h] at h3
        omega
      · exact h.symm
    have step : ∀ (y z : Fin N) (i : ℕ), E y z → i + 1 ≤ 2 * k →
        (y = u ∨ (pos y ≠ 0 ∧ A^[pos y] y = u ∧ pos y ≤ i) ∨
          (pos y ≠ 0 ∧ B^[2 * k + 1 - pos y] y = u ∧ 2 * k + 1 - pos y ≤ i)) →
        (z = u ∨ (pos z ≠ 0 ∧ A^[pos z] z = u ∧ pos z ≤ i + 1) ∨
          (pos z ≠ 0 ∧ B^[2 * k + 1 - pos z] z = u ∧ 2 * k + 1 - pos z ≤ i + 1)) := by
      intro y z i hyz hi hy
      rcases hy with hyu | ⟨hp, hit, hpi⟩ | ⟨hp, hit, hqi⟩
      · rw [hyu] at hyz
        have hz : pos z ≠ 0 := by
          rcases H1 u z hyz with h | h
          · exact absurd hu h
          · exact h
        have hzle := hle z hz
        rcases nbr z u hz (hsymm u z hyz) with h | h
        · have h1 := hA z hz
          rw [← h, hu] at h1
          have h1' : pos z = 1 := by omega
          right; left
          refine ⟨hz, ?_, by omega⟩
          rw [h1', Function.iterate_one]
          exact h.symm
        · have h1 := hB z hz
          rw [← h, hu] at h1
          have h2 : pos z = 2 * k := by
            by_contra hne
            rw [Nat.mod_eq_of_lt (by omega)] at h1
            omega
          right; right
          refine ⟨hz, ?_, by omega⟩
          have e : 2 * k + 1 - pos z = 1 := by omega
          rw [e, Function.iterate_one]
          exact h.symm
      · have hyle := hle y hp
        rcases nbr y z hp hyz with rfl | rfl
        · have h1 := hA y hp
          by_cases hp1 : pos y = 1
          · left
            rw [hp1, Function.iterate_one] at hit
            exact hit
          · right; left
            have hz : pos (A y) ≠ 0 := by omega
            refine ⟨hz, ?_, by omega⟩
            have e : pos y = pos (A y) + 1 := by omega
            rw [e, Function.iterate_succ_apply] at hit
            exact hit
        · have h1 := hB y hp
          by_cases hp2 : pos y = 2 * k
          · exfalso
            omega
          · have hlt : pos y + 1 < 2 * k + 1 := by omega
            rw [Nat.mod_eq_of_lt hlt] at h1
            have hz : pos (B y) ≠ 0 := by omega
            have hback : A (B y) = y := back_A y hp (by omega)
            right; left
            refine ⟨hz, ?_, by omega⟩
            rw [h1, Function.iterate_succ_apply, hback]
            exact hit
      · have hyle := hle y hp
        rcases nbr y z hp hyz with rfl | rfl
        · have h1 := hA y hp
          by_cases hp1 : pos y = 1
          · exfalso
            omega
          · have hz : pos (A y) ≠ 0 := by omega
            have hback : B (A y) = y := back_B y hp (by omega)
            right; right
            refine ⟨hz, ?_, by omega⟩
            have e : 2 * k + 1 - pos (A y) = (2 * k + 1 - pos y) + 1 := by omega
            rw [e, Function.iterate_succ_apply, hback]
            exact hit
        · have h1 := hB y hp
          by_cases hp2 : pos y = 2 * k
          · left
            have e : 2 * k + 1 - pos y = 1 := by omega
            rw [e, Function.iterate_one] at hit
            exact hit
          · have hlt : pos y + 1 < 2 * k + 1 := by omega
            rw [Nat.mod_eq_of_lt hlt] at h1
            have hz : pos (B y) ≠ 0 := by omega
            right; right
            refine ⟨hz, ?_, by omega⟩
            have e : 2 * k + 1 - pos y = (2 * k + 1 - pos (B y)) + 1 := by omega
            rw [e, Function.iterate_succ_apply] at hit
            exact hit
    have all : ∀ i, i ≤ L → i ≤ 2 * k →
        (w i = u ∨ (pos (w i) ≠ 0 ∧ A^[pos (w i)] (w i) = u ∧ pos (w i) ≤ i) ∨
          (pos (w i) ≠ 0 ∧ B^[2 * k + 1 - pos (w i)] (w i) = u ∧ 2 * k + 1 - pos (w i) ≤ i)) := by
      intro i
      induction i with
      | zero => intro _ _; exact Or.inl rfl
      | succ i ih =>
        intro h1 h2
        exact step (w i) (w (i + 1)) i (hadj i (by omega)) h2 (ih (by omega) (by omega))
    by_contra hcon
    have hL : L ≤ 2 * k := by omega
    rcases all L le_rfl hL with h | ⟨h, _⟩ | ⟨h, _⟩
    · exact hne h.symm
    · exact h hwL
    · exact h hwL
  · intro v a b c hva hvb hvc hab hac hbc
    by_contra hv
    obtain ⟨-, a0, b0, hiff, -, -⟩ := H2 v hv
    have ea : a = a0 ∨ a = b0 := (hiff a).1 hva
    have eb : b = a0 ∨ b = b0 := (hiff b).1 hvb
    have ec : c = a0 ∨ c = b0 := (hiff c).1 hvc
    rcases ea with rfl | rfl <;> rcases eb with rfl | rfl <;> rcases ec with rfl | rfl <;>
      first | exact hab rfl | exact hac rfl | exact hbc rfl
