import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Tactic

def Sigma_DLO : FirstOrder.Language where
  Functions := fun _ => Empty
  Relations := fun n => if n = 2 then Unit else Empty

def xi_lessthan_xj : (n : ℕ) → (i j : Fin n) → Sigma_DLO.BoundedFormula Empty n := by
  intro n i j
  let rel : Sigma_DLO.Relations 2 := ()
  exact FirstOrder.Language.BoundedFormula.rel rel
    (fun inp => match inp with
              | 0 => FirstOrder.Language.Term.var (Sum.inr i)
              | 1 => FirstOrder.Language.Term.var (Sum.inr j))

def DLO1 : Sigma_DLO.Sentence :=
  let x0lx1 := xi_lessthan_xj 2 0 1

  let x1lx0 := xi_lessthan_xj 2 1 0

  (x0lx1.imp (x1lx0.not)).all.all

def DLO2 : Sigma_DLO.Sentence :=
  let x0lx1 := xi_lessthan_xj 3 0 1
  let x1lx2 := xi_lessthan_xj 3 1 2
  let x0lx2 := xi_lessthan_xj 3 0 2

  ((x1lx2.imp x0lx1.not ).not.imp x0lx2).all.all.all

def DLO3 : Sigma_DLO.Sentence :=
  let x0lx1 := xi_lessthan_xj 2 0 1
  let x1lx0 := xi_lessthan_xj 2 1 0
  let x0eqx1 : Sigma_DLO.BoundedFormula Empty 2 :=
    FirstOrder.Language.BoundedFormula.equal
    (FirstOrder.Language.Term.var (Sum.inr 0))
    (FirstOrder.Language.Term.var (Sum.inr 1))

  ((x1lx0.not.imp x0eqx1).not.imp x0lx1).all.all

def DLO4 : Sigma_DLO.Sentence :=
  let x0lx1 := xi_lessthan_xj 2 0 1
  let x2lx1 := xi_lessthan_xj 3 2 1
  let x0lx2 := xi_lessthan_xj 3 0 2

  (x0lx1.imp (x0lx2.imp x2lx1.not).all.not).all.all

def DLO5 : Sigma_DLO.Sentence :=
  let x1lx0 := xi_lessthan_xj 2 1 0
  x1lx0.not.all.not.all

def DLO6 : Sigma_DLO.Sentence :=
  let x0lx1 := xi_lessthan_xj 2 0 1
  x0lx1.not.all.not.all

def Ax_DLO : Sigma_DLO.Theory :=
  {DLO1, DLO2, DLO3, DLO4, DLO5, DLO6}

instance Q_interprets_Sigma_DLO : Sigma_DLO.Structure Rat where
  funMap := by
    intro n p
    exact Empty.elim p

  RelMap := by
    intro n
    if h : n = 2 then
      intro p
      cases h
      exact fun ts : (Fin 2 → Rat) => Rat.instLT.lt (ts 0) (ts 1)
    else
      intro x y
      exact True

instance Z_interprets_Sigma_DLO : Sigma_DLO.Structure Int where
  funMap := by
    intro n f ts
    exact 0
  RelMap := by
    intro n
    if h : n = 2 then
      intro p ts
      cases h
      exact LT.lt (ts 0) (ts 1)
    else
      intro p ts
      exact False


@[simp]
lemma realize_xi_lt_atQ
  {n : ℕ} {i j : Fin n} {v : Fin n → Rat} :
  (xi_lessthan_xj n i j).Realize ρ v ↔ v i < v j := by
    apply Iff.intro
    · intro h
      trivial
    · intro h
      trivial

@[simp]
lemma realize_xi_lt_atZ
  {n : ℕ} {i j : Fin n} {v : Fin n → Int} :
  (xi_lessthan_xj n i j).Realize ρ v ↔ v i < v j := by
    apply Iff.intro
    · intro h
      trivial
    · intro h
      trivial

def ltM [inst : Sigma_DLO.Structure M] : M → M → Prop := by
  intro m1 m2
  have p : Sigma_DLO.Relations 2 := by exact ()
  have ts : (i : Fin 2) →  M := fun i =>
    match i with
    | 0 => m1
    | 1 => m2
  exact inst.RelMap p ts

instance proof_Q_is_DLO_model : Ax_DLO.Model Rat where
  realize_of_mem := by
    letI := Rat.instPartialOrder
    intro ϕ h
    have h' : ϕ = DLO1 ∨ ϕ = DLO2 ∨ ϕ = DLO3 ∨ ϕ = DLO4 ∨
              ϕ = DLO5 ∨ ϕ = DLO6 := by simpa [Ax_DLO]
    rcases h' with h1 | h2 | h3 | h4 | h5 | h6
    · subst h1
      simp [DLO1]
      intro q1 q2 h1
      rw [FirstOrder.Language.BoundedFormula.realize_not]
      intro h2
      simp only [realize_xi_lt_atQ] at h2
      simp only [realize_xi_lt_atQ] at h1
      have h1' : q1 < q2 := by simpa using h1
      have h2' : q2 < q1 := by simpa using h2
      exact lt_asymm (a := q2) (b := q1) h2' h1'
    · subst h2
      intro q1 q2 q3
      simp
      intro h1 h2
      have h1' : q2 < q3 := by simpa using h1
      have h2' : q1 < q2 := by simpa using h2
      have h3' : q1 < q3 := lt_trans h2' h1'
      exact h3'
    · subst h3
      intro q1 q2
      simp
      intro h1 h2
      have h1' : q1 ≤ q2 := by simpa using h1
      have h2' : ¬ (q1 = q2) := by simpa using h2
      apply Or.elim (le_iff_lt_or_eq.mp h1')
      · intro h3
        trivial
      · intro h3
        rw[h3] at h2'
        contradiction
    · subst h4
      intro q1 q2
      simp
      intro h1
      have h1' : q1 < q2 := by simpa using h1
      exists (q1 + q2) / 2
      apply And.intro
      · letI : q1 < (q1 + q2) /2 := by linarith
        trivial
      · letI : (q1 + q2) /2 < q2 := by linarith
        trivial
    · subst h5
      intro q
      simp
      exists q-1
      letI : q - 1< q := by simp
      trivial
    · subst h6
      intro q
      simp
      exists q + 1
      letI : q < q + 1 := by simp
      trivial

theorem Z_doesnt_model_DLO : ¬ Ax_DLO.Model ℤ := by
  simp
  exists DLO4
  apply And.intro
  · simp[Ax_DLO]
  · unfold DLO4
    simp
    intro h
    specialize h 0 1
    simp at h
    specialize h zero_lt_one
    rcases h with ⟨ x, x_pos , x_lt_one ⟩
    let x_pos' : 0 < x := by simpa using x_pos
    let x_lt_one' : x < 1 := by simpa using x_lt_one
    linarith

-----------Entailment Proof----------------

@[simp]
lemma realize_xi_lt_atM [inst : Sigma_DLO.Structure M]
  {n : ℕ} {i j : Fin n} {v : Fin n → M} :
  (xi_lessthan_xj n i j).Realize ρ v ↔ ltM (v i) (v j) := by
    apply Iff.intro
    · intro h
      unfold xi_lessthan_xj at h
      simp at h
      unfold ltM
      simp
      unfold FirstOrder.Language.BoundedFormula.Realize at h
      simp at h
      -- magia negra daqui para baixo
      have h_eq : (fun i_1 => FirstOrder.Language.Term.realize (L := Sigma_DLO) (Sum.elim ρ v)
          (match (i_1 : Fin 2) with
          | 0 => FirstOrder.Language.var (Sum.inr i)
          | 1 => FirstOrder.Language.var (Sum.inr j))) =
          (fun i_1 => match i_1 with | 0 => v i | 1 => v j) := by
        ext x
        fin_cases x <;> simp [FirstOrder.Language.Term.realize]
      rw [h_eq] at h
      exact h
    · intro h
      unfold xi_lessthan_xj
      unfold ltM at h
      simp
      simp at h
      rw [FirstOrder.Language.BoundedFormula.Realize]
      have h_eq : (fun i_1 => FirstOrder.Language.Term.realize (L := Sigma_DLO) (Sum.elim ρ v)
          (match (i_1 : Fin 2) with
          | 0 => FirstOrder.Language.var (Sum.inr i)
          | 1 => FirstOrder.Language.var (Sum.inr j))) =
          (fun i_1 => match i_1 with | 0 => v i | 1 => v j) := by
        ext x
        fin_cases x <;> simp [FirstOrder.Language.Term.realize]
      rw[h_eq]
      exact h


def exists_triple : Sigma_DLO.Sentence :=
  let x0lx1 := xi_lessthan_xj 3 0 1
  let x1lx2 := xi_lessthan_xj 3 1 2

  (x0lx1.imp x1lx2.not).alls.not

theorem DLO_implies_exists_triple [inst : Sigma_DLO.Structure M] {m : M} :
    Ax_DLO.Model M → exists_triple.Realize M := by
  simp
  unfold exists_triple
  simp
  intro h1 h2
  have h_smaller : ∃ x0 , ltM x0 m := by
    have DLO5M : M ⊨ DLO5 := h1 DLO5 (by unfold Ax_DLO; simp)
    unfold DLO5 at DLO5M
    simp at DLO5M
    have means := DLO5M m
    simp at means
    trivial
  have h_bigger : ∃ x0 , ltM m x0 := by
    have DLO6M : M ⊨ DLO6 := h1 DLO6 (by unfold Ax_DLO; simp)
    unfold DLO6 at DLO6M
    simp at DLO6M
    have means := DLO6M m
    simp at means
    trivial
  let m0 := h_smaller.choose
  let m2 := h_bigger.choose
  have h3 := h2 m0 m m2
  simp at h3
  exact h3
    (by
    have m0lm : ltM m0 m := by
      unfold m0
      exact h_smaller.choose_spec
    exact m0lm)
    (by
    have mlm2 : ltM m m2 := by
      unfold m2
      exact h_bigger.choose_spec
    exact mlm2)
