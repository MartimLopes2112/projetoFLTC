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
      simp at h2
      simp at h1
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
