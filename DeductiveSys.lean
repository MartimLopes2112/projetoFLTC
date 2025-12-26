import Mathlib.Data.List.Defs
import Mathlib.Data.Vector.Defs
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Defs.LinearOrder

structure Language where
  Functions : Nat → Type
  Relations : Nat → Type
  Variables : Type

  [instFunctions : ∀ n : Nat, DecidableEq (Functions n)]
  [instRelations : ∀ n : Nat, DecidableEq (Relations n)]
  [instVariables : DecidableEq Variables]

inductive Term (L : Language) : Type
  | var : L.Variables → Term L
  | func : ∀ {l : Nat}, L.Functions l → (Fin l → Term L) → Term L

instance term_decEq : DecidableEq (Term L)
  | Term.var x, Term.var y => letI : DecidableEq (L.Variables) := L.instVariables
                              decidable_of_iff (x = y) <| by simp
  | @Term.func L l f ts, @Term.func L l' g ts' =>
      letI : ∀ i : Nat, DecidableEq (L.Functions i) := L.instFunctions
      letI : DecidableEq (Term L) := term_decEq
      if h : l = l' then
        decidable_of_iff (f = h ▸ g ∧ ∀ i : Fin l, ts i = ts' (Fin.cast h i)) <| by
        subst h
        simp[funext_iff]
      else .isFalse <| by simp [h]
  | Term.var _, Term.func _ _ | Term.func _ _, Term.var _ => .isFalse <| by simp

inductive Formula (L : Language) : Type
  | atomic : ∀ {l : Nat}, L.Relations l →  (Fin l → Term L) → Formula L
  | bot : Formula L
  | implies : Formula L → Formula L → Formula L
  | quantifier : L.Variables → Formula L → Formula L

instance formula_decEq : DecidableEq (Formula L)
  | @Formula.atomic L l p ts , @Formula.atomic L l' p' ts' =>
          if h : l = l' then
            letI : DecidableEq (Formula L) := formula_decEq
            letI : ∀ n : Nat, DecidableEq (L.Relations n) := L.instRelations
            decidable_of_iff (p = h ▸ p' ∧ ∀ i : Fin l, ts i = ts' (Fin.cast h i)) <| by
              subst h
              simp [funext_iff]
          else
          isFalse (by simp[h])
  | Formula.bot, Formula.bot => isTrue rfl
  | Formula.implies φ1 φ2, Formula.implies ψ1 ψ2 =>
          letI : DecidableEq (Formula L) := formula_decEq
          decidable_of_iff (φ1 = ψ1 ∧ φ2 = ψ2) <| by simp
  | Formula.quantifier x φ, Formula.quantifier y ψ =>
          letI : DecidableEq (Formula L) := formula_decEq
          letI : DecidableEq (L.Variables) := L.instVariables
          decidable_of_iff (x = y ∧ φ = ψ) <| by simp
  | Formula.atomic .., Formula.bot .. => isFalse (by intro h; cases h)
  | Formula.atomic .., Formula.implies .. => isFalse (by intro h; cases h)
  | Formula.atomic .., Formula.quantifier .. => isFalse (by intro h; cases h)
  | Formula.bot .., Formula.atomic .. => isFalse (by intro h; cases h)
  | Formula.bot .., Formula.implies .. => isFalse (by intro h; cases h)
  | Formula.bot .., Formula.quantifier .. => isFalse (by intro h; cases h)
  | Formula.implies .., Formula.atomic .. => isFalse (by intro h; cases h)
  | Formula.implies .., Formula.bot .. => isFalse (by intro h; cases h)
  | Formula.implies .., Formula.quantifier .. => isFalse (by intro h; cases h)
  | Formula.quantifier .., Formula.atomic .. => isFalse (by intro h; cases h)
  | Formula.quantifier .., Formula.bot .. => isFalse (by intro h; cases h)
  | Formula.quantifier .., Formula.implies .. => isFalse (by intro h; cases h)

def var : Term L → List L.Variables := by
  intro t
  cases t with
    | var x => exact [x]
    | @func l f ts =>
      exact List.foldl (fun acc i => acc ++ (var (ts i)))
                 [] (List.ofFn id)

def fv : Formula L → List L.Variables := by
  intro ψ
  letI : DecidableEq L.Variables := L.instVariables
  cases ψ with
  | @atomic l p ts =>
    exact List.foldl List.append [] ((List.ofFn ts).map var)
  | bot => exact []
  | implies φ1 φ2 => exact (fv φ1) ∪ (fv φ2)
  | quantifier x φ => exact (fv φ).removeAll [x]

def freeForVarInFormula : Term L → L.Variables → Formula L → Prop := by
  intro t x ϕ
  cases ϕ with
  | atomic => exact True
  | bot => exact True
  | implies ψ1 ψ2 => exact (freeForVarInFormula t x ψ1) ∧ (freeForVarInFormula t x ψ2)
  | quantifier y ψ => exact x = y ∨ ((¬ x ∈ fv ψ ∨ ¬ y ∈ var t ) ∧ freeForVarInFormula t x ψ)

instance freeForVarInFormula_decidable (t : Term L) (x : L.Variables)
   (ϕ : Formula L) : Decidable (freeForVarInFormula t x ϕ) := by
   cases ϕ with
   | bot => exact isTrue trivial
   | atomic => exact isTrue trivial
   | implies ψ1 ψ2 =>
        let p1 := freeForVarInFormula_decidable t x ψ1
        let p2 := freeForVarInFormula_decidable t x ψ2
        cases p1 with
        | isTrue h1 => cases p2 with
                      | isTrue h2 => exact isTrue (by dsimp [freeForVarInFormula]; exact ⟨h1,h2⟩ )
                      | isFalse h2 => exact isFalse (by
                            intro h
                            have : freeForVarInFormula t x ψ2 := h.right
                            exact h2 this)
        | isFalse h1 => exact isFalse (by
              intro h
              have : freeForVarInFormula t x ψ1 := h.left
              exact h1 this)
   | quantifier y ψ =>  letI := L.instVariables
                        letI := freeForVarInFormula_decidable t x ψ
                        if x = y then exact isTrue (by
                                    dsimp[freeForVarInFormula]
                                    left; trivial)
                       else if g : (x ∈ fv ψ) ∧ (y ∈ var t) then
                          exact isFalse (by
                           dsimp[freeForVarInFormula]; intro h;
                           cases h with
                           | inl hl => trivial
                           | inr hr => letI := hr.left
                                       aesop
                           )
                       else if h : freeForVarInFormula t x ψ then
                          exact isTrue (by
                           dsimp[freeForVarInFormula]
                           right
                           exact ⟨not_and_or.mp g, h ⟩  )
                       else exact isFalse (by
                            dsimp[freeForVarInFormula]
                            intro abs
                            cases abs with
                            | inl hl => contradiction
                            | inr hr => letI := hr.right; contradiction
                            )

def swapOccurences : Term L → Term L → L.Variables → Term L := by
  intro t t' x
  cases t with
  | var y => letI := L.instVariables
             if x = y then exact t'
             else exact Term.var y
  | @func l f ts => exact Term.func f (fun i => swapOccurences (ts i) t' x)

def swapFreeOccurences : Formula L → Term L → L.Variables → Formula L := by
  intro ϕ t x
  cases ϕ with
  | bot => exact Formula.bot
  | atomic p ts => exact Formula.atomic p (fun i => swapOccurences (ts i) t x)
  | implies φ1 φ2 => exact Formula.implies (swapFreeOccurences φ1 t x) (swapFreeOccurences φ2 t x)
  | quantifier y φ => letI := L.instVariables
                      if x = y then exact Formula.quantifier y φ
                      else exact Formula.quantifier y (swapFreeOccurences φ t x)

def findTerm_inTerms : Term L → Term L → L.Variables
            → Option (Option (Term L)) := by
  intro u v x --want to check if u = [v]^x_t
  letI := L.instVariables
  letI := L.instFunctions
  cases u with
  | var y => cases v with
              | var z => if ¬ y = z then exact none
                         else if y = x
                         then exact some (some (Term.var x))
                         else exact some none
              | _ => exact none
  | @func l f us => cases v with
              | @func l' g vs =>
              if h : l = l' then
                if f = h ▸ g then
                  have combineResults : Option (Option (Term L))
                                →  Option (Option (Term L))
                                →  Option (Option (Term L)) := by
                      intro t1 t2
                      exact do
                      let o1 ← t1
                      let o2 ← t2
                      match o1, o2 with
                      | none, none => pure none
                      | some a, none => pure (some a)
                      | none, some b => pure (some b)
                      | some a, some b =>
                        if a = b then pure (some a) else failure

                  let verdicts := fun i => findTerm_inTerms (us i) (vs (Fin.cast h i)) x
                  exact (List.ofFn verdicts).foldl combineResults (some none)
                else exact none
              else exact none
              | _ => exact none

def findTerm : Formula L → Formula L → L.Variables
            → Option (Option (Term L)) := by
  -- none -> nao da
  -- some none -> da qualquer termo
  -- some some t -> so da com o t
  intro ϕ ψ x --want to check if ϕ = [ψ]^x_t
  letI := L.instVariables
  letI := L.instRelations
  cases ϕ with
  | bot => cases ψ with
            | bot => exact some none
            | _ => exact none
  | implies φ1 φ2 => cases ψ with
                      | implies ψ1 ψ2 =>
                            let t1 := findTerm φ1 ψ1 x
                            let t2 := findTerm φ2 ψ2 x
                            if t1 = none ∨ t2 = none then exact none
                            else if t1 = some none then
                              exact t2
                            else if t2 = some none then
                              exact t1
                            else if t1 = t2 then
                              exact t1
                            else exact none
                      | _ => exact none
  | @atomic l p ts =>
    cases ψ with
    | @atomic l' p' ts' => if h : l = l' then
              if p = h ▸ p' then
              have combineResults : Option (Option (Term L))
                            →  Option (Option (Term L))
                            →  Option (Option (Term L)) := by
                            intro t1 t2
                            exact do
                            let o1 ← t1
                            let o2 ← t2
                            match o1, o2 with
                            | none, none => pure none
                            | some a, none => pure (some a)
                            | none, some b => pure (some b)
                            | some a, some b =>
                              if a = b then pure (some a) else failure

              let verdicts := fun i => findTerm_inTerms (ts i) (ts' (Fin.cast h i)) x
              exact (List.ofFn verdicts).foldl combineResults (some none)
              else exact none
              else exact none
    | _ => exact none
  | quantifier y φ => cases ψ with
                      | quantifier z ψ' =>
                          if y = z then
                          if ¬ x = y then exact (findTerm φ ψ' x)
                          else exact (if φ = ψ' then some none else none)
                          else exact none
                      | _ => exact none

def Syllogism (L : Language) : Type := List (Formula L) × List (Formula L)

def isAxiom : Syllogism L  → Prop := by
  intro sil
  exact ¬ sil.fst ∩ sil.snd = []

instance isAxiomDecidable : (sil : Syllogism L) → Decidable (isAxiom sil) := by
  intro sil
  unfold isAxiom
  infer_instance

def isLeftBot : Syllogism L → Prop := fun sil => Formula.bot ∈ sil.fst

instance isLeftBotDecidable : (sil : Syllogism L) → Decidable (isLeftBot sil) := by
  intro sil
  if h : Formula.bot ∈ sil.fst then exact isTrue h else exact isFalse h

def extractElement : (Δ : List α) → Δ.length = 1 → PSigma (fun a : α => a ∈ Δ) := by
  intro Δ h_length
  cases Δ with
  | nil  => simp; contradiction
  | cons a as => exact ⟨ a , by simp⟩

def subtractLists [DecidableEq α] (A B : List α) : List α := by
   cases B with
    | nil     => exact A
    | cons b bs => exact subtractLists (A.erase b) bs

def isLeftImplication : Syllogism L → Syllogism L → Syllogism L → Prop := by
  intro hyp1 hyp2 sil
  let Γ := hyp1.fst
  let Δ := hyp2.snd
  --Δ e Γ estao presentes nos antecedentes e consequentes das hipoteses e da conclusao
  if Δ.isPerm sil.snd ∧ (Δ ∩ hyp1.snd).isPerm Δ
      ∧ (Γ ∩ sil.fst).isPerm Γ ∧ (Γ ∩ hyp2.fst).isPerm Γ then
    --Os antecedentes tem formulas ϕ e φ
    if h : (subtractLists hyp1.snd Δ).length = 1 ∧
              (subtractLists hyp2.fst Γ).length = 1 then
      let ϕ := (extractElement (subtractLists hyp1.snd Δ) h.left).fst
      let ψ := (extractElement (subtractLists hyp2.fst Γ) h.right).fst
      let hϕ := (extractElement (subtractLists hyp1.snd Δ) h.left).snd
      let hψ := (extractElement (subtractLists hyp2.fst Γ) h.right).snd

      if hyp1.snd.isPerm (ϕ :: Δ) ∧ hyp2.fst.isPerm (ψ :: Γ)
            ∧ sil.fst.isPerm (Formula.implies ϕ ψ :: Γ) then
            exact True
      else exact False
    else exact False
  else exact False

instance isLeftImplicationDecidable : (hyp1 hyp2 sil : Syllogism L)
    → Decidable (isLeftImplication hyp1 hyp2 sil) := by
    intro hyp1 hyp2 sil
    unfold isLeftImplication
    infer_instance

def isRightImplication : Syllogism L → Syllogism L → Prop := by
  intro hyp sil
  let Γ := sil.fst
  if h1 : Γ ∩ hyp.fst = Γ ∧ (subtractLists hyp.fst Γ).length = 1 then
      let ϕ := (extractElement (subtractLists hyp.fst Γ) h1.right).fst
      let Δ := hyp.snd ∩ sil.snd

      if h2 : ((Δ.bagInter hyp.snd).isPerm Δ ∧ (Δ.bagInter sil.snd).isPerm Δ)
                ∧ (subtractLists hyp.snd Δ).length = 1
                ∧ (subtractLists sil.snd Δ).length = 1 then

        let ψ := (extractElement (subtractLists hyp.snd Δ) h2.right.left).fst
        let γ := (extractElement (subtractLists sil.snd Δ) h2.right.right).fst

        if γ = Formula.implies ϕ ψ then exact True else exact False
      else exact False
  else exact False

instance isRightImplicationDecidable : (hyp sil : Syllogism L)
    → Decidable (isRightImplication hyp sil) := by
    intro hyp sil
    unfold isRightImplication
    infer_instance

def isLeftQuantification : Syllogism L → Syllogism L →
            (t : Term L) → (x : L.Variables) → (ϕ : Formula L) → Prop := by
  intro hyp sil t x ϕ
  if h : hyp.snd.isPerm sil.snd ∧ (sil.fst.bagInter hyp.fst).isPerm sil.fst
     ∧ (subtractLists hyp.fst sil.fst).length = 1 ∧ Formula.quantifier x ϕ ∈ sil.fst
  then let ⟨ψ, hψ⟩ := extractElement (subtractLists hyp.fst sil.fst) h.right.right.left
       exact ψ = swapFreeOccurences ϕ t x
  else exact False

instance isLeftQuantificationDecidable : (hyp sil : Syllogism L) →
            (t : Term L) → (x : L.Variables) → (ϕ : Formula L) →
            Decidable (isLeftQuantification hyp sil t x ϕ) := by
  intro hyp sil t x ϕ
  unfold isLeftQuantification
  infer_instance

def isRightQuantification : Syllogism L → Syllogism L →
    L.Variables → L.Variables → Formula L →  Prop := by
  intro hyp sil x y ϕ
  let Γ := sil.fst
  let Δ := sil.snd.bagInter hyp.snd
  if subtractLists sil.snd Δ = [Formula.quantifier x ϕ] ∧
      subtractLists hyp.snd Δ = [swapFreeOccurences ϕ (Term.var y) x]  ∧
        hyp.fst.isPerm Γ
  then exact ∀ φ : Formula L, φ ∈ (Γ ++ Δ ++ [Formula.quantifier x ϕ]) → y ∉ fv φ
  else exact False

instance isRightQuantificationDecidable : (hyp sil : Syllogism L ) →
  (x y : L.Variables) → (ϕ : Formula L) → Decidable (isRightQuantification hyp sil x y ϕ) := by
  intro hyp sil x y ϕ
  unfold isRightQuantification
  letI := L.instVariables
  infer_instance


inductive TreeProof {L : Language} : Syllogism L → Type
  | ax sil : isAxiom sil → TreeProof sil
  | l_bot sil : isLeftBot sil → TreeProof sil
  | l_impl sil {hyp1 hyp2 : Syllogism L} : TreeProof hyp1 → TreeProof hyp2
          → isLeftImplication hyp1 hyp2 sil → TreeProof sil
  | r_impl sil {hyp : Syllogism L} : TreeProof hyp → isRightImplication hyp sil
          → TreeProof sil
  | l_quant sil {hyp : Syllogism L} : TreeProof hyp → (x : L.Variables) →
        (t : Term L) → (ϕ : Formula L) → isLeftQuantification hyp sil t x ϕ
        → TreeProof sil
  | r_quant sil {hyp : Syllogism L} : TreeProof hyp → (x y : L.Variables)
     → (ϕ : Formula L) → isRightQuantification hyp sil x y ϕ
     → TreeProof sil

-------------------------------------------------------------------------
def Sigma_S : Language where
  Functions := fun n => match n with| 0 => Unit
                                    | 1 => Unit
                                    | _ => Empty
  Relations := fun n => match n with | 2 => Unit
                                     | _ => Empty
  Variables := String
  instFunctions (n : Nat) := by
    split
    · infer_instance
    · infer_instance
    · infer_instance
  instRelations (n : Nat):= by
    split
    · infer_instance
    · infer_instance
  instVariables := by infer_instance

def S : Term Sigma_S → Term Sigma_S := by
  intro t
  let SSymbol : Sigma_S.Functions 1 := by exact ()
  exact Term.func SSymbol (fun (_ : Fin 1) => t)

def zero : Term Sigma_S := by
  let zeroSymb : Sigma_S.Functions 0 := by exact ()
  exact Term.func zeroSymb Fin.elim0

def eqS : Term Sigma_S → Term Sigma_S → Formula Sigma_S := by
  intro t1 t2
  let eqSymbol : Sigma_S.Relations 2 := by exact ()
  exact Formula.atomic eqSymbol (fun i : Fin 2 => if i =0 then t1 else t2)

def x : Term Sigma_S := Term.var "x"

def y : Term Sigma_S := Term.var "y"

-- Abbreviations for terms
def S1 : Formula Sigma_S :=
  Formula.quantifier "x" (Formula.implies (eqS (S x) zero) Formula.bot)

def S2 : Formula Sigma_S :=
  Formula.quantifier "x" (Formula.quantifier "y" (
    Formula.implies (eqS (S x) (S y)) (eqS x y)
  ))

def ϕ : Formula Sigma_S :=
  Formula.quantifier "y" (Formula.implies
  (eqS (S (S x)) (S y))
  (eqS (S x) y))

def ψ : Formula Sigma_S :=
  Formula.quantifier "y" (Formula.implies
  (eqS (S x) (S y))
  (eqS x y))

def sil12 : Syllogism Sigma_S :=
  ⟨ [ψ, ϕ, S2,
    eqS (S (S x)) (S (S y)),
    eqS (S x) (S y)]
  ,
  [eqS x y,
  eqS (S x) (S y)]⟩

def sil11 : Syllogism Sigma_S :=
  ⟨ [ψ, ϕ, S2,
    eqS (S (S x)) (S (S y)),
    eqS (S x) (S y),
    eqS x y]
  ,
  [eqS x y]⟩

def sil10 : Syllogism Sigma_S :=
  ⟨ [ψ, ϕ, S2,
     Formula.implies (eqS (S x) (S y))
      (eqS x y),
     eqS (S (S x)) (S (S y)),
     eqS (S x) (S y)]
  ,
    [eqS x y] ⟩

def sil9 : Syllogism Sigma_S :=
  ⟨ [ψ, ϕ, S2,
     eqS (S (S x)) (S (S y)),
     eqS (S x) (S y)]
  ,
    [eqS x y] ⟩


def sil8 : Syllogism Sigma_S :=
  ⟨ [ϕ, S2,
     eqS (S (S x)) (S (S y))]
  ,
    [eqS x y,
    eqS (S (S x)) (S (S y))] ⟩

def sil7 : Syllogism Sigma_S :=
  ⟨ [eqS (S (S x)) (S (S y)),
     eqS (S x) (S y),
     ϕ, S2]
  ,
    [eqS x y] ⟩

def sil6 : Syllogism Sigma_S :=
  ⟨ [eqS (S (S x)) (S (S y)),
     Formula.implies (eqS (S (S x)) (S (S y))) (eqS (S x) (S y)),
     ϕ, S2]
  ,
    [eqS x y] ⟩

def sil5 : Syllogism Sigma_S :=
  ⟨ [Formula.implies (eqS (S (S x)) (S (S y))) (eqS (S x) (S y)),
     ϕ, S2]
  ,
    [Formula.implies (eqS (S (S x)) (S (S y))) (eqS x y)] ⟩

def sil4 : Syllogism Sigma_S :=
  ⟨ [ϕ, S2]
  ,
    [Formula.implies (eqS (S (S x)) (S (S y))) (eqS x y)] ⟩

def sil3 : Syllogism Sigma_S :=
  ⟨ [S2]
  ,
    [Formula.implies (eqS (S (S x)) (S (S y))) (eqS x y)] ⟩

def sil2 : Syllogism Sigma_S :=
  ⟨ [S2]
  ,
    [Formula.quantifier "y"
      (Formula.implies (eqS (S (S x)) (S (S y))) (eqS x y))
      ] ⟩

def sil1 : Syllogism Sigma_S :=
  ⟨ [S2]
  ,
    [Formula.quantifier "x"
      (Formula.quantifier "y"
      (Formula.implies (eqS (S (S x)) (S (S y))) (eqS x y)))
      ] ⟩

def full_proof : TreeProof sil1 :=
by
  -- line 12
  have h12 : TreeProof sil12 :=
    TreeProof.ax sil12 (by decide)

  -- line 11
  have h11 : TreeProof sil11 :=
    TreeProof.ax sil11 (by decide)

  -- line 10
  have h10 : TreeProof sil10 :=
    TreeProof.l_impl sil10 h12 h11 (by decide)

  -- line 9
  have h9 : TreeProof sil9 :=
    TreeProof.l_quant sil9 h10 "y" y (Formula.implies (eqS (S x) (S y)) (eqS x y)) (by decide)

  -- line 8
  have h8 : TreeProof sil8 :=
    TreeProof.ax sil8 (by decide)

  -- line 7
  have h7 : TreeProof sil7 :=
    TreeProof.l_quant sil7 h9 "x" x ψ (by decide)

  -- line 6
  have h6 : TreeProof sil6 :=
    TreeProof.l_impl sil6 h8 h7 (by decide)

  -- line 5
  have h5 : TreeProof sil5 :=
    TreeProof.r_impl sil5 h6 (by decide)

  -- line 4
  have h4 : TreeProof sil4 :=
    TreeProof.l_quant sil4 h5 "y" (S y)
    (Formula.implies (eqS (S (S x)) (S y)) (eqS (S x) y))
    (by decide)

  -- line 3
  have h3 : TreeProof sil3 :=
    TreeProof.l_quant sil3 h4 "x" (S x) ψ (by decide)

  -- line 2
  have h2 : TreeProof sil2 :=
   TreeProof.r_quant sil2 h3 "y" "y"
          (Formula.implies (eqS (S (S x)) (S (S y))) (eqS x y))
            (by decide)

  -- line 1
  exact
    TreeProof.r_quant sil1 h2 "x" "x"
      (Formula.quantifier "y" (Formula.implies (eqS (S (S x)) (S (S y))) (eqS x y)))
        (by decide)
