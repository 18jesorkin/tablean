-- TABLEAU

import data.finset.basic
import data.finset.pimage
import algebra.big_operators.order
import tactic
import order.well_founded_set

import syntax
import semantics
import setsimp

set_option pp.beta true

open formula
open hasLength

-- Definition 9, page 15
-- A set X is closed  iff  0 ∈ X or X contains a formula and its negation.
def closed : finset formula → Prop := λ X, ⊥ ∈ X ∨ ∃ f ∈ X, ~f ∈ X
-- A set X is simple  iff  all P ∈ X are (negated) atoms or [A]_ or ¬[A]_.
def simpleForm : formula → Prop
| ⊥       := true
| (~⊥)    := true -- added!
| (· _)   := true
| ~(· _)  := true
| (□ _)   := true
| ~(□ _)  := true
| _       := false
instance (ϕ) : decidable (simpleForm ϕ) := begin
  cases ϕ,
  case bottom: { apply decidable.is_true, tauto, },
  case atom_prop: { apply decidable.is_true, tauto, },
  case neg: { cases ϕ,
    case bottom: { apply decidable.is_true, tauto, },
    case atom_prop: { apply decidable.is_true, tauto, },
    case neg: { apply decidable.is_false, tauto, },
    case and: { apply decidable.is_false, tauto, },
    case box: { apply decidable.is_true, tauto, },
  },
  case and: { apply decidable.is_false, tauto, },
  case box: { apply decidable.is_true, tauto, },
end
@[derive decidable]
def simple : finset formula → Prop
| X := ∀ P ∈ X, simpleForm P
-- Let X_A := { R | [A]R ∈ X }.
@[simp]
def formProjection : formula → option formula
| (□f) := some f
| _    := none
def projection : finset formula → finset formula
| X := X.bUnion (λ x, (formProjection x).to_finset)

lemma proj { g: formula } { X : finset formula } :
  g ∈ projection X ↔ □g ∈ X :=
begin
  unfold projection,
  simp,
  split,
  { intro lhs,
    rcases lhs with ⟨ boxg, boxg_in_X, projboxg_is_g ⟩,
    cases boxg,
    repeat { finish },
  },
  { intro rhs,
    use □g,
    split,
    exact rhs,
    simp,
  },
end

lemma projSet {X : finset formula} : ↑(projection X) = { ϕ | □ϕ ∈ X } :=
begin
  ext1,
  unfold_coes,
  simp,
  exact proj,
end

lemma projection_length_leq : ∀ f, (projection {f}).sum lengthOfFormula ≤ lengthOfFormula f :=
begin
  intro f,
  cases f,
  { omega, },
  { exact dec_trivial, },
  { exact dec_trivial, },
  { exact dec_trivial, },
  { have subsubClaim : projection {□f} = {f}, {
      ext1, rw proj, simp,
    },
    rw subsubClaim,
    unfold lengthOfFormula, simp,
  },
end

lemma projection_set_length_leq : ∀ X, lengthOfSet (projection X) ≤ lengthOfSet X :=
begin
  intro X,
  apply finset.induction_on X,
  { unfold lengthOfSet, simp, intros f f_in_empty, cases f_in_empty, },
  { intros f S f_not_in_S IH,
    unfold lengthOfSet,
    rw finset.sum_insert f_not_in_S,
    simp,
    have insert_comm_proj : ∀ X f, projection (insert f X) = (projection {f}) ∪ (projection X), {
      intros X f,
      unfold projection,
      ext1 g,
      simp,
    },
    { calc (projection (insert f S)).sum lengthOfFormula
        = (projection (insert f S)).sum lengthOfFormula : refl _
    ... = (projection {f} ∪ projection S).sum lengthOfFormula : by { rw insert_comm_proj S f, }
    ... ≤ (projection {f}).sum lengthOfFormula + (projection S).sum lengthOfFormula : by { apply sum_union_le, }
    ... ≤ lengthOfFormula f + (projection S).sum lengthOfFormula : by { simp only [add_le_add_iff_right, projection_length_leq], }
    ... ≤ lengthOfFormula f + S.sum lengthOfFormula : by { simp, apply IH, },
    },
  },
end

-- local rules: given this set, we get these sets as child nodes
inductive localRule : finset formula → finset (finset formula) → Type
-- closing rules:
| bot {X    } (h : ⊥          ∈ X) : localRule X ∅
| not {X ϕ  } (h : ϕ ∈ X ∧ ~ϕ ∈ X) : localRule X ∅
-- one-child rules:
| neg {X ϕ  } (h : ~~ϕ        ∈ X) : localRule X { X \ {~~ϕ}    ∪ {ϕ}   }
| con {X ϕ ψ} (h : ϕ ⋏ ψ      ∈ X) : localRule X { X \ {ϕ⋏ψ}    ∪ {ϕ,ψ} }
-- splitting rule:
| nCo {X ϕ ψ} (h : ~(ϕ ⋏ ψ)   ∈ X) : localRule X { X \ {~(ϕ⋏ψ)} ∪ {~ϕ}
                                                 , X \ {~(ϕ⋏ψ)} ∪ {~ψ}  }



--instance h0 {X : finset formula} {Y : finset (finset formula)} : decidable (⊥ ∈ X ∧ Y = ∅) := 
--begin
  --exact and.decidable,
--end

--instance h1 {X : finset formula} {Y : finset (finset formula)} : decidable (∃ ϕ ∈ X, ~ϕ ∈ X ∧ Y = ∅) := 
--begin
  --exact finset.decidable_dexists_finset,
--end


instance h2 {X : finset formula} {Y : finset (finset formula)} : decidable (∃ nnα ∈ X, ∃ X' ∈ Y, ∃ α ∈ X', (nnα = ~~α) ∧ (X' = X \ {nnα} ∪ {α}) ∧ (Y = {X'})) := 
begin
  exact finset.decidable_dexists_finset,
end

instance h3 {X : finset formula} {Y : finset (finset formula)} : decidable (∃ ϕ_ψ ∈ X, ∃ X' ∈ Y, ∃ ϕ ψ ∈ X', (ϕ_ψ = ϕ ⋏ ψ) ∧ (X' = X \ {ϕ_ψ} ∪ {ϕ,ψ}) ∧ (Y = {X'})) := 
begin
  exact finset.decidable_dexists_finset,
end

instance h4_1 {nϕ} :  decidable(∃ ϕ, nϕ = ~ϕ) :=
begin
  sorry,
end

instance h4_2 {ϕ_ψ} : decidable(∃ ϕ ψ, ϕ_ψ = (ϕ ⋏ ψ)) :=
begin
  sorry,
end

instance h4_3 {nϕ_ψ} : decidable(∃ ϕ ψ, nϕ_ψ = ~(ϕ ⋏ ψ)) :=
begin
  sorry,
end

instance h4_4 {nϕ_ψ nϕ nψ} :  decidable(∃ ϕ ψ, nϕ_ψ = ~(ϕ ⋏ ψ) ∧ nϕ = ~ϕ ∧ nψ = ~ψ) :=
begin
  by_cases h_ϕ1    : ∃ ϕ1, (nϕ = ~ϕ1),
  by_cases h_ψ1    : ∃ ψ1, (nψ = ~ψ1),
  by_cases h_ϕ2_ψ2 : ∃ ϕ2 ψ2, nϕ_ψ = ~(ϕ2 ⋏ ψ2),
  rotate 1,
  refine is_false _, intro h0, rcases h0 with ⟨ϕ, ψ, h0⟩, finish,
  refine is_false _, intro h0, rcases h0 with ⟨ϕ, ψ, h0⟩, finish,
  refine is_false _, intro h0, rcases h0 with ⟨ϕ, ψ, h0⟩, finish,
  rcases h_ϕ1,
end

instance h4 {X : finset formula} {Y : finset (finset formula)} : decidable (∃ nϕ_ψ ∈ X, ∃ A B ∈ Y, ∃ nϕ ∈ A, ∃ nψ ∈ B, (∃ ϕ ψ, nϕ_ψ = ~(ϕ ⋏ ψ) ∧ nϕ = ~ϕ ∧ nψ = ~ψ) ∧ (A = X \ {nϕ_ψ} ∪ {nϕ}) ∧ (B = X \ {nϕ_ψ} ∪ {nψ}) ∧ (Y = {A,B})):=
begin
  exact finset.decidable_dexists_finset,
end



instance    {X : finset formula} {Y : finset (finset formula)} : decidable (nonempty (localRule X Y)) :=
begin
  --by_cases (⊥ ∈ X ∧ Y = ∅) ∨ (∃ ϕ, ϕ ∈ X ∧ ~ϕ ∈ X ∧ Y = ∅) ∨ (∃ ϕ, ~~ϕ ∈ X ∧ Y = { X \ {~~ϕ} ∪ {ϕ} }) ∨ (∃ ϕ ψ, ϕ ⋏ ψ ∈ X ∧ Y = { X \ {ϕ⋏ψ} ∪ {ϕ,ψ} }) ∨ (∃ ϕ ψ, ~(ϕ ⋏ ψ)∈ X ∧ Y = { X \ {~(ϕ⋏ψ)} ∪ {~ϕ}, X \ {~(ϕ⋏ψ)} ∪ {~ψ} }),
  by_cases h0 : ⊥ ∈ X ∧ Y = ∅,
  refine is_true _, cases h0, subst h0_right, fconstructor, exact localRule.bot h0_left,

  by_cases h1 : (∃ ϕ ∈ X, ~ϕ ∈ X ∧ Y = ∅),
  refine is_true _, cases h1 with α, cases h1_h with h1, cases h1_h_h with h2 h3, subst h3, fconstructor, exact localRule.not ⟨h1,h2⟩,

  by_cases h2 : (∃ ϕ, ~~ϕ ∈ X ∧ Y = { X \ {~~ϕ} ∪ {ϕ} }),
  refine is_true _, cases h2 with α, cases h2_h with h2 h3,                           subst h3, fconstructor, exact localRule.neg h2,

  by_cases h3 : (∃ ϕ ψ, ϕ ⋏ ψ ∈ X ∧ Y = { X \ {ϕ⋏ψ} ∪ {ϕ,ψ} }),
  refine is_true _, cases h3 with α, cases h3_h with β, cases h3_h_h with h3 h4,      subst h4, fconstructor, exact localRule.con h3,

  by_cases h4 : (∃ ϕ ψ, ~(ϕ ⋏ ψ)∈ X ∧ Y = { X \ {~(ϕ⋏ψ)} ∪ {~ϕ}, X \ {~(ϕ⋏ψ)} ∪ {~ψ} }),
  refine is_true _, cases h4 with α, cases h4_h with β, cases h4_h_h with h4 h5,      subst h5, fconstructor, exact localRule.nCo h4, 


  refine is_false _,
  refine imp_false.mp _, intro h5, cases h5, cases h5,
  finish, finish, simp at h2, specialize h2 h5_ϕ h5_h, finish, simp at h3, specialize h3 h5_ϕ h5_ψ h5_h, finish, simp at h4, specialize h4 h5_ϕ h5_ψ h5_h, finish,
end







-- If X is not simple, then a local rule can be applied.
-- (page 13)
lemma notSimpleThenLocalRule { X } :
  ¬ simple X → ∃ B, nonempty (localRule X B) :=
begin
  intro notSimple,
  unfold simple at notSimple,
  simp at notSimple,
  rcases notSimple with ⟨ ϕ , ϕ_in_X, ϕ_not_simple ⟩,
  cases ϕ,
  case bottom: { tauto },
  case atom_prop: { tauto },
  case neg: ψ {
    cases ψ,
    case bottom: { tauto, },
    case atom_prop: { tauto, },
    case neg: {
      use { (X \ {~~ψ}) ∪ { ψ } },
      use localRule.neg ϕ_in_X,
    },
    case and: ψ1 ψ2 {
      unfold simpleForm at *,
      use { X \ { ~ (ψ1 ⋏ ψ2) } ∪ {~ψ1}, X \ { ~ (ψ1 ⋏ ψ2) } ∪ {~ψ2} },
      use localRule.nCo ϕ_in_X,
    },
    case box: { unfold simpleForm at *, tauto, },
  },
  case and: ψ1 ψ2 {
      unfold simpleForm at *,
      use { (X \ {ψ1 ⋏ ψ2}) ∪ { ψ1, ψ2 } },
      use localRule.con ϕ_in_X,
  },
  case box: { tauto, },
end

lemma localRulesDecreaseLength { X : finset formula } { B : finset (finset formula) } (r : localRule X B) :
  ∀ Y ∈ B, lengthOfSet Y < lengthOfSet X :=
begin
  cases r,
  all_goals { intros β inB, simp at *, },
  case bot : {
    cases inB, -- no premises
  },
  case not : {
    cases inB, -- no premises
  },
  case neg : X ϕ notnot_in_X {
    subst inB,
    { calc lengthOfSet (insert ϕ (X.erase (~~ϕ)))
         ≤ lengthOfSet (X.erase (~~ϕ)) + lengthOf (ϕ) : by { apply lengthOf_insert_leq_plus, }
     ... < lengthOfSet (X.erase (~~ϕ)) + lengthOf (ϕ) + 2 : by { simp, }
     ... = lengthOfSet (X.erase (~~ϕ)) + lengthOf (~~ϕ) : by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... = lengthOfSet X : lengthRemove X (~~ϕ) notnot_in_X,
    },
  },
  case con : X ϕ ψ in_X {
    subst inB,
    { calc lengthOf (insert ϕ (insert ψ (X.erase (ϕ⋏ψ))))
         ≤ lengthOf (insert ψ (X.erase (ϕ⋏ψ))) + lengthOf ϕ : by { apply lengthOf_insert_leq_plus, }
     ... ≤ lengthOf (X.erase (ϕ⋏ψ)) + lengthOf ψ + lengthOf ϕ : by { simp, apply lengthOf_insert_leq_plus, }
     ... = lengthOf (X.erase (ϕ⋏ψ)) + lengthOf ϕ + lengthOf ψ : by { ring, }
     ... < lengthOf (X.erase (ϕ⋏ψ)) + lengthOf ϕ + lengthOf ψ + 1 : by { unfold lengthOf, simp, }
     ... = lengthOf (X.erase (ϕ⋏ψ)) + lengthOf (ϕ⋏ψ) : by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... = lengthOfSet X : (lengthRemove X (ϕ⋏ψ) in_X)
    },
  },
  case nCo : X ϕ ψ in_X {
    cases inB, -- splitting rule!
    all_goals {
      subst inB,
    },
    { -- f
    calc lengthOfSet (insert (~ϕ) (X.erase (~(ϕ⋏ψ))))
         ≤ lengthOfSet (X.erase (~(ϕ⋏ψ))) + lengthOf (~ϕ) : lengthOf_insert_leq_plus
     ... < lengthOfSet (X.erase (~(ϕ⋏ψ))) + 1 + 1 + lengthOf ϕ + lengthOf ψ :
           by { unfold lengthOf, unfold lengthOfFormula, ring_nf, simp, }
     ... = lengthOfSet (X.erase (~(ϕ⋏ψ))) + lengthOf (~(ϕ⋏ψ)) : by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... = lengthOfSet X : lengthRemove X (~(ϕ⋏ψ)) in_X,
    },
    { -- g
    calc lengthOfSet (insert (~ψ) (X.erase (~(ϕ⋏ψ))))
         ≤ lengthOfSet (X.erase (~(ϕ⋏ψ))) + lengthOf (~ψ) : lengthOf_insert_leq_plus
     ... < lengthOfSet (X.erase (~(ϕ⋏ψ))) + 1 + 1 + lengthOf ϕ + lengthOf ψ :
           by { unfold lengthOf, unfold lengthOfFormula, ring_nf, simp, }
     ... = lengthOfSet (X.erase (~(ϕ⋏ψ))) + lengthOf (~(ϕ⋏ψ)) : by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... = lengthOfSet X : lengthRemove X (~(ϕ⋏ψ)) in_X,
    },
  },
end

lemma atmRuleDecreasesLength { X : finset formula } { ϕ } :
  ~□ϕ ∈ X → lengthOfSet (projection X ∪ {~ϕ}) < lengthOfSet X :=
begin
  intro notBoxPhi_in_X,
  simp,
    have proj_form_lt : ∀ f g, some g = formProjection f → lengthOfFormula g < lengthOfFormula f, {
      intros f g g_is_fP_f, cases f, all_goals { finish, },
    },
    have lengthSingleton : ∀ f, lengthOfFormula f = lengthOfSet { f }, {
      intro f, unfold lengthOfSet, simp,
    },
    have otherClaim : projection X = projection (X.erase (~□ϕ)), {
      ext1 phi,
      rw proj, rw proj,
      simp,
    },
    { calc lengthOfSet (insert (~ϕ) (projection X))
         ≤ lengthOfSet (projection X) + lengthOf (~ϕ) : lengthOf_insert_leq_plus
     ... = lengthOfSet (projection X) + 1 + lengthOf ϕ : by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... < lengthOfSet (projection X) + 1 + 1 + lengthOf ϕ : by { simp, }
     ... = lengthOfSet (projection X) + lengthOf (~□ϕ) : by { unfold lengthOf, unfold lengthOfFormula, ring, }
     ... = lengthOfSet (projection (X.erase (~□ϕ))) + lengthOf (~□ϕ) : by { rw otherClaim, }
     ... ≤ lengthOfSet (X.erase (~□ϕ)) + lengthOf (~□ϕ) : by { simp, apply projection_set_length_leq, }
     ... = lengthOfSet X : lengthRemove X (~□ϕ) notBoxPhi_in_X,
    }
end

-- Definition 8, page 14
-- mixed with Definition 11 (with all PDL stuff missing for now)
-- a local tableau for X, must be maximal
inductive localTableau : finset formula → Type
| byLocalRule { X B } (_ : localRule X B) (next : Π Y ∈ B, localTableau Y) : localTableau X
| sim { X } : simple X → localTableau X

open localTableau



-- Classification of localTableau for simple X
lemma SimplelocalTab {X : finset formula} {T : localTableau X}
            : (simple X) → (∃ h0, T = sim h0) ∨ (∃ h0 h1, T = byLocalRule(@localRule.bot X h0) h1) ∨ (∃ h0 ϕ h1, T = byLocalRule(@localRule.not X h0 ϕ) h1) :=
begin
  intro simple_X,
  cases T, swap 2,
  finish,
  cases T__x,
  finish,
  finish,
  unfold simple at simple_X, specialize simple_X (~~T__x_ϕ) T__x_h, tauto,
  unfold simple at simple_X, specialize simple_X (T__x_ϕ⋏T__x_ψ) T__x_h, tauto,
  unfold simple at simple_X, specialize simple_X (~(T__x_ϕ⋏T__x_ψ)) T__x_h, tauto,
end





-- needed for endNodesOf
instance localTableau_has_sizeof : has_sizeof (Σ {X}, localTableau X) := ⟨ λ ⟨X, T⟩, lengthOfSet X ⟩

-- nodes of a given localTableau
@[simp]
def NodesOf : (Σ X, localTableau X) → finset (finset formula)
| ⟨X, @byLocalRule _ B lr next⟩ := { X } ∪ B.attach.bUnion (λ ⟨Y,h⟩, have lengthOfSet Y < lengthOfSet X := localRulesDecreaseLength lr Y h, NodesOf ⟨Y, next Y h⟩)
| ⟨X, sim _                   ⟩ := { X }



-- Pairs of nodes of a given localTableau
def pairNodesOf : (Σ X, localTableau X) → finset (finset formula × finset formula)
| ⟨X, @byLocalRule _ B lr next⟩ := { (X,X) } ∪ B.attach.bUnion (λ ⟨Y,h⟩, have lengthOfSet Y < lengthOfSet X := localRulesDecreaseLength lr Y h, ({(X,Y), (Y,X)} ∪ pairNodesOf ⟨Y, next Y h⟩))
| ⟨X, sim _                   ⟩ := { (X,X) }




-- A path is a list of nodes in a localTab T.
-- This function appends a head node to every path in Paths (if path.inth 0 ≠ head).
def append (head : finset formula) (Paths : finset (list (finset formula))) : finset (list (finset formula))
                        := finset.bUnion Paths (λ path, {ite (path.inth 0 ≠ head) (head :: path) (path)})      

-- Finset of all paths in a localTableau.
-- 
def all_paths : (Σ root, localTableau root) → finset (list (finset formula))
| ⟨root, @byLocalRule _ B lr next⟩ := {[root]} ∪ (B.attach.bUnion (λ ⟨Y,h⟩, have lengthOfSet Y < lengthOfSet root := localRulesDecreaseLength lr Y h, all_paths ⟨Y, next Y h⟩)) ∪ (append root (B.attach.bUnion (λ ⟨Y,h⟩, have lengthOfSet Y < lengthOfSet root := localRulesDecreaseLength lr Y h, append Y (all_paths ⟨Y, next Y h⟩))))

| ⟨root, sim _                   ⟩ := {[root]} 

-- Collection of all paths starting at head and ending at tail in localTab rootT.
-- NEED TO PROVE LATER: localRulesDecreaseLength implies length of all paths is ≤ lengthOfSet(head)+1
def Paths (head  tail : finset formula) (rootT : Σ root, localTableau root) (n : ℕ := lengthOfSet(head)+1) : finset (list (finset formula))

    :=  finset.filter (λ l, (list.head' l = some head) ∧ (list.last' l = some tail) ∧ (list.length l ≤ n)) (all_paths rootT)


#reduce (10-400)


#reduce (2 ∈ [1,2,3])

example : ([{p}] ++ [{q}, {r}]).inth 2 = ({r} : finset formula) :=
begin
  exact rfl,
end
example : ([{p}] ++ [{q}, {r}]).inth 3 = (∅ : finset formula) :=
begin
  exact rfl,
end



-- OLD DEFINITION OF DIRECT SUCCESSOR
-- nodes that are the direct successor of node A
-- w.r.t. a given localTableau
def SuccOf (A : finset formula) : (Σ X, localTableau X) → finset (finset formula)
| ⟨X, @byLocalRule _ B lr next⟩ := 
ite (A = X) (NodesOf ⟨X, @byLocalRule _ B lr next⟩) (B.attach.bUnion (λ ⟨Y,h⟩, have lengthOfSet Y < lengthOfSet X := localRulesDecreaseLength lr Y h, SuccOf ⟨Y, next Y h⟩))

| ⟨X, sim _                   ⟩ := {(ite (A = X) A ∅)} 











-- open end nodes of a given localTableau
@[simp]
def endNodesOf : (Σ X, localTableau X) → finset (finset formula)
| ⟨X, @byLocalRule _ B lr next⟩ := B.attach.bUnion (λ ⟨Y,h⟩, have lengthOfSet Y < lengthOfSet X := localRulesDecreaseLength lr Y h, endNodesOf ⟨Y, next Y h⟩)
| ⟨X, sim _                   ⟩ := { X }

@[simp]
lemma botNoEndNodes {X h n} : endNodesOf ⟨X, localTableau.byLocalRule (@localRule.bot X h) n⟩ = ∅ := by { unfold endNodesOf, simp, }

@[simp]
lemma notNoEndNodes {X h ϕ n} : endNodesOf ⟨X, localTableau.byLocalRule (@localRule.not X h ϕ) n⟩ = ∅ := by { unfold endNodesOf, simp, }

lemma negEndNodes {X ϕ h n} : endNodesOf ⟨X, localTableau.byLocalRule (@localRule.neg X ϕ h) n⟩ =
  endNodesOf ⟨X \ {~~ϕ} ∪ {ϕ}, n (X \ {~~ϕ} ∪ {ϕ}) (by simp)⟩ :=
begin
  ext1,
  simp only [endNodesOf, finset.mem_singleton, finset.mem_bUnion, finset.mem_attach, exists_true_left, subtype.exists],
  split,
  { intro lhs, rcases lhs with ⟨b,bDef,bIn⟩, subst bDef, exact bIn, },
  { intro rhs, use (X \ {~~ϕ} ∪ {ϕ}), split, exact rhs, refl, },
end

lemma conEndNodes {X ϕ ψ h n} : endNodesOf ⟨X, localTableau.byLocalRule (@localRule.con X ϕ ψ h) n⟩ =
  endNodesOf ⟨X \ {ϕ⋏ψ} ∪ {ϕ,ψ}, n (X \ {ϕ⋏ψ} ∪ {ϕ,ψ}) (by simp)⟩ :=
begin
  ext1,
  simp only [endNodesOf, finset.mem_singleton, finset.mem_bUnion, finset.mem_attach, exists_true_left, subtype.exists],
  split,
  { intro lhs, rcases lhs with ⟨b,bDef,bIn⟩, subst bDef, exact bIn, },
  { intro rhs, use (X \ {ϕ⋏ψ} ∪ {ϕ,ψ}), split, exact rhs, refl, },
end

lemma nCoEndNodes {X ϕ ψ h n} : endNodesOf ⟨X, localTableau.byLocalRule (@localRule.nCo X ϕ ψ h) n⟩ =
  endNodesOf ⟨X \ {~(ϕ⋏ψ)} ∪ {~ϕ}, n (X \ {~(ϕ⋏ψ)} ∪ {~ϕ}) (by simp)⟩
  ∪ endNodesOf ⟨X \ {~(ϕ⋏ψ)} ∪ {~ψ}, n (X \ {~(ϕ⋏ψ)} ∪ {~ψ}) (by simp)⟩ :=
begin
  ext1,
  simp only [endNodesOf, finset.mem_singleton, finset.mem_bUnion, finset.mem_attach, exists_true_left, subtype.exists],
  split,
  { intro lhs, rcases lhs with ⟨b,bDef,bIn⟩,
    simp only [finset.mem_insert, finset.mem_singleton] at bDef, cases bDef with bD1 bD2,
    { subst bD1, simp, left, exact bIn, },
    { subst bD2, simp, right, exact bIn, },
  },
  { intro rhs, rw finset.mem_union at rhs, cases rhs,
    { use (X \ {~(ϕ⋏ψ)} ∪ {~ϕ}), split, exact rhs, simp, },
    { use (X \ {~(ϕ⋏ψ)} ∪ {~ψ}), split, exact rhs, simp, },
  },
end

lemma endNodesSimple {Z} {T : localTableau Z} : ∀ en ∈ endNodesOf ⟨Z, T⟩, simple en :=
begin
  induction T with Y B locRuleYB Z_next IH Y simple_Y, swap 2,
  intros en h0, simp at h0, finish,
  dsimp at IH, intros en h0, norm_num at h0, cases h0 with a a_h, cases a_h with h0 h1,
  exact IH a ((iff.refl (a ∈ B)).mpr h0) en h1,
end

lemma SuccOfEndNodes {en Z : finset formula} {T : localTableau Z} 
                    :  (en ∈ endNodesOf ⟨Z,T⟩) → (SuccOf en ⟨Z,T⟩ ⊆ {en}) := 
begin
  revert en,
  induction T with Y B locRuleYB Y_next IH Y simple_Y, swap 2,
  sorry, sorry,
end




-- Definition 16, page 29
inductive closedTableau : finset formula → Type
| loc {X} (lt : localTableau X) : (Π Y ∈ endNodesOf ⟨X, lt⟩, closedTableau Y) → closedTableau X
| atm {X ϕ} : ~□ϕ ∈ X → simple X → closedTableau (projection X ∪ {~ϕ}) → closedTableau X








inductive provable : formula → Prop
| byTableau {φ : formula} : closedTableau { ~ φ } → provable φ

-- Definition 17, page 30
def inconsistent : finset formula → Prop
| X := nonempty (closedTableau X)

def consistent : finset formula → Prop
| X := ¬ inconsistent X


noncomputable instance (X) : decidable (consistent X) := classical.dec (consistent X)



-- annoying def, ideally this would give a tableau, not nonempty Prop
def existsLocalTableauFor : ∀ N α, N = lengthOf α → nonempty (localTableau α) :=
begin
  intro N,
  apply nat.strong_induction_on N,
  intros n IH α nDef,
  have canApplyRule := em (¬ ∃ B, nonempty (localRule α B)),
  cases canApplyRule,
  { split,
    apply localTableau.sim,
    by_contradiction hyp,
    have := notSimpleThenLocalRule hyp,
    tauto,
  },
  { simp at canApplyRule,
    cases canApplyRule with B r_exists,
    cases r_exists with r,
    cases r,
    case bot : _ h {
      have t := localTableau.byLocalRule (localRule.bot h) _, use t,
      intro Y, intro Y_in_empty, tauto,
    },
    case not : _ _ h {
      have t := localTableau.byLocalRule (localRule.not h) _, use t,
      intro Y, intro Y_in_empty, tauto,
    },
    case neg : _ f h {
      have t:= localTableau.byLocalRule (localRule.neg h) _, use t,
      intros Y Y_def,
      have rDec := localRulesDecreaseLength (localRule.neg h) Y Y_def,
      subst nDef,
      specialize IH (lengthOf Y) rDec Y (refl _),
      apply classical.choice IH,
    },
    case con : _ f g h {
      have t := localTableau.byLocalRule (localRule.con h) _, use t,
      intros Y Y_def,
      have rDec := localRulesDecreaseLength (localRule.con h) Y Y_def,
      subst nDef,
      specialize IH (lengthOf Y) rDec Y (refl _),
      apply classical.choice IH,
    },
    case nCo : _ f g h {
      have t := localTableau.byLocalRule (localRule.nCo h) _, use t,
      intros Y Y_def,
      have rDec := localRulesDecreaseLength (localRule.nCo h) Y Y_def,
      subst nDef,
      specialize IH (lengthOf Y) rDec Y (refl _),
      apply classical.choice IH,
    },
  }
end

lemma endNodesOfLEQ {X Z ltX} :
  Z ∈ endNodesOf ⟨X, ltX⟩ → lengthOf Z ≤ lengthOf X :=
begin
  induction ltX,
  case byLocalRule : Y B lr next IH {
    intro Z_endOf_Y,
    have foo := localRulesDecreaseLength lr Y,
    unfold endNodesOf at Z_endOf_Y,
    simp at Z_endOf_Y,
    rcases Z_endOf_Y with ⟨W, W_in_B, Z_endOf_W⟩,
    apply le_of_lt,
    { calc lengthOf Z
         ≤ lengthOf W : IH W W_in_B Z_endOf_W
     ... < lengthOf Y : localRulesDecreaseLength lr W W_in_B },
  },
  case sim : a b {
    intro Z_endOf_Y,
    unfold endNodesOf at Z_endOf_Y,
    finish,
  },
end

lemma endNodesOfLocalRuleLT {X Z B next lr} :
  Z ∈ endNodesOf ⟨X, (@localTableau.byLocalRule _ B lr next)⟩ → lengthOf Z < lengthOf X :=
begin
  intros ZisEndNode,
  rw endNodesOf at ZisEndNode,
  simp only [finset.mem_bUnion, finset.mem_attach, exists_true_left, subtype.exists] at ZisEndNode,
  rcases ZisEndNode with ⟨a,a_in_WS,Z_endOf_a⟩,
  change Z ∈ endNodesOf ⟨a, next a a_in_WS⟩ at Z_endOf_a,
  { calc lengthOf Z
       ≤ lengthOf a : endNodesOfLEQ Z_endOf_a
   ... < lengthOfSet X : localRulesDecreaseLength lr a a_in_WS },
end
