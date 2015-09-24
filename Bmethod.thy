theory Bmethod

imports Main LTS Simulation

begin

section {* B machine *}

text {* A B machine is a state-transition system together with an invariant. An invariant
is a predicate on the states of the system. *}

record ('st, 'ev) B_machine =
  lts :: "('st, 'ev) LTS"
  invariant :: "'st \<Rightarrow> bool"
  
text {* A B machine is considered correct when all the reachable states satisfy the
        invariant. *}

definition sound_B_machine :: "('st, 'ev) B_machine \<Rightarrow> bool" where
  "sound_B_machine m \<equiv> \<forall> s \<in> states (lts m) . (invariant m) s"

text {* The following theorem states two sufficient conditions to establish that a machine is
correct. *}

theorem machine_po:
  assumes po_init: "\<forall> s \<in> init (lts m) . (invariant m) s" and 
          po_step: "\<forall> t \<in> trans (lts m) . (invariant m)(src t) \<longrightarrow> (invariant m)(dst t)"
  shows "sound_B_machine m"
sorry

text {*
  proof -
  from assms have "\<forall> s \<in> states (lts m). (invariant m) s"
    proof(rule reachable_induct_predicate[of  "(lts m)" "(invariant m)"])
    qed
  then show ?thesis by (simp only:sound_B_machine_def) 
*}

section {* B refinement *}

text {* A B refinement is composed of an \emph{abstract} component and a \emph{concrete}
component related by an \emph{invariant}. The invariant is a binary relation from the states 
of the abstract component to the states of the concrete one. *}

record ('st, 'ev) B_refinement =
  abstract :: "('st, 'ev) LTS" -- "the abstract component"
  concrete :: "('st, 'ev) LTS"  -- "the concrete component "
  invariant :: "'st \<times> 'st \<Rightarrow> bool" -- "relates the abstract to the concrete component"
  
text {* A refinement is considered \emph{sound} if the invariant establishes a simulation
from the concrete component by the abstract component: every execution of the former corresponds
to some execution of the latter. Isabelle's operator @{text "Collect"}, applied to a relation,
returns its characteristic predicate. *}

definition sound_B_refinement :: "('st, 'ev) B_refinement \<Rightarrow> bool" where
  "sound_B_refinement r \<equiv> simulation (Collect (invariant r)) (concrete r) (abstract r)"

text {* Thus, in a refinement, the abstract component simulates its concrete counterpart: *}

lemma refinement_sim: "\<lbrakk> sound_B_refinement r \<rbrakk> \<Longrightarrow> (abstract r) \<preceq> (concrete r)"
sorry
text {*  unfolding sound_B_refinement_def simulates_def by auto *}

text {* A special refinement is one that does not change anything, namely the
identity refinement. It is defined as a function that takes a machine and
returns the identity refinement. *}

definition refinement_id :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) B_refinement" where
"refinement_id m \<equiv> \<lparr> abstract = m, concrete = m, invariant = (\<lambda> p . fst p = snd p) \<rparr>"

text {* The identity refinement is sound: *}

lemma "sound_B_refinement(refinement_id m)"
sorry
text {*
unfolding refinement_id_def sound_B_refinement_def simulation_def sim_lts_init_def sim_lts_trans_def sim_transition_def
by auto
*}

text {* Next, we definement composition of refinements. This is a partial operation as it is only 
meaningful when the composed refinements have matching set of states. *}

definition refinement_compose :: "('st, 'ev) B_refinement \<Rightarrow> ('st, 'ev) B_refinement \<Rightarrow> ('st, 'ev) B_refinement option" where
"refinement_compose r1 r2 \<equiv> 
  (if concrete r1 = abstract r2 then
  Some \<lparr> abstract = abstract r1, concrete = concrete r2, 
         invariant = \<lambda> p . p \<in> Collect (invariant r2) O Collect (invariant r1) \<rparr>
  else None)"

text {* The following lemma states that the composition of two refinements @{text "r1"} and
@{text "r2"} is defined whenever the concrete component of @{text "r1"} and the abstract
component of @{text "r2"} are equal. The abstract (resp. concrete) component of the result
are the abstract (resp. concrete) component of @{text "r1"} (resp. @{text "r2"}), and the
invariant is obtained by relational composition of the invariants of @{text "r1"} and @{text "r2"}.*}

lemma refinement_compose_matching:
  "\<lbrakk> concrete r1 = abstract r2 \<rbrakk> \<Longrightarrow>
   refinement_compose r1 r2 = 
     Some \<lparr> abstract = abstract r1,
            concrete = concrete r2, 
            invariant = \<lambda> p . p \<in> Collect (invariant r2) O Collect (invariant r1) \<rparr>"
unfolding refinement_compose_def by auto

text {* The composition of two sound refinements, when it is defined, is sound. This is 
the object of the following lemma @{text "refinement_compose_soundness"}: *}

lemma refinement_compose_soundness:
  assumes 
    sound_r1: "sound_B_refinement r1" and sound_r2: "sound_B_refinement r2" and
    "refinement_compose r1 r2 = Some r"
  shows "sound_B_refinement r"
proof(cases "concrete r1 = abstract r2")
  case False
    hence "refinement_compose r1 r2 = None" by (simp add:refinement_compose_def)
    with assms(3)
    have "Some r = None" by simp
    thus ?thesis by simp
next
  case True
  assume glue: "concrete r1 = abstract r2"
  show "sound_B_refinement r" unfolding sound_B_refinement_def refinement_compose_def
  proof -
    def rs1 \<equiv> "Collect (invariant r1)"
    def rs2 \<equiv> "Collect (invariant r2)"
    let ?rs = "rs2 O rs1"
    def rv \<equiv> "\<lparr> abstract = abstract r1, concrete = concrete r2, invariant = \<lambda> p . (p \<in> ?rs) \<rparr>"
    with glue and assms(3) have value_r: "r = rv" unfolding refinement_compose_def rs2_def rs1_def rv_def 
      by simp
    with sound_r2 have rs2: "simulation rs2 (concrete r2) (abstract r2)"
      unfolding simulation_def sound_B_refinement_def rs2_def by auto
    with sound_r1 and glue have rs1: "simulation rs1 (abstract r2) (abstract r1)"
      unfolding simulation_def sound_B_refinement_def rs1_def by auto
    with rs2 have "simulation (rs2 O rs1) (concrete r2) (abstract r1)"  
      by (metis simulation_composition)
    with value_r show "simulation (Collect (invariant r)) (concrete r) (abstract r)"
      unfolding rv_def rs1_def rs2_def by simp
  qed
qed

text {* We now want to verify that our definition of refinement composition satisfies
some simple properties. First any identity refinement is left-neutral: *}

lemma refinement_compose_neutral_left:
  "refinement_compose (refinement_id (abstract r)) r = Some r"
  unfolding refinement_compose_def
proof-
  have "concrete (refinement_id (abstract r)) = abstract r"
    unfolding refinement_id_def by simp
moreover
  let ?invariant = "\<lambda>p. p \<in> Collect (invariant r) O Collect (invariant (refinement_id (abstract r)))"
  let ?r = "\<lparr>abstract = abstract (refinement_id (abstract r)), concrete = concrete r, invariant = ?invariant\<rparr>"
  have "Some ?r = Some r"
    proof -
      have "abstract (refinement_id (abstract r)) = abstract r" unfolding refinement_id_def by simp
    moreover
      have "?invariant = (\<lambda>p. p \<in> Collect (invariant r))"
        unfolding refinement_id_def relcomp_def by auto
    ultimately show ?thesis by simp
    qed
ultimately
  show "(if concrete (refinement_id (abstract r)) = abstract r then Some ?r else None) = Some r" 
    by simp
qed

text {* Second, any identity refinement is right-neutral for refinement composition. *}

lemma refinement_compose_neutral_right:
  "refinement_compose r (refinement_id (concrete r)) = Some r"
  unfolding refinement_compose_def
proof -
  have "concrete r = abstract (refinement_id (concrete r))"
    unfolding refinement_id_def by simp
moreover
  let ?invariant = "\<lambda>p. p \<in> Collect (invariant (refinement_id (concrete r))) O Collect (invariant r)"
  let ?r = "\<lparr>abstract = abstract r, concrete = concrete (refinement_id (concrete r)), invariant = ?invariant\<rparr>"
  have "?r = r"
  proof-
    have "concrete(refinement_id(concrete r)) = concrete r" 
      unfolding refinement_id_def by simp
  moreover
    have "?invariant = (\<lambda>p. p \<in> Collect (invariant r))"
      unfolding refinement_id_def relcomp_def by auto
  ultimately
    show ?thesis by simp
  qed
ultimately
  show "(if concrete r = abstract (refinement_id (concrete r)) then Some ?r else None) = Some r"
    by simp
qed
  
text {* Last, refinement composition is associative. The expression of this
property is not as straightforward as we could expect due to the partialness
of composition. *}

lemma refinement_compose_associative:
  "\<lbrakk> sound_B_refinement r1; sound_B_refinement r2; sound_B_refinement r3;
     concrete r1 = abstract r2; concrete r2 = abstract r3 \<rbrakk> \<Longrightarrow>
  \<exists> r12 r23 . Some r12 = refinement_compose r1 r2 \<and> 
         Some r23 = refinement_compose r2 r3 \<and>
         refinement_compose r12 r3 = refinement_compose r1 r23"
proof(simp add:sound_B_refinement_def refinement_compose_def, auto)
qed

section {* B development *}

text {* A B development is a specification and the development of an implementation of that
specification by stepwise refinements. We first provide a formalization of design, as a list
of refinements: *}

type_synonym ('st, 'ev) B_design = "('st, 'ev) B_refinement list"

text {* We specify a predicate @{text "sound_B_design"}, responsible for identifying sound 
developments: each refinement is sound, and the chain of refinements is continuous, i.e. the
concrete component of a refinement is the abstract component of the next refinement: *}

inductive sound_B_design :: "('st, 'ev) B_design \<Rightarrow> bool" where
  base: "sound_B_design []" |
  step: "\<lbrakk> sound_B_refinement x; xs \<noteq> []; concrete x = abstract (hd xs); sound_B_design xs \<rbrakk> \<Longrightarrow> 
           sound_B_design (x # xs)"

text {* In such a design, by transitivity of the simulates relation, the abstract component of the 
first refinement simulates the concrete component of the last refinement: *}

lemma 
  design_sim: "\<lbrakk> sound_B_design dev; dev \<noteq> [] \<rbrakk>  \<Longrightarrow> (abstract(hd dev)) \<preceq> (concrete (last dev))"
proof(induct rule:sound_B_design.induct, simp, simp)
  fix x xs
  assume "sound_B_refinement x" "concrete x = abstract (hd xs)"
         "abstract (hd xs) \<preceq> concrete (last xs)"
  from `sound_B_refinement x` have "abstract x \<preceq> concrete x" by (rule refinement_sim)
  with `concrete x = abstract (hd xs)` `abstract (hd xs) \<preceq> concrete (last xs)`
  show "abstract x \<preceq> concrete (last xs)" by (metis simulates_transitive)
qed

text {* Eventually, we give a formalization of a B development as a pair formed by a specification,
namely a B machine, and a design: *}

record ('st, 'ev) B_development =
  spec :: "('st, 'ev) B_machine"
  design :: "('st, 'ev) B_design"

text {* Then a B development is sound when the machine and the design are sound. Moreover, the
design must have the specification machine as initial abstract component: *}

definition sound_B_development :: "('st, 'ev) B_development \<Rightarrow> bool" where
  "sound_B_development dev \<equiv> 
    sound_B_machine (spec dev) \<and> sound_B_design (design dev) \<and>
    (design dev \<noteq> [] \<longrightarrow> (lts (spec dev)) = (abstract (hd (design dev))))"

text {* The following theorem states that, in a sound B development, the initial specification
  simulates the concrete component of the final refinement of the design: *}

theorem development_sim: 
  "\<lbrakk> sound_B_development d ; design d \<noteq> [] \<rbrakk> \<Longrightarrow> lts (spec d) \<preceq> concrete (last (design d))"
  by(metis design_sim sound_B_development_def)

end
