theory BmethodSimplified

imports Simulation

begin

section {* B machine *}

text {* 
  A B machine is a state-transition system together with an invariant,
  i.e. a state predicate.
*}

record ('st, 'ev) B_machine =
  lts :: "('st, 'ev) LTS"
  invariant :: "'st \<Rightarrow> bool"
  
text {* 
  A B machine is considered correct when all the reachable states 
  satisfy the invariant.
*}

definition sound_B_machine :: "('st, 'ev) B_machine \<Rightarrow> bool" where
  "sound_B_machine m \<equiv> \<forall>s \<in> states (lts m). invariant m s"

text {* 
  The following theorem states two sufficient conditions to establish 
  that a machine is correct.
*}

theorem machine_po:
  assumes "\<And>s. s \<in> init (lts m) \<Longrightarrow> invariant m s"
      and "\<And>t. \<lbrakk>t \<in> trans (lts m); invariant m (src t)\<rbrakk> \<Longrightarrow> invariant m (dst t)"
    shows "sound_B_machine m"
  unfolding sound_B_machine_def using assms by (auto elim: states.induct)


section {* B refinement *}

text {* 
  A B refinement is composed of an \emph{abstract} and a \emph{concrete}
  LTS related by a \emph{gluing invariant}. The gluing invariant is a
  binary predicate over the states of the abstract LTS and the states
  of the concrete one. 
*}

(* SM: Should we allow for the two LTSs to have different state types? *)
record ('st, 'ev) B_refinement =
  abstract :: "('st, 'ev) LTS"     -- "the abstract component"
  concrete :: "('st, 'ev) LTS"     -- "the concrete component "
  invariant :: "'st \<times> 'st \<Rightarrow> bool" -- "gluing invariant"

text {* 
  A refinement is considered \emph{sound} if the invariant establishes
  a simulation from the concrete component by the abstract component.
  It then follows that every concrete execution corresponds to some
  execution of the abstract LTS. In the following definition, note that
  Isabelle's operator @{text "Collect"} yields the extension of a predicate.
*}

definition sound_B_refinement :: "('st, 'ev) B_refinement \<Rightarrow> bool" where
  "sound_B_refinement r \<equiv> 
  (concrete r, abstract r) \<in> simulation (Collect (invariant r))"

text {* 
  In particular, the abstract LTS in a sound refinement simulates
  the concrete LTS.
*}

lemma refinement_sim: 
  assumes "sound_B_refinement r"
  shows "concrete r \<preceq> abstract r"
  using assms unfolding sound_B_refinement_def simulated_def by auto

lemma refinement_sim2: 
  "\<lbrakk> sound_B_refinement r \<rbrakk> \<Longrightarrow> concrete r \<preceq> abstract r"
using assms unfolding sound_B_refinement_def simulated_def by auto

text {*
  The identity refinement relates an LTS with itself; the invariant
  requires the two states to be identical.
*}

definition refinement_id :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) B_refinement" where
  "refinement_id l \<equiv> \<lparr> abstract = l, 
                       concrete = l, 
                       invariant = (\<lambda>(s,t). s = t) \<rparr>"

text {* The identity refinement is sound. *}

lemma "sound_B_refinement (refinement_id l)"
  unfolding refinement_id_def sound_B_refinement_def simulation_def sim_transition_def
  by auto

text {* 
  Given two refinements, the following operation defines their composition.
  It is meaningful only if the concrete LTS of the first refinement agrees
  with the abstract LTS of the second one.
*}

definition refinement_compose  where
"refinement_compose r r' \<equiv> 
 \<lparr> abstract = abstract r, concrete = concrete r',
   invariant = \<lambda> p . p \<in> Collect (invariant r') O Collect (invariant r) \<rparr>"

text {*
  The composition of two sound refinements whose intermediate LTSs agree
  yields a sound refinement.
*}

lemma refinement_compose_soundness:
  "\<lbrakk> sound_B_refinement r ; sound_B_refinement r'; concrete r = abstract r'\<rbrakk>
     \<Longrightarrow> sound_B_refinement (refinement_compose r r')"
  using assms simulation_composition
  unfolding sound_B_refinement_def refinement_compose_def
  by fastforce

text {* 
  We now verify some simple properties of refinement composition.
  First, identity refinement is left-neutral.
*}

lemma refinement_compose_neutral_left:
  "refinement_compose (refinement_id (abstract r)) r = r" (is "?lhs = r")
proof -
  have "abstract ?lhs = abstract r"
       "concrete ?lhs = concrete r"
       "invariant ?lhs = invariant r"
    unfolding refinement_compose_def refinement_id_def by auto
  thus ?thesis by simp
qed

text {* 
  Similarly, identity refinement is right-neutral for refinement composition.
*}

lemma refinement_compose_neutral_right:
  "refinement_compose r (refinement_id (concrete r)) = r" (is "?lhs = r")
proof -
  have "abstract ?lhs = abstract r"
       "concrete ?lhs = concrete r"
       "invariant ?lhs = invariant r"
    unfolding refinement_compose_def refinement_id_def by auto
  thus ?thesis by simp
qed

text {* 
  Finally, refinement composition is associative.
*}
lemma refinement_compose_associative:
  "refinement_compose (refinement_compose r r') r'' =
   refinement_compose r (refinement_compose r' r'')"
   unfolding refinement_compose_def by auto


section {* B development *}

text {* 
  A B design is represented as a sequence of refinements.
  The idea is that the abstract LTS of the first refinement is
  gradually refined into the concrete LTS of the last refinement.
*}
(* sm: If we were to generalize refinements so that states of the
   LTSs can be of different types then we would be in trouble in
   assigning a type to a design. *)
type_synonym ('st, 'ev) B_design = "('st, 'ev) B_refinement list"

text {* 
  A design is \emph{sound} if every refinement in the list is sound
  and if the concrete LTS of every refinement agrees with the abstract
  LTS of its successor in the design.
*}
definition sound_B_design where
  "sound_B_design refs \<equiv> \<forall>i < size refs.
     sound_B_refinement (refs!i)
   \<and> (Suc i < size refs \<longrightarrow> concrete (refs!i) = abstract (refs!(Suc i)))"

text {* 
  In a sound design, the abstract LTS of the first refinement
  simulates the concrete LTS of the last refinement.
*}
lemma design_sim:
  assumes refs: "sound_B_design refs" and nempty: "refs \<noteq> []"
  shows "concrete (last refs) \<preceq> abstract (hd refs)"
proof -
  { fix i
    have "i < size refs \<Longrightarrow> concrete (refs!i) \<preceq> abstract (refs!0)" (is "?P i \<Longrightarrow> ?Q i")
    proof (induct i)
      assume "0 < size refs"
      with refs show "?Q 0" 
        unfolding sound_B_design_def by (auto intro: refinement_sim)
    next
      fix j
      assume ih: "?P j \<Longrightarrow> ?Q j" and j: "Suc j < size refs"
      hence "?Q j" by auto
      moreover
      from refs j 
      have "concrete (refs!j) = abstract (refs!(Suc j))" 
           "concrete (refs!(Suc j)) \<preceq> abstract (refs!(Suc j))"
        unfolding sound_B_design_def by (auto intro: refinement_sim)
      ultimately show "?Q (Suc j)" by (auto elim: simulates_transitive)
    qed
  }
  with nempty show ?thesis by (simp add: hd_conv_nth last_conv_nth)
qed

text {* 
  Finally, we define a B development as consisting of a B machine
  and a B design. A sound B development consists of a sound B
  machine and a sound B design such that the abstract LTS of the
  first refinement in the design is the LTS of the B machine.
*}

record ('st, 'ev) B_development =
  spec :: "('st, 'ev) B_machine"
  design :: "('st, 'ev) B_design"

definition sound_B_development where
  "sound_B_development dev \<equiv> 
    sound_B_machine (spec dev) \<and> sound_B_design (design dev) \<and>
    (design dev \<noteq> [] \<longrightarrow> (lts (spec dev)) = (abstract (hd (design dev))))"

text {* 
  It follows that in a sound B development, the concrete LTS of the
  final refinement simulates the initial specification.
*}

theorem development_sim:
  assumes "sound_B_development d" and "design d \<noteq> []"
  shows "concrete (last (design d)) \<preceq> lts (spec d)"
  using assms by(metis design_sim sound_B_development_def)

end
