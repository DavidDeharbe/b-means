theory Bmethod

imports Simulation
begin

text {* 
  In theory @{text "Simulation"}, we consider that when a LTS $l$ is
  simulated by $l'$, then for a transition $t$ in $l$, on some event
  $e$, to be simulated, one needs a transition $t'$ in $l'$ that
  simulates $t$. In particular, $t$ and $t'$ share the same event $e$
  as their label.

  This condition imposes stronger constraints than needed in full
  generality to reflect the exact conditions relating a refinement to
  its abstraction in the B method. In particular it requires that the
  simulating LTS must react to the same set of events as the simulated
  LTS. This is the case in B only when operations have the same domain
  in the abstraction and in the refinement. However, in general,
  operations in the refinement may have weaker preconditions than in
  the abstraction. To phrase this rule in terms of events, the
  refinement LTS may accept more events than the abstraction LTS. It
  only needs to be simulated, in the classic sense, on the domain
  (i.e. set of accepted events) as the abstraction.

  Indeed, in B, a refinement is allowed to react to some events that
  would not be allowed in its abstract counterpart. In this theory,
  the notion of simulation is redefined (as @{text "simulation_B"}) to
  take this into account.

   We first introduce auxiliary definitions for some useful
   concepts. The function @{text "outgoing_trans"}, given a LTS and a
   state, returns the set of outgoing transitions in that state.  
*}

definition
  outgoing_trans :: "('st, 'ev) LTS \<Rightarrow> 'st \<Rightarrow> ('st, 'ev) Tr set"
where
  "outgoing_trans l s \<equiv> { t | t . t \<in> trans l \<and> src t = s}"

text {*
  The function @{text "accepted_events"}, given an LTS and a state,
  returns the set of events that label the outgoing transitions in
  that state. It corresponds to the operations and the corresponding
  parameter valuations that are applicable in that state.  
*}

definition
  accepted_events :: "('st, 'ev) LTS \<Rightarrow> 'st \<Rightarrow> 'ev set"
where
  "accepted_events l s \<equiv> lbl ` (outgoing_trans l s)"
(*  "accepted_events l s \<equiv> { e | e t . t \<in> outgoing_trans l s \<and> lbl t = e}" *)

text {*
  We now provide the formalization of the concept of simulation
  corresponding to the relation between the abstract and concrete
  counterparts of a refinement in the B method.
*}
definition simulation_B :: "'st rel \<Rightarrow> ('st, 'ev) LTS rel" where
  (* sm: added inclusion of accepted events and slightly simplified remaining definition *)
  "simulation_B r \<equiv> { (l,l') | l l'.
     (\<forall>s \<in> init l. \<exists>s' \<in> init l'. (s, s') \<in> r)
   \<and> (\<forall>s s'. (s, s') \<in> r \<longrightarrow>
         accepted_events l' s' \<subseteq> accepted_events l s \<and>
         (\<forall>t \<in> outgoing_trans l s.
             lbl t \<in> accepted_events l' s' \<longrightarrow> 
             (\<exists>t' \<in> outgoing_trans l' s'. 
                  src t' = s' \<and> lbl t' = lbl t \<and> (dst t, dst t') \<in> r))) }"

definition is_simulated_by_B (infixl "\<preceq>B" 50)
  where "l \<preceq>B l' \<equiv> \<exists>r. (l,l') \<in> simulation_B r"

text {*
   We have that the composition of two simulation relations is
   a simulation relation.
*}

lemma simulation_B_composition:
  assumes "(l, l') \<in> simulation_B r" and "(l', l'') \<in> simulation_B r'"
  shows "(l, l'') \<in> simulation_B (r O r')"
  using assms unfolding simulation_B_def sim_transition_def relcomp_unfold
  by fastforce

lemma simulates_B_transitive:
  assumes "l \<preceq>B l'" and "l' \<preceq>B l''"
  shows   "l \<preceq>B l''"
  using assms simulation_B_composition
  unfolding is_simulated_by_B_def
  by blast

definition run_accepted_events :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) Run \<Rightarrow> 'ev set" where 
"run_accepted_events l r \<equiv> 
   if r = [] then UNION (init l) (accepted_events l)
   else accepted_events l (dst (last r))"

text {* 
  The external, or observable, behavior of an LTS is an expression of
  the events to which the LTS responds. The observable behavior is
  then a pair composed of the list of the successive events found
  along a \emph{run} and the set of events that are accepted when the
  run has reached the last state.

  The type corresponding to such observations is defined as follows:
*}
type_synonym 'ev TrB = "'ev list * 'ev set"

text {*
  Next, the function @{text run_trace} maps observations of internal
  behavior to observations of external behavior.
*}

definition run_trace :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) Run \<Rightarrow> 'ev TrB" where 
  "run_trace l r \<equiv> (map lbl r, run_accepted_events l r)"

text {*
  The following function returns the external behavior of an LTS, as
  the set of its traces.
*}

definition traces_B :: "('st, 'ev) LTS \<Rightarrow> 'ev TrB set" where
  "traces_B l \<equiv> (run_trace l) ` (runs l)"

text {*
  At that point, we propose a few lemmas, without proofs. They may, or
  may not, be useful to prove more interesting properties.
*}
lemma run_trace_empty_inv:
  "([], UNION (init l) (accepted_events l)) \<in> traces_B l"
sorry

lemma run_trace_inv:
assumes
   "r \<in> runs l" and "tr = run_trace l r" and  "tr \<in> traces_B l" and "acc = snd tr"
and 
   "r \<noteq> []" and "t \<in> trans l" and "src t = dst (last r)" and "lbl t \<in> acc"
shows
   "run_trace l (r @ [t]) \<in> traces_B l"
sorry

text {*
  It would be interesting to come up with a proof of the following theorem. It
  establishes a property on the traces of between LTSes that relate through
  the (B inspired notion of) simulation.
*}
lemma sim_traces_B:
  assumes sim: "l \<preceq>B l'" and tr: "(tr, acc) \<in> traces_B l"
  shows "\<exists> (tr', acc') \<in> traces_B l'.
          acc \<supseteq> acc' \<and>
          (tr = tr' \<or> prefix tr' tr \<and> (\<exists> d \<in> acc'. prefixeq (tr' @ [d]) tr))"
sorry

(* 
  -------------------------------------------------------------------------
  -------------------------------------------------------------------------
  dd: follows a lightly edited copy of the contents of BMethod.thy, where
  the editions correspond to updates required by the development of the new
  notion of simulation.
  -------------------------------------------------------------------------
  -------------------------------------------------------------------------
*)

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
  assumes po_init: "\<And>s. s \<in> init (lts m) \<Longrightarrow> invariant m s"
  and po_step: "\<And>t. \<lbrakk>t \<in> trans (lts m); invariant m (src t)\<rbrakk> \<Longrightarrow> invariant m (dst t)"
  shows "sound_B_machine m"
  unfolding sound_B_machine_def using assms by (auto elim: states.induct)


section {* B refinement *}

text {* 
  A B refinement is composed of an \emph{abstract} and a \emph{concrete}
  LTS related by a \emph{gluing invariant}. The gluing invariant is a
  binary predicate over the states of the abstract LTS and the states
  of the concrete one. 

  We assume that the two LTSs are defined over the same types of states
  and events. For example, the type of states could be some universal
  type mapping variable names to values.
*}

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

(* dd: modified definition *)
definition sound_B_refinement :: "('st, 'ev) B_refinement \<Rightarrow> bool" where
  "sound_B_refinement r \<equiv> 
  (concrete r, abstract r) \<in> simulation_B (Collect (invariant r))"

text {* 
  In particular, the abstract LTS in a sound refinement simulates
  the concrete LTS.
*}

lemma refinement_sim: 
  assumes "sound_B_refinement r"
  shows "concrete r \<preceq>B abstract r"
  using assms unfolding sound_B_refinement_def is_simulated_by_B_def by auto

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
  unfolding refinement_id_def sound_B_refinement_def simulation_B_def 
            sim_transition_def outgoing_trans_def
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
  assumes sound: "sound_B_refinement r"
  and sound': "sound_B_refinement r'" 
  and match: "concrete r = abstract r'"
  shows "sound_B_refinement (refinement_compose r r')"
  using assms simulation_B_composition
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
  shows "concrete (last refs) \<preceq>B abstract (hd refs)"
proof -
  { fix i
    have "i < size refs \<Longrightarrow> concrete (refs!i) \<preceq>B abstract (refs!0)" (is "?P i \<Longrightarrow> ?Q i")
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
           "concrete (refs!(Suc j)) \<preceq>B abstract (refs!(Suc j))"
        unfolding sound_B_design_def by (auto intro: refinement_sim)
      ultimately show "?Q (Suc j)" by (auto elim: simulates_B_transitive)
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
  shows "concrete (last (design d)) \<preceq>B lts (spec d)"
  using assms by(metis design_sim sound_B_development_def)

end
