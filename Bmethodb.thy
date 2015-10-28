theory Bmethodb
imports Simulationb
begin

section {* A Notion of Simulation Tailored for the B Method *}

(**
text {* A useful rule for proving conditional statements. *}
lemma bool_ifI [intro!]:
  assumes "P \<Longrightarrow> Q" and "~P \<Longrightarrow> R"
  shows "if P then Q else R"
  using assms by auto
**)

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
*}

text {*
  We now provide the formalization of the concept of simulation
  corresponding to the relation between the abstract and concrete
  counterparts of a refinement in the B method.
*}
definition simulation_B :: "'st rel \<Rightarrow> ('st, 'ev) LTS rel" where
  "simulation_B r \<equiv> { (l,l') | l l'.
     (\<forall>s \<in> init l. \<exists>s' \<in> init l'. (s, s') \<in> r)
   \<and> (\<forall>s s'. (s, s') \<in> r \<longrightarrow>
         accepted_events l s \<supseteq> accepted_events l' s' \<and>
         (\<forall>t \<in> outgoing l s.
            lbl t \<in> accepted_events l' s' \<longrightarrow> 
             (\<exists>t' \<in> outgoing l' s'. 
                  lbl t' = lbl t \<and> (dst t, dst t') \<in> r))) }"

definition simulated_B (infixl "\<preceq>B" 50)
  where "l \<preceq>B l' \<equiv> \<exists>r. (l,l') \<in> simulation_B r"

text {*
   We have that the composition of two simulation relations is
   a simulation relation.
*}

lemma simulation_B_identity : "(Id::('st,'ev) LTS rel) \<subseteq> simulation_B (Id::'st rel)" 
  unfolding simulation_B_def by auto

lemma simulation_B_composition:
  assumes "(l, l') \<in> simulation_B r" and "(l', l'') \<in> simulation_B r'"
  shows "(l, l'') \<in> simulation_B (r O r')"
  using assms unfolding simulation_B_def sim_transition_def relcomp_unfold
  by fastforce

lemma simulated_B_reflexive: "l \<preceq>B l" 
  unfolding simulated_B_def using simulation_B_identity by blast

lemma simulates_B_transitive:
  assumes "l \<preceq>B l'" and "l' \<preceq>B l''"
  shows   "l \<preceq>B l''"
  using assms simulation_B_composition
  unfolding simulated_B_def
  by blast

text {*
  The following lemma relates runs of a simulating LTS with those
  of a simulated one. It differs from theorem @{text "sim_run"}
  because in B the simulating system may take extra steps. The
  following definition relates runs such that the abstract run
  simulates the concrete run for as long as it can, i.e. until the
  concrete run makes a transition for an event that is not accepted.
*}

definition sim_B_run where
  "sim_B_run r l' \<equiv>
   {(run, run') | run run' . 
     length (trns run') \<le> length (trns run)
   \<and> (\<forall>i < length (trns run'). 
           (fst (trns run ! i), fst (trns run' ! i)) \<in> r
         \<and> snd (trns run ! i) = snd (trns run' ! i))
   \<and> (if length (trns run') = length (trns run)
      then (fins run, fins run') \<in> r
      else snd (trns run ! (length (trns run'))) \<notin> accepted_events l' (fins run'))}"

lemma sim_B_run:
  assumes sim: "(l,l') \<in> simulation_B r"
      and run: "run \<in> runs l"
  obtains run' where "run' \<in> runs l'" "(run, run') \<in> sim_B_run r l'"
proof -
  from run have "\<exists>run' \<in> runs l'. (run, run') \<in> sim_B_run r l'" (is "?P run")
  proof (induct)
    fix s
    assume "s \<in> init l"
    with sim obtain s' where s': "s' \<in> init l'" "(s,s') \<in> r"
      unfolding simulation_B_def by blast
    hence "\<lparr>trns = [], fins = s'\<rparr> \<in> runs l'" by (blast intro: runs.start)
    with s'
    show "?P \<lparr>trns = [], fins = s\<rparr>"
      unfolding sim_B_run_def by force
  next
    fix rn t
    assume rn: "rn \<in> runs l" and t: "t \<in> outgoing l (fins rn)"
       and ih: "?P rn"
    then obtain rn' where
      rn': "rn' \<in> runs l'" "(rn, rn') \<in> sim_B_run r l'"
      by blast
    let ?run = "append_tr rn t"
    show "?P ?run"
    proof (cases "length (trns rn') < length (trns rn)")
      case True with rn' show ?thesis
        unfolding sim_B_run_def
        by (auto simp: append_tr_def nth_append)
    next
      case False
      with rn' have len: "length (trns rn') = length (trns rn)"
        unfolding sim_B_run_def by simp
      with rn' have fins: "(fins rn, fins rn') \<in> r"
        unfolding sim_B_run_def by simp
      show ?thesis
      proof (cases "lbl t \<in> accepted_events l' (fins rn')")
        case True
        with sim fins t obtain t' where 
          t': "t' \<in> outgoing l' (fins rn')" "lbl t' = lbl t" "(dst t, dst t') \<in> r"
          unfolding simulation_B_def by blast
        let ?run' = "append_tr rn' t'"
        from `rn' \<in> runs l'` `t' \<in> outgoing l' (fins rn')`
        have "?run' \<in> runs l'" by (rule runs.step)
        moreover
        from rn' t' len have "(?run, ?run') \<in> sim_B_run r l'"
          unfolding sim_B_run_def
          by (auto simp: append_tr_def nth_append)
        ultimately show ?thesis ..
      next
        case False
        with rn' len have "(?run, rn') \<in> sim_B_run r l'"
          unfolding sim_B_run_def
          by (auto simp: append_tr_def nth_append)
        with `rn' \<in> runs l'` show ?thesis ..
      qed
    qed
  qed
  with that show ?thesis by blast
qed

text {* 
  The external, or observable, behavior of an LTS is expressed in terms
  of the events to which the LTS responds. Similar to the refusals semantics
  of CSP, we define an external behavior as a pair whose first component is
  a finite sequence of events that occurred in a run, and whose second
  component is the set of events that are enabled when the run has been
  executed by the LTS.

  The type corresponding to such observations is defined as follows:
*}
type_synonym 'ev TrB = "'ev list * 'ev set"

definition traces_B :: "('st, 'ev) LTS \<Rightarrow> 'ev TrB set" where
  "traces_B l \<equiv> { (trace_of r, accepted_events l (fins r)) | r . r \<in> runs l }"

lemma run_trace_inv:
  assumes "run \<in> runs l" and "t \<in> outgoing l (fins run)"
  shows "(trace_of run @ [lbl t], accepted_events l (dst t)) \<in> traces_B l"
proof -
  from assms have "append_tr run t \<in> runs l" by (rule runs.step)
  moreover
  have "trace_of run @ [lbl t] = trace_of (append_tr run t)"
    unfolding trace_of_def append_tr_def by simp
  moreover
  have "fins (append_tr run t) = dst t"
    unfolding append_tr_def by simp
  ultimately show ?thesis
    unfolding traces_B_def by auto
qed

text {*
  The following theorem establishes a property on the traces of LTSes
  that relate through the (B inspired notion of) simulation.
*}
lemma sim_traces_B:
  assumes sim: "l \<preceq>B l'" and tr: "(tr, acc) \<in> traces_B l"
  obtains tr' acc' where
    "(tr', acc') \<in> traces_B l'" "length tr' \<le> length tr"
    "\<forall>i < length tr'. tr'!i = tr!i"
    "if length tr' = length tr then acc' \<subseteq> acc else tr ! (length tr') \<notin> acc'"
proof -
  from sim obtain r where r: "(l,l') \<in> simulation_B r"
    by (auto simp: simulated_B_def)
  from tr obtain run where 
    run: "run \<in> runs l" "tr = trace_of run" "acc = accepted_events l (fins run)"
    by (auto simp: traces_B_def)
  with r obtain run' where
    run': "run' \<in> runs l'" "(run, run') \<in> sim_B_run r l'"
    by (blast dest: sim_B_run)
  let ?tr' = "trace_of run'"
  let ?acc' = "accepted_events l' (fins run')"
  from run' have "(?tr', ?acc') \<in> traces_B l'" by (auto simp: traces_B_def)
  moreover
  from run run' have "length ?tr' \<le> length tr" "\<forall>i < length ?tr'. ?tr'!i = tr!i"
    unfolding sim_B_run_def trace_of_def by auto
  moreover
  from r run run'
  have "if length ?tr' = length tr then ?acc' \<subseteq> acc else tr ! (length ?tr') \<notin> ?acc'"
    unfolding sim_B_run_def simulation_B_def trace_of_def by auto
  ultimately show ?thesis using that by blast
qed

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
  unfolding sound_B_machine_def using assms 
  by (auto elim: states.induct simp: outgoing_def)


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
  using assms unfolding sound_B_refinement_def simulated_B_def by auto

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
            sim_transition_def outgoing_def
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
