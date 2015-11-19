theory Simulation
imports LTS
begin

section {* Relating LTSes: simulation *}

subsection {* Basic definitions *}

text {* 
  We formalize a notion of simulation on LTSes. Classic definitions of simulation
  often consider a single LTS, and simulation is established between two states of the same
  LTS. Here, a simulation is a relation @{text "r"} between the states of one LTS
  and the states of another LTS such that any transition taken by the former can be simulated
  by the latter. The development presented in this section aims to achieve the final theorem
  that extends the simulation to full behavior, i.e. sequences of transitions.

  The following function @{text "sim_transition"} lifts a relation on states to
  a relation on transitions: it requires the source and destination states to be
  related, and the labels to coincide.
*}

definition sim_transition :: "'st rel \<Rightarrow> ('st, 'ev) Tr rel" where
  "sim_transition r \<equiv> { (t,t') | t t'. (src t, src t') \<in> r
                                     \<and> lbl t = lbl t' \<and> (dst t, dst t') \<in> r }"

text {* 
  A relation @{text r} on states induces a simulation relation over LTSes @{text l}
  and @{text "l'"} if both of the following conditions hold:
  \begin{itemize}
  \item Every initial state of @{text l} is related to some initial state of @{text "l'"}.
  \item For any states @{text "(s,s')"} related by @{text r} and any
    transition @{text t} of @{text l} originating at @{text s} there exists a
    transition of @{text "l'"} originating at @{text "s'"} that simulates @{text t}.
  \end{itemize}
*}

definition simulation :: "'st rel \<Rightarrow> ('st, 'ev) LTS rel" where
  "simulation r \<equiv> { (l,l') | l l'.
     (\<forall>s \<in> init l. \<exists>s' \<in> init l'. (s, s') \<in> r)
   \<and> (\<forall>s s'. (s, s') \<in> r \<longrightarrow>
        (\<forall>t \<in> outgoing l s. \<exists>t' \<in> outgoing l' s'. (t,t') \<in> sim_transition r)) }"

text {* 
  We say that @{text "l'"} simulates @{text l} if is there is a simulation between
  @{text l} and @{text "l'"}.
*}
definition simulated (infixl "\<preceq>" 50) where
  "l \<preceq> l' \<equiv> \<exists>r. (l,l') \<in> simulation r"

subsection {* Properties *}

text {*
  Let us verify some basic properties of simulations. First we have that
  every LTS simulates itself, through a lifting of the identity relation
  over states.
*}

lemma simulation_identity : "(Id::('st,'ev) LTS rel) \<subseteq> simulation (Id::'st rel)" 
  unfolding simulation_def sim_transition_def by auto

text {*
   Second, we have that the composition of two simulation relations is a simulation relation.
*}
lemma simulation_composition:
  assumes "(l, l') \<in> simulation r" and "(l', l'') \<in> simulation r'"
  shows "(l, l'') \<in> simulation (r O r')"
  using assms unfolding simulation_def sim_transition_def relcomp_unfold
  by auto (metis+)

text {* 
  These properties are lifted to the simulates relation over LTS.
*}

lemma simulated_reflexive: "l \<preceq> l" 
  unfolding simulated_def using simulation_identity by blast

lemma simulated_transitive:
  assumes "l \<preceq> l'" and "l' \<preceq> l''"
  shows "l \<preceq> l''"
  using assms unfolding simulated_def using simulation_composition by blast

subsection {* Simulation and behavior *}

text {*
  Similarly, a relation @{text r} on states induces a simulation between two runs:
  corresponding transitions must be related according to @{text r}, lifted to
  transitions.
*}
definition sim_run :: "'st rel \<Rightarrow> ('st, 'ev) Run rel" where
  "sim_run r \<equiv> {(run, run') | run run'. 
                   length (trns run) = length (trns run')
                 \<and> (\<forall>i < length (trns run). 
                       (fst (trns run ! i), fst (trns run' ! i)) \<in> r
                     \<and> snd (trns run ! i) = snd (trns run' ! i))
                 \<and> (fins run, fins run') \<in> r}"

text {* 
  It immediately follows that two similar runs yield the same trace
  (i.e., observable behavior).
*}

theorem sim_run_trace_eq: 
  assumes "(run, run') \<in> sim_run r"
  shows "trace_of run = trace_of run'"
  using assms by (simp add: sim_run_def trace_of_def nth_equalityI)

theorem sim_run:
  assumes sim: "(l,l') \<in> simulation r" and run: "run \<in> runs l"
  obtains run' where "run' \<in> runs l'" "(run,run') \<in> sim_run r"
proof -
  from run have "\<exists>run' \<in> runs l'. (run, run') \<in> sim_run r"
  proof (induct)
    fix s
    assume "s \<in> init l"
    with sim obtain s' where s': "s' \<in> init l'" "(s,s') \<in> r"
      unfolding simulation_def by blast
    hence "\<lparr> trns = [], fins = s' \<rparr> \<in> runs l'"
      by (auto intro: runs.start)
    with s' show "\<exists>run' \<in> runs l'. (\<lparr>trns = [], fins = s\<rparr>, run') \<in> sim_run r"
      unfolding sim_run_def by force
  next
    fix rn t
    assume rn: "rn \<in> runs l"
       and ih: "\<exists>rn' \<in> runs l'. (rn, rn') \<in> sim_run r"
       and t: "t \<in> outgoing l (fins rn)"
    from ih obtain rn' where
      rn': "rn' \<in> runs l'" "length (trns rn) = length (trns rn')"
           "\<forall>i < length (trns rn).
               (fst (trns rn ! i), fst (trns rn' ! i)) \<in> r
             \<and> snd (trns rn ! i) = snd (trns rn' ! i)"
           "(fins rn, fins rn') \<in> r"
      unfolding sim_run_def by blast
    with sim t obtain t' where
      t': "t' \<in> outgoing l' (fins rn')" "lbl t' = lbl t" "(dst t, dst t') \<in> r"
      unfolding simulation_def sim_transition_def by force
    let ?run = "append_tr rn t"
    let ?run' = "append_tr rn' t'"
    from `rn' \<in> runs l'` `t' \<in> outgoing l' (fins rn')` have "?run' \<in> runs l'"
      by (rule runs.step)
    moreover
    from rn' t' have "(?run, ?run') \<in> sim_run r"
      unfolding sim_run_def by (auto simp: append_tr_def nth_append)
    ultimately show "\<exists>run' \<in> runs l'. (?run, run') \<in> sim_run r" ..
  qed
  with that show ?thesis by blast
qed

lemma sim_traces:
  assumes sim: "(l,l') \<in> simulation r" and tr: "tr \<in> traces l"
  shows "tr \<in> traces l'"
proof -
  from tr obtain run where run: "run \<in> runs l" "tr = trace_of run"
    by (auto simp: traces_def)
  with sim obtain run' where "run' \<in> runs l'" "(run,run') \<in> sim_run r"
    by (blast dest: sim_run)
  with run show ?thesis
    by (auto simp: traces_def sim_run_trace_eq)
qed

theorem sim_trace_inclusion: "(l,l') \<in> simulation r \<Longrightarrow> traces l \<subseteq> traces l'"
  by (blast dest: sim_traces)

corollary simulates_traces: "l \<preceq> l' \<Longrightarrow> traces l \<subseteq> traces l'"
  unfolding simulated_def by (auto dest: sim_trace_inclusion)

end

