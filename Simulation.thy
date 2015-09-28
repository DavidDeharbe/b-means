theory Simulation
imports LTS
begin

section {* Relating LTSes: simulation *}

subsection {* Basic definitions *}

text {* 
  We formalize the notion of simulation on LTSes. Classic definitions of simulation
  often consider a single LTS, and simulation is established between two states of the same
  LTS. Here, a simulation is a relation @{text "r"} between the states of one LTS
  and the states of another LTS such that any transition taken by the former can be simulated
  by the latter. The development presented in this section aims to achieve the final theorem
  that extends the simulation to full behavior, i.e. sequences of transitions.

  The following function @{text "sim_transition"} lifts a relation on states to
  a relation on transitions: it requires the source and destination states to be
  related, and the labels to coincide.
*}

(* sm: should this notion be generalized to a relation between two possibly
   distinct state types? *)
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
        (\<forall>t \<in> trans l. src t = s \<longrightarrow>
          (\<exists>t' \<in> trans l'. src t' = s' \<and> (t,t') \<in> sim_transition r))) }"

text {* 
  We say that @{text "l'"} simulates @{text l} if is there is a simulation between
  @{text l} and @{text "l'"}.
*}
definition simulates (infixl "\<preceq>" 50)
where "(l \<preceq> l') \<equiv> \<exists>r. (l,l') \<in> simulation r"

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

lemma simulates_reflexive: "l \<preceq> l" 
  unfolding simulates_def using simulation_identity by blast

lemma simulates_transitive:
  assumes "l \<preceq> l'" and "l' \<preceq> l''"
  shows "l \<preceq> l''"
  using assms unfolding simulates_def using simulation_composition by blast


subsection {* Simulation and behavior *}

text {*
  Similarly, a relation @{text r} on states induces a simulation between two runs:
  corresponding transitions must be related according to @{text r}, lifted to
  transitions.
*}
definition sim_run :: "'st rel \<Rightarrow> ('st, 'ev) Run rel" where
  "sim_run r \<equiv> {(ts, ts') | ts ts'. 
                            list_all2 (\<lambda>t t'. (t,t') \<in> sim_transition r) ts ts'}"

(* original definition -- note that the one above is weaker because it does
   not enforce that the arguments are actually runs; however, it seems more
   useful to separate the notions of runs and of simulation.
inductive sim_run :: "'st rel \<Rightarrow> ('st, 'ev) Run \<Rightarrow> ('st, 'ev) Run \<Rightarrow> bool" where
  "sim_run r [] []"
| "sim_transition r t1 t2 \<Longrightarrow> sim_run r [t1] [t2]"
| "ts1 \<noteq> [] \<and> sim_run r ts1 ts2 \<and> 
   sim_transition r t1 t2 \<and> dst t1 = src(hd ts1) \<and> dst t2 = src(hd ts2) \<Longrightarrow> 
   sim_run r (t1 # ts1) (t2 # ts2)"
*)

text {* 
  It is easy to see that two similar runs yield the same trace
  (i.e., observable behavior).
*}

theorem sim_run_trace_eq: 
  assumes "(ts, ts') \<in> sim_run r"
  shows "map lbl ts = map lbl ts'"
  using assms
  by (simp add: list_all2_conv_all_nth nth_equalityI sim_run_def sim_transition_def)

text {*
  If two runs are similar, they have the same length.
  In particular, one is empty iff the other one is.
*}
lemma sim_run_eq_length: "(ts, ts') \<in> sim_run r \<Longrightarrow> length ts = length ts'"
  unfolding sim_run_def by (auto dest: list_all2_lengthD)

lemma sim_run_empty_iff: "(ts, ts') \<in> sim_run r \<Longrightarrow> (ts = [] \<longleftrightarrow> ts' = [])"
  by (auto dest: sim_run_eq_length)

lemma sim_run_empty [simp]:
  "([], ts) \<in> sim_run r = (ts = [])" "(ts, []) \<in> sim_run r = (ts = [])"
  unfolding sim_run_def by auto

text {*
  Two singleton runs are similar if the transitions are related.
*}
lemma sim_run_singleton [simp]:
  "([t], ts) \<in> sim_run r = (\<exists>t'. ts = [t'] \<and> (t,t') \<in> sim_transition r)"
  "(ts, [t]) \<in> sim_run r = (\<exists>t'. ts = [t'] \<and> (t',t) \<in> sim_transition r)"
  unfolding sim_run_def by (auto simp: list_all2_Cons1 list_all2_Cons2)

text {*
  For two similar runs, all transitions at corresponding positions are related.
  In particular, the last transitions of two similar, non-empty runs are related,
  as are the last states.
*}
lemma sim_run_nth:
  "(ts, ts') \<in> sim_run r \<Longrightarrow> \<forall>i < length ts. (ts!i, ts'!i) \<in> sim_transition r"
  by (simp add: sim_run_def list_all2_conv_all_nth)
 
lemma sim_run_last_trans: 
  "\<lbrakk> (ts, ts') \<in> sim_run r; ts \<noteq> [] \<rbrakk> \<Longrightarrow> (last ts, last ts') \<in> sim_transition r"
  by (simp add: last_conv_nth sim_run_empty_iff sim_run_eq_length sim_run_nth)

lemma sim_run_last_state: 
  "\<lbrakk> (ts, ts') \<in> sim_run r; ts \<noteq> [] \<rbrakk> \<Longrightarrow> (dst (last ts), dst(last ts')) \<in> r"
  by (auto dest: sim_run_last_trans simp: sim_transition_def)

text {*
  The concatenation of two similar runs is similar.
*}
lemma sim_run_append [simp]:
  assumes "(us,vs) \<in> sim_run r" and "(xs,ys) \<in> sim_run r"
  shows "(us @ xs, vs @ ys) \<in> sim_run r"
  using assms unfolding sim_run_def by (auto intro: list_all2_appendI)

text {*
  As a special case, appending two similar transitions to two similar runs
  yields again two similar runs.
*}
lemma sim_run_append_trans:
  assumes "(ts, ts') \<in> sim_run r" and "(t, t') \<in> sim_transition r"
  shows "(ts @ [t], ts' @ [t']) \<in> sim_run r"
  using assms by simp

text {*
  We now prove that a simulation between transition systems gives rise to
  simulations between runs.
*}

theorem sim_run:
  assumes sim: "(l,l') \<in> simulation r" and ts: "ts \<in> runs l"
  obtains ts' where "ts' \<in> runs l'" "(ts,ts') \<in> sim_run r"
proof -
  from ts have "\<exists>ts' \<in> runs l'. (ts, ts') \<in> sim_run r"
  proof (induct)
    show "\<exists>ts' \<in> runs l'. ([], ts') \<in> sim_run r" by (auto intro: runs.base)
  next
    fix t
    assume "t \<in> trans l" "src t \<in> init l"
    with sim obtain s' t' where
      "(src t, s') \<in> r" "s' \<in> init l'"
      "t' \<in> trans l'" "src t' = s'" "(t,t') \<in> sim_transition r"
      unfolding simulation_def by blast
    thus "\<exists>ts'\<in>runs l'. ([t], ts') \<in> sim_run r"
      by (auto intro: runs.start)
  next
    fix t ts
    assume t: "t \<in> trans l" "src t = dst (last ts)"
       and ts: "ts \<in> runs l" "ts \<noteq> []"
       and ih: "\<exists>ts'\<in>runs l'. (ts, ts') \<in> sim_run r"
    from ih obtain ts' where ts': "ts' \<in> runs l'" "(ts,ts') \<in> sim_run r" by blast
    from ts ts' have "(dst (last ts), dst (last ts')) \<in> r"
      by (metis sim_run_last_state)
    with sim t obtain t' where
      t': "t' \<in> trans l'" "src t' = dst (last ts')" "(t,t') \<in> sim_transition r"
      unfolding simulation_def by blast
    from ts ts' have "ts' \<noteq> []" by (simp add: sim_run_empty_iff)
    with ts' t' have "ts' @ [t'] \<in> runs l'" by (blast intro: runs.step)
    with ts' t' show "\<exists>ts'\<in>runs l'. (ts @ [t], ts') \<in> sim_run r"
      by (blast dest: sim_run_append_trans)
  qed
  with that show ?thesis by blast
qed

lemma sim_traces:
  assumes sim: "(l,l') \<in> simulation r" and t: "t \<in> traces l"
  shows "t \<in> traces l'"
proof -
  from t obtain ts where ts: "ts \<in> runs l" "t = map lbl ts"
    by (auto simp: traces_def)
  with sim obtain ts' where ts': "ts' \<in> runs l'" "(ts,ts') \<in> sim_run r"
    by (blast dest: sim_run)
  with ts show ?thesis
    by (auto simp: traces_def sim_run_trace_eq)
qed

theorem sim_trace_inclusion: "(l,l') \<in> simulation r \<Longrightarrow> traces l \<subseteq> traces l'"
  by (blast dest: sim_traces)

corollary simulates_traces: "l \<preceq> l' \<Longrightarrow> traces l \<subseteq> traces l'"
  unfolding simulates_def by (auto dest: sim_trace_inclusion)

end

