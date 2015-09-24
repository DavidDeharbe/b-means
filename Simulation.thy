theory Simulation

imports Main LTS

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

(* NB: Instead of making sim_transition a predicate, we could define
   sim_transition :: "'st rel \<Rightarrow> ('st, 'ev) Tr rel"
*)
definition sim_transition :: "'st rel \<Rightarrow> ('st, 'ev) Tr \<Rightarrow> ('st, 'ev) Tr \<Rightarrow> bool" where
  "sim_transition r \<equiv> \<lambda>t t'. (src t, src t') \<in> r \<and> lbl t = lbl t' \<and> (dst t, dst t') \<in> r"

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

definition simulation :: "'st rel \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> bool" where
  "simulation r l l' \<equiv>
     (\<forall>s \<in> init l. \<exists>s' \<in> init l'. (s, s') \<in> r)
   \<and> (\<forall>s s'. (s, s') \<in> r \<longrightarrow>
        (\<forall>t \<in> trans l. src t = s \<longrightarrow>
          (\<exists>t' \<in> trans l'. src t' = s' \<and> sim_transition r t t')))"

text {* 
  We say that @{text "l'"} simulates @{text l} if is there is a simulation between
  @{text l} and @{text "l'"}.
*}
definition simulates :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> bool" (infixl "\<preceq>" 50)
where "(l \<preceq> l') \<equiv> \<exists>r. simulation r l l'"

subsection {* Properties *}

text {*
   Let us verify some basic properties of simulations. First we have that the
   identity relation establishes that a LTS simulates itself.
*}

lemma simulation_identity : "simulation Id l l" 
  unfolding simulation_def sim_transition_def by auto

text {*
   Second, we have that the composition of two simulation relations is a simulation relation.
*}
lemma simulation_composition:
  assumes "simulation r l l'" and "simulation r' l' l''"
  shows "simulation (r O r') l l''"
  using assms unfolding simulation_def sim_transition_def relcomp_unfold
  by auto (metis+)

text {* Next we carry these properties over to the simulates relation over LTS. *}

lemma simulates_reflexive: "l \<preceq> l" 
  unfolding simulates_def using simulation_identity ..

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
definition sim_run :: "'st rel \<Rightarrow> ('st, 'ev) Run \<Rightarrow> ('st, 'ev) Run \<Rightarrow> bool" where
  "sim_run r ts ts' \<equiv> list_all2 (sim_transition r) ts ts'"

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
  assumes "sim_run r ts ts'"
  shows "trace_of_run ts = trace_of_run ts'"
  using assms
  by (simp add: list_all2_conv_all_nth nth_equalityI sim_run_def sim_transition_def trace_of_run_def)

text {*
  If two runs are similar, they have the same length.
  In particular, one is empty iff the other one is.
*}
lemma sim_run_eq_length: "sim_run r ts ts' \<Longrightarrow> length ts = length ts'"
  unfolding sim_run_def by (auto dest: list_all2_lengthD)

lemma sim_run_empty_iff: "sim_run r ts ts' \<Longrightarrow> (ts = [] \<longleftrightarrow> ts' = [])"
  by (auto dest: sim_run_eq_length)

lemma sim_run_empty [simp]:
  "sim_run r [] ts = (ts = [])" "sim_run r ts [] = (ts = [])"
  unfolding sim_run_def by auto

text {*
  Two singleton runs are similar if the transitions are related.
*}
lemma sim_run_singleton [simp]:
  "sim_run r [t] ts = (\<exists>t'. ts = [t'] \<and> sim_transition r t t')"
  "sim_run r ts [t] = (\<exists>t'. ts = [t'] \<and> sim_transition r t' t)"
  unfolding sim_run_def by (auto simp: list_all2_Cons1 list_all2_Cons2)

text {*
  For two similar runs, all transitions at corresponding positions are related.
  In particular, the last transitions of two similar, non-empty runs are related,
  as are the last states.
*}
lemma sim_run_nth:
  "sim_run r ts ts' \<Longrightarrow> \<forall>i < length ts. sim_transition r (ts!i) (ts'!i)"
  by (simp add: sim_run_def list_all2_conv_all_nth)
 
lemma sim_run_last_trans: 
  "\<lbrakk> sim_run r ts ts'; ts \<noteq> [] \<rbrakk> \<Longrightarrow> sim_transition r (last ts) (last ts')"
  by (simp add: last_conv_nth sim_run_empty_iff sim_run_eq_length sim_run_nth)

lemma sim_run_last_state: 
  "\<lbrakk> sim_run r ts ts'; ts \<noteq> [] \<rbrakk> \<Longrightarrow> (dst (last ts), dst(last ts')) \<in> r"
  by (auto dest: sim_run_last_trans simp: sim_transition_def)

text {*
  The concatenation of two similar runs is similar.
*}
lemma sim_run_append [simp]:
  assumes "sim_run r us vs" and "sim_run r xs ys"
  shows "sim_run r (us @ xs) (vs @ ys)"
  using assms unfolding sim_run_def by (rule list_all2_appendI)

text {*
  As a special case, appending two similar transitions to two similar runs
  yields again two similar runs.
*}
lemma sim_run_append_trans:
  assumes "sim_run r ts ts'" and "sim_transition r t t'"
  shows "sim_run r (ts @ [t]) (ts' @ [t'])"
  using assms by simp

text {*
  We now prove that a simulation between transition systems gives rise to
  simulations between runs.
*}

theorem sim_run:
  assumes sim: "simulation r l l'" and ts: "ts \<in> runs l"
  obtains ts' where "ts' \<in> runs l'" "sim_run r ts ts'"
proof -
  from ts have "\<exists>ts' \<in> runs l'. sim_run r ts ts'"
  proof (induct)
    show "\<exists>ts' \<in> runs l'. sim_run r [] ts'" by (auto intro: runs.base)
  next
    fix t
    assume "t \<in> trans l" "src t \<in> init l"
    with sim obtain s' t' where
      "(src t, s') \<in> r" "s' \<in> init l'"
      "t' \<in> trans l'" "src t' = s'" "sim_transition r t t'"
      unfolding simulation_def by blast
    thus "\<exists>ts'\<in>runs l'. sim_run r [t] ts'"
      by (auto intro: runs.start)
  next
    fix t ts
    assume t: "t \<in> trans l" "src t = dst (last ts)"
       and ts: "ts \<in> runs l" "ts \<noteq> []"
       and ih: "\<exists>ts'\<in>runs l'. sim_run r ts ts'"
    from ih obtain ts' where ts': "ts' \<in> runs l'" "sim_run r ts ts'" by blast
    from ts ts' have "(dst (last ts), dst (last ts')) \<in> r"
      by (metis sim_run_last_state)
    with sim t obtain t' where
      t': "t' \<in> trans l'" "src t' = dst (last ts')" "sim_transition r t t'"
      unfolding simulation_def by blast
    from ts ts' have "ts' \<noteq> []" by (simp add: sim_run_empty_iff)
    with ts' t' have "ts' @ [t'] \<in> runs l'" by (blast intro: runs.step)
    with ts' t' show "\<exists>ts'\<in>runs l'. sim_run r (ts @ [t]) ts'"
      by (blast dest: sim_run_append_trans)
  qed
  with that show ?thesis by blast
qed

lemma sim_traces:
  assumes sim: "simulation r l l'" and t: "t \<in> traces l"
  shows "t \<in> traces l'"
proof -
  from t obtain ts where ts: "ts \<in> runs l" "t = trace_of_run ts"
    by (auto simp: traces_def)
  with sim obtain ts' where ts': "ts' \<in> runs l'" "sim_run r ts ts'"
    by (blast dest: sim_run)
  with ts show ?thesis
    by (auto simp: traces_def sim_run_trace_eq)
qed

theorem sim_trace_inclusion: "simulation r l l' \<Longrightarrow> traces l \<subseteq> traces l'"
by (blast dest: sim_traces)

end

