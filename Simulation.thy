theory Simulation

imports Main LTS List2

begin
section {* Relating LTSes: simulation *}

subsection {* Basic definitions *}

text {* We formalize the notion of simulation on LTSes. Classic definitions of simulation
often consider a single LTS, and simulation is established between two states of the same
LTS. Here, a simulation is a relation @{text "r"} between the states of one LTS
and the states of another LTS such that any transition taken by the former can be simulated
by the latter. The development presented in this section aims to achieve the final theorem
that extends the simulation to full behavior, i.e. sequence of transitions runs.

The relation between states is the basis of a relation between transitions:
the source and destinations must be pairwise related, and the label shall coincide. This
is formalized in the function @{text "sim_transition"} *}

definition sim_transition :: "'st rel \<Rightarrow> ('st, 'ev) Tr \<Rightarrow> ('st, 'ev) Tr \<Rightarrow> bool"
where "sim_transition r t t' \<equiv> (src t, src t') \<in> r \<and> lbl t = lbl t' \<and> (dst t, dst t') \<in> r"

text {* The former transition used to extend the notion of simulation to the set of
transitions of two LTSes @{text "l1"} and @{text "l2"}. This is specified in the function 
@{text "sim_trans"}: *}

definition sim_lts_trans :: "'st rel \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> bool" where
  "sim_lts_trans r l l' \<equiv> 
    \<forall> s s' . (s, s') \<in> r \<longrightarrow>
      (\<forall> t \<in> trans l . src t = s \<longrightarrow>
        (\<exists> t' \<in> trans l' . src t' = s' \<and> sim_transition r t t'))"

text {* Another condition to establish a simulation between @{text "l"} and @{text "l'"}, is that 
every initial state of the former must be related to an initial state of the latter by @{text "s"}: *}

definition sim_lts_init :: "'st rel \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> bool" where
  "sim_lts_init r l l' \<equiv> \<forall> s \<in> init l . \<exists> s' \<in> init l' . (s, s') \<in> r"

text {* We are now equiped to give the characterize that a relation @{text "r"} defines a simulation 
of @{text "l"} by @{text "l'"}: *}

definition simulation :: "'st rel \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> bool" where
  "simulation r l l' \<equiv> sim_lts_init r l l' \<and> sim_lts_trans r l l'"

text {* Based on the notion of simulation, we introduce the relation simulates on LTS: *}
definition simulates :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> bool" (infixl "\<sim>" 50) where
  "(l1 \<sim> l2) \<equiv> \<exists> r . simulation r l2 l1"

subsection {* Properties *}

text {* Let us verify some basic properties of simulations. First we have that the
identity relation establishes that a LTS simulates itself. *}

lemma simulation_identity : "simulation Id l l" 
  unfolding simulation_def sim_lts_init_def sim_lts_trans_def sim_transition_def by auto

text {* Second, we have that the composition of two simulation relations is a simulation relation. *}
lemma simulation_closed:
assumes s12: "simulation r12 l1 l2" and s23: "simulation r23 l2 l3"
shows "simulation (r12 O r23) l1 l3"
proof -
  from s12 s23
  have "sim_lts_init (r12 O r23) l1 l3"
  unfolding simulation_def sim_lts_init_def relcomp_unfold
  by simp metis
moreover
  from s12 s23
  have "sim_lts_trans (r12 O r23) l1 l3"
  unfolding sim_lts_trans_def simulation_def sim_transition_def relcomp_unfold
  by simp metis
  ultimately show ?thesis unfolding simulation_def ..
qed

text {* Next we carry these properties over to the simulates relation over LTS. *}

lemma simulates_reflexivity: "l \<sim> l" 
  unfolding simulates_def
proof
  show "simulation Id l l" by (rule simulation_identity)
qed

lemma simulates_transitivity:
assumes
  s12: "l1 \<sim> l2" and s23: "l2 \<sim> l3"
shows
  "l1 \<sim> l3"
proof -
  from s23 obtain s where "simulation s l3 l2" unfolding simulates_def ..
moreover
  from s12 obtain r where "simulation r l2 l1" unfolding simulates_def ..
ultimately
  have "simulation (s O r) l3 l1" 
    by (rule simulation_closed[of "s" "l3" "l2" "r" "l1"])
  then show ?thesis unfolding simulates_def by auto
qed

subsection {* Simulation and behavior *}

text {* The predicate @{text "sim_run"} defines when a state relation @{text "r"} establishes 
  a simulation between two runs *}
  
inductive sim_run :: "'st rel \<Rightarrow> ('st, 'ev) Run \<Rightarrow> ('st, 'ev) Run \<Rightarrow> bool"
where
  "sim_run s [] []"
| "sim_transition s t1 t2 \<Longrightarrow> sim_run s [t1] [t2]"
| "ts1 \<noteq> [] \<and> sim_run s ts1 ts2 \<and> 
   sim_transition s t1 t2 \<and> dst t1 = src(hd ts1) \<and> dst t2 = src(hd ts2) \<Longrightarrow> 
   sim_run s (t1 # ts1) (t2 # ts2)"

text {* An important property on simulation and runs is that if a relation @{text "s"}
establishes a simulation of a run @{text "r"} with a run @{text "r'"}, then 
@{text "r"} and @{text "r'"} are exhibit the same observable behavior: *}

theorem sim_run_trace_eq: "\<lbrakk>sim_run s r r'\<rbrakk> \<Longrightarrow> trace_of_run r = trace_of_run r'"
proof(induct rule: sim_run.induct, simp, unfold sim_transition_def, simp, simp)
qed

text {* Lemma @{text "sim_run_empty_iff"} establishes that if there is a simulation
between two runs, one run is empty if and only if the other run is also empty. *}

lemma sim_run_empty_iff: "sim_run s r r' \<Longrightarrow> (r = [] \<longleftrightarrow> r' = [])"
proof(induct rule: sim_run.induct, simp, simp, simp)
qed

text {* Lemma @{text "sim_run_all_trans"} gives that if there is a simulation @{text "s"}
of run @{text "r"} by run @{text "r'"}, then @{text "s"} establishes a simulation of each
transition of @{text "r"} with the corresponding transition of @{text "r'"}. *}

lemma sim_run_all_trans: 
  "\<lbrakk> sim_run s r r' \<rbrakk> \<Longrightarrow> List2.all (sim_transition s) r r'"
proof(induct rule: sim_run.induct, auto)
qed

text {* The next lemma states that if \isasym{s} is a simulation between two non-empty runs,
 then it is a simulation between the last states of these runs. *}
 
lemma sim_run_last_trans: 
  "\<lbrakk> sim_run s r r'; r \<noteq> [] \<rbrakk> \<Longrightarrow> sim_transition s (last r) (last r')"
proof-
  assume "sim_run s r r'" "r \<noteq> []"
moreover
  from `sim_run s r r'` and `r \<noteq> []` 
    have "r' \<noteq> []" by (simp add: sim_run_empty_iff)
moreover
  from `sim_run s r r'` have "List2.all (sim_transition s) r r'" 
    by (simp add: sim_run_all_trans)
ultimately
  show "(sim_transition s) (last r) (last r')" by (simp add: List2.last)
qed

text {* The next lemma states that if \isasym{s} is a simulation between two non-empty runs,
 then the pair formed by the last states of the runs belongs to \isasym{s}. *}
 
lemma sim_run_last_state: 
  "\<lbrakk> sim_run s r r'; r \<noteq> [] \<rbrakk> \<Longrightarrow> (dst(last r), dst(last r')) \<in> s"
proof-
  assume "sim_run s r r'" "r \<noteq> []"
  from `sim_run s r r'` and `r \<noteq> []` have "sim_transition s (last r) (last r')"
    by (simp add: sim_run_last_trans)
  then show ?thesis by (simp add:sim_transition_def)
qed

text {* Next, the following lemma establishes if \isasym{s} establishes a simulation between two 
pairs of runs and the last state in the first pair coincides with the first state in the second run,
then it also is a simulation between the concatenations of the runs. *}

lemma sim_run_app_run: 
  "\<lbrakk> sim_run (s :: 'st rel) (r1 :: ('st, 'ev) Run) (r1' :: ('st, 'ev) Run); 
     sim_run s r2 r2'; r1 \<noteq> []; r2 \<noteq> []; dst(last r1) = src(hd r2); dst(last r1') = src(hd r2') \<rbrakk>
   \<Longrightarrow> sim_run s (r1 @ r2) (r1' @ r2')"
proof(induct rule: sim_run.induct, simp, simp)
  fix s t1 t2
  assume "sim_transition (s :: 'st rel) (t1 :: ('st, 'ev) Tr) (t2 :: ('st, 'ev) Tr)" 
         "sim_run s r2 r2'" "r2 \<noteq> []" "dst t1 = src (hd r2)" "dst t2 = src (hd r2')"
  then show "sim_run s (t1 # r2) (t2 # r2')" by(simp add:sim_run.intros(3))
next
  fix ts1 s ts2 t1 t2
  assume hyp_induct: "ts1 \<noteq> [] \<and>
       (sim_run s ts1 ts2 \<and>
        (sim_run s r2 r2' \<longrightarrow>
         ts1 \<noteq> [] \<longrightarrow> r2 \<noteq> [] \<longrightarrow> dst (last ts1) = src (hd r2) \<longrightarrow> dst (last ts2) = src (hd r2') 
         \<longrightarrow> sim_run s (ts1 @ r2) (ts2 @ r2'))) \<and>
       sim_transition s t1 t2 \<and> dst t1 = src (hd ts1) \<and> dst t2 = src (hd ts2)" 
       "sim_run s r2 r2'" "r2 \<noteq> []"
       "dst (last (t1 # ts1)) = src (hd r2)" "dst (last (t2 # ts2)) = src (hd r2')"
  show "sim_run s ((t1 # ts1) @ r2) ((t2 # ts2) @ r2')"
  proof-
    from hyp_induct have "ts1 \<noteq> []" by simp
  moreover
    from hyp_induct have "sim_run s ts1 ts2" by simp
    with `ts1 \<noteq> []` have "ts2 \<noteq> []" by (simp add:sim_run_empty_iff)
    with hyp_induct have "dst (last ts2) = src (hd r2')" by simp
    with `ts1 \<noteq> []` `sim_run s ts1 ts2` hyp_induct have "sim_run s (ts1 @ r2) (ts2 @ r2')" by simp
  moreover
    from hyp_induct have "sim_transition s t1 t2" by simp
  moreover
    from hyp_induct have "dst t1 = src (hd (ts1 @ r2))" by simp
  moreover
    from hyp_induct have "dst t2 = src (hd ts2)" by simp
    with `ts2 \<noteq> []` have "dst t2 = src (hd (ts2 @ r2'))" by simp
  ultimately
    show "sim_run s ((t1 # ts1) @ r2) ((t2 # ts2) @ r2')" by (simp add:sim_run.intros)
  qed
qed

text {* The following is a specialization of the latter lemma and establishes the property when
exactly one transition is appended to two runs. *}

lemma sim_run_app_trans: 
  "\<lbrakk> sim_run s r r'; r \<noteq> []; src t = dst(last r); src t' = dst(last r'); sim_transition s t t'\<rbrakk> \<Longrightarrow> 
  sim_run s (r @ [t]) (r' @ [t'])"
proof-
  assume "sim_run s r r'" "r \<noteq> []" "src t = dst(last r)" "src t' = dst(last r')" "sim_transition s t t'"
moreover
  from `sim_transition s t t'` have "sim_run s [t] [t']" by (simp add: sim_run.intros)
moreover
  from `sim_run s r r'` and `r \<noteq> []` have "r' \<noteq> []" by (simp add:sim_run_empty_iff)
ultimately
  show "sim_run s (r @ [t]) (r' @ [t'])" by (simp add:sim_run_app_run)
qed

text {* Next, we present the an essential theorem, namely that a simulation @{text "s"} 
of the LTS @{text "l"} by the LTS @{text "l'"} is also such that every run of the former may be 
simulated with @{text "s"} by a run of the latter. *}

theorem sim_run:
  assumes sim: "simulation s l l'" 
  shows "\<forall> r \<in> runs l . \<exists> r' \<in> runs l' . sim_run s r r'"
proof
  fix r
  show "r \<in> runs l \<Longrightarrow> \<exists> r' \<in> runs l'. sim_run s r r'"
  proof(induct rule: runs.induct, auto)
    have "[] \<in> runs l' \<and> sim_run s [] []" by (simp add: runs.base sim_run.intros(1))
    thus "\<exists> r' \<in> runs l'. sim_run s [] r'" by auto
  next
    fix t
    assume "t \<in> trans l" and "src t \<in> init l"
    with assms obtain s' where s': "(src t, s') \<in> s \<and> s' \<in> init l'" 
      unfolding simulation_def sim_lts_init_def by blast
    with `t \<in> trans l` and assms obtain t' 
      where t': "t' \<in> trans l' \<and> src t' = s' \<and> sim_transition s t t'"
      unfolding simulation_def sim_lts_trans_def by blast
    with s' and t' have "[t'] \<in> runs l' \<and> sim_run s [t] [t']"
      by (metis runs.start sim_run.intros(2))
    thus "\<exists> r' \<in> runs l'. sim_run s [t] r'" by auto
  next
    fix t r x
    assume 
      "t \<in> trans l" and "r \<noteq> []" and "src t = dst (last r)" and
      "x \<in> runs l'" and "sim_run s r x"
    with sim have "x \<noteq> []" by (metis sim_run_empty_iff)
    from `r \<noteq> []` and `sim_run s r x` 
      have "(dst(last r), dst(last x)) \<in> s" by (metis sim_run_last_state)
    with sim and `t \<in> trans l` and `src t = dst (last r)`
      obtain t' where t': "t' \<in> trans l' \<and> src t' = dst(last x) \<and> sim_transition s t t'" 
      unfolding simulation_def sim_lts_trans_def by (blast)
    with `x \<in> runs l'` and `x \<noteq> []`
      have "x @ [t'] \<in> runs l'" by (metis runs.step)
  moreover
    from `r \<noteq> []` and `sim_run s r x` and `src t = dst (last r)` and t' 
      have "sim_run s (r @ [t]) (x @ [t'])" by (metis sim_run_app_trans)
  ultimately
    show "\<exists> r' \<in> runs l'. sim_run s (r @ [t]) r'" by auto
  qed
qed

lemma sim_traces:
  "\<lbrakk> simulation s l l' \<rbrakk> \<Longrightarrow> \<forall> t \<in> traces l . t \<in> traces l'"
proof
  fix t
  assume "simulation s l l'" "t \<in> traces l"
  from `t \<in> traces l` obtain r where "r \<in> runs l \<and> t = trace_of_run r" unfolding traces_def
    by auto
  with `simulation s l l'` obtain r' where "r' \<in> runs l' \<and> sim_run s r r'" 
    by (metis sim_run)
  with `r \<in> runs l \<and> t = trace_of_run r` have "t = trace_of_run r'" by (metis sim_run_trace_eq)
  with `r' \<in> runs l' \<and> sim_run s r r'` show "t \<in> traces l'" unfolding traces_def by auto
qed

theorem sim_trace_inclusion: "\<lbrakk> simulation s l l' \<rbrakk> \<Longrightarrow> traces l \<subseteq> traces l'"
by (metis sim_traces subsetI)

end

