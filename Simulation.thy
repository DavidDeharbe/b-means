theory Simulation

imports Main LTS

begin
section {* Relating LTSes: simulation *}

subsection {* Basic definitions *}

text {* We formalize the notion of simulation on LTSes. Classic definitions of simulation
often consider a single LTS, and simulation is established between two states of the same
LTS. Here, a simulation is a relation @{text "r"} between the states of one LTS
and the states of another LTS such that any transition taken by the former can be simulated
by the latter. 

The relation between states is the basis of a relation between transitions:
the source and destinations must be pairwise related, and the label shall coincide. This
is formalized in the function @{text "sim_transition"} *}

definition sim_transition :: "'st rel \<Rightarrow> ('st, 'ev) Tr \<Rightarrow> ('st, 'ev) Tr \<Rightarrow> bool"
where "sim_transition r t t' \<equiv> (src t, src t') \<in> r \<and> lbl t = lbl t' \<and> (dst t, dst t') \<in> r"

text {* The former transition used to extend the notion of simulation to the set of
transitions of two LTSes @{text "l1"} and @{text "l2"}. This is specified in the function 
@{text "sim_trans"}: *}

definition sim_trans :: "'st rel \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> bool" where
  "sim_trans r l l' \<equiv> 
    \<forall> s s' . (s, s') \<in> r \<longrightarrow>
      (\<forall> t \<in> trans l . src t = s \<longrightarrow>
        (\<exists> t' \<in> trans l' . src t' = s' \<and> sim_transition r t t'))"

text {* Another condition to establish a simulation between @{text "l"} and @{text "l'"}, is that 
every initial state of the former must be related to an initial state of the latter by @{text "s"}: *}

definition simulation_init :: "'st rel \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> bool" where
  "simulation_init r l l' \<equiv> \<forall> s \<in> init l . \<exists> s' \<in> init l' . (s, s') \<in> r"

text {* We are now equiped to give the characterize that a relation @{text "r"} defines a simulation 
of @{text "l"} by @{text "l'"}: *}

definition simulation :: "'st rel \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> bool" where
  "simulation r l l' \<equiv> simulation_init r l l' \<and> sim_trans r l l'"

text {* Based on the notion of simulation, we introduce the relation simulates on LTS: *}
definition simulates :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) LTS \<Rightarrow> bool" (infixl "\<sim>" 50) where
  "(l1 \<sim> l2) \<equiv> \<exists> r . simulation r l2 l1"

subsection {* Properties *}

text {* Let us verify some basic properties of simulations. First we have that the
identity relation establishes that a LTS simulates itself. *}

lemma simulation_identity : "simulation Id l l" 
  unfolding simulation_def simulation_init_def sim_trans_def sim_transition_def by auto

text {* Second, we have that the composition of two simulation relations is a simulation relation. *}
lemma simulation_closed:
assumes s12: "simulation r12 l1 l2" and s23: "simulation r23 l2 l3"
shows "simulation (r12 O r23) l1 l3"
proof -
  from s12 s23
  have "simulation_init (r12 O r23) l1 l3"
  unfolding simulation_def simulation_init_def relcomp_unfold
  by simp metis
moreover
  from s12 s23
  have "sim_trans (r12 O r23) l1 l3"
  unfolding sim_trans_def simulation_def sim_transition_def relcomp_unfold
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
| "ts1 \<noteq> [] \<and> ts2 \<noteq> [] \<and> sim_run s ts1 ts2 \<and> 
   sim_transition s t1 t2 \<and> dst t1 = src(hd ts1) \<and> dst t2 = src(hd ts2) \<Longrightarrow> 
   sim_run s (t1 # ts1) (t2 # ts2)"

text {* An important property on simulation and runs is that if a relation @{text "s"}
establishes a simulation of a run @{text "r"} with a run @{text "r'"}, then 
@{text "r"} and @{text "r'"} are exhibit the same observable behavior: *}

theorem "sim_run s r r' \<Longrightarrow> trace_of_run r = trace_of_run r'"
proof(induct rule: sim_run.induct, simp, unfold sim_transition_def, simp, simp)
qed

lemma sim_run_empty_iff: "sim_run s r r' \<Longrightarrow> (r = [] \<longleftrightarrow> r' = [])"
proof(induct rule: sim_run.induct, simp, simp, simp)
qed

lemma "sim_run s r r' \<and> r = [] \<Longrightarrow> r' = []"
by (metis sim_run_empty_iff)

lemma sim_run_last_trans: "sim_run s r r' \<Longrightarrow> r \<noteq> [] \<Longrightarrow> (dst(last r), dst(last r')) \<in> s"
sorry

lemma sim_run_app_trans: 
  "sim_run s r r' \<Longrightarrow> r \<noteq> [] \<and> src t = dst(last r) \<and> src t' = dst(last r') \<and>
  sim_transition s t t' \<Longrightarrow> sim_run s (r @ [t]) (r' @ [t'])"
sorry

text {* Next, we enunciate, and prove, the property that the existence of a simulation @{text "s"} 
of the LTS @{text "l"} by the LTS @{text "l'"} guarantees that every run of the former may be 
simulated with @{text "s"} by a run of the latter. *}

lemma 
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
    assume step: "t \<in> trans l" and init: "src t \<in> init l"
    with assms obtain s' where src: "(src t, s') \<in> s \<and> s' \<in> init l'" 
      unfolding simulation_def simulation_init_def by blast
    with step and assms obtain t' 
      where t': "t' \<in> trans l' \<and> src t' = s' \<and> sim_transition s t t'"
      unfolding simulation_def sim_trans_def by blast
    with src have "[t'] \<in> runs l'" by (metis runs.start)
    with t' have "[t'] \<in> runs l' \<and> sim_run s [t] [t']" by (metis sim_run.intros(2))
    hence "\<exists> r' . r' \<in> runs l' \<and> sim_run s [t] r'" ..
    thus "\<exists> r' \<in> runs l'. sim_run s [t] r'" by auto
  next
    fix t r x
    assume h0: "t \<in> trans l" and h1: "r \<noteq> []" and h2: "r \<in> runs l" and h3: "src t = dst (last r)" and
    h4: "x \<in> runs l'" and h5: "sim_run s r x"
    with sim have h6: "x \<noteq> []" by (metis sim_run_empty_iff)
    from h1 and h5 have h7: "(dst(last r), dst(last x)) \<in> s" by (metis sim_run_last_trans)
    obtain s' where h8: "s' = dst(last x)" by blast
    from h7 and h8 have h9: "(dst(last r), s') \<in> s" by simp
    from sim h0 h3 h9 obtain t' where t': "t' \<in> trans l' \<and> src t' = s' \<and> sim_transition s t t'" 
      unfolding simulation_def sim_trans_def by blast
    from t' h4 h6 and h8 have h10: "x @ [t'] \<in> runs l'" by (metis runs.step)
    from h1 h5 h6 h3 h8 t' have h11: "sim_run s (r @ [t]) (x @ [t'])" by (metis sim_run_app_trans)
    from h10 and h11 have "x @ [t'] \<in> runs l' \<and> sim_run s (r @ [t]) (x @ [t'])" ..
    hence "\<exists> r' . r' \<in> runs l' \<and> sim_run s (r @ [t]) r'" ..
    thus "\<exists> r' \<in> runs l'. sim_run s (r @ [t]) r'" by auto
  qed
qed

end


