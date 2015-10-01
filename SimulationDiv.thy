theory SimulationDiv
imports LTSDiv
begin

section {* Relating LTSes with divergences: simulation *}

subsection {* Basic definitions *}

text {* 
  We formalize a notion of simulation with divergences on LTSes. This formalization is carried
  out having in mind its application to the concept of refinement in the B method. In B, when
  a module $R$ refines a module $A$, a simulation-like relation is established from $R$ to $A$,
  i.e. every action taken by $R$, \emph{in response to an event that is considered acceptable
  by $A$}, shall be simulated by a corresponding action in $A$.

  Essentially, we want to formalize this as follows: assuming $R$ is a refinement of $A$.
  For every trace $t_R$ of $R$, there is a trace $t_A$ in $A$, with corresponding divergence
  set $E_A$, such that $t_A = t_R$ or $t_A \conc e$, with $e in E_A$ is a prefix of $t_R$.  

  Conversely, for every trace $t_A$ of $A$ leading to a state with divergence set $E_A$, 
  there is a corresponding trace $t_R$ in $R$ (i.e. $t_R = t_A$) with
  a divergence set $E_R \supseteq E_A$.

  This relation is called a \emph{gluing invariant} and must be such that $R$ shall not diverge 
  in situations where $A$ does not diverge. But $R$ may well be more "robust" and not diverge in
  a state where $A$ would diverge. Of course, in that cases, the behavior of $R$ is not 
  constrained. In the case where $A$ does not diverge, then $R$ must exhibit a behavior that 
  corresponds to one of the possible behaviors of $A$, i.e. the transition taken on the event
  leads $R$ to a state where it may still be simulated by $A$.

  A simulation with divergence is a relation @{text "r"} between the states of one LTS
  and the states of another LTS such that any transition taken by the former, 
  \emph{on an event that does not cause the latter to diverge}, can be simulated
  by the latter. 

*}

text {*
  Notice that the classic notion of transition simulation is symmetric, since it does 
  not consider possible divergences. This property is no longer desirable when divergences
  are accounted for. 
  The following function @{text "sim_transition"} lifts a relation on states to
  a relation on transitions: it requires the source and destination states to be
  related, and the labels to coincide. It takes an additional input parameter that
  corresponds to the set of diverging events. 
*}

(* original definition *)
definition sim_transition :: "'st rel \<Rightarrow> ('st, 'ev) Tr rel" where
  "sim_transition r \<equiv> 
    { (tc,ta) | tc ta. 
      (src tc, src ta) \<in> r \<and> lbl tc = lbl ta \<and> (dst tc, dst ta) \<in> r }"

definition div_sim_transition :: "'st rel \<Rightarrow> ('st * 'ev) set \<Rightarrow> ('st, 'ev) Tr rel" where
  "div_sim_transition r d \<equiv> 
    { (tc,ta) | tc ta. 
      (src tc, src ta) \<in> r \<and> 
      lbl tc = lbl ta \<and>
      ((src ta, lbl ta) \<notin> d \<longrightarrow> (tc, ta) \<in> sim_transition r) }"

text {*
  With this definition, if @{text "(sa, e)"} diverges, then any transition from a state 
  @{text "sc"} related to @{text "sa"} by @{text "r"}, and labeled @{text "e"} is 
  considered to be in the relation.
*}

text {* 
  A relation @{text r} on states induces a simulation relation of LTS @{text l}
  by LTS @{text "l'"} if both of the following conditions hold:
  \begin{itemize}
  \item Every initial state of @{text l} is related, by @{text "r"} to some initial state 
    of @{text "l'"}.
  \item For any states @{text "(s,s')"} related by @{text r} and, for any event @{text "e"}
    accepted by @{text "l'"}, @{text "e"} is also accepted by @{text "l"} and
    for any @{text "l"}-transition @{text "t"} from @{text s} labelled by @{text "e"}, there 
    is an @{text "l'"}-transition @{text "t'"} from @{text "s'"}, also labelled by @{text "e"} 
    that simulates @{text t}.
  \end{itemize}
*}

text {*
  The definition of simulation with divergences between LTSes can also be phrased using the
  simulation with divergences on transitions. This new version uses the second definition of
  transition simulation, and reads more gracefully than the previous version:
*}

definition div_simulation :: "'st rel \<Rightarrow> ('st, 'ev) LTSDiv rel" where
  "div_simulation r \<equiv> { (l,l') | l l'.
     (\<forall>s \<in> init l. \<exists>s' \<in> init l'. (s, s') \<in> r)
   \<and> (\<forall>s s'. (s, s') \<in> r \<longrightarrow>
        (\<forall>t \<in> trans l. src t = s \<longrightarrow>
           (\<exists>t' \<in> trans l'. src t' = s' \<and> lbl t' = lbl t \<and> 
              (t,t') \<in> div_sim_transition r (divergences l')))) }"

(* alternative definition: *)
definition simulation :: "'st rel \<Rightarrow> ('st, 'ev) LTSDiv rel" where
  "simulation r \<equiv> { (l,l') | l l'.
     (\<forall>s \<in> init l. \<exists>s' \<in> init l'. (s, s') \<in> r)
   \<and> (\<forall>s s'. (s, s') \<in> r \<longrightarrow>
        (\<forall>t \<in> trans l. src t = s \<longrightarrow> (s', lbl t) \<notin> divergences l' \<longrightarrow>
           (\<exists>t' \<in> trans l'. src t' = s' \<and> lbl t' = lbl t \<and> 
              (t,t') \<in> sim_transition r))) }"

text {* 
  We say that @{text "l'"} simulates @{text "l"} (through @{text "r"}), or that 
  @{text "l"} is simulated by @{text "l'"} through @{text "r"}, if there is a 
  simulation @{text "r"} from @{text "l"} to @{text "l'"}.
*}
definition div_simulated_by (infixl "\<preceq>" 50)
where "(l \<preceq> l') \<equiv> \<exists>r. (l,l') \<in> div_simulation r"

definition simulated_by (infixl "\<preceq>\<preceq>" 50)
where "(l \<preceq>\<preceq> l') \<equiv> \<exists>r. (l,l') \<in> simulation r"

(* A lemma that we might want to prove is the containment of the set of diverging events:

l \<preceq> l' \<longrightarrow>
s \<in> states l \<longrightarrow>
s' \<in> states l' \<longrightarrow>
(s, s') \<in> r \<longrightarrow>
div_state l s \<subseteq> div_state l' s'
*)

(* A lemma that we might want to prove is the containment of the set of diverging events:

l \<preceq> l' \<longrightarrow>
s \<in> states l \<longrightarrow>
s' \<in> states l' \<longrightarrow>
(s, s') \<in> r \<longrightarrow>
div_state l s \<subseteq> div_state l' s'
*)
lemma div_simulation_contains:
  assumes 
    "(l, l') \<in> div_simulation r"
  shows 
    "div_trans l \<subseteq> div_trans l'"
using assms unfolding simulation_def div_trans_def sim_transition_def
sorry (*sledgehammer[verbose, max_facts=100, provers="cvc4 e z3 spass remote_vampire"] *)

subsection {* Properties *}

text {*
  Let us verify some basic properties of simulations. First we have that
  every LTS simulates itself, through a lifting of the identity relation
  over states.
*}

lemma simulation_identity : "(Id::('st,'ev) LTSDiv rel) \<subseteq> simulation (Id::'st rel)" 
  unfolding simulation_def sim_transition_def by auto

lemma div_simulation_identity : "(Id::('st,'ev) LTSDiv rel) \<subseteq> div_simulation (Id::'st rel)" 
  unfolding div_simulation_def div_sim_transition_def sim_transition_def by auto

text {*
   Second, we have that the composition of two simulation relations is a simulation relation.
*}
lemma simulation_composition:
  assumes "(l, l') \<in> simulation r" and "(l', l'') \<in> simulation r'"
  shows "(l, l'') \<in> simulation (r O r')"
  using assms unfolding simulation_def
  using assms unfolding sim_transition_def relcomp_unfold
sorry
(* was: by auto(metis+) *)

lemma div_simulation_composition:
  assumes "(l, l') \<in> div_simulation r" and "(l', l'') \<in> div_simulation r'"
  shows "(l, l'') \<in> div_simulation (r O r')"
  using assms unfolding div_simulation_def
  using assms unfolding div_sim_transition_def sim_transition_def relcomp_unfold
sorry


text {* 
  These properties are lifted to the simulates relation over LTS.
*}

lemma div_simulated_by_reflexive: "l \<preceq> l" 
  unfolding div_simulated_by_def using div_simulation_identity by blast

lemma div_simulated_by_transitive:
  assumes "l \<preceq> l'" and "l' \<preceq> l''"
  shows "l \<preceq> l''"
  using assms unfolding div_simulated_by_def using div_simulation_composition by blast

lemma simulated_by_reflexive: "l \<preceq>\<preceq> l" 
  unfolding simulated_by_def using simulation_identity by (auto)

lemma simulated_by_transitive:
  assumes "l \<preceq>\<preceq> l'" and "l' \<preceq>\<preceq> l''"
  shows "l \<preceq>\<preceq> l''"
  using assms unfolding simulated_by_def using simulation_composition by blast

subsection {* Simulation and behavior *}

text {*
  Similarly, a relation @{text r} on states induces a simulation between two runs:
  corresponding transitions must be related according to @{text r}, lifted to
  transitions.

  If ts is simulated by ts' through r, we only care as long as ts takes transition
  that do not provoke a divergence in ts.
*}

definition sim_run :: "'st rel \<Rightarrow> ('st, 'ev) Run rel" where
  "sim_run r \<equiv> {(ts, ts') | ts ts'. 
                   list_all2 (\<lambda>t t'. (t,t') \<in> sim_transition r) ts ts'}"

definition div_sim_run :: "'st rel \<Rightarrow> ('st * 'ev) set \<Rightarrow> ('st, 'ev) Run rel" where
  "div_sim_run r d \<equiv> {(ts, ts') | ts ts'. 
                            list_all2 (\<lambda>t t'. (t,t') \<in> div_sim_transition r d) ts ts'}"

(* original definition -- note that the one above is weaker because it does
   not enforce that the arguments are actually runs; however, it seems more
   useful to separate the notions of runs and of simulation.
inductive sim_run :: "'st rel \<Rightarrow> ('st, 'ev) Run \<Rightarrow> ('st, 'ev) Run \<Rightarrow> bool" where
  "sim_run' r [] []"
| "sim_transition r t1 t2 \<Longrightarrow> sim_run r [t1] [t2]"
| "ts1 \<noteq> [] \<and> sim_run r ts1 ts2 \<and> 
   sim_transition r t1 t2 \<and> dst t1 = src(hd ts1) \<and> dst t2 = src(hd ts2) \<Longrightarrow> 
   sim_run r (t1 # ts1) (t2 # ts2)"
*)

text {*
  If two runs are similar, they have the same length.
  In particular, one is empty iff the other one is.
*}

lemma div_sim_run_eq_length: "(ts, ts') \<in> div_sim_run r d \<Longrightarrow> length ts = length ts'"
  unfolding div_sim_run_def by (auto dest: list_all2_lengthD)

lemma div_sim_run_empty_iff: "(ts, ts') \<in> div_sim_run r d \<Longrightarrow> (ts = [] \<longleftrightarrow> ts' = [])"
  by (auto dest: div_sim_run_eq_length)

lemma div_sim_run_empty [simp]:
  "([], ts) \<in> div_sim_run r d = (ts = [])" 
  "(ts, []) \<in> div_sim_run r d = (ts = [])"
  unfolding div_sim_run_def by auto

text {*
  Two singleton runs are similar if the transitions are related.
*}

lemma div_sim_run_singleton [simp]:
  "([t], ts) \<in> div_sim_run r d = (\<exists> t'. ts = [t'] \<and> (t, t') \<in> div_sim_transition r d)"
  "(ts, [t]) \<in> div_sim_run r d = (\<exists> t'. ts = [t'] \<and> (t', t) \<in> div_sim_transition r d)"
  unfolding div_sim_run_def by (auto simp:list_all2_Cons1 list_all2_Cons2)

text {*
  For two similar runs, all transitions at corresponding positions are related.
  In particular, the last transitions of two similar, non-empty runs are related,
  as are the last states.
*}
 
lemma div_sim_run_nth:
  "(ts, ts') \<in> div_sim_run r d \<Longrightarrow> \<forall>i < length ts. (ts!i, ts'!i) \<in> div_sim_transition r d"
  by (simp add: div_sim_run_def list_all2_conv_all_nth)

lemma div_sim_run_last_trans: 
  "\<lbrakk> (ts, ts') \<in> div_sim_run r d; ts \<noteq> [] \<rbrakk> \<Longrightarrow> (last ts, last ts') \<in> div_sim_transition r d"
  by (simp add: last_conv_nth div_sim_run_empty_iff div_sim_run_eq_length div_sim_run_nth)

lemma div_sim_run_last_state: 
  "\<lbrakk> (ts, ts') \<in> div_sim_run r d; ts \<noteq> [] \<rbrakk> \<Longrightarrow> 
     (src (last ts'), lbl(last ts)) \<in> d \<or> ((dst (last ts), dst(last ts')) \<in> r)"
  by (auto dest: div_sim_run_last_trans simp: div_sim_transition_def simp: sim_transition_def)

text {*
  The concatenation of two similar runs is similar.
*}

lemma div_sim_run_append [simp]:
  assumes "(us,vs) \<in> div_sim_run r d" and "(xs,ys) \<in> div_sim_run r d"
  shows "(us @ xs, vs @ ys) \<in> div_sim_run r d"
  using assms unfolding div_sim_run_def by (auto intro: list_all2_appendI)

text {*
  As a special case, appending two similar transitions to two similar runs
  yields again two similar runs.
*}
lemma div_sim_run_append_trans:
  assumes "(ts, ts') \<in> div_sim_run r d" and "(t, t') \<in> div_sim_transition r d"
  shows "(ts @ [t], ts' @ [t']) \<in> div_sim_run r d"
  using assms by simp

text {*
  We now prove that a simulation between transition systems gives rise to
  simulations between runs.
*}

theorem div_sim_run:
  assumes 
    sim: "(l, l') \<in> div_simulation r" 
  and 
    ts: "ts \<in> runs l"
  obtains ts' where "ts' \<in> runs l'" "(ts,ts') \<in> div_sim_run r (divergences l')"
sorry
(*
proof
  from ts have "\<exists>ts' \<in> runs l'. (ts, ts') \<in> div_sim_run r (divergences l')"
  proof (induct)
    show "\<exists>ts' \<in> runs l'. ([], ts') \<in> div_sim_run r (divergences l')" by (auto intro: runs.base)
  next
    fix t
    assume "t \<notin> div_trans l" "src t \<in> init l"
    with sim obtain t' where
      "src t' \<in> init l'"
      "(src t, src t') \<in> r"
      "src t' = src t"
      "lbl t' = lbl t" 
      "(t, t') \<in> div_sim_transition r (divergences l')"
      unfolding div_simulation_def div_trans_def sorry
    thus "\<exists>ts'\<in>runs l'. ([t], ts') \<in> div_sim_run r (divergences l')"
      by (auto intro: runs.start)
  next
    fix t ts
    assume t: "t \<notin> div_trans l" "src t = dst (last ts)"
       and ts: "ts \<in> runs l" "ts \<noteq> []"
       and ih: "\<exists>ts'\<in>runs l'. (ts, ts') \<in> div_sim_run r (divergences l')"
    from ih obtain ts' where ts': "ts' \<in> runs l'" "(ts,ts') \<in> div_sim_run r (divergences l')" by blast
    from ts ts' have "(dst (last ts), dst (last ts')) \<in> r"
      by (metis div_sim_run_last_state)
    with sim t obtain t' where
      t': "t' \<notin> div_trans l'" "src t' = dst (last ts')" "(t,t') \<in> div_sim_transition r (divergences l')"
      unfolding div_simulation_def sorry
    from ts ts' have "ts' \<noteq> []" by (simp add: div_sim_run_empty_iff)
    with ts' t' have "ts' @ [t'] \<in> runs l'" by (blast intro: runs.step)
    with ts' t' show "\<exists>ts'\<in>runs l'. (ts @ [t], ts') \<in> div_sim_run r (divergences l')"
      sorry
  qed
  with that show ?thesis by blast
qed
*)

lemma div_sim_traces_1:
  assumes sim: "l \<preceq>\<preceq> l'" and tev: "(t, ev) \<in> trace_div l"
  shows "\<exists> (t', ev') \<in> trace_div l'. t' = t \<or> 
             (\<exists> e' \<in> ev' . (\<exists> t'' . t' @ [e'] @ t'' = t))"
sorry

lemma div_sim_traces_2:
  assumes sim: "l \<preceq>\<preceq> l'" and tev: "(t', ev') \<in> trace_div l'"
  shows "\<exists> (t, ev) \<in> trace_div l. t = t' \<and> ev \<supseteq> ev'"
sorry

(*
theorem sim_trace_inclusion: "(l,l') \<in> simulation r \<Longrightarrow> traces l \<subseteq> traces l'"
  by (blast dest: sim_traces)

corollary simulates_traces: "l \<preceq> l' \<Longrightarrow> traces l \<subseteq> traces l'"
  unfolding simulates_def by (auto dest: sim_trace_inclusion)
*)

end

