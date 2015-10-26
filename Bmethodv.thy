theory Bmethodv

imports Simulationv

begin
sledgehammer_params[provers="z3 cvc4"]

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

lemma simulation_B_composition:
  assumes "(l, l') \<in> simulation_B r" and "(l', l'') \<in> simulation_B r'"
  shows "(l, l'') \<in> simulation_B (r O r')"
  using assms unfolding simulation_B_def sim_transition_def relcomp_unfold
  by fastforce

lemma simulates_B_transitive:
  assumes "l \<preceq>B l'" and "l' \<preceq>B l''"
  shows   "l \<preceq>B l''"
  using assms simulation_B_composition
  unfolding simulated_B_def
  by blast

text {*
  The following lemma relates runs of a simulating LTS with those
  of a simulated one. It differs from theorem @{text "sim_run"}
  because in B the simulating system may take extra steps. We
  define a suitable predicate on runs of two systems @{text "l"}
  and @{text "l'"} related by @{text "r"}.
*}

definition maximal_similar_runs where
  "maximal_similar_runs r l l' run run' \<equiv> 
     length run' \<le> length run
   \<and> (\<forall>i < length run'. (run!i, run'!i) \<in> sim_transition r)
   \<and> (length run' < length run \<longrightarrow> 
        (if run' = [] 
         then \<forall>s' \<in> init l'. (src (hd run), s') \<in> r \<longrightarrow> lbl (hd run) \<notin> accepted_events l' s'
         else lbl (run!length run') \<notin> accepted_events l' (dst (last run'))))"

definition maximal_similar_runs3 where
  "maximal_similar_runs3 r l l' run run' \<equiv> 
    (let (ts, ts') = (exe run, exe run') in
     length ts' \<le> length ts
   \<and> (\<forall>i < length ts'. (ts!i, ts'!i) \<in> sim_transition r)
   \<and> (length ts' < length ts \<longrightarrow> 
        lbl (ts!length ts') \<notin> accepted_events l' (fin run')))"

lemma simulation_B_maximal_similar_runs:
  assumes l: "(l,l') \<in> simulation_B r"
      and run: "run \<in> runs l"
  obtains run' where "run' \<in> runs l'" "maximal_similar_runs r l l' run run'"
proof -
  from run 
  have "\<exists>run' \<in> runs l'. maximal_similar_runs r l l' run run'"
  proof (induct)
    have "maximal_similar_runs r l l' [] []"
      by (simp add: maximal_similar_runs_def)
    thus "\<exists>run' \<in> runs l'. maximal_similar_runs r l l' [] run'"
      by (auto intro: runs.base)
  next
    fix s t
    assume s: "s \<in> init l" and t: "t \<in> outgoing l s"
    show "\<exists>run' \<in> runs l'. maximal_similar_runs r l l' [t] run'"
    proof (cases "\<exists>s' \<in> init l'. (s,s') \<in> r \<and> lbl t \<in> accepted_events l' s'")
      case True
      then obtain s' where 
        s': "s' \<in> init l'" "(s,s') \<in> r" "lbl t \<in> accepted_events l' s'"
        by blast
      with l t obtain t' where
        t': "t' \<in> outgoing l' s'" "lbl t' = lbl t" "(dst t, dst t') \<in> r"
        unfolding simulation_B_def by force
      from s' t t' have "maximal_similar_runs r l l' [t] [t']"
        unfolding sim_transition_def outgoing_def maximal_similar_runs_def 
        by auto
      moreover
      from s' t' have "[t'] \<in> runs l'" by (auto intro: runs.start)
      ultimately show ?thesis by blast
    next
      case False
      with t have "maximal_similar_runs r l l' [t] []"
        unfolding maximal_similar_runs_def outgoing_def by auto
      thus ?thesis by (auto intro: runs.base)
    qed
  next
    fix ts t
    assume ts: "ts \<in> runs l" "ts \<noteq> []"
       and t: "t \<in> outgoing l (dst (last ts))"
       and ih: "\<exists>ts' \<in> runs l'. maximal_similar_runs r l l' ts ts'"
    from ih obtain ts' where
      ts': "ts' \<in> runs l'" "maximal_similar_runs r l l' ts ts'"
      by blast
    show "\<exists>run' \<in> runs l'. maximal_similar_runs r l l' (ts @ [t]) run'"
    proof (cases "length ts' < length ts")
      case True
      with ts ts' have "maximal_similar_runs r l l' (ts @ [t]) ts'"
        unfolding maximal_similar_runs_def by (simp add: nth_append)
      with ts' show ?thesis by blast
    next
      case False
      with ts' ts have eq: "length ts' = length ts" "ts' \<noteq> []"
        unfolding maximal_similar_runs_def by auto
      show ?thesis
      proof (cases "lbl t \<in> accepted_events l' (dst (last ts'))")
        case False
        with ts ts' eq have "maximal_similar_runs r l l' (ts @ [t]) ts'"
          unfolding maximal_similar_runs_def by (auto simp: nth_append)
        with ts' show ?thesis by blast
      next
        case True
        from ts eq 
        have dst: "dst (last ts') = dst (ts'!(length ts' - 1))" "dst (last ts) = dst (ts!(length ts' - 1))"
          by (auto simp: last_conv_nth)
        from ts' ts eq 
        have rel: "(dst (ts!(length ts' - 1)), dst (ts'!(length ts' - 1))) \<in> r"
          unfolding maximal_similar_runs_def sim_transition_def by auto
        with True ts eq l t dst obtain t' where
          t': "t' \<in> outgoing l' (dst (ts'!(length ts' - 1)))" "lbl t' = lbl t" "(dst t, dst t') \<in> r"
          unfolding simulation_B_def by (force simp: Pair_inject)
        with t dst rel have "(t, t') \<in> sim_transition r"
          unfolding sim_transition_def outgoing_def by simp
        with ts' eq have "maximal_similar_runs r l l' (ts@[t]) (ts'@[t'])"
          unfolding maximal_similar_runs_def by (simp add: nth_append)
        moreover
        from ts' t' dst eq have "ts' @ [t'] \<in> runs l'"
          by (auto intro: runs.step)
        ultimately
        show ?thesis ..
      qed
    qed
  qed
  with that show ?thesis by blast
qed

lemma simulation_B_maximal_similar_runs3:
  assumes sim: "(l,l') \<in> simulation_B r"
      and run: "run \<in> runs3 l"
  obtains run' where "run' \<in> runs3 l'" "maximal_similar_runs3 r l l' run run'"
proof -
  from run 
  have "\<exists>run' \<in> runs3 l'. maximal_similar_runs3 r l l' run run'"
  proof (induct)
    fix s
    assume s: "s \<in> init l"
    with sim obtain s' where s': "s' \<in> init l'" "(s, s') \<in> r"
        unfolding simulation_B_def by blast
    then have in_run3: "\<lparr>ini = s', exe = []\<rparr> \<in> runs3 l'" by (simp add: runs3.base)
    moreover
    from s s' sim have 
      "maximal_similar_runs3 r l l' \<lparr>ini = s, exe = []\<rparr>  \<lparr>ini = s', exe = []\<rparr>"
      by (simp add: maximal_similar_runs3_def)
   ultimately show "\<exists> run' \<in> runs3 l'. maximal_similar_runs3 r l l' \<lparr>ini = s, exe = []\<rparr>  run'"
     by blast
  next
    fix run t
    assume run: "run \<in> runs3 l"
       and ih: "\<exists>run'\<in>runs3 l'. maximal_similar_runs3 r l l' run run'"
       and run_not_empty: "exe run \<noteq> []"
       and t: "t \<in> outgoing l (fin run)"
    from ih obtain run' where
      run': "run' \<in> runs3 l'" "maximal_similar_runs3 r l l' run run'" by blast
    show "\<exists>run'\<in>runs3 l'.
           maximal_similar_runs3 r l l' \<lparr>ini = ini run, exe = exe run @ [t]\<rparr> run'"
    proof (cases "length (exe run') < length (exe run)")
      case True
      with run run' have "maximal_similar_runs3 r l l' \<lparr> ini = ini run, exe = exe run @ [t] \<rparr> run'"
        unfolding maximal_similar_runs3_def
        by (simp add: nth_append)
      with run' show ?thesis by blast
    next
      case False
      with run' run have eq_len: "length (exe run') = length (exe run)"
        unfolding maximal_similar_runs3_def by auto
      with run' run have run'_not_empty: "exe run' \<noteq> []"
        using run_not_empty by auto
      show ?thesis
      proof (cases "lbl t \<in> accepted_events l' (fin run')")
        case True
        from run eq_len
        have dst': "fin run' = dst ((exe run')!(length (exe run') - 1))" 
          by (simp add: fin_def last_conv_nth list.case_eq_if run'_not_empty)
        from run eq_len
        have dst: "fin run = dst ((exe run)!(length (exe run) - 1))" 
          by (simp add: fin_def last_conv_nth list.case_eq_if run_not_empty)
        from run' run eq_len
        have rel: "(dst ((exe run)!(length (exe run') - 1)), fin run') \<in> r"
          unfolding maximal_similar_runs3_def sim_transition_def
          using run_not_empty dst' by auto
        with True run eq_len sim t dst dst' obtain t' where
          t': "t' \<in> outgoing l' (fin run')" "lbl t' = lbl t" "(dst t, dst t') \<in> r"
          unfolding simulation_B_def by (force simp: Pair_inject)
        with t dst rel have "(t, t') \<in> sim_transition r"
          unfolding sim_transition_def outgoing_def
          by (simp add: eq_len)
        with run' eq_len have "maximal_similar_runs3 r l l' \<lparr> ini = ini run, exe = exe run @[t] \<rparr> \<lparr> ini = ini run', exe = exe run' @ [t'] \<rparr>"
          unfolding maximal_similar_runs3_def by (simp add: nth_append)
        moreover
        from run' t' dst eq_len have "\<lparr> ini = ini run', exe = exe run' @ [t'] \<rparr> \<in> runs3 l'"
          using run'_not_empty runs3.step by blast
        ultimately
        show ?thesis ..
      next
        case False
        with run run' eq_len have "maximal_similar_runs3 r l l' \<lparr> ini = ini run, exe = exe run @ [t] \<rparr> run'"
          unfolding maximal_similar_runs3_def by (auto simp: nth_append)
        with run' show ?thesis by blast
      qed
    qed
  qed
  with that show ?thesis by blast
qed

text {* 
  The external, or observable, behavior of an LTS is an expression of
  the events to which the LTS responds. The observable behavior is
  then a pair composed of the list of the successive events found
  along a \emph{run} and the set of events that are accepted when the
  run has reached the last state.

  The type corresponding to such observations is defined as follows:
*}
type_synonym 'ev TrB = "'ev list * 'ev set"

(* sm: in the following definition, changed UNION to INTER in order to
   prove lemma sim_traces_B -- the definition returns the set of
   events that are accepted in every initial state. *)
definition run_accepted_events :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) Run \<Rightarrow> 'ev set" where 
"run_accepted_events l r \<equiv> 
   if r = [] then INTER (init l) (accepted_events l)
   else accepted_events l (dst (last r))"

definition run3_accepted_events :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) Run3 \<Rightarrow> 'ev set" where 
  "run3_accepted_events l run \<equiv> accepted_events l (fin run)"

text {*
  Next, the function @{text run_trace} maps observations of internal
  behavior to observations of external behavior.
*}

definition run_trace :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) Run \<Rightarrow> 'ev TrB" where 
  "run_trace l r \<equiv> (map lbl r, run_accepted_events l r)"

definition run3_trace :: "('st, 'ev) LTS \<Rightarrow> ('st, 'ev) Run3 \<Rightarrow> 'ev TrB" where 
  "run3_trace l r \<equiv> (map lbl (exe r), run3_accepted_events l r)"

definition traces3_B :: "('st, 'ev) LTS \<Rightarrow> 'ev TrB set" where
  "traces3_B l \<equiv> 
     { ([], accepted_events l s) | s . s \<in> init l }
   \<union> { (map lbl (exe r), accepted_events l (fin r)) | r . r \<in> runs3 l \<and> exe r \<noteq> [] }"


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
  "([], INTER (init l) (accepted_events l)) \<in> traces_B l"
unfolding traces_B_def
by (simp add: image_iff run_accepted_events_def run_trace_def runs.base)

lemma run3_trace_empty_inv:
  "\<lbrakk> s \<in> init l \<rbrakk> \<Longrightarrow>
    ([], accepted_events l s) \<in> traces3_B l"
using traces3_B_def by fastforce

lemma run3_trace_inv:
assumes "run \<in> runs3 l" and "exe run \<noteq> []" and "t \<in> outgoing l (fin run)"
shows "(map lbl (exe run) @ [lbl t], accepted_events l (dst t)) \<in> traces3_B l"
proof -
  from assms have "\<lparr> ini = ini run, exe = exe run @ [t] \<rparr> \<in> runs3 l" by (rule runs3.step)
  moreover
  have "run3_trace l \<lparr> ini = ini run, exe = (exe run) @ [t] \<rparr> = (map lbl (exe run) @ [lbl t], accepted_events l (dst t))"
    unfolding run3_trace_def accepted_events_def run3_accepted_events_def fin_def
    by (simp add: list.case_eq_if)
  ultimately show ?thesis
  unfolding traces3_B_def
  by (metis (mono_tags, lifting) CollectI Run3.select_convs(2) UnI2 append_is_Nil_conv assms(2) run3_accepted_events_def run3_trace_def)
qed

lemma run_trace_inv:
assumes "run \<in> runs l" and "run \<noteq> []" and "t \<in> outgoing l (dst (last run))"
shows "(map lbl run @ [lbl t], accepted_events l (dst t)) \<in> traces_B l"
proof -
  from assms have "run @ [t] \<in> runs l" by (rule runs.step)
  moreover
  have "run_trace l (run @ [t]) = (map lbl run @ [lbl t], accepted_events l (dst t))"
    unfolding run_trace_def run_accepted_events_def by auto
  ultimately show ?thesis
    unfolding traces_B_def using image_iff by fastforce
qed

lemma sim_init_accepted:
  assumes "l \<preceq>B l'"
  shows "INTER (init l') (accepted_events l') \<subseteq> INTER (init l) (accepted_events l)"
  using assms unfolding simulated_B_def simulation_B_def by blast

text {*
  The following theorem establishes a property on the traces of LTSes
  that relate through the (B inspired notion of) simulation.
*}
lemma sim_traces_B:
  assumes sim: "l \<preceq>B l'" and tr: "(tr, acc) \<in> traces_B l"
  shows "\<exists> (tr', acc') \<in> traces_B l'.
            length tr' \<le> length tr
          \<and> (\<forall>i<length tr'. tr'!i = tr!i)
          \<and> (if length tr' < length tr
             then tr!(length tr') \<notin> acc'
             else acc' \<subseteq> acc)"
    (is "\<exists>(tr',acc') \<in> _. ?P tr' acc'")
proof -
  from sim obtain r where r: "(l,l') \<in> simulation_B r"
    by (auto simp: simulated_B_def)
  from tr obtain run where
    run: "run \<in> runs l" "tr = map lbl run" "acc = run_accepted_events l run"
    by (auto simp: traces_B_def run_trace_def)
  with r obtain run' where
    run': "run' \<in> runs l'" "maximal_similar_runs r l l' run run'"
    by (blast dest: simulation_B_maximal_similar_runs)
  let ?tr' = "map lbl run'"
  let ?acc' = "run_accepted_events l' run'"
  from run' have "(?tr',?acc') \<in> traces_B l'"
    by (auto simp: traces_B_def run_trace_def)
  moreover
  from run' run have "length ?tr' \<le> length tr" "\<forall>i < length ?tr'. ?tr'!i = tr!i"
    unfolding maximal_similar_runs_def sim_transition_def by auto
  moreover
  have "if length ?tr' < length tr then tr!(length ?tr') \<notin> ?acc' else ?acc' \<subseteq> acc"
  proof (cases "length ?tr' < length tr")
    case True
    with run have len: "length run' < length run" by simp
    have "tr!(length ?tr') \<notin> ?acc'"
    proof (cases "run' = []")
      case True
      from len run have "src (hd run) \<in> init l"
        by (auto intro: run_starts_initial)
      with r obtain s' where s': "s' \<in> init l'" "(src (hd run), s') \<in> r"
        unfolding simulation_B_def by blast
      with len run' True have "lbl (hd run) \<notin> accepted_events l' s'"
        unfolding maximal_similar_runs_def by auto
      with s' True have "lbl (hd run) \<notin> ?acc'"
        unfolding run_accepted_events_def by auto
      with run True len show ?thesis 
        by (auto simp: hd_conv_nth)
    next
      case False
      with len run' run show ?thesis
        unfolding maximal_similar_runs_def run_accepted_events_def by auto
    qed
    with True show ?thesis by simp
  next
    case False
    with run' run have len: "length run' = length run"
      unfolding maximal_similar_runs_def by simp
    have "?acc' \<subseteq> acc"
    proof (cases "length run = 0")
      case True
      with len have "run = []" "run' = []" by auto
      with run sim_init_accepted[OF sim] show ?thesis
        by (simp add: run_accepted_events_def)
    next
      case False
      with len run' have "(last run, last run') \<in> sim_transition r"
        unfolding maximal_similar_runs_def
        by (metis One_nat_def diff_less last_conv_nth length_0_conv length_greater_0_conv zero_less_Suc)
      hence "(dst (last run), dst (last run')) \<in> r"
        by (simp add: sim_transition_def)
      with r run False len show ?thesis
        unfolding simulation_B_def run_accepted_events_def by auto
    qed
    with False show ?thesis by simp
  qed
  ultimately show ?thesis by blast
qed

lemma sim_traces3_B:
  assumes sim: "l \<preceq>B l'" and tr: "(ts, acc) \<in> traces3_B l"
  shows "\<exists> (ts', acc') \<in> traces_B l'.
            length ts' \<le> length ts
          \<and> (\<forall>i<length ts'. ts'!i = ts!i)
          \<and> (if length ts' < length ts
             then ts!(length ts') \<notin> acc'
             else acc' \<subseteq> acc)"
    (is "\<exists>(ts',acc') \<in> _. ?P ts' acc'")
proof -
  from sim obtain r where r: "(l,l') \<in> simulation_B r"
    by (auto simp: simulated_B_def)
  from tr obtain run where
    run: "run \<in> runs3 l" "ts = map lbl (exe run)" "acc = run3_accepted_events l run"
    unfolding traces3_B_def run3_accepted_events_def
    by (smt CollectD Pair_inject Run3.select_convs(1) Run3.select_convs(2) Un_iff fin_def list.case_eq_if list.simps(8) runs3.base)
  with r obtain run' where
    run': "run' \<in> runs3 l'" "maximal_similar_runs3 r l l' run run'"
    using simulation_B_maximal_similar_runs3
    by blast
  let ?ts' = "map lbl (exe run')"
  let ?acc' = "run3_accepted_events l' run'"
  from run' have "(?ts',?acc') \<in> traces3_B l'"
    by (smt CollectI UnI2 fin_def list.case_eq_if list.simps(8) run3_accepted_events_def run3_ini_initial run3_trace_empty_inv traces3_B_def)
  from run' run have "length ?ts' \<le> length ts" "\<forall>i < length ?ts'. ?ts'!i = ts!i"
    unfolding maximal_similar_runs3_def sim_transition_def
    apply auto[1]
    sorry
  moreover
    have "if length ?ts' < length ts then ts!(length ?ts') \<notin> ?acc' else ?acc' \<subseteq> acc"
    sorry
  ultimately show ?thesis
  sorry
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
*)